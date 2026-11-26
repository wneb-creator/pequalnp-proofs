import PEqualNP.Defs
import Mathlib.Data.Multiset.AddSub
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_meta_2590

namespace OnceResource

abbrev State := ℕ × List ℕ × List ℕ × Bool

def values (bits : ℕ) : List ℕ := (List.range 64).filter bits.testBit

def pairMasks (op : ℕ → ℕ → ℕ) (a b : ℕ) : ℕ :=
  (values a).foldl (fun acc x =>
    (values b).foldl (fun acc y => acc ||| (1 <<< op x y)) acc) 0

def mergePools (a b : ℕ) : ℕ := pairMasks (· ||| ·) a b

def addCarrier (pool k : ℕ) : ℕ := pool ||| mergePools pool (1 <<< k)

def live (used loc : ℕ) : Bool :=
  if loc = 0 then !used.testBit 0
  else if loc < 4 then !used.testBit 0 || !used.testBit loc
  else !used.testBit (loc - 3)

def prune (s : State) : State :=
  (s.1, (List.range 7).map (fun i =>
    if live s.1 i then s.2.1.getD i 1 else 1), s.2.2.1, s.2.2.2)

def sortedInsert (k : ℕ) : List ℕ → List ℕ
  | [] => [k]
  | x :: xs => if k ≤ x then k :: x :: xs else x :: sortedInsert k xs

def zeroSort : List ℕ → List ℕ
  | [] => []
  | x :: xs => sortedInsert x (zeroSort xs)

def insertZero (k : ℕ) (zs : List ℕ) : List ℕ := zeroSort (k :: zs)

def basis : ℕ → ℕ | 0 => 0 | 1 => 25 | 2 => 42 | _ => 52

def rightPool (ps : List ℕ) (g : ℕ) : ℕ :=
  if g = 0 then mergePools (mergePools (ps.getD 1 1) (ps.getD 2 1)) (ps.getD 3 1)
  else mergePools (1 <<< basis g) (ps.getD (g + 3) 1)

def groupNext (s : State) : List State :=
  (List.range 4).flatMap fun g =>
    if s.1.testBit g then [] else
    (values (pairMasks (· &&& ·) (s.2.1.getD g 1) (rightPool s.2.1 g))).filterMap
      fun k => if k = 0 then none else
        some (prune (s.1 ||| (1 <<< g), s.2.1, insertZero k s.2.2.1, s.2.2.2))

def forkNext (s : State) : List State :=
  if s.2.2.2 then [] else s.2.2.1.map fun k =>
    prune (s.1, s.2.1, insertZero k s.2.2.1, true)

def liftNext (s : State) : List State :=
  s.2.2.1.flatMap fun k => (List.range 7).filterMap fun loc =>
    if live s.1 loc then
      let old := s.2.1.getD loc 1
      let new := addCarrier old k
      if new = old then none else
        some (prune (s.1, s.2.1.set loc new, s.2.2.1.erase k, s.2.2.2))
    else none

def discardNext (s : State) : List State :=
  s.2.2.1.map fun k => prune (s.1, s.2.1, s.2.2.1.erase k, s.2.2.2)

def combineNext (s : State) : List State :=
  s.2.2.1.flatMap fun a => (s.2.2.1.erase a).flatMap fun b =>
    [a &&& b, a ||| b].filterMap fun k => if k = 0 then none else
      some (prune (s.1, s.2.1, insertZero k ((s.2.2.1.erase a).erase b), s.2.2.2))

def successors (s : State) : List State :=
  groupNext s ++ forkNext s ++ liftNext s ++ discardNext s ++ combineNext s

def initial : State := (0, List.replicate 7 1, [63], false)

def listLess : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then listLess as bs else decide (a < b)

def stateLess (a b : State) : Bool :=
  if a.1 ≠ b.1 then decide (a.1 < b.1)
  else if a.2.1 ≠ b.2.1 then listLess a.2.1 b.2.1
  else if a.2.2.1 ≠ b.2.2.1 then listLess a.2.2.1 b.2.2.1
  else !a.2.2.2 && b.2.2.2

def safe (s : State) : Bool := !s.2.2.1.contains 56


lemma mem_values_iff {bits x : ℕ} : x ∈ values bits ↔ x < 64 ∧ bits.testBit x = true := by
  simp [values]

lemma testBit_singleton_iff {k x : ℕ} : (1 <<< k : ℕ).testBit x = true ↔ k = x := by
  simp [Nat.shiftLeft_eq, Nat.testBit_two_pow]

lemma testBit_fold_or_iff (xs : List ℕ) (f : ℕ → ℕ) (acc z : ℕ) :
    (xs.foldl (fun a x => a ||| f x) acc).testBit z = true ↔
      acc.testBit z = true ∨ ∃ x ∈ xs, (f x).testBit z = true := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons, ih, or_assoc]

lemma testBit_fold_pairs_iff (xs ys : List ℕ) (op : ℕ → ℕ → ℕ) (acc z : ℕ) :
    (xs.foldl (fun acc x => ys.foldl (fun acc y => acc ||| (1 <<< op x y)) acc) acc).testBit z = true ↔
      acc.testBit z = true ∨ ∃ x ∈ xs, ∃ y ∈ ys, op x y = z := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, testBit_fold_or_iff, testBit_singleton_iff]
    simp [or_assoc]

lemma mem_pairMasks_iff {op : ℕ → ℕ → ℕ} {a b z : ℕ} :
    z ∈ values (pairMasks op a b) ↔
      z < 64 ∧ ∃ x ∈ values a, ∃ y ∈ values b, op x y = z := by
  simp [mem_values_iff, pairMasks, testBit_fold_pairs_iff]

lemma mem_pairMasks {op : ℕ → ℕ → ℕ} {a b x y : ℕ}
    (hx : x ∈ values a) (hy : y ∈ values b) (hxy : op x y < 64) :
    op x y ∈ values (pairMasks op a b) := by
  exact mem_pairMasks_iff.mpr ⟨hxy, x, hx, y, hy, rfl⟩

lemma mem_singleton_iff {k x : ℕ} :
    x ∈ values (1 <<< k) ↔ x < 64 ∧ k = x := by
  rw [mem_values_iff, testBit_singleton_iff]

lemma mem_singleton {k : ℕ} (hk : k < 64) : k ∈ values (1 <<< k) := by
  exact mem_singleton_iff.mpr ⟨hk, rfl⟩

lemma or_lt_64 {x y : ℕ} (hx : x < 64) (hy : y < 64) : x ||| y < 64 := by
  exact Nat.or_lt_two_pow (n := 6) hx hy

lemma mem_addCarrier_of_mem {p k x : ℕ} (hx : x ∈ values p) :
    x ∈ values (addCarrier p k) := by
  obtain ⟨hxb, hxt⟩ := mem_values_iff.mp hx
  apply mem_values_iff.mpr
  simp [addCarrier, hxb, hxt]

lemma mem_addCarrier_or {p k x : ℕ} (hx : x ∈ values p) (hk : k < 64) :
    x ||| k ∈ values (addCarrier p k) := by
  apply mem_values_iff.mpr
  have hb := or_lt_64 (mem_values_iff.mp hx).1 hk
  have hm := mem_pairMasks (op := (· ||| ·)) hx (mem_singleton hk) hb
  have ht := (mem_values_iff.mp hm).2
  simp [addCarrier, mergePools, hb, ht]

lemma mem_addCarrier_iff {p k z : ℕ} (hk : k < 64) :
    z ∈ values (addCarrier p k) ↔
      z ∈ values p ∨ ∃ x ∈ values p, x ||| k = z := by
  constructor
  · intro hz
    obtain ⟨hzb, hzt⟩ := mem_values_iff.mp hz
    simp only [addCarrier, Nat.testBit_or, Bool.or_eq_true] at hzt
    rcases hzt with hp | hm
    · exact Or.inl (mem_values_iff.mpr ⟨hzb, hp⟩)
    · have hm' : z ∈ values (pairMasks (· ||| ·) p (1 <<< k)) :=
        mem_values_iff.mpr ⟨hzb, hm⟩
      obtain ⟨_, x, hx, y, hy, heq⟩ := mem_pairMasks_iff.mp hm'
      obtain ⟨_, rfl⟩ := mem_singleton_iff.mp hy
      exact Or.inr ⟨x, hx, heq⟩
  · rintro (hz | ⟨x, hx, rfl⟩)
    · exact mem_addCarrier_of_mem hz
    · exact mem_addCarrier_or hx hk

lemma addCarrier_or_closed {p k : ℕ} (hk : k < 64)
    (hclosed : ∀ x ∈ values p, ∀ y ∈ values p, x ||| y ∈ values p) :
    ∀ x ∈ values (addCarrier p k), ∀ y ∈ values (addCarrier p k),
      x ||| y ∈ values (addCarrier p k) := by
  intro x hx y hy
  rcases (mem_addCarrier_iff hk).mp hx with hx | ⟨a, ha, rfl⟩
  · rcases (mem_addCarrier_iff hk).mp hy with hy | ⟨b, hb, rfl⟩
    · exact mem_addCarrier_of_mem (hclosed x hx y hy)
    · rw [← Nat.or_assoc]
      exact mem_addCarrier_or (hclosed x hx b hb) hk
  · rcases (mem_addCarrier_iff hk).mp hy with hy | ⟨b, hb, rfl⟩
    · have heq : (a ||| k) ||| y = (a ||| y) ||| k := by ac_rfl
      rw [heq]
      exact mem_addCarrier_or (hclosed a ha y hy) hk
    · have heq : (a ||| k) ||| (b ||| k) = (a ||| b) ||| (k ||| k) := by ac_rfl
      rw [heq, Nat.or_self]
      exact mem_addCarrier_or (hclosed a ha b hb) hk

lemma addCarrier_zero_and_or_closed {p k : ℕ} (hk : k < 64)
    (hzero : 0 ∈ values p)
    (hclosed : ∀ x ∈ values p, ∀ y ∈ values p, x ||| y ∈ values p) :
    0 ∈ values (addCarrier p k) ∧
      ∀ x ∈ values (addCarrier p k), ∀ y ∈ values (addCarrier p k),
        x ||| y ∈ values (addCarrier p k) := by
  exact ⟨mem_addCarrier_of_mem hzero, addCarrier_or_closed hk hclosed⟩

end OnceResource
section CommonPrefixScope

def edgeFn (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

end CommonPrefixScope

namespace OnceGeometry

def rowSet (r : Fin 6) : Finset (Fin 10) :=
  match r.val with
  | 0 => {2, 6}
  | 1 => {3, 9}
  | 2 => {7, 8}
  | 3 => {2, 3}
  | 4 => {6, 8}
  | _ => {7, 9}

def vertexClass (v : Fin 10) : Fin 7 :=
  match v.val with
  | 0 => 0
  | 1 => 1
  | 4 => 2
  | 5 => 3
  | 2 => 4
  | 6 => 4
  | 3 => 5
  | 9 => 5
  | _ => 6

def port (g : Fin 4) (right : Bool) : Finset (Fin 10) :=
  if right then match g.val with
    | 0 => {1, 4, 5}
    | 1 => {2, 6}
    | 2 => {3, 9}
    | _ => {7, 8}
  else match g.val with
    | 0 => {0}
    | 1 => {1}
    | 2 => {4}
    | _ => {5}

def locations (g : Fin 4) (right : Bool) : Finset (Fin 7) :=
  if right then match g.val with
    | 0 => {1, 2, 3}
    | 1 => {4}
    | 2 => {5}
    | _ => {6}
  else {⟨g.val, by omega⟩}

lemma port_class : ∀ (g : Fin 4) (b : Bool) (v : Fin 10),
    v ∈ port g b ↔ vertexClass v ∈ locations g b := by decide

lemma support_class {S : Finset (Fin 10)} {g : Fin 4} {b : Bool}
    (hS : S ⊆ port g b) {v : Fin 10} (hv : v ∈ S) :
    vertexClass v ∈ locations g b := (port_class g b v).mp (hS hv)

lemma port_locations_live {used : ℕ} (hu : used < 16) {g : Fin 4}
    (hg : used.testBit g.val = false) (b : Bool) {loc : Fin 7}
    (hl : loc ∈ locations g b) : OnceResource.live used loc.val = true := by
  have h : ∀ (u : Fin 16) (g : Fin 4) (b : Bool) (loc : Fin 7),
      u.val.testBit g.val = false → loc ∈ locations g b →
      OnceResource.live u.val loc.val = true := by decide
  exact h ⟨used, hu⟩ g b loc hg hl

def bits (f : Fin 6 → Bool) : BitVec 6 :=
  BitVec.ofBoolListLE [f 0, f 1, f 2, f 3, f 4, f 5]

def mask (f : Fin 6 → Bool) : ℕ := (bits f).toNat

lemma bits_get (f : Fin 6 → Bool) (r : Fin 6) : (bits f).getLsbD r.val = f r := by
  unfold bits
  rw [BitVec.getLsbD_ofBoolListLE]
  fin_cases r <;> rfl

lemma bits_or (f g : Fin 6 → Bool) : bits (fun r => f r || g r) = bits f ||| bits g := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hf := bits_get f ⟨i, hi⟩
  have hg := bits_get g ⟨i, hi⟩
  have hr := bits_get (fun r => f r || g r) ⟨i, hi⟩
  simpa only [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_or] using hr.trans (congrArg₂ (· || ·) hf.symm hg.symm)

lemma bits_and (f g : Fin 6 → Bool) : bits (fun r => f r && g r) = bits f &&& bits g := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hf := bits_get f ⟨i, hi⟩
  have hg := bits_get g ⟨i, hi⟩
  have hr := bits_get (fun r => f r && g r) ⟨i, hi⟩
  simpa only [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_and] using hr.trans (congrArg₂ (· && ·) hf.symm hg.symm)

lemma mask_or (f g : Fin 6 → Bool) : mask (fun r => f r || g r) = mask f ||| mask g := by
  simp [mask, bits_or]

lemma mask_and (f g : Fin 6 → Bool) : mask (fun r => f r && g r) = mask f &&& mask g := by
  simp [mask, bits_and]

lemma mask_lt (f : Fin 6 → Bool) : mask f < 64 := by
  exact (bits f).isLt

lemma mask_testBit (f : Fin 6 → Bool) (r : Fin 6) : (mask f).testBit r.val = f r :=
  bits_get f r

lemma mask_injective : Function.Injective mask := by
  intro f g h
  funext r
  rw [← mask_testBit f r, ← mask_testBit g r, h]

def rawMask (S : Finset (Fin 10)) : ℕ :=
  mask (fun r => decide ((S ∩ rowSet r).Nonempty))

lemma rawMask_port : ∀ (g : Fin 4) (b : Bool),
    rawMask (port g b) = if b then OnceResource.basis g.val else 0 := by decide

lemma petersen_rows : ∀ r : Fin 6,
    edgeFn (fun v => decide (v ∈ rowSet r)) = decide (3 ≤ r.val) := by decide

lemma petersen_mask : mask (fun r => edgeFn (fun v => decide (v ∈ rowSet r))) = 56 := by decide

lemma rawMask_empty : rawMask ∅ = 0 := by decide

lemma rawMask_union (S T : Finset (Fin 10)) : rawMask (S ∪ T) = rawMask S ||| rawMask T := by
  unfold rawMask
  have h : (fun r => decide (((S ∪ T) ∩ rowSet r).Nonempty)) =
      (fun r => decide ((S ∩ rowSet r).Nonempty) || decide ((T ∩ rowSet r).Nonempty)) := by
    funext r
    simp [Finset.union_inter_distrib_right]
  rw [h, mask_or]

end OnceGeometry

namespace OncePositive

open OnceResource OnceGeometry

abbrev Pools := Fin 7 → ℕ

def or7 (f : Fin 7 → ℕ) : ℕ :=
  f 0 ||| f 1 ||| f 2 ||| f 3 ||| f 4 ||| f 5 ||| f 6

def PoolsGood (P : Pools) : Prop := ∀ i,
  0 ∈ values (P i) ∧ ∀ a ∈ values (P i), ∀ b ∈ values (P i), a ||| b ∈ values (P i)

def Witness (P : Pools) (L : Finset (Fin 7)) (f : Fin 7 → ℕ) : Prop :=
  ∀ i, f i ∈ values (P i) ∧ (i ∉ L → f i = 0)

def Rep (used : ℕ) (P : Pools) (S : Finset (Fin 10)) (m : ℕ) : Prop :=
  ∀ (g : Fin 4) (b : Bool), used.testBit g.val = false → S ⊆ port g b →
    ∃ f, Witness P (locations g b) f ∧ m = rawMask S ||| or7 f

def liftPool (P : Pools) (loc : Fin 7) (k : ℕ) : Pools :=
  Function.update P loc (addCarrier (P loc) k)

lemma or7_or (f h : Fin 7 → ℕ) :
    or7 (fun i => f i ||| h i) = or7 f ||| or7 h := by
  dsimp only [or7]
  ac_rfl

lemma or7_update (f : Fin 7 → ℕ) (loc : Fin 7) (k : ℕ) :
    or7 (Function.update f loc (f loc ||| k)) = or7 f ||| k := by
  fin_cases loc <;> simp [or7, Function.update]
  all_goals
    generalize f (0 : Fin 7) = x0
    generalize f (1 : Fin 7) = x1
    generalize f (2 : Fin 7) = x2
    generalize f (3 : Fin 7) = x3
    generalize f (4 : Fin 7) = x4
    generalize f (5 : Fin 7) = x5
    generalize f (6 : Fin 7) = x6
    ac_rfl

lemma rep_raw {used : ℕ} {P : Pools} (hp : PoolsGood P) (S : Finset (Fin 10)) :
    Rep used P S (rawMask S) := by
  intro g b _ _
  refine ⟨fun _ => 0, ?_, ?_⟩
  · exact fun i => ⟨(hp i).1, fun _ => rfl⟩
  · simp [or7]

lemma rep_or {used : ℕ} {P : Pools} (hp : PoolsGood P)
    {S T : Finset (Fin 10)} {a b : ℕ} (ha : Rep used P S a) (hb : Rep used P T b) :
    Rep used P (S ∪ T) (a ||| b) := by
  intro g side hu hST
  have hS : S ⊆ port g side := fun v hv => hST (Finset.mem_union_left _ hv)
  have hT : T ⊆ port g side := fun v hv => hST (Finset.mem_union_right _ hv)
  obtain ⟨f, hf, ha⟩ := ha g side hu hS
  obtain ⟨h, hh, hb⟩ := hb g side hu hT
  refine ⟨fun i => f i ||| h i, ?_, ?_⟩
  · intro i
    refine ⟨(hp i).2 _ (hf i).1 _ (hh i).1, ?_⟩
    intro hi
    change f i ||| h i = 0
    rw [(hf i).2 hi, (hh i).2 hi]
    rfl
  · rw [ha, hb, rawMask_union, or7_or]
    ac_rfl

lemma rep_mono {used : ℕ} {P Q : Pools} {S : Finset (Fin 10)} {m : ℕ}
    (hPQ : ∀ i x, x ∈ values (P i) → x ∈ values (Q i))
    (h : Rep used P S m) : Rep used Q S m := by
  intro g b hg hS
  obtain ⟨f, hf, hm⟩ := h g b hg hS
  exact ⟨f, fun i => ⟨hPQ i _ (hf i).1, (hf i).2⟩, hm⟩

lemma liftPool_mono (P : Pools) (loc : Fin 7) (k : ℕ) :
    ∀ i x, x ∈ values (P i) → x ∈ values (liftPool P loc k i) := by
  intro i x hx
  by_cases hi : i = loc
  · subst i
    simpa [liftPool] using mem_addCarrier_of_mem (k := k) hx
  · simpa [liftPool, hi] using hx

lemma poolsGood_lift {P : Pools} (hp : PoolsGood P) (loc : Fin 7) {k : ℕ} (hk : k < 64) :
    PoolsGood (liftPool P loc k) := by
  intro i
  by_cases hi : i = loc
  · subst i
    simpa [liftPool] using addCarrier_zero_and_or_closed hk (hp loc).1 (hp loc).2
  · simpa [liftPool, hi] using hp i

lemma rep_lift {used : ℕ} {P : Pools} {S : Finset (Fin 10)} {m k : ℕ}
    (h : Rep used P S m) (hk : k < 64) {v : Fin 10} (hv : v ∈ S) :
    Rep used (liftPool P (vertexClass v) k) S (m ||| k) := by
  intro g b hg hS
  have hvL := support_class hS hv
  obtain ⟨f, hf, hm⟩ := h g b hg hS
  refine ⟨Function.update f (vertexClass v) (f (vertexClass v) ||| k), ?_, ?_⟩
  · intro i
    by_cases hi : i = vertexClass v
    · subst i
      constructor
      · simpa [liftPool] using mem_addCarrier_or (hf (vertexClass v)).1 hk
      · intro hnot
        exact False.elim (hnot hvL)
    · simpa [liftPool, Function.update_apply, hi] using hf i
  · rw [or7_update, hm]
    ac_rfl

lemma rep_restrict_pools {old new : ℕ} {P Q : Pools} {S : Finset (Fin 10)} {m : ℕ}
    (hgroups : ∀ g : Fin 4, new.testBit g.val = false → old.testBit g.val = false)
    (hzero : ∀ i, 0 ∈ values (Q i))
    (hpools : ∀ (g : Fin 4) (b : Bool), new.testBit g.val = false →
      ∀ i ∈ locations g b, Q i = P i)
    (h : Rep old P S m) : Rep new Q S m := by
  intro g b hg hS
  obtain ⟨f, hf, hm⟩ := h g b (hgroups g hg) hS
  refine ⟨f, ?_, hm⟩
  intro i
  refine ⟨?_, (hf i).2⟩
  by_cases hi : i ∈ locations g b
  · rw [hpools g b hg i hi]
    exact (hf i).1
  · rw [(hf i).2 hi]
    exact hzero i

end OncePositive

namespace OncePositive

open OnceResource OnceGeometry

def rightChoices (P : Pools) (g : Fin 4) : ℕ :=
  match g.val with
  | 0 => mergePools (mergePools (P 1) (P 2)) (P 3)
  | 1 => mergePools (1 <<< 25) (P 4)
  | 2 => mergePools (1 <<< 42) (P 5)
  | _ => mergePools (1 <<< 52) (P 6)

def portChoices (P : Pools) (g : Fin 4) (b : Bool) : ℕ :=
  if b then rightChoices P g else P ⟨g.val, by omega⟩

def poolView (ps : List ℕ) : Pools := fun i => ps.getD i.val 1

lemma portChoices_view (ps : List ℕ) (g : Fin 4) (b : Bool) :
    portChoices (poolView ps) g b =
      if b then rightPool ps g.val else ps.getD g.val 1 := by
  fin_cases g <;> cases b <;> rfl

lemma or7_filtered {L : Finset (Fin 7)} {f : Fin 7 → ℕ}
    (hf : ∀ i, i ∉ L → f i = 0) :
    or7 f = or7 (fun i => if i ∈ L then f i else 0) := by
  congr 1
  funext i
  by_cases hi : i ∈ L
  · simp [hi]
  · simp [hi, hf i hi]

lemma merge_mem {p q a b : ℕ} (ha : a ∈ values p) (hb : b ∈ values q) :
    a ||| b ∈ values (mergePools p q) := by
  exact mem_pairMasks ha hb (or_lt_64 (mem_values_iff.mp ha).1 (mem_values_iff.mp hb).1)

lemma portChoices_membership (P : Pools) (g : Fin 4) (b : Bool) (f : Fin 7 → ℕ)
    (hf : ∀ i, f i ∈ values (P i)) :
    rawMask (port g b) ||| or7 (fun i => if i ∈ locations g b then f i else 0) ∈
      values (portChoices P g b) := by
  rw [rawMask_port]
  fin_cases g <;> cases b
  · simpa [portChoices, locations, or7] using hf 0
  · simpa [portChoices, rightChoices, locations, or7, basis] using
      merge_mem (merge_mem (hf 1) (hf 2)) (hf 3)
  · simpa [portChoices, locations, or7] using hf 1
  · simpa [portChoices, rightChoices, locations, or7, basis] using
      merge_mem (mem_singleton (by decide : 25 < 64)) (hf 4)
  · simpa [portChoices, locations, or7] using hf 2
  · simpa [portChoices, rightChoices, locations, or7, basis] using
      merge_mem (mem_singleton (by decide : 42 < 64)) (hf 5)
  · simpa [portChoices, locations, or7] using hf 3
  · simpa [portChoices, rightChoices, locations, or7, basis] using
      merge_mem (mem_singleton (by decide : 52 < 64)) (hf 6)

lemma rep_port_mem {used : ℕ} {P : Pools} {g : Fin 4} {b : Bool} {m : ℕ}
    (h : Rep used P (port g b) m) (hu : used.testBit g.val = false) :
    m ∈ values (portChoices P g b) := by
  obtain ⟨f, hf, hm⟩ := h g b hu (Finset.Subset.refl _)
  rw [hm, or7_filtered (fun i => (hf i).2)]
  exact portChoices_membership P g b f (fun i => (hf i).1)

lemma group_candidate {used : ℕ} {P : Pools} {g : Fin 4} {a b : ℕ}
    (ha : Rep used P (port g false) a) (hb : Rep used P (port g true) b)
    (hu : used.testBit g.val = false) (hab : a &&& b < 64) :
    a &&& b ∈ values (pairMasks (· &&& ·) (P ⟨g.val, by omega⟩) (rightChoices P g)) := by
  have hleft := rep_port_mem ha hu
  have hright := rep_port_mem hb hu
  exact mem_pairMasks hleft hright hab

end OncePositive

namespace S18Resource

abbrev State := Nat × List Nat × List Nat

def values (bits : Nat) : List Nat := (List.range 64).filter bits.testBit

def pairMasks (op : Nat → Nat → Nat) (a b : Nat) : Nat :=
  (values a).foldl (fun acc x =>
    (values b).foldl (fun acc y => acc ||| (1 <<< op x y)) acc) 0

def mergePools (a b : Nat) : Nat := pairMasks (· ||| ·) a b

def addCarrier (pool k : Nat) : Nat := pool ||| mergePools pool (1 <<< k)

def live (used loc : Nat) : Bool :=
  if loc = 0 then !used.testBit 0
  else if loc = 1 then !used.testBit 0 || !used.testBit 1 || !used.testBit 4
  else if loc = 2 then !used.testBit 0 || !used.testBit 1 || !used.testBit 2
  else if loc = 3 then !used.testBit 0 || !used.testBit 3
  else !used.testBit (loc - 3)

def prune (s : State) : State :=
  (s.1, (List.range 7).map (fun i =>
    if live s.1 i then s.2.1.getD i 1 else 1), s.2.2)

def sortedInsert (k : Nat) : List Nat → List Nat
  | [] => [k]
  | x :: xs => if k ≤ x then k :: x :: xs else x :: sortedInsert k xs

def zeroSort : List Nat → List Nat
  | [] => []
  | x :: xs => sortedInsert x (zeroSort xs)

def insertZero (k : Nat) (zs : List Nat) : List Nat := zeroSort (k :: zs)

def basis : Nat → Nat | 0 => 0 | 1 => 25 | 2 => 42 | _ => 52

def leftPool (ps : List Nat) (g : Nat) : Nat :=
  if g = 1 then mergePools (ps.getD 1 1) (ps.getD 2 1)
  else ps.getD g 1

def rightPool (ps : List Nat) (g : Nat) : Nat :=
  if g = 0 then mergePools (mergePools (ps.getD 1 1) (ps.getD 2 1)) (ps.getD 3 1)
  else mergePools (1 <<< basis g) (ps.getD (g + 3) 1)

def groupNext (s : State) : List State :=
  (List.range 4).flatMap fun g =>
    if s.1.testBit g then [] else
    (values (pairMasks (· &&& ·) (leftPool s.2.1 g) (rightPool s.2.1 g))).filterMap
      fun k => if k = 0 then none else
        some (prune (s.1 ||| (1 <<< g), s.2.1, insertZero k s.2.2))

def filterNext (s : State) : List State :=
  if s.1.testBit 4 then [] else
    s.2.2.flatMap fun k => (values (s.2.1.getD 1 1)).filterMap fun carrier =>
      let result := k &&& carrier
      if result = 0 then none else
        some (prune (s.1 ||| 16, s.2.1, insertZero result (s.2.2.erase k)))

def liftNext (s : State) : List State :=
  s.2.2.flatMap fun k => (List.range 7).filterMap fun loc =>
    if live s.1 loc then
      let old := s.2.1.getD loc 1
      let new := addCarrier old k
      if new = old then none else
        some (prune (s.1, s.2.1.set loc new, s.2.2.erase k))
    else none

def discardNext (s : State) : List State :=
  s.2.2.map fun k => prune (s.1, s.2.1, s.2.2.erase k)

def combineNext (s : State) : List State :=
  s.2.2.flatMap fun a => (s.2.2.erase a).flatMap fun b =>
    [a &&& b, a ||| b].filterMap fun k => if k = 0 then none else
      some (prune (s.1, s.2.1, insertZero k ((s.2.2.erase a).erase b)))

def successors (s : State) : List State :=
  groupNext s ++ filterNext s ++ liftNext s ++ discardNext s ++ combineNext s

-- Bit 5 records the distinguished dirty group, already used to create the seed.
def initial : State := (32, List.replicate 7 1, [63])

def listLess : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then listLess as bs else decide (a < b)

def stateLess (a b : State) : Bool :=
  if a.1 ≠ b.1 then decide (a.1 < b.1)
  else if a.2.1 ≠ b.2.1 then listLess a.2.1 b.2.1
  else listLess a.2.2 b.2.2

def safe (s : State) : Bool := !s.2.2.contains 56

end S18Resource

namespace S18Geometry

open OnceGeometry

def port (g : Fin 5) (right : Bool) : Finset (Fin 10) :=
  if right then match g.val with
    | 0 => {1, 4, 5}
    | 1 => {2, 6}
    | 2 => {3, 9}
    | 3 => {7, 8}
    | _ => {1}
  else match g.val with
    | 0 => {0}
    | 1 => {1, 4}
    | 2 => {4}
    | 3 => {5}
    | _ => ∅

def locations (g : Fin 5) (right : Bool) : Finset (Fin 7) :=
  if right then match g.val with
    | 0 => {1, 2, 3}
    | 1 => {4}
    | 2 => {5}
    | 3 => {6}
    | _ => {1}
  else match g.val with
    | 0 => {0}
    | 1 => {1, 2}
    | 2 => {2}
    | 3 => {3}
    | _ => ∅

def consumers (loc : Fin 7) : Finset (Fin 5) :=
  match loc.val with
  | 0 => {0}
  | 1 => {0, 1, 4}
  | 2 => {0, 1, 2}
  | 3 => {0, 3}
  | 4 => {1}
  | 5 => {2}
  | _ => {3}

lemma port_class : ∀ (g : Fin 5) (b : Bool) (v : Fin 10),
    v ∈ port g b ↔ vertexClass v ∈ locations g b := by decide

lemma support_class {S : Finset (Fin 10)} {g : Fin 5} {b : Bool}
    (hS : S ⊆ port g b) {v : Fin 10} (hv : v ∈ S) :
    vertexClass v ∈ locations g b := (port_class g b v).mp (hS hv)

lemma consumer_iff : ∀ (g : Fin 5) (loc : Fin 7),
    g ∈ consumers loc ↔ ∃ b : Bool, loc ∈ locations g b := by decide

lemma port_locations_live {used : ℕ} {g : Fin 5}
    (hg : used.testBit g.val = false) (b : Bool) {loc : Fin 7}
    (hl : loc ∈ locations g b) : S18Resource.live used loc.val = true := by
  fin_cases g <;> cases b <;> fin_cases loc <;>
    simp_all [locations, S18Resource.live]

lemma live_mark_dirty (used : ℕ) (loc : Fin 7) :
    S18Resource.live (used ||| 32) loc.val = S18Resource.live used loc.val := by
  have h1 : Nat.testBit 32 1 = false := by decide
  have h2 : Nat.testBit 32 2 = false := by decide
  have h3 : Nat.testBit 32 3 = false := by decide
  have h4 : Nat.testBit 32 4 = false := by decide
  fin_cases loc <;> simp [S18Resource.live, Nat.testBit_or, h1, h2, h3, h4]

lemma initial_locations_live : ∀ loc : Fin 7, S18Resource.live 32 loc.val = true := by decide

lemma rawMask_port : ∀ (g : Fin 5) (b : Bool),
    rawMask (port g b) = if b then if g.val < 4 then S18Resource.basis g.val else 0 else 0 := by
  decide

end S18Geometry

namespace S18Resource

lemma prune_getD_of_live {s : State} {loc : ℕ}
    (hloc : loc < 7) (hlive : live s.1 loc = true) :
    (prune s).2.1.getD loc 1 = s.2.1.getD loc 1 := by
  simp [prune, List.getD_eq_getElem?_getD, List.getElem?_range hloc, hlive]

lemma prune_pools_length (s : State) : (prune s).2.1.length = 7 := by simp [prune]

lemma prune_port_getD {s : State} {g : Fin 5} {b : Bool} {loc : Fin 7}
    (hg : s.1.testBit g.val = false) (hl : loc ∈ S18Geometry.locations g b) :
    (prune s).2.1.getD loc.val 1 = s.2.1.getD loc.val 1 :=
  prune_getD_of_live loc.isLt (S18Geometry.port_locations_live hg b hl)

lemma prune_leftPool {s : State} {g : Fin 4} (hg : s.1.testBit g.val = false) :
    leftPool (prune s).2.1 g.val = leftPool s.2.1 g.val := by
  fin_cases g
  · exact prune_port_getD (g := 0) (b := false) (loc := 0) hg (by decide)
  · exact congrArg₂ mergePools
      (prune_port_getD (g := 1) (b := false) (loc := 1) hg (by decide))
      (prune_port_getD (g := 1) (b := false) (loc := 2) hg (by decide))
  · exact prune_port_getD (g := 2) (b := false) (loc := 2) hg (by decide)
  · exact prune_port_getD (g := 3) (b := false) (loc := 3) hg (by decide)

lemma prune_rightPool {s : State} {g : Fin 4} (hg : s.1.testBit g.val = false) :
    rightPool (prune s).2.1 g.val = rightPool s.2.1 g.val := by
  fin_cases g
  · exact congrArg₂ mergePools
      (congrArg₂ mergePools
        (prune_port_getD (g := 0) (b := true) (loc := 1) hg (by decide))
        (prune_port_getD (g := 0) (b := true) (loc := 2) hg (by decide)))
      (prune_port_getD (g := 0) (b := true) (loc := 3) hg (by decide))
  · exact congrArg (mergePools (1 <<< 25))
      (prune_port_getD (g := 1) (b := true) (loc := 4) hg (by decide))
  · exact congrArg (mergePools (1 <<< 42))
      (prune_port_getD (g := 2) (b := true) (loc := 5) hg (by decide))
  · exact congrArg (mergePools (1 <<< 52))
      (prune_port_getD (g := 3) (b := true) (loc := 6) hg (by decide))

lemma prune_filterPool {s : State} (hg : s.1.testBit 4 = false) :
    (prune s).2.1.getD 1 1 = s.2.1.getD 1 1 :=
  prune_port_getD (g := 4) (b := true) (loc := 1) hg (by decide)

lemma prune_group_pairMasks {s : State} {g : Fin 4} (hg : s.1.testBit g.val = false) :
    pairMasks (· &&& ·) (leftPool (prune s).2.1 g.val) (rightPool (prune s).2.1 g.val) =
      pairMasks (· &&& ·) (leftPool s.2.1 g.val) (rightPool s.2.1 g.val) := by
  rw [prune_leftPool hg, prune_rightPool hg]

end S18Resource

namespace S18Positive

open S18Resource OnceGeometry

abbrev Pools := OncePositive.Pools
abbrev or7 := OncePositive.or7
abbrev PoolsGood := OncePositive.PoolsGood
abbrev Witness := OncePositive.Witness
abbrev liftPool := OncePositive.liftPool
abbrev poolView := OncePositive.poolView

lemma or7_or (f h : Fin 7 → ℕ) : or7 (fun i => f i ||| h i) = or7 f ||| or7 h :=
  OncePositive.or7_or f h

lemma or7_update (f : Fin 7 → ℕ) (loc : Fin 7) (k : ℕ) :
    or7 (Function.update f loc (f loc ||| k)) = or7 f ||| k :=
  OncePositive.or7_update f loc k

lemma or7_filtered {L : Finset (Fin 7)} {f : Fin 7 → ℕ}
    (hf : ∀ i, i ∉ L → f i = 0) :
    or7 f = or7 (fun i => if i ∈ L then f i else 0) :=
  OncePositive.or7_filtered hf

def Rep (used : ℕ) (P : Pools) (S : Finset (Fin 10)) (m : ℕ) : Prop :=
  ∀ (g : Fin 5) (b : Bool), used.testBit g.val = false → S ⊆ S18Geometry.port g b →
    ∃ f, Witness P (S18Geometry.locations g b) f ∧ m = rawMask S ||| or7 f

lemma rep_raw {used : ℕ} {P : Pools} (hp : PoolsGood P) (S : Finset (Fin 10)) :
    Rep used P S (rawMask S) := by
  intro g b _ _
  refine ⟨fun _ => 0, ?_, ?_⟩
  · exact fun i => ⟨(hp i).1, fun _ => rfl⟩
  · simp [or7, OncePositive.or7]

lemma rep_or {used : ℕ} {P : Pools} (hp : PoolsGood P)
    {S T : Finset (Fin 10)} {a b : ℕ} (ha : Rep used P S a) (hb : Rep used P T b) :
    Rep used P (S ∪ T) (a ||| b) := by
  intro g side hu hST
  have hS : S ⊆ S18Geometry.port g side := fun v hv => hST (Finset.mem_union_left _ hv)
  have hT : T ⊆ S18Geometry.port g side := fun v hv => hST (Finset.mem_union_right _ hv)
  obtain ⟨f, hf, ha⟩ := ha g side hu hS
  obtain ⟨h, hh, hb⟩ := hb g side hu hT
  refine ⟨fun i => f i ||| h i, ?_, ?_⟩
  · intro i
    refine ⟨(hp i).2 _ (hf i).1 _ (hh i).1, ?_⟩
    intro hi
    change f i ||| h i = 0
    rw [(hf i).2 hi, (hh i).2 hi]
    rfl
  · rw [ha, hb, rawMask_union, or7_or]
    ac_rfl

lemma rep_mono {used : ℕ} {P Q : Pools} {S : Finset (Fin 10)} {m : ℕ}
    (hPQ : ∀ i x, x ∈ values (P i) → x ∈ values (Q i))
    (h : Rep used P S m) : Rep used Q S m := by
  intro g b hg hS
  obtain ⟨f, hf, hm⟩ := h g b hg hS
  exact ⟨f, fun i => ⟨hPQ i _ (hf i).1, (hf i).2⟩, hm⟩

lemma liftPool_mono (P : Pools) (loc : Fin 7) (k : ℕ) :
    ∀ i x, x ∈ values (P i) → x ∈ values (liftPool P loc k i) :=
  OncePositive.liftPool_mono P loc k

lemma poolsGood_lift {P : Pools} (hp : PoolsGood P) (loc : Fin 7) {k : ℕ} (hk : k < 64) :
    PoolsGood (liftPool P loc k) := OncePositive.poolsGood_lift hp loc hk

lemma rep_lift {used : ℕ} {P : Pools} {S : Finset (Fin 10)} {m k : ℕ}
    (h : Rep used P S m) (hk : k < 64) {v : Fin 10} (hv : v ∈ S) :
    Rep used (liftPool P (vertexClass v) k) S (m ||| k) := by
  intro g b hg hS
  have hvL := S18Geometry.support_class hS hv
  obtain ⟨f, hf, hm⟩ := h g b hg hS
  refine ⟨Function.update f (vertexClass v) (f (vertexClass v) ||| k), ?_, ?_⟩
  · intro i
    by_cases hi : i = vertexClass v
    · subst i
      constructor
      · simpa [liftPool, OncePositive.liftPool] using OnceResource.mem_addCarrier_or (hf (vertexClass v)).1 hk
      · intro hnot
        exact False.elim (hnot hvL)
    · simpa [liftPool, OncePositive.liftPool, Function.update_apply, hi] using hf i
  · rw [or7_update, hm]
    ac_rfl

lemma rep_restrict_pools {old new : ℕ} {P Q : Pools} {S : Finset (Fin 10)} {m : ℕ}
    (hgroups : ∀ g : Fin 5, new.testBit g.val = false → old.testBit g.val = false)
    (hzero : ∀ i, 0 ∈ values (Q i))
    (hpools : ∀ (g : Fin 5) (b : Bool), new.testBit g.val = false →
      ∀ i ∈ S18Geometry.locations g b, Q i = P i)
    (h : Rep old P S m) : Rep new Q S m := by
  intro g b hg hS
  obtain ⟨f, hf, hm⟩ := h g b (hgroups g hg) hS
  refine ⟨f, ?_, hm⟩
  intro i
  refine ⟨?_, (hf i).2⟩
  by_cases hi : i ∈ S18Geometry.locations g b
  · rw [hpools g b hg i hi]
    exact (hf i).1
  · rw [(hf i).2 hi]
    exact hzero i

lemma poolView_prune (s : State) (i : Fin 7) :
    poolView (prune s).2.1 i = if live s.1 i.val then poolView s.2.1 i else 1 := by
  simp [poolView, OncePositive.poolView, prune, List.getD_eq_getElem?_getD]

lemma mem_values_one_iff {x : ℕ} : x ∈ values 1 ↔ x = 0 := by
  rw [show (x ∈ values 1) ↔ x < 64 ∧ (1 : ℕ).testBit x = true from OnceResource.mem_values_iff,
    Nat.testBit_one_eq_true_iff_self_eq_zero]
  constructor
  · exact And.right
  · intro h; subst x; exact ⟨by decide, rfl⟩

lemma one_pool_good :
    0 ∈ values 1 ∧ ∀ a ∈ values 1, ∀ b ∈ values 1, a ||| b ∈ values 1 := by
  constructor
  · exact mem_values_one_iff.mpr rfl
  · intro a ha b hb
    obtain rfl := mem_values_one_iff.mp ha
    obtain rfl := mem_values_one_iff.mp hb
    exact mem_values_one_iff.mpr rfl

lemma poolsGood_prune {s : State} (hp : PoolsGood (poolView s.2.1)) :
    PoolsGood (poolView (prune s).2.1) := by
  intro i
  rw [poolView_prune]
  split
  · exact hp i
  · exact one_pool_good

lemma rep_prune {s : State} {S : Finset (Fin 10)} {m : ℕ}
    (hp : PoolsGood (poolView s.2.1)) (h : Rep s.1 (poolView s.2.1) S m) :
    Rep (prune s).1 (poolView (prune s).2.1) S m := by
  apply rep_restrict_pools (fun _ hg => hg) (fun i => (poolsGood_prune hp i).1) ?_ h
  intro g b hg i hi
  rw [poolView_prune, S18Geometry.port_locations_live hg b hi]
  rfl

lemma unused_of_or_unused {used extra i : ℕ}
    (h : (used ||| extra).testBit i = false) : used.testBit i = false := by
  rw [Nat.testBit_or] at h
  exact (Bool.or_eq_false_iff.mp h).1

lemma mark_used_lt {used : ℕ} (hu : used < 64) (g : Fin 5) :
    used ||| (1 <<< g.val) < 64 := by
  have hg : (1 <<< g.val : ℕ) < 64 := by fin_cases g <;> decide
  exact Nat.or_lt_two_pow (n := 6) hu hg

lemma rep_mark {used : ℕ} {P : Pools} {S : Finset (Fin 10)} {m : ℕ}
    (h : Rep used P S m) (g : Fin 5) : Rep (used ||| (1 <<< g.val)) P S m := by
  intro g' b hg hS
  exact h g' b (unused_of_or_unused hg) hS

lemma rep_mark_prune {used : ℕ} {ps : List ℕ} {S : Finset (Fin 10)} {m : ℕ}
    (hp : PoolsGood (poolView ps)) (h : Rep used (poolView ps) S m)
    (g : Fin 5) (zs : List ℕ) :
    Rep (used ||| (1 <<< g.val))
      (poolView (prune (used ||| (1 <<< g.val), ps, zs)).2.1) S m := by
  exact rep_prune (s := (used ||| (1 <<< g.val), ps, zs)) hp (rep_mark h g)

lemma poolView_set {ps : List ℕ} (hlen : ps.length = 7) (loc : Fin 7) (k : ℕ) :
    poolView (ps.set loc.val (addCarrier (ps.getD loc.val 1) k)) =
      liftPool (poolView ps) loc k := by
  funext i
  by_cases hi : i = loc
  · subst i
    have hb : loc.val < ps.length := by simpa only [hlen] using loc.isLt
    simp [poolView, OncePositive.poolView, liftPool, OncePositive.liftPool,
      List.getD_eq_getElem?_getD, List.getElem?_set_self hb]
    rfl
  · have hne : loc.val ≠ i.val := fun h => hi (Fin.ext h.symm)
    simp [poolView, OncePositive.poolView, liftPool, OncePositive.liftPool, hi,
      List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma poolsGood_set {ps : List ℕ} (hlen : ps.length = 7)
    (hp : PoolsGood (poolView ps)) (loc : Fin 7) {k : ℕ} (hk : k < 64) :
    PoolsGood (poolView (ps.set loc.val (addCarrier (ps.getD loc.val 1) k))) := by
  rw [poolView_set hlen]
  exact poolsGood_lift hp loc hk

lemma poolView_replicate_one : poolView (List.replicate 7 1) = fun _ => 1 := by
  funext i
  fin_cases i <;> rfl

lemma poolsGood_replicate_one : PoolsGood (poolView (List.replicate 7 1)) := by
  rw [poolView_replicate_one]
  exact fun _ => one_pool_good

def leftChoices (P : Pools) (g : Fin 5) : ℕ :=
  match g.val with
  | 0 => P 0
  | 1 => mergePools (P 1) (P 2)
  | 2 => P 2
  | 3 => P 3
  | _ => 1

def rightChoices (P : Pools) (g : Fin 5) : ℕ :=
  match g.val with
  | 0 => mergePools (mergePools (P 1) (P 2)) (P 3)
  | 1 => mergePools (1 <<< 25) (P 4)
  | 2 => mergePools (1 <<< 42) (P 5)
  | 3 => mergePools (1 <<< 52) (P 6)
  | _ => P 1

def portChoices (P : Pools) (g : Fin 5) (b : Bool) : ℕ :=
  if b then rightChoices P g else leftChoices P g

lemma portChoices_view (ps : List ℕ) (g : Fin 4) (b : Bool) :
    portChoices (poolView ps) ⟨g.val, by omega⟩ b =
      if b then rightPool ps g.val else leftPool ps g.val := by
  fin_cases g <;> cases b <;> rfl

lemma merge_mem {p q a b : ℕ} (ha : a ∈ values p) (hb : b ∈ values q) :
    a ||| b ∈ values (mergePools p q) :=
  OncePositive.merge_mem ha hb

lemma portChoices_membership (P : Pools) (g : Fin 5) (b : Bool) (f : Fin 7 → ℕ)
    (hf : ∀ i, f i ∈ values (P i)) :
    rawMask (S18Geometry.port g b) ||| or7 (fun i => if i ∈ S18Geometry.locations g b then f i else 0) ∈
      values (portChoices P g b) := by
  rw [S18Geometry.rawMask_port]
  fin_cases g <;> cases b
  · simpa [portChoices, leftChoices, S18Geometry.locations, or7, OncePositive.or7] using hf 0
  · simpa [portChoices, rightChoices, S18Geometry.locations, or7, OncePositive.or7, basis] using
      merge_mem (merge_mem (hf 1) (hf 2)) (hf 3)
  · simpa [portChoices, leftChoices, S18Geometry.locations, or7, OncePositive.or7] using
      merge_mem (hf 1) (hf 2)
  · simpa [portChoices, rightChoices, S18Geometry.locations, or7, OncePositive.or7, basis] using
      merge_mem (OnceResource.mem_singleton (by decide : 25 < 64)) (hf 4)
  · simpa [portChoices, leftChoices, S18Geometry.locations, or7, OncePositive.or7] using hf 2
  · simpa [portChoices, rightChoices, S18Geometry.locations, or7, OncePositive.or7, basis] using
      merge_mem (OnceResource.mem_singleton (by decide : 42 < 64)) (hf 5)
  · simpa [portChoices, leftChoices, S18Geometry.locations, or7, OncePositive.or7] using hf 3
  · simpa [portChoices, rightChoices, S18Geometry.locations, or7, OncePositive.or7, basis] using
      merge_mem (OnceResource.mem_singleton (by decide : 52 < 64)) (hf 6)
  · simpa [portChoices, leftChoices, S18Geometry.locations, or7, OncePositive.or7] using one_pool_good.1
  · simpa [portChoices, rightChoices, S18Geometry.locations, or7, OncePositive.or7] using hf 1

lemma rep_port_mem {used : ℕ} {P : Pools} {g : Fin 5} {b : Bool} {m : ℕ}
    (h : Rep used P (S18Geometry.port g b) m) (hu : used.testBit g.val = false) :
    m ∈ values (portChoices P g b) := by
  obtain ⟨f, hf, hm⟩ := h g b hu (Finset.Subset.refl _)
  rw [hm, or7_filtered (fun i => (hf i).2)]
  exact portChoices_membership P g b f (fun i => (hf i).1)

lemma group_candidate {used : ℕ} {ps : List ℕ} {g : Fin 4} {a b : ℕ}
    (ha : Rep used (poolView ps) (S18Geometry.port ⟨g.val, by omega⟩ false) a)
    (hb : Rep used (poolView ps) (S18Geometry.port ⟨g.val, by omega⟩ true) b)
    (hu : used.testBit g.val = false) (hab : a &&& b < 64) :
    a &&& b ∈ values (pairMasks (· &&& ·) (leftPool ps g.val) (rightPool ps g.val)) := by
  have hleft := rep_port_mem ha hu
  have hright := rep_port_mem hb hu
  simp only [portChoices_view, Bool.false_eq_true, ↓reduceIte] at hleft hright
  exact OnceResource.mem_pairMasks hleft hright hab

lemma filter_candidate {used : ℕ} {ps : List ℕ} {m : ℕ}
    (h : Rep used (poolView ps) (S18Geometry.port 4 true) m)
    (hu : used.testBit 4 = false) : m ∈ values (ps.getD 1 1) :=
  rep_port_mem h hu

end S18Positive

namespace OnceResource.IndexCopies

def Reads (start : ℕ) (A B : ℕ → ℕ) (t x : ℕ) : Prop :=
  A (start + t) = x ∨ B (start + t) = x

def Readers (start : ℕ) (A B : ℕ → ℕ) (t x : ℕ) : Finset ℕ :=
  (Finset.range t).filter (fun j => A (start + j) = x ∨ B (start + j) = x)

def ReadCount (start : ℕ) (A B : ℕ → ℕ) (t x : ℕ) : ℕ :=
  (Readers start A B t x).card

def Capacity (fork x : ℕ) : ℕ := if x = fork then 2 else 1

def Valid (start : ℕ) (A B : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ t < n, A (start + t) < start + t ∧ B (start + t) < start + t ∧
    A (start + t) ≠ B (start + t)

lemma readers_mono {start t n x : ℕ} {A B : ℕ → ℕ} (ht : t ≤ n) :
    Readers start A B t x ⊆ Readers start A B n x := by
  intro j hj
  obtain ⟨hj, hr⟩ := Finset.mem_filter.mp hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) ht), hr⟩

lemma readCount_succ (start : ℕ) (A B : ℕ → ℕ) (t x : ℕ) :
    ReadCount start A B (t + 1) x = ReadCount start A B t x +
      if A (start + t) = x ∨ B (start + t) = x then 1 else 0 := by
  have hnot : t ∉ Readers start A B t x := by simp [Readers]
  unfold ReadCount Readers
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with hr
  · exact Finset.card_insert_of_notMem hnot
  · simp

lemma earlier_readers_lt_capacity {start n t x fork : ℕ} {A B : ℕ → ℕ}
    (ht : t < n) (hr : Reads start A B t x)
    (hcap : ReadCount start A B n x ≤ Capacity fork x) :
    ReadCount start A B t x < Capacity fork x := by
  have hle := Finset.card_le_card (readers_mono (start := start) (A := A) (B := B)
    (x := x) (show t + 1 ≤ n by omega))
  change ReadCount start A B (t + 1) x ≤ ReadCount start A B n x at hle
  rw [readCount_succ] at hle
  change A (start + t) = x ∨ B (start + t) = x at hr
  rw [ite_eq_left hr] at hle
  omega

lemma earlier_readers_fork_le_one {start n t fork : ℕ} {A B : ℕ → ℕ}
    (ht : t < n) (hr : Reads start A B t fork)
    (hcap : ReadCount start A B n fork ≤ 2) :
    ReadCount start A B t fork ≤ 1 := by
  have h := earlier_readers_lt_capacity (fork := fork) ht hr (by simpa [Capacity] using hcap)
  simp [Capacity] at h
  omega

lemma earlier_readers_other_zero {start n t x fork : ℕ} {A B : ℕ → ℕ}
    (hx : x ≠ fork) (ht : t < n) (hr : Reads start A B t x)
    (hcap : ReadCount start A B n x ≤ 1) :
    ReadCount start A B t x = 0 := by
  have h := earlier_readers_lt_capacity (fork := fork) ht hr (by simpa [Capacity, hx] using hcap)
  simp only [Capacity, ite_eq_right hx] at h
  omega

lemma readCount_zero_of_future {start n t x : ℕ} {A B : ℕ → ℕ}
    (hv : Valid start A B n) (ht : t ≤ n) (hx : start + t ≤ x) :
    ReadCount start A B t x = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨hj, hr⟩ := Finset.mem_filter.mp hj
  have hjt := Finset.mem_range.mp hj
  obtain ⟨ha, hb, _⟩ := hv j (by omega)
  rcases hr with hr | hr <;> omega

variable (Z : ℕ → Prop) [DecidablePred Z]

def Copies (fork x : ℕ) : ℕ := if Z x then Capacity fork x else 1

def Drop (i : ℕ) (ids : Multiset ℕ) : Multiset ℕ :=
  if Z i then ids.erase i else ids

def Give (fork out : ℕ) (ids : Multiset ℕ) : Multiset ℕ :=
  out ::ₘ (if Z out ∧ out = fork then out ::ₘ ids else ids)

def Initial (start fork : ℕ) : Multiset ℕ :=
  Multiset.range start + if Z fork ∧ fork < start then {fork} else 0

def Available (start fork : ℕ) (A B : ℕ → ℕ) : ℕ → Multiset ℕ
  | 0 => Initial Z start fork
  | t + 1 => Give Z fork (start + t)
      (Drop Z (B (start + t)) (Drop Z (A (start + t)) (Available start fork A B t)))

lemma count_drop (ids : Multiset ℕ) (i x : ℕ) :
    (Drop Z i ids).count x = ids.count x - if Z x ∧ x = i then 1 else 0 := by
  by_cases hxi : x = i
  · subst x
    by_cases hi : Z i <;> simp [Drop, hi, Multiset.count_erase_self]
  · by_cases hi : Z i <;> simp [Drop, hi, hxi, Multiset.count_erase_of_ne hxi]

lemma count_drop_two (ids : Multiset ℕ) {a b : ℕ} (hab : a ≠ b) (x : ℕ) :
    (Drop Z b (Drop Z a ids)).count x =
      ids.count x - if Z x ∧ (a = x ∨ b = x) then 1 else 0 := by
  rw [count_drop, count_drop]
  by_cases hz : Z x
  · by_cases hxa : x = a
    · subst x
      simp [hz, hab]
    · by_cases hxb : x = b
      · subst x
        simp [hz, hxa, Ne.symm hxa]
      · simp [hz, hxa, hxb, Ne.symm hxa, Ne.symm hxb]
  · simp [hz]

lemma count_give (ids : Multiset ℕ) (fork out x : ℕ) :
    (Give Z fork out ids).count x = ids.count x + if x = out then Copies Z fork out else 0 := by
  by_cases hf : out = fork
  · subst out
    by_cases hx : x = fork
    · subst x
      by_cases hz : Z fork <;> simp [Give, Copies, Capacity, hz, Nat.add_assoc]
    · by_cases hz : Z fork <;> simp [Give, hz, hx]
  · by_cases hx : x = out
    · subst x
      by_cases hz : Z out <;> simp [Give, Copies, Capacity, hz, hf]
    · simp [Give, hf, hx]

lemma count_initial (start fork x : ℕ) :
    (Initial Z start fork).count x = if x < start then Copies Z fork x else 0 := by
  have hrange : (Multiset.range start).count x = if x < start then 1 else 0 := by
    simpa using Multiset.count_eq_of_nodup (a := x) (Multiset.nodup_range start)
  by_cases hx : x < start <;> by_cases hxf : x = fork
  · subst x
    by_cases hz : Z fork <;>
      simp [Initial, Multiset.count_add, hrange, hx, hz, Copies, Capacity]
  · by_cases hz : Z fork ∧ fork < start <;> by_cases hzx : Z x <;>
      simp [Initial, Multiset.count_add, hrange, hx, hz, Copies, Capacity, hxf, hzx]
  · subst x
    simp [Initial, hx]
  · by_cases hz : Z fork ∧ fork < start <;>
      simp [Initial, hx, hz, hxf]

lemma count_available {start fork n : ℕ} {A B : ℕ → ℕ}
    (hv : Valid start A B n) (t : ℕ) (ht : t ≤ n) (x : ℕ) :
    (Available Z start fork A B t).count x =
      if x < start + t then
        if Z x then Capacity fork x - ReadCount start A B t x else 1
      else 0 := by
  induction t with
  | zero => simp [Available, count_initial, Copies, ReadCount, Readers]
  | succ t ih =>
    have ht' : t ≤ n := by omega
    have ih' := ih ht'
    obtain ⟨ha, hb, hab⟩ := hv t (by omega)
    rw [Available, count_give, count_drop_two Z _ hab, ih']
    by_cases hf : x = start + t
    · subst x
      have hrc := readCount_zero_of_future hv ht' (x := start + t) (by omega)
      have hr : ¬(A (start + t) = start + t ∨ B (start + t) = start + t) := by omega
      have hn : start + t < start + (t + 1) := by omega
      simp [readCount_succ, hrc, hr, hn, Copies]
    · by_cases hold : x < start + t
      · have hn : x < start + (t + 1) := by omega
        simp only [ite_eq_left hold, ite_eq_right hf, Nat.add_zero, ite_eq_left hn]
        rw [readCount_succ]
        by_cases hz : Z x
        · by_cases hr : A (start + t) = x ∨ B (start + t) = x <;>
            simp [hz, hr, Nat.sub_sub]
        · simp [hz]
      · have hn : ¬ x < start + (t + 1) := by omega
        have hna : A (start + t) ≠ x := by omega
        have hnb : B (start + t) ≠ x := by omega
        simp [hold, hf, hn, hna, hnb]

lemma source_available {start fork n t x : ℕ} {A B : ℕ → ℕ}
    (hv : Valid start A B n)
    (hcap : ∀ x, Z x → ReadCount start A B n x ≤ Capacity fork x)
    (ht : t < n) (hx : x < start + t) (hr : Reads start A B t x) :
    x ∈ Available Z start fork A B t := by
  apply Multiset.count_pos.mp
  rw [count_available Z hv t (by omega) x, ite_eq_left hx]
  by_cases hz : Z x
  · rw [ite_eq_left hz]
    have hlt := earlier_readers_lt_capacity ht hr (hcap x hz)
    omega
  · simp [hz]

lemma available_bounded {start fork n t x : ℕ} {A B : ℕ → ℕ}
    (hv : Valid start A B n) (ht : t ≤ n)
    (hx : x ∈ Available Z start fork A B t) : x < start + t := by
  have hpos := Multiset.count_pos.mpr hx
  rw [count_available Z hv t ht x] at hpos
  by_contra hnot
  simp [hnot] at hpos

lemma mem_drop_of_ne {ids : Multiset ℕ} {i x : ℕ} (hx : x ∈ ids) (hne : x ≠ i) :
    x ∈ Drop Z i ids := by
  unfold Drop
  split_ifs
  · exact (Multiset.mem_erase_of_ne hne).mpr hx
  · exact hx

lemma sources_available {start fork n t : ℕ} {A B : ℕ → ℕ}
    (hv : Valid start A B n)
    (hcap : ∀ x, Z x → ReadCount start A B n x ≤ Capacity fork x)
    (ht : t < n) :
    A (start + t) ∈ Available Z start fork A B t ∧
      B (start + t) ∈ Drop Z (A (start + t)) (Available Z start fork A B t) := by
  obtain ⟨ha, hb, hab⟩ := hv t ht
  constructor
  · exact source_available Z hv hcap ht ha (Or.inl rfl)
  · apply mem_drop_of_ne Z (source_available Z hv hcap ht hb (Or.inr rfl))
    exact Ne.symm hab

lemma initial_extra_iff (start fork : ℕ) :
    (if Z fork ∧ fork < start then ({fork} : Multiset ℕ) else 0) ≠ 0 ↔
      Z fork ∧ fork < start := by
  split_ifs with h
  · simp [h]
  · simp [h]

lemma creation_extra_unique {start fork t u : ℕ}
    (ht : Z (start + t) ∧ start + t = fork)
    (hu : Z (start + u) ∧ start + u = fork) : t = u := by omega

lemma initial_extra_excludes_creation {start fork t : ℕ}
    (hi : Z fork ∧ fork < start) : ¬(Z (start + t) ∧ start + t = fork) := by omega

lemma extra_before_iff (start fork t : ℕ) :
    (Z fork ∧ fork < start) ∨
      (∃ j < t, Z (start + j) ∧ start + j = fork) ↔
      Z fork ∧ fork < start + t := by
  constructor
  · rintro (hi | ⟨j, hj, hz, heq⟩)
    · exact ⟨hi.1, by omega⟩
    · exact ⟨heq ▸ hz, by omega⟩
  · intro h
    by_cases hi : fork < start
    · exact Or.inl ⟨h.1, hi⟩
    · refine Or.inr ⟨fork - start, by omega, ?_, by omega⟩
      have heq : start + (fork - start) = fork := by omega
      simpa only [heq] using h.1

def ExtraCount (start fork t : ℕ) : ℕ :=
  (if Z fork ∧ fork < start then 1 else 0) +
    ((Finset.range t).filter (fun j => Z (start + j) ∧ start + j = fork)).card

lemma extraCount_le_one (start fork t : ℕ) : ExtraCount Z start fork t ≤ 1 := by
  by_cases hi : Z fork ∧ fork < start
  · have he : (Finset.range t).filter (fun j => Z (start + j) ∧ start + j = fork) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hj' := (Finset.mem_filter.mp hj).2
      omega
    simp [ExtraCount, hi, he]
  · simp only [ExtraCount, ite_eq_right hi, Nat.zero_add]
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    omega

lemma extraCount_pos_iff (start fork t : ℕ) :
    0 < ExtraCount Z start fork t ↔ Z fork ∧ fork < start + t := by
  rw [← extra_before_iff Z start fork t]
  by_cases hi : Z fork ∧ fork < start <;>
    simp [ExtraCount, hi, Nat.add_pos_iff_pos_or_pos, Finset.card_pos, Finset.Nonempty, Finset.mem_filter]

lemma extraCount_eq (start fork t : ℕ) :
    ExtraCount Z start fork t = if Z fork ∧ fork < start + t then 1 else 0 := by
  have hle := extraCount_le_one Z start fork t
  have hpos := extraCount_pos_iff Z start fork t
  split_ifs with h
  · have hp := hpos.mpr h
    omega
  · have hp : ¬0 < ExtraCount Z start fork t := fun hp => h (hpos.mp hp)
    omega

def Retain (x : ℕ) : Multiset ℕ := if Z x then 0 else {x}

lemma two_decomp {ids : Multiset ℕ} {a b : ℕ}
    (ha : a ∈ ids) (hb : b ∈ ids) (hab : a ≠ b) :
    ids = a ::ₘ b ::ₘ ((ids.erase a).erase b) := by
  have hb' := (Multiset.mem_erase_of_ne (Ne.symm hab)).mpr hb
  calc
    ids = a ::ₘ ids.erase a := (Multiset.cons_erase ha).symm
    _ = a ::ₘ b ::ₘ ((ids.erase a).erase b) :=
      congrArg (Multiset.cons a) (Multiset.cons_erase hb').symm

lemma drop_two_decomp {ids : Multiset ℕ} {a b : ℕ}
    (ha : a ∈ ids) (hb : b ∈ ids) (hab : a ≠ b) :
    Drop Z b (Drop Z a ids) =
      Retain Z a + Retain Z b + ((ids.erase a).erase b) := by
  by_cases hza : Z a <;> by_cases hzb : Z b
  · simp [Drop, Retain, hza, hzb]
  · simp only [Drop, Retain, hza, hzb, ↓reduceIte, Multiset.zero_add, Multiset.singleton_add]
    exact (Multiset.cons_erase ((Multiset.mem_erase_of_ne (Ne.symm hab)).mpr hb)).symm
  · simp only [Drop, Retain, hza, hzb, ↓reduceIte, Multiset.add_zero, Multiset.singleton_add]
    rw [Multiset.erase_comm]
    exact (Multiset.cons_erase ((Multiset.mem_erase_of_ne hab).mpr ha)).symm
  · simp only [Drop, Retain, hza, hzb, ↓reduceIte, Multiset.cons_add, Multiset.singleton_add]
    exact two_decomp ha hb hab

lemma available_step_decomp {start fork n t : ℕ} {A B : ℕ → ℕ}
    (hv : Valid start A B n)
    (hcap : ∀ x, Z x → ReadCount start A B n x ≤ Capacity fork x)
    (ht : t < n) :
    ∃ rest : Multiset ℕ,
      Available Z start fork A B t = A (start + t) ::ₘ B (start + t) ::ₘ rest ∧
      Available Z start fork A B (t + 1) =
        (start + t) ::ₘ
          (if Z (start + t) ∧ start + t = fork then
            (start + t) ::ₘ (Retain Z (A (start + t)) + Retain Z (B (start + t)) + rest)
          else Retain Z (A (start + t)) + Retain Z (B (start + t)) + rest) := by
  obtain ⟨ha, hb, hab⟩ := hv t ht
  have haa := source_available Z hv hcap ht ha (Or.inl rfl)
  have hba := source_available Z hv hcap ht hb (Or.inr rfl)
  refine ⟨((Available Z start fork A B t).erase (A (start + t))).erase (B (start + t)),
    two_decomp haa hba hab, ?_⟩
  simp only [Available, Give, drop_two_decomp Z haa hba hab]

end OnceResource.IndexCopies


namespace OnceResource.TokenMap

open IndexCopies

def token (k : ℕ) : Multiset ℕ := if k = 0 then 0 else {k}

def project (Z : ℕ → Prop) [DecidablePred Z] (M : ℕ → ℕ) (ids : Multiset ℕ) : Multiset ℕ :=
  (ids.filter (fun i => Z i ∧ M i ≠ 0)).map M

variable (Z : ℕ → Prop) [DecidablePred Z] (M : ℕ → ℕ)

lemma project_zero : project Z M 0 = 0 := by simp [project]

lemma project_cons (i : ℕ) (ids : Multiset ℕ) :
    project Z M (i ::ₘ ids) = (if Z i then token (M i) else 0) + project Z M ids := by
  by_cases hz : Z i <;> by_cases hm : M i = 0 <;>
    simp [project, hz, hm, token]

lemma project_add (ids rest : Multiset ℕ) :
    project Z M (ids + rest) = project Z M ids + project Z M rest := by
  simp [project]

lemma project_retain (i : ℕ) : project Z M (Retain Z i) = 0 := by
  by_cases hz : Z i <;> simp [Retain, project, hz]

lemma project_mem {i : ℕ} {ids : Multiset ℕ} (hi : i ∈ ids)
    (hz : Z i) (hm : M i ≠ 0) : M i ∈ project Z M ids := by
  exact Multiset.mem_map.mpr ⟨i, Multiset.mem_filter.mpr ⟨hi, hz, hm⟩, rfl⟩

lemma project_drop {i : ℕ} {ids : Multiset ℕ} (hi : i ∈ ids) :
    project Z M (Drop Z i ids) =
      if Z i ∧ M i ≠ 0 then (project Z M ids).erase (M i) else project Z M ids := by
  have heq : ids = i ::ₘ ids.erase i := (Multiset.cons_erase hi).symm
  by_cases hz : Z i
  · by_cases hm : M i = 0
    · simp only [Drop, hz, ↓reduceIte]
      rw [heq, project_cons]
      simp [hz, hm, token]
    · have hp : project Z M ids = M i ::ₘ project Z M (ids.erase i) := by
        rw [heq, project_cons]
        simp [hz, hm, token]
      simp [Drop, hz, hm, hp]
  · simp [Drop, hz]

lemma project_give (fork out : ℕ) (ids : Multiset ℕ) :
    project Z M (Give Z fork out ids) =
      (if Z out then token (M out) else 0) +
      (if Z out ∧ out = fork then token (M out) else 0) + project Z M ids := by
  by_cases hf : out = fork
  · subst out
    by_cases hz : Z fork <;> simp [Give, hz, project_cons, Multiset.add_assoc]
  · by_cases hz : Z out <;> simp [Give, hz, hf, project_cons]

lemma project_step {ids rest : Multiset ℕ} {a b out fork : ℕ}
    (hid : ids = a ::ₘ b ::ₘ rest) (hab : a ≠ b) :
    project Z M (Give Z fork out (Drop Z b (Drop Z a ids))) =
      (if Z out then token (M out) else 0) +
      (if Z out ∧ out = fork then token (M out) else 0) + project Z M rest := by
  rw [project_give]
  have ha : a ∈ ids := by rw [hid]; simp
  have hb : b ∈ ids := by rw [hid]; simp
  rw [drop_two_decomp Z ha hb hab, project_add, project_add, project_retain, project_retain]
  simp only [Multiset.zero_add]
  have herase : (ids.erase a).erase b = rest := by rw [hid]; simp
  rw [herase]

lemma project_initial_one {start seed : ℕ} (hseed : seed < start)
    (hzseed : Z seed) (hmseed : M seed ≠ 0)
    (hother : ∀i<start, Z i → i ≠ seed → M i = 0) :
    project Z M (Multiset.range start) = {M seed} := by
  have hf : (Multiset.range start).filter (fun i => Z i ∧ M i ≠ 0) = {seed} := by
    apply Multiset.ext.mpr
    intro i
    rw [Multiset.count_eq_of_nodup ((Multiset.nodup_range start).filter _)]
    by_cases hi : i = seed
    · subst i
      simp [hseed, hzseed, hmseed]
    · have hn : ¬(i ∈ Multiset.range start ∧ Z i ∧ M i ≠ 0) := by
        rintro ⟨hi', hz, hm⟩
        exact hm (hother i (Multiset.mem_range.mp hi') hz hi)
      simp only [Multiset.mem_range] at hn
      simp [hn, hi]
  simp [project, hf]

lemma project_initial {start seed fork : ℕ} (hseed : seed < start)
    (hzseed : Z seed) (hmseed : M seed ≠ 0)
    (hother : ∀i<start, Z i → i ≠ seed → M i = 0) :
    project Z M (Initial Z start fork) =
      {M seed} + if fork = seed then {M seed} else 0 := by
  rw [Initial, project_add, project_initial_one Z M hseed hzseed hmseed hother]
  congr 1
  by_cases hf : fork = seed
  · subst fork
    simp [hseed, hzseed, hmseed, project, Multiset.filter_singleton]
  · by_cases h : Z fork ∧ fork < start
    · have hm : M fork = 0 := hother fork h.2 h.1 hf
      simp [h, hf, project, hm]
    · simp [h, hf, project]

end OnceResource.TokenMap

namespace S18Simulation

open S18Resource S18Positive
open OnceResource.IndexCopies OnceResource.TokenMap

abbrev Reach (s t : State) : Prop :=
  Relation.ReflTransGen (fun a b : State => b ∈ successors a) s t

def contrib (S : Finset (Fin 10)) (m : ℕ) : Multiset ℕ :=
  if S = ∅ then OnceResource.TokenMap.token m else 0

def Healthy (s : State) : Prop :=
  s.1 < 64 ∧ s.2.1.length = 7 ∧ OncePositive.PoolsGood (OncePositive.poolView s.2.1)

def Preserves (s t : State) : Prop :=
  ∀ T m, S18Positive.Rep s.1 (OncePositive.poolView s.2.1) T m →
    S18Positive.Rep t.1 (OncePositive.poolView t.2.1) T m

def LocalResult (s q : State) (S : Finset (Fin 10)) (m : ℕ)
    (rest : Multiset ℕ) (group : Option (Fin 5)) : Prop :=
  Reach s q ∧ Healthy q ∧ (q.2.2 : Multiset ℕ) = contrib S m + rest ∧
  Preserves s q ∧ (S.Nonempty → Rep q.1 (OncePositive.poolView q.2.1) S m) ∧
  (∀ g : Fin 5, q.1.testBit g.val = true → s.1.testBit g.val = true ∨ group = some g)

def ProgramCallback (S : ℕ → Finset (Fin 10)) (M A B : ℕ → ℕ)
    (G : ℕ → Option (Fin 5)) (start n : ℕ) : Prop :=
  ∀ t < n, ∀ (s : State) (rest : Multiset ℕ), Healthy s →
    ((S (A (start + t))).Nonempty →
      Rep s.1 (OncePositive.poolView s.2.1) (S (A (start + t))) (M (A (start + t)))) →
    ((S (B (start + t))).Nonempty →
      Rep s.1 (OncePositive.poolView s.2.1) (S (B (start + t))) (M (B (start + t)))) →
    (s.2.2 : Multiset ℕ) = contrib (S (A (start + t))) (M (A (start + t))) +
      contrib (S (B (start + t))) (M (B (start + t))) + rest →
    (∀ g : Fin 5, G (start + t) = some g → s.1.testBit g.val = false) →
    ∃ q, LocalResult s q (S (start + t)) (M (start + t)) rest (G (start + t))

def GroupUnique (G : ℕ → Option (Fin 5)) (start n : ℕ) : Prop :=
  ∀ i < n, ∀ j < n, ∀ g : Fin 5,
    G (start + i) = some g → G (start + j) = some g → i = j

def ProgramInv (S : ℕ → Finset (Fin 10)) (M A B : ℕ → ℕ)
    (G : ℕ → Option (Fin 5)) (start n t : ℕ) (s : State) : Prop :=
  Healthy s ∧ (s.2.2 : Multiset ℕ) =
    project (fun w => S w = ∅) M (Available (fun w => S w = ∅) start (start+n) A B t) ∧
  (∀ w < start + t, (S w).Nonempty →
    Rep s.1 (OncePositive.poolView s.2.1) (S w) (M w)) ∧
  ∀ g : Fin 5, s.1.testBit g.val = true → ∃ j < t, G (start + j) = some g

lemma program_inv_step {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 5)} {start n t : ℕ} {s : State}
    (hv : Valid start A B n)
    (hcap : ∀ w, S w = ∅ → ReadCount start A B n w ≤ 1)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback S M A B G start n)
    (ht : t < n) (hinv : ProgramInv S M A B G start n t s) :
    ∃ q, Reach s q ∧ ProgramInv S M A B G start n (t+1) q := by
  obtain ⟨hhealthy, hzeros, hreps, hused⟩ := hinv
  obtain ⟨ha, hb, hab⟩ := hv t ht
  have hcap' : ∀ w, S w = ∅ → ReadCount start A B n w ≤ Capacity (start+n) w := by
    intro w hw
    apply (hcap w hw).trans
    unfold Capacity
    split_ifs <;> decide
  obtain ⟨rest, hids, _⟩ := available_step_decomp (fun w => S w = ∅) hv hcap' ht
  have hzero_input : (s.2.2 : Multiset ℕ) =
      contrib (S (A (start + t))) (M (A (start + t))) +
      contrib (S (B (start + t))) (M (B (start + t))) + project (fun w => S w = ∅) M rest := by
    rw [hzeros, hids, project_cons, project_cons]
    simp only [contrib, Multiset.add_assoc]
  have hunused : ∀ g : Fin 5, G (start + t) = some g → s.1.testBit g.val = false := by
    intro g hg
    cases hbit : s.1.testBit g.val with
    | false => rfl
    | true =>
      obtain ⟨j, hj, hjg⟩ := hused g hbit
      have heq := hgroups t ht j (by omega) g hg hjg
      omega
  obtain ⟨q, hreach, hhealth, hzero, hpres, hnew, huse⟩ :=
    hcallback t ht s (project (fun w => S w = ∅) M rest) hhealthy
      (hreps _ ha) (hreps _ hb) hzero_input hunused
  refine ⟨q, hreach, hhealth, ?_, ?_, ?_⟩
  · rw [Available, project_step (fun w => S w = ∅) M hids hab]
    have hne : start+t ≠ start+n := by omega
    simpa only [hne, and_false, ite_false, Multiset.add_zero, contrib] using hzero
  · intro w hw hSw
    by_cases hold : w < start+t
    · exact hpres _ _ (hreps w hold hSw)
    · have heq : w = start+t := by omega
      subst w
      exact hnew hSw
  · intro g hg
    rcases huse g hg with hg | hg
    · obtain ⟨j, hj, hjg⟩ := hused g hg
      exact ⟨j, by omega, hjg⟩
    · exact ⟨t, by omega, hg⟩

lemma program_induction_prefix {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 5)} {start n : ℕ} {s₀ : State}
    (hv : Valid start A B n) (hcap : ∀ w, S w = ∅ → ReadCount start A B n w ≤ 1)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback S M A B G start n)
    (hinit : ProgramInv S M A B G start n 0 s₀) :
    ∀ t ≤ n, ∃ s, Reach s₀ s ∧ ProgramInv S M A B G start n t s := by
  intro t
  induction t with
  | zero => intro _; exact ⟨s₀, Relation.ReflTransGen.refl, hinit⟩
  | succ t ih =>
    intro ht
    obtain ⟨s, hreach, hinv⟩ := ih (by omega)
    obtain ⟨q, hstep, hiq⟩ := program_inv_step hv hcap hgroups hcallback (by omega) hinv
    exact ⟨q, hreach.trans hstep, hiq⟩

lemma program_target_excluded {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 5)} {start n w : ℕ}
    (hsafe : ∀ s : State, Reach initial s → 56 ∉ s.2.2)
    (hv : Valid start A B n) (hcap : ∀ u, S u = ∅ → ReadCount start A B n u ≤ 1)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback S M A B G start n)
    (hinit : ProgramInv S M A B G start n 0 initial)
    (hw : w ∈ Available (fun u => S u = ∅) start (start+n) A B n)
    (hSw : S w = ∅) (hMw : M w = 56) : False := by
  obtain ⟨s, hr, hi⟩ := program_induction_prefix hv hcap hgroups hcallback hinit n (Nat.le_refl n)
  have hMne : M w ≠ 0 := by omega
  have hm := project_mem (fun u => S u = ∅) M hw hSw hMne
  rw [hMw] at hm
  have ht : 56 ∈ s.2.2 := by
    change 56 ∈ (s.2.2 : Multiset ℕ)
    rw [hi.2.1]
    exact hm
  exact hsafe s hr ht

end S18Simulation

namespace S200Resource

abbrev State := Nat × List Nat × List Nat

def values (bits : Nat) : List Nat := (List.range 64).filter bits.testBit

def pairMasks (op : Nat → Nat → Nat) (a b : Nat) : Nat :=
  (values a).foldl (fun acc x =>
    (values b).foldl (fun acc y => acc ||| (1 <<< op x y)) acc) 0

def mergePools (a b : Nat) : Nat := pairMasks (· ||| ·) a b

def addCarrier (pool k : Nat) : Nat := pool ||| mergePools pool (1 <<< k)

def live (used loc : Nat) : Bool :=
  if loc = 0 then !used.testBit 0
  else if loc < 4 then !used.testBit 0 || !used.testBit loc
  else if loc = 4 then !used.testBit 1 || !used.testBit 4
  else !used.testBit (loc - 3) || !used.testBit 5

def prune (s : State) : State :=
  (s.1, (List.range 7).map (fun i =>
    if live s.1 i then s.2.1.getD i 1 else 1), s.2.2)

def sortedInsert (k : Nat) : List Nat → List Nat
  | [] => [k]
  | x :: xs => if k ≤ x then k :: x :: xs else x :: sortedInsert k xs

def zeroSort : List Nat → List Nat
  | [] => []
  | x :: xs => sortedInsert x (zeroSort xs)

def insertZero (k : Nat) (zs : List Nat) : List Nat := zeroSort (k :: zs)

def basis : Nat → Nat | 0 => 0 | 1 => 25 | 2 => 42 | _ => 52

def leftPool (ps : List Nat) (g : Nat) : Nat :=
  if g < 4 then ps.getD g 1 else 1 <<< 63

def rightPool (ps : List Nat) (g : Nat) : Nat :=
  if g = 0 then mergePools (mergePools (ps.getD 1 1) (ps.getD 2 1)) (ps.getD 3 1)
  else if g < 4 then mergePools (1 <<< basis g) (ps.getD (g + 3) 1)
  else if g = 4 then mergePools (1 <<< 9) (ps.getD 4 1)
  else mergePools (1 <<< 54) (mergePools (ps.getD 5 1) (ps.getD 6 1))

def groupNext (s : State) : List State :=
  (List.range 6).flatMap fun g =>
    if s.1.testBit g then [] else
    (values (pairMasks (· &&& ·) (leftPool s.2.1 g) (rightPool s.2.1 g))).filterMap
      fun k => if k = 0 then none else
        some (prune (s.1 ||| (1 <<< g), s.2.1, insertZero k s.2.2))

def liftNext (s : State) : List State :=
  s.2.2.flatMap fun k => (List.range 7).filterMap fun loc =>
    if live s.1 loc then
      let old := s.2.1.getD loc 1
      let new := addCarrier old k
      if new = old then none else
        some (prune (s.1, s.2.1.set loc new, s.2.2.erase k))
    else none

def discardNext (s : State) : List State :=
  s.2.2.map fun k => prune (s.1, s.2.1, s.2.2.erase k)

def combineNext (s : State) : List State :=
  s.2.2.flatMap fun a => (s.2.2.erase a).flatMap fun b =>
    [a &&& b, a ||| b].filterMap fun k => if k = 0 then none else
      some (prune (s.1, s.2.1, insertZero k ((s.2.2.erase a).erase b)))

def successors (s : State) : List State :=
  groupNext s ++ liftNext s ++ discardNext s ++ combineNext s

def initial : State := (0, List.replicate 7 1, [])

def listLess : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then listLess as bs else decide (a < b)

def stateLess (a b : State) : Bool :=
  if a.1 ≠ b.1 then decide (a.1 < b.1)
  else if a.2.1 ≠ b.2.1 then listLess a.2.1 b.2.1
  else listLess a.2.2 b.2.2

def safe (s : State) : Bool := !s.2.2.contains 56

end S200Resource

namespace S200Geometry

open OnceGeometry

def physicalPort (g : Fin 6) (right : Bool) : Finset (Fin 10) :=
  if right then match g.val with
    | 0 => {1, 4, 5}
    | 1 => {2, 6}
    | 2 => {3, 9}
    | 3 => {7, 8}
    | 4 => {2}
    | _ => {8, 9}
  else match g.val with
    | 0 => {0}
    | 1 => {1}
    | 2 => {4}
    | 3 => {5}
    | _ => {3, 6, 7}

-- The two dirty left inputs are evaluated directly from their full row mask.
def carrierPort (g : Fin 6) (right : Bool) : Finset (Fin 10) :=
  if g.val < 4 ∨ right = true then physicalPort g right else ∅

def locations (g : Fin 6) (right : Bool) : Finset (Fin 7) :=
  if right then match g.val with
    | 0 => {1, 2, 3}
    | 1 => {4}
    | 2 => {5}
    | 3 => {6}
    | 4 => {4}
    | _ => {5, 6}
  else if h : g.val < 4 then {⟨g.val, by omega⟩} else ∅

lemma carrier_class : ∀ (g : Fin 6) (b : Bool) (v : Fin 10),
    v ∈ carrierPort g b → vertexClass v ∈ locations g b := by decide

lemma raw_physical_left : ∀ g : Fin 6,
    rawMask (physicalPort g false) = if g.val < 4 then 0 else 63 := by decide

lemma raw_physical_right : ∀ g : Fin 6,
    rawMask (physicalPort g true) =
      match g.val with | 0 => 0 | 1 => 25 | 2 => 42 | 3 => 52 | 4 => 9 | _ => 54 := by
  decide

lemma physical_disjoint : ∀ g : Fin 6,
    physicalPort g false ∩ physicalPort g true = ∅ := by decide

end S200Geometry

namespace S200Geometry

open OnceGeometry

lemma support_class {S : Finset (Fin 10)} {g : Fin 6} {b : Bool}
    (hS : S ⊆ carrierPort g b) {v : Fin 10} (hv : v ∈ S) :
    vertexClass v ∈ locations g b := carrier_class g b v (hS hv)

lemma port_locations_live {used : ℕ} {g : Fin 6}
    (hg : used.testBit g.val = false) (b : Bool) {loc : Fin 7}
    (hl : loc ∈ locations g b) : S200Resource.live used loc.val = true := by
  fin_cases g <;> cases b <;> fin_cases loc <;>
    simp_all [locations, S200Resource.live]

lemma raw_carrier_left : ∀ g : Fin 6,
    rawMask (carrierPort g false) = 0 := by decide

lemma raw_carrier_right : ∀ g : Fin 6,
    rawMask (carrierPort g true) =
      match g.val with | 0 => 0 | 1 => 25 | 2 => 42 | 3 => 52 | 4 => 9 | _ => 54 := by decide

end S200Geometry

namespace S200Resource

lemma prune_getD_of_live {s : State} {loc : ℕ}
    (hloc : loc < 7) (hlive : live s.1 loc = true) :
    (prune s).2.1.getD loc 1 = s.2.1.getD loc 1 := by
  simp [prune, List.getD_eq_getElem?_getD, List.getElem?_range hloc, hlive]

lemma prune_pools_length (s : State) : (prune s).2.1.length = 7 := by simp [prune]

lemma prune_port_getD {s : State} {g : Fin 6} {b : Bool} {loc : Fin 7}
    (hg : s.1.testBit g.val = false) (hl : loc ∈ S200Geometry.locations g b) :
    (prune s).2.1.getD loc.val 1 = s.2.1.getD loc.val 1 :=
  prune_getD_of_live loc.isLt (S200Geometry.port_locations_live hg b hl)

lemma prune_leftPool {s : State} {g : Fin 6} (hg : s.1.testBit g.val = false) :
    leftPool (prune s).2.1 g.val = leftPool s.2.1 g.val := by
  fin_cases g
  · exact prune_port_getD (g := 0) (b := false) (loc := 0) hg (by decide)
  · exact prune_port_getD (g := 1) (b := false) (loc := 1) hg (by decide)
  · exact prune_port_getD (g := 2) (b := false) (loc := 2) hg (by decide)
  · exact prune_port_getD (g := 3) (b := false) (loc := 3) hg (by decide)
  · rfl
  · rfl

lemma prune_rightPool {s : State} {g : Fin 6} (hg : s.1.testBit g.val = false) :
    rightPool (prune s).2.1 g.val = rightPool s.2.1 g.val := by
  fin_cases g
  · exact congrArg₂ mergePools
      (congrArg₂ mergePools
        (prune_port_getD (g := 0) (b := true) (loc := 1) hg (by decide))
        (prune_port_getD (g := 0) (b := true) (loc := 2) hg (by decide)))
      (prune_port_getD (g := 0) (b := true) (loc := 3) hg (by decide))
  · exact congrArg (mergePools (1 <<< 25))
      (prune_port_getD (g := 1) (b := true) (loc := 4) hg (by decide))
  · exact congrArg (mergePools (1 <<< 42))
      (prune_port_getD (g := 2) (b := true) (loc := 5) hg (by decide))
  · exact congrArg (mergePools (1 <<< 52))
      (prune_port_getD (g := 3) (b := true) (loc := 6) hg (by decide))
  · exact congrArg (mergePools (1 <<< 9))
      (prune_port_getD (g := 4) (b := true) (loc := 4) hg (by decide))
  · exact congrArg (mergePools (1 <<< 54))
      (congrArg₂ mergePools
        (prune_port_getD (g := 5) (b := true) (loc := 5) hg (by decide))
        (prune_port_getD (g := 5) (b := true) (loc := 6) hg (by decide)))

lemma prune_group_pairMasks {s : State} {g : Fin 6} (hg : s.1.testBit g.val = false) :
    pairMasks (· &&& ·) (leftPool (prune s).2.1 g.val) (rightPool (prune s).2.1 g.val) =
      pairMasks (· &&& ·) (leftPool s.2.1 g.val) (rightPool s.2.1 g.val) := by
  rw [prune_leftPool hg, prune_rightPool hg]

end S200Resource

namespace S200Positive

open S200Resource OnceGeometry

abbrev Pools := OncePositive.Pools
abbrev or7 := OncePositive.or7
abbrev PoolsGood := OncePositive.PoolsGood
abbrev Witness := OncePositive.Witness
abbrev liftPool := OncePositive.liftPool
abbrev poolView := OncePositive.poolView

lemma or7_or (f h : Fin 7 → ℕ) : or7 (fun i => f i ||| h i) = or7 f ||| or7 h :=
  OncePositive.or7_or f h

lemma or7_update (f : Fin 7 → ℕ) (loc : Fin 7) (k : ℕ) :
    or7 (Function.update f loc (f loc ||| k)) = or7 f ||| k :=
  OncePositive.or7_update f loc k

lemma or7_filtered {L : Finset (Fin 7)} {f : Fin 7 → ℕ}
    (hf : ∀ i, i ∉ L → f i = 0) :
    or7 f = or7 (fun i => if i ∈ L then f i else 0) :=
  OncePositive.or7_filtered hf

def Rep (used : ℕ) (P : Pools) (S : Finset (Fin 10)) (m : ℕ) : Prop :=
  ∀ (g : Fin 6) (b : Bool), used.testBit g.val = false → S ⊆ S200Geometry.carrierPort g b →
    ∃ f, Witness P (S200Geometry.locations g b) f ∧ m = rawMask S ||| or7 f

lemma rep_raw {used : ℕ} {P : Pools} (hp : PoolsGood P) (S : Finset (Fin 10)) :
    Rep used P S (rawMask S) := by
  intro g b _ _
  refine ⟨fun _ => 0, ?_, ?_⟩
  · exact fun i => ⟨(hp i).1, fun _ => rfl⟩
  · simp [or7, OncePositive.or7]

lemma rep_or {used : ℕ} {P : Pools} (hp : PoolsGood P)
    {S T : Finset (Fin 10)} {a b : ℕ} (ha : Rep used P S a) (hb : Rep used P T b) :
    Rep used P (S ∪ T) (a ||| b) := by
  intro g side hu hST
  have hS : S ⊆ S200Geometry.carrierPort g side := fun v hv => hST (Finset.mem_union_left _ hv)
  have hT : T ⊆ S200Geometry.carrierPort g side := fun v hv => hST (Finset.mem_union_right _ hv)
  obtain ⟨f, hf, ha⟩ := ha g side hu hS
  obtain ⟨h, hh, hb⟩ := hb g side hu hT
  refine ⟨fun i => f i ||| h i, ?_, ?_⟩
  · intro i
    refine ⟨(hp i).2 _ (hf i).1 _ (hh i).1, ?_⟩
    intro hi
    change f i ||| h i = 0
    rw [(hf i).2 hi, (hh i).2 hi]
    rfl
  · rw [ha, hb, rawMask_union, or7_or]
    ac_rfl

lemma rep_mono {used : ℕ} {P Q : Pools} {S : Finset (Fin 10)} {m : ℕ}
    (hPQ : ∀ i x, x ∈ values (P i) → x ∈ values (Q i))
    (h : Rep used P S m) : Rep used Q S m := by
  intro g b hg hS
  obtain ⟨f, hf, hm⟩ := h g b hg hS
  exact ⟨f, fun i => ⟨hPQ i _ (hf i).1, (hf i).2⟩, hm⟩

lemma liftPool_mono (P : Pools) (loc : Fin 7) (k : ℕ) :
    ∀ i x, x ∈ values (P i) → x ∈ values (liftPool P loc k i) :=
  OncePositive.liftPool_mono P loc k

lemma poolsGood_lift {P : Pools} (hp : PoolsGood P) (loc : Fin 7) {k : ℕ} (hk : k < 64) :
    PoolsGood (liftPool P loc k) := OncePositive.poolsGood_lift hp loc hk

lemma rep_lift {used : ℕ} {P : Pools} {S : Finset (Fin 10)} {m k : ℕ}
    (h : Rep used P S m) (hk : k < 64) {v : Fin 10} (hv : v ∈ S) :
    Rep used (liftPool P (vertexClass v) k) S (m ||| k) := by
  intro g b hg hS
  have hvL := S200Geometry.support_class hS hv
  obtain ⟨f, hf, hm⟩ := h g b hg hS
  refine ⟨Function.update f (vertexClass v) (f (vertexClass v) ||| k), ?_, ?_⟩
  · intro i
    by_cases hi : i = vertexClass v
    · subst i
      constructor
      · simpa [liftPool, OncePositive.liftPool] using OnceResource.mem_addCarrier_or (hf (vertexClass v)).1 hk
      · intro hnot
        exact False.elim (hnot hvL)
    · simpa [liftPool, OncePositive.liftPool, Function.update_apply, hi] using hf i
  · rw [or7_update, hm]
    ac_rfl

lemma rep_restrict_pools {old new : ℕ} {P Q : Pools} {S : Finset (Fin 10)} {m : ℕ}
    (hgroups : ∀ g : Fin 6, new.testBit g.val = false → old.testBit g.val = false)
    (hzero : ∀ i, 0 ∈ values (Q i))
    (hpools : ∀ (g : Fin 6) (b : Bool), new.testBit g.val = false →
      ∀ i ∈ S200Geometry.locations g b, Q i = P i)
    (h : Rep old P S m) : Rep new Q S m := by
  intro g b hg hS
  obtain ⟨f, hf, hm⟩ := h g b (hgroups g hg) hS
  refine ⟨f, ?_, hm⟩
  intro i
  refine ⟨?_, (hf i).2⟩
  by_cases hi : i ∈ S200Geometry.locations g b
  · rw [hpools g b hg i hi]
    exact (hf i).1
  · rw [(hf i).2 hi]
    exact hzero i

lemma poolView_prune (s : State) (i : Fin 7) :
    poolView (prune s).2.1 i = if live s.1 i.val then poolView s.2.1 i else 1 := by
  simp [poolView, OncePositive.poolView, prune, List.getD_eq_getElem?_getD]

lemma mem_values_one_iff {x : ℕ} : x ∈ values 1 ↔ x = 0 := by
  rw [show (x ∈ values 1) ↔ x < 64 ∧ (1 : ℕ).testBit x = true from OnceResource.mem_values_iff,
    Nat.testBit_one_eq_true_iff_self_eq_zero]
  constructor
  · exact And.right
  · intro h; subst x; exact ⟨by decide, rfl⟩

lemma one_pool_good :
    0 ∈ values 1 ∧ ∀ a ∈ values 1, ∀ b ∈ values 1, a ||| b ∈ values 1 := by
  constructor
  · exact mem_values_one_iff.mpr rfl
  · intro a ha b hb
    obtain rfl := mem_values_one_iff.mp ha
    obtain rfl := mem_values_one_iff.mp hb
    exact mem_values_one_iff.mpr rfl

lemma poolsGood_prune {s : State} (hp : PoolsGood (poolView s.2.1)) :
    PoolsGood (poolView (prune s).2.1) := by
  intro i
  rw [poolView_prune]
  split
  · exact hp i
  · exact one_pool_good

lemma rep_prune {s : State} {S : Finset (Fin 10)} {m : ℕ}
    (hp : PoolsGood (poolView s.2.1)) (h : Rep s.1 (poolView s.2.1) S m) :
    Rep (prune s).1 (poolView (prune s).2.1) S m := by
  apply rep_restrict_pools (fun _ hg => hg) (fun i => (poolsGood_prune hp i).1) ?_ h
  intro g b hg i hi
  rw [poolView_prune, S200Geometry.port_locations_live hg b hi]
  rfl

lemma unused_of_or_unused {used extra i : ℕ}
    (h : (used ||| extra).testBit i = false) : used.testBit i = false := by
  rw [Nat.testBit_or] at h
  exact (Bool.or_eq_false_iff.mp h).1

lemma mark_used_lt {used : ℕ} (hu : used < 64) (g : Fin 6) :
    used ||| (1 <<< g.val) < 64 := by
  have hg : (1 <<< g.val : ℕ) < 64 := by fin_cases g <;> decide
  exact Nat.or_lt_two_pow (n := 6) hu hg

lemma rep_mark {used : ℕ} {P : Pools} {S : Finset (Fin 10)} {m : ℕ}
    (h : Rep used P S m) (g : Fin 6) : Rep (used ||| (1 <<< g.val)) P S m := by
  intro g' b hg hS
  exact h g' b (unused_of_or_unused hg) hS

lemma rep_mark_prune {used : ℕ} {ps : List ℕ} {S : Finset (Fin 10)} {m : ℕ}
    (hp : PoolsGood (poolView ps)) (h : Rep used (poolView ps) S m)
    (g : Fin 6) (zs : List ℕ) :
    Rep (used ||| (1 <<< g.val))
      (poolView (prune (used ||| (1 <<< g.val), ps, zs)).2.1) S m := by
  exact rep_prune (s := (used ||| (1 <<< g.val), ps, zs)) hp (rep_mark h g)

lemma poolView_set {ps : List ℕ} (hlen : ps.length = 7) (loc : Fin 7) (k : ℕ) :
    poolView (ps.set loc.val (addCarrier (ps.getD loc.val 1) k)) =
      liftPool (poolView ps) loc k := by
  funext i
  by_cases hi : i = loc
  · subst i
    have hb : loc.val < ps.length := by simpa only [hlen] using loc.isLt
    simp [poolView, OncePositive.poolView, liftPool, OncePositive.liftPool,
      List.getD_eq_getElem?_getD, List.getElem?_set_self hb]
    rfl
  · have hne : loc.val ≠ i.val := fun h => hi (Fin.ext h.symm)
    simp [poolView, OncePositive.poolView, liftPool, OncePositive.liftPool, hi,
      List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma poolsGood_set {ps : List ℕ} (hlen : ps.length = 7)
    (hp : PoolsGood (poolView ps)) (loc : Fin 7) {k : ℕ} (hk : k < 64) :
    PoolsGood (poolView (ps.set loc.val (addCarrier (ps.getD loc.val 1) k))) := by
  rw [poolView_set hlen]
  exact poolsGood_lift hp loc hk

lemma poolView_replicate_one : poolView (List.replicate 7 1) = fun _ => 1 := by
  funext i
  fin_cases i <;> rfl

lemma poolsGood_replicate_one : PoolsGood (poolView (List.replicate 7 1)) := by
  rw [poolView_replicate_one]
  exact fun _ => one_pool_good

def leftChoices (P : Pools) (g : Fin 6) : ℕ :=
  match g.val with | 0 => P 0 | 1 => P 1 | 2 => P 2 | 3 => P 3 | _ => 1

def rightChoices (P : Pools) (g : Fin 6) : ℕ :=
  match g.val with
  | 0 => mergePools (mergePools (P 1) (P 2)) (P 3)
  | 1 => mergePools (1 <<< 25) (P 4)
  | 2 => mergePools (1 <<< 42) (P 5)
  | 3 => mergePools (1 <<< 52) (P 6)
  | 4 => mergePools (1 <<< 9) (P 4)
  | _ => mergePools (1 <<< 54) (mergePools (P 5) (P 6))

def portChoices (P : Pools) (g : Fin 6) (b : Bool) : ℕ :=
  if b then rightChoices P g else leftChoices P g

lemma portChoices_view (ps : List ℕ) (g : Fin 6) (b : Bool)
    (htracked : g.val < 4 ∨ b = true) :
    portChoices (poolView ps) g b =
      if b then rightPool ps g.val else leftPool ps g.val := by
  cases b with
  | false =>
    have hg : g.val < 4 := htracked.resolve_right (by decide)
    have hcases : g.val = 0 ∨ g.val = 1 ∨ g.val = 2 ∨ g.val = 3 := by omega
    rcases hcases with heq | heq | heq | heq <;>
      simp [portChoices, leftChoices, poolView, OncePositive.poolView, leftPool, heq]
  | true =>
    fin_cases g <;> simp [portChoices, rightChoices, rightPool, poolView, OncePositive.poolView, basis]

lemma mem_singleton {k : ℕ} (hk : k < 64) : k ∈ values (1 <<< k) :=
  OnceResource.mem_singleton hk

lemma merge_mem {p q a b : ℕ} (ha : a ∈ values p) (hb : b ∈ values q) :
    a ||| b ∈ values (mergePools p q) := OncePositive.merge_mem ha hb

lemma portChoices_membership (P : Pools) (g : Fin 6) (b : Bool) (f : Fin 7 → ℕ)
    (hf : ∀ i, f i ∈ values (P i)) :
    rawMask (S200Geometry.carrierPort g b) |||
      or7 (fun i => if i ∈ S200Geometry.locations g b then f i else 0) ∈
      values (portChoices P g b) := by
  fin_cases g <;> cases b
  · rw [S200Geometry.raw_carrier_left]
    simpa [portChoices, leftChoices, S200Geometry.locations, or7, OncePositive.or7] using hf 0
  · rw [S200Geometry.raw_carrier_right]
    simpa [portChoices, rightChoices, S200Geometry.locations, or7, OncePositive.or7] using
      merge_mem (merge_mem (hf 1) (hf 2)) (hf 3)
  · rw [S200Geometry.raw_carrier_left]
    simpa [portChoices, leftChoices, S200Geometry.locations, or7, OncePositive.or7] using hf 1
  · rw [S200Geometry.raw_carrier_right]
    simpa [portChoices, rightChoices, S200Geometry.locations, or7, OncePositive.or7] using
      merge_mem (OnceResource.mem_singleton (by decide : 25 < 64)) (hf 4)
  · rw [S200Geometry.raw_carrier_left]
    simpa [portChoices, leftChoices, S200Geometry.locations, or7, OncePositive.or7] using hf 2
  · rw [S200Geometry.raw_carrier_right]
    simpa [portChoices, rightChoices, S200Geometry.locations, or7, OncePositive.or7] using
      merge_mem (OnceResource.mem_singleton (by decide : 42 < 64)) (hf 5)
  · rw [S200Geometry.raw_carrier_left]
    simpa [portChoices, leftChoices, S200Geometry.locations, or7, OncePositive.or7] using hf 3
  · rw [S200Geometry.raw_carrier_right]
    simpa [portChoices, rightChoices, S200Geometry.locations, or7, OncePositive.or7] using
      merge_mem (OnceResource.mem_singleton (by decide : 52 < 64)) (hf 6)
  · rw [S200Geometry.raw_carrier_left]
    simpa [portChoices, leftChoices, S200Geometry.locations, or7, OncePositive.or7] using one_pool_good.1
  · rw [S200Geometry.raw_carrier_right]
    simpa [portChoices, rightChoices, S200Geometry.locations, or7, OncePositive.or7] using
      merge_mem (OnceResource.mem_singleton (by decide : 9 < 64)) (hf 4)
  · rw [S200Geometry.raw_carrier_left]
    simpa [portChoices, leftChoices, S200Geometry.locations, or7, OncePositive.or7] using one_pool_good.1
  · rw [S200Geometry.raw_carrier_right]
    simpa [portChoices, rightChoices, S200Geometry.locations, or7, OncePositive.or7] using
      merge_mem (OnceResource.mem_singleton (by decide : 54 < 64)) (merge_mem (hf 5) (hf 6))

lemma rep_port_mem {used : ℕ} {P : Pools} {g : Fin 6} {b : Bool} {m : ℕ}
    (h : Rep used P (S200Geometry.carrierPort g b) m) (hu : used.testBit g.val = false) :
    m ∈ values (portChoices P g b) := by
  obtain ⟨f, hf, hm⟩ := h g b hu (Finset.Subset.refl _)
  rw [hm, or7_filtered (fun i => (hf i).2)]
  exact portChoices_membership P g b f (fun i => (hf i).1)

lemma physical_port_mem {used : ℕ} {ps : List ℕ} {g : Fin 6} {b : Bool} {m : ℕ}
    (h : Rep used (poolView ps) (S200Geometry.physicalPort g b) m)
    (hu : used.testBit g.val = false) (htracked : g.val < 4 ∨ b = true) :
    m ∈ values (if b then rightPool ps g.val else leftPool ps g.val) := by
  have hport : S200Geometry.carrierPort g b = S200Geometry.physicalPort g b := by
    simp [S200Geometry.carrierPort, htracked]
  have hm := rep_port_mem (g := g) (b := b) (hport ▸ h) hu
  rwa [portChoices_view ps g b htracked] at hm

lemma group_candidate {used : ℕ} {ps : List ℕ} {g : Fin 6} {a b : ℕ}
    (ha : if g.val < 4 then Rep used (poolView ps) (S200Geometry.physicalPort g false) a
      else a = 63)
    (hb : Rep used (poolView ps) (S200Geometry.physicalPort g true) b)
    (hu : used.testBit g.val = false) (hab : a &&& b < 64) :
    a &&& b ∈ values (pairMasks (· &&& ·) (leftPool ps g.val) (rightPool ps g.val)) := by
  have hleft : a ∈ values (leftPool ps g.val) := by
    by_cases hg : g.val < 4
    · rw [ite_eq_left hg] at ha
      exact physical_port_mem ha hu (Or.inl hg)
    · rw [ite_eq_right hg] at ha
      subst a
      rw [leftPool, ite_eq_right hg]
      exact mem_singleton (by decide : 63 < 64)
  have hright : b ∈ values (rightPool ps g.val) := physical_port_mem hb hu (Or.inr rfl)
  exact OnceResource.mem_pairMasks hleft hright hab

end S200Positive

namespace S200Resource

lemma sortedInsert_perm (k : ℕ) (xs : List ℕ) :
    List.Perm (sortedInsert k xs) (k :: xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
      simp only [sortedInsert]
      split
      · exact List.Perm.refl _
      · exact (List.Perm.cons x ih).trans (List.Perm.swap _ _ _)

lemma zeroSort_perm (xs : List ℕ) : List.Perm (zeroSort xs) xs := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
      exact (sortedInsert_perm x (zeroSort xs)).trans (List.Perm.cons x ih)

lemma insertZero_perm (k : ℕ) (xs : List ℕ) :
    List.Perm (insertZero k xs) (k :: xs) :=
  zeroSort_perm (k :: xs)

lemma mem_sortedInsert (a k : ℕ) (xs : List ℕ) :
    a ∈ sortedInsert k xs ↔ a = k ∨ a ∈ xs := by
  rw [(sortedInsert_perm k xs).mem_iff, List.mem_cons]

lemma mem_zeroSort (a : ℕ) (xs : List ℕ) :
    a ∈ zeroSort xs ↔ a ∈ xs :=
  (zeroSort_perm xs).mem_iff

lemma mem_insertZero (a k : ℕ) (xs : List ℕ) :
    a ∈ insertZero k xs ↔ a = k ∨ a ∈ xs := by
  rw [(insertZero_perm k xs).mem_iff, List.mem_cons]

lemma sortedInsert_length (k : ℕ) (xs : List ℕ) :
    (sortedInsert k xs).length = xs.length + 1 := by
  simpa only [List.length_cons] using (sortedInsert_perm k xs).length_eq

lemma zeroSort_length (xs : List ℕ) : (zeroSort xs).length = xs.length :=
  (zeroSort_perm xs).length_eq

lemma insertZero_length (k : ℕ) (xs : List ℕ) :
    (insertZero k xs).length = xs.length + 1 := by
  simpa only [List.length_cons] using (insertZero_perm k xs).length_eq

lemma prune_used (s : State) : (prune s).1 = s.1 := rfl

lemma prune_zeros (s : State) : (prune s).2.2 = s.2.2 := rfl

lemma prune_pool_getD (s : State) (i : ℕ) (hi : i < 7) :
    (prune s).2.1.getD i 1 = if live s.1 i then s.2.1.getD i 1 else 1 := by
  change ((List.range 7).map (fun j =>
    if live s.1 j then s.2.1.getD j 1 else 1)).getD i 1 = _
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]

lemma prune_idempotent (s : State) : prune (prune s) = prune s := by
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  change (List.range 7).map (fun i =>
    if live s.1 i then (prune s).2.1.getD i 1 else 1) =
      (List.range 7).map (fun i => if live s.1 i then s.2.1.getD i 1 else 1)
  apply List.map_congr_left
  intro i hi
  rw [prune_pool_getD s i (List.mem_range.mp hi)]
  split <;> rfl

lemma prune_pools_congr (s t : State) (hused : s.1 = t.1)
    (hpools : s.2.1 = t.2.1) : (prune s).2.1 = (prune t).2.1 := by
  change (List.range 7).map (fun i => if live s.1 i then s.2.1.getD i 1 else 1) =
    (List.range 7).map (fun i => if live t.1 i then t.2.1.getD i 1 else 1)
  rw [hused, hpools]

lemma groupNext_mem_successors {s t : State} (h : t ∈ groupNext s) :
    t ∈ successors s := by
  simp only [successors, List.mem_append, h, true_or]

lemma liftNext_mem_successors {s t : State} (h : t ∈ liftNext s) :
    t ∈ successors s := by
  simp only [successors, List.mem_append, h, true_or, or_true]

lemma discardNext_mem_successors {s t : State} (h : t ∈ discardNext s) :
    t ∈ successors s := by
  simp only [successors, List.mem_append, h, true_or, or_true]

lemma combineNext_mem_successors {s t : State} (h : t ∈ combineNext s) :
    t ∈ successors s := by
  simp only [successors, List.mem_append, h, or_true]

lemma group_successor {s : State} {g k : ℕ}
    (hg : g < 6) (hunused : s.1.testBit g = false)
    (hk : k ∈ values (pairMasks (· &&& ·) (leftPool s.2.1 g) (rightPool s.2.1 g)))
    (hkn : k ≠ 0) :
    prune (s.1 ||| (1 <<< g), s.2.1, insertZero k s.2.2) ∈ successors s := by
  apply groupNext_mem_successors
  apply List.mem_flatMap.mpr
  refine ⟨g, List.mem_range.mpr hg, ?_⟩
  simp only [hunused, Bool.false_eq_true, ↓reduceIte]
  apply List.mem_filterMap.mpr
  exact ⟨k, hk, by simp [hkn]⟩

lemma lift_successor {s : State} {k loc : ℕ}
    (hk : k ∈ s.2.2) (hloc : loc < 7) (hlive : live s.1 loc = true)
    (hchange : addCarrier (s.2.1.getD loc 1) k ≠ s.2.1.getD loc 1) :
    prune (s.1, s.2.1.set loc (addCarrier (s.2.1.getD loc 1) k),
      s.2.2.erase k) ∈ successors s := by
  apply liftNext_mem_successors
  apply List.mem_flatMap.mpr
  refine ⟨k, hk, ?_⟩
  apply List.mem_filterMap.mpr
  exact ⟨loc, List.mem_range.mpr hloc, by simp only [hlive, hchange, ↓reduceIte]⟩

lemma discard_successor {s : State} {k : ℕ} (hk : k ∈ s.2.2) :
    prune (s.1, s.2.1, s.2.2.erase k) ∈ successors s := by
  apply discardNext_mem_successors
  exact List.mem_map.mpr ⟨k, hk, rfl⟩

lemma combine_successor {s : State} {a b k : ℕ}
    (ha : a ∈ s.2.2) (hb : b ∈ s.2.2.erase a)
    (hk : k = a &&& b ∨ k = a ||| b) (hkn : k ≠ 0) :
    prune (s.1, s.2.1, insertZero k ((s.2.2.erase a).erase b)) ∈ successors s := by
  apply combineNext_mem_successors
  apply List.mem_flatMap.mpr
  refine ⟨a, ha, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨b, hb, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨k, ?_, by simp [hkn]⟩
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using hk

lemma reachable_of_eq_or_successor {s t : State}
    (h : t = s ∨ t ∈ successors s) :
    Relation.ReflTransGen (fun a b : State => b ∈ successors a) s t := by
  rcases h with rfl | h
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single h

namespace ZeroTransitions

def token (k : ℕ) : Multiset ℕ := if k = 0 then 0 else {k}

lemma mem_of_zero_eq {zs : List ℕ} {a : ℕ} {rest : Multiset ℕ}
    (hz : (zs : Multiset ℕ) = {a} + rest) : a ∈ zs := by
  change a ∈ (zs : Multiset ℕ)
  rw [hz]
  simp

lemma erase_of_zero_eq {zs : List ℕ} {a : ℕ} {rest : Multiset ℕ}
    (hz : (zs : Multiset ℕ) = {a} + rest) :
    (zs.erase a : Multiset ℕ) = rest := by
  change (zs : Multiset ℕ).erase a = rest
  rw [hz]
  simp

lemma coe_insertZero (k : ℕ) (zs : List ℕ) :
    (insertZero k zs : Multiset ℕ) = {k} + (zs : Multiset ℕ) := by
  change (insertZero k zs : Multiset ℕ) = ((k :: zs : List ℕ) : Multiset ℕ)
  exact Quot.sound (insertZero_perm k zs)

lemma discard_one {s : State} {a : ℕ} {rest : Multiset ℕ}
    (hz : (s.2.2 : Multiset ℕ) = {a} + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      (t.2.2 : Multiset ℕ) = rest ∧ t.1 = s.1 ∧
      t.2.1 = (prune s).2.1 := by
  refine ⟨prune (s.1, s.2.1, s.2.2.erase a),
    Relation.ReflTransGen.single (discard_successor (mem_of_zero_eq hz)),
    erase_of_zero_eq hz, rfl, rfl⟩

lemma discard_two {s : State} {a b : ℕ} {rest : Multiset ℕ}
    (hz : (s.2.2 : Multiset ℕ) = {a} + {b} + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      (t.2.2 : Multiset ℕ) = rest ∧ t.1 = s.1 ∧
      t.2.1 = (prune s).2.1 := by
  have hz' : (s.2.2 : Multiset ℕ) = {a} + ({b} + rest) := by
    simpa only [Multiset.add_assoc] using hz
  have ha := mem_of_zero_eq hz'
  have hz1 := erase_of_zero_eq hz'
  have hb := mem_of_zero_eq hz1
  have hz2 := erase_of_zero_eq hz1
  let t1 : State := prune (s.1, s.2.1, s.2.2.erase a)
  let t2 : State := prune (s.1, s.2.1, (s.2.2.erase a).erase b)
  have h1 : t1 ∈ successors s := discard_successor ha
  have h2 : t2 ∈ successors t1 := by
    have hh := discard_successor (s := t1) (k := b) hb
    change prune (prune (s.1, s.2.1, (s.2.2.erase a).erase b)) ∈
      successors t1 at hh
    rw [prune_idempotent] at hh
    exact hh
  exact ⟨t2, (Relation.ReflTransGen.single h1).trans (Relation.ReflTransGen.single h2),
    hz2, rfl, rfl⟩

lemma combine_nonzero {s : State} {a b k : ℕ} {rest : Multiset ℕ}
    (hz : (s.2.2 : Multiset ℕ) = {a} + {b} + rest)
    (hop : k = a &&& b ∨ k = a ||| b) (hk : k ≠ 0) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      (t.2.2 : Multiset ℕ) = {k} + rest ∧ t.1 = s.1 ∧
      t.2.1 = (prune s).2.1 := by
  have hz' : (s.2.2 : Multiset ℕ) = {a} + ({b} + rest) := by
    simpa only [Multiset.add_assoc] using hz
  have ha := mem_of_zero_eq hz'
  have hz1 := erase_of_zero_eq hz'
  have hb := mem_of_zero_eq hz1
  have hz2 := erase_of_zero_eq hz1
  refine ⟨prune (s.1, s.2.1, insertZero k ((s.2.2.erase a).erase b)),
    Relation.ReflTransGen.single (combine_successor ha hb hop hk), ?_, rfl, rfl⟩
  change (insertZero k ((s.2.2.erase a).erase b) : Multiset ℕ) = {k} + rest
  rw [coe_insertZero, hz2]

lemma zero_binary {s : State} (a b : ℕ) (isAnd : Bool) (rest : Multiset ℕ)
    (hz : (s.2.2 : Multiset ℕ) = token a + token b + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      (t.2.2 : Multiset ℕ) = token (if isAnd then a &&& b else a ||| b) + rest ∧
      t.1 = s.1 ∧
      (t.2.1 = s.2.1 ∨ t.2.1 = (prune s).2.1) := by
  by_cases ha : a = 0
  · subst a
    cases isAnd
    · refine ⟨s, Relation.ReflTransGen.refl, ?_, rfl, Or.inl rfl⟩
      simpa [token] using hz
    · by_cases hb : b = 0
      · subst b
        refine ⟨s, Relation.ReflTransGen.refl, ?_, rfl, Or.inl rfl⟩
        simpa [token] using hz
      · have hz' : (s.2.2 : Multiset ℕ) = {b} + rest := by simpa [token, hb] using hz
        obtain ⟨t, hr, ht, hu, hp⟩ := discard_one hz'
        exact ⟨t, hr, by simpa [token] using ht, hu, Or.inr hp⟩
  · by_cases hb : b = 0
    · subst b
      cases isAnd
      · refine ⟨s, Relation.ReflTransGen.refl, ?_, rfl, Or.inl rfl⟩
        simpa [token] using hz
      · have hz' : (s.2.2 : Multiset ℕ) = {a} + rest := by simpa [token, ha] using hz
        obtain ⟨t, hr, ht, hu, hp⟩ := discard_one hz'
        exact ⟨t, hr, by simpa [token] using ht, hu, Or.inr hp⟩
    · have hz' : (s.2.2 : Multiset ℕ) = {a} + {b} + rest := by
        simpa [token, ha, hb] using hz
      let k := if isAnd then a &&& b else a ||| b
      by_cases hk : k = 0
      · obtain ⟨t, hr, ht, hu, hp⟩ := discard_two hz'
        refine ⟨t, hr, ?_, hu, Or.inr hp⟩
        change (t.2.2 : Multiset ℕ) = token k + rest
        rw [hk]
        simpa [token] using ht
      · have hop : k = a &&& b ∨ k = a ||| b := by cases isAnd <;> simp [k]
        obtain ⟨t, hr, ht, hu, hp⟩ := combine_nonzero hz' hop hk
        refine ⟨t, hr, ?_, hu, Or.inr hp⟩
        change (t.2.2 : Multiset ℕ) = token k + rest
        simpa [token, hk] using ht

end ZeroTransitions

end S200Resource

namespace S200Resource

lemma set_getD_self (xs : List ℕ) (i d : ℕ) : xs.set i (xs.getD i d) = xs := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact congrArg (List.cons x) (ih i)

lemma lift_successor_or_discard {s : State} {k loc : ℕ}
    (hk : k ∈ s.2.2) (hloc : loc < 7) (hlive : live s.1 loc = true) :
    prune (s.1, s.2.1.set loc (addCarrier (s.2.1.getD loc 1) k), s.2.2.erase k) ∈ successors s := by
  by_cases hchange : addCarrier (s.2.1.getD loc 1) k = s.2.1.getD loc 1
  · rw [hchange, set_getD_self]
    exact discard_successor hk
  · exact lift_successor hk hloc hlive hchange

lemma lift_reachable {s : State} {k loc : ℕ}
    (hk : k ∈ s.2.2) (hloc : loc < 7) (hlive : live s.1 loc = true) :
    Relation.ReflTransGen (fun a b : State => b ∈ successors a) s
      (prune (s.1, s.2.1.set loc (addCarrier (s.2.1.getD loc 1) k), s.2.2.erase k)) :=
  Relation.ReflTransGen.single (lift_successor_or_discard hk hloc hlive)

end S200Resource

namespace S200Positive

open S200Resource OnceGeometry

lemma rep_of_dead_class {used : ℕ} {P : Pools} {S : Finset (Fin 10)} {v : Fin 10}
    (hv : v ∈ S) (hd : live used (vertexClass v).val = false) (m : ℕ) :
    Rep used P S m := by
  intro g b hg hS
  have hl := S200Geometry.port_locations_live hg b (S200Geometry.support_class hS hv)
  simp [hd] at hl

lemma positive_lift_step {s : State} {S : Finset (Fin 10)} {m k : ℕ}
    (hlen : s.2.1.length = 7) (hp : PoolsGood (poolView s.2.1))
    (h : Rep s.1 (poolView s.2.1) S m) (hs : S.Nonempty)
    (hk : k < 64) (hmem : k ∈ s.2.2) :
    ∃ t : State,
      Relation.ReflTransGen (fun a b : State => b ∈ successors a) s t ∧
      t.1 = s.1 ∧ t.2.2 = s.2.2.erase k ∧
      t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep s.1 (poolView s.2.1) T n → Rep t.1 (poolView t.2.1) T n) ∧
      Rep t.1 (poolView t.2.1) S (m ||| k) := by
  obtain ⟨v, hv⟩ := hs
  by_cases hl : live s.1 (vertexClass v).val = true
  · let q : State := (s.1,
        s.2.1.set (vertexClass v).val (addCarrier (s.2.1.getD (vertexClass v).val 1) k),
        s.2.2.erase k)
    have hqgood : PoolsGood (poolView q.2.1) := poolsGood_set hlen hp (vertexClass v) hk
    refine ⟨prune q, lift_reachable hmem (vertexClass v).isLt hl, rfl, rfl,
      prune_pools_length q, poolsGood_prune hqgood, ?_, ?_⟩
    · intro T n hT
      apply rep_prune (s := q) hqgood
      change Rep s.1 (poolView (s.2.1.set (vertexClass v).val
        (addCarrier (s.2.1.getD (vertexClass v).val 1) k))) T n
      rw [poolView_set hlen]
      exact rep_mono (liftPool_mono _ _ _) hT
    · apply rep_prune (s := q) hqgood
      change Rep s.1 (poolView (s.2.1.set (vertexClass v).val
        (addCarrier (s.2.1.getD (vertexClass v).val 1) k))) S (m ||| k)
      rw [poolView_set hlen]
      exact rep_lift h hk hv
  · have hd : live s.1 (vertexClass v).val = false := Bool.eq_false_of_not_eq_true hl
    let q : State := (s.1, s.2.1, s.2.2.erase k)
    refine ⟨prune q, Relation.ReflTransGen.single (discard_successor hmem), rfl, rfl,
      prune_pools_length q, poolsGood_prune hp, ?_, ?_⟩
    · intro T n hT
      exact rep_prune (s := q) hp hT
    · exact rep_of_dead_class hv hd _

lemma positive_group_step {s : State} {g : Fin 6} {a b : ℕ}
    (hu : s.1 < 64) (hp : PoolsGood (poolView s.2.1))
    (ha : if g.val < 4 then Rep s.1 (poolView s.2.1) (S200Geometry.physicalPort g false) a
      else a = 63)
    (hb : Rep s.1 (poolView s.2.1) (S200Geometry.physicalPort g true) b)
    (hg : s.1.testBit g.val = false) (hab : a &&& b < 64) (hne : a &&& b ≠ 0) :
    let t := prune (s.1 ||| (1 <<< g.val), s.2.1, insertZero (a &&& b) s.2.2)
    t ∈ successors s ∧ t.1 < 64 ∧ t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep s.1 (poolView s.2.1) T n → Rep t.1 (poolView t.2.1) T n) := by
  dsimp only
  have hc := group_candidate ha hb hg hab
  refine ⟨group_successor g.isLt hg hc hne, mark_used_lt hu g,
    prune_pools_length _, poolsGood_prune hp, ?_⟩
  intro T n hT
  exact rep_mark_prune hp hT g _

end S200Positive

namespace S200Simulation

open S200Resource S200Positive
open OnceResource.IndexCopies OnceResource.TokenMap

abbrev Reach (s t : State) : Prop :=
  Relation.ReflTransGen (fun a b : State => b ∈ successors a) s t

def contrib (S : Finset (Fin 10)) (m : ℕ) : Multiset ℕ :=
  if S = ∅ then OnceResource.TokenMap.token m else 0

def Healthy (s : State) : Prop :=
  s.1 < 64 ∧ s.2.1.length = 7 ∧ OncePositive.PoolsGood (OncePositive.poolView s.2.1)

def Preserves (s t : State) : Prop :=
  ∀ T m, S200Positive.Rep s.1 (OncePositive.poolView s.2.1) T m →
    S200Positive.Rep t.1 (OncePositive.poolView t.2.1) T m

def LocalResult (s q : State) (S : Finset (Fin 10)) (m : ℕ)
    (rest : Multiset ℕ) (group : Option (Fin 6)) : Prop :=
  Reach s q ∧ Healthy q ∧ (q.2.2 : Multiset ℕ) = contrib S m + rest ∧
  Preserves s q ∧ (S.Nonempty → Rep q.1 (OncePositive.poolView q.2.1) S m) ∧
  (∀ g : Fin 6, q.1.testBit g.val = true → s.1.testBit g.val = true ∨ group = some g)

def ProgramCallback (S : ℕ → Finset (Fin 10)) (M A B : ℕ → ℕ)
    (G : ℕ → Option (Fin 6)) (start n : ℕ) : Prop :=
  ∀ t < n, ∀ (s : State) (rest : Multiset ℕ), Healthy s →
    ((S (A (start + t))).Nonempty →
      Rep s.1 (OncePositive.poolView s.2.1) (S (A (start + t))) (M (A (start + t)))) →
    ((S (B (start + t))).Nonempty →
      Rep s.1 (OncePositive.poolView s.2.1) (S (B (start + t))) (M (B (start + t)))) →
    (s.2.2 : Multiset ℕ) = contrib (S (A (start + t))) (M (A (start + t))) +
      contrib (S (B (start + t))) (M (B (start + t))) + rest →
    (∀ g : Fin 6, G (start + t) = some g → s.1.testBit g.val = false) →
    ∃ q, LocalResult s q (S (start + t)) (M (start + t)) rest (G (start + t))

def GroupUnique (G : ℕ → Option (Fin 6)) (start n : ℕ) : Prop :=
  ∀ i < n, ∀ j < n, ∀ g : Fin 6,
    G (start + i) = some g → G (start + j) = some g → i = j

def ProgramInv (S : ℕ → Finset (Fin 10)) (M A B : ℕ → ℕ)
    (G : ℕ → Option (Fin 6)) (start n t : ℕ) (s : State) : Prop :=
  Healthy s ∧ (s.2.2 : Multiset ℕ) =
    project (fun w => S w = ∅) M (Available (fun w => S w = ∅) start (start+n) A B t) ∧
  (∀ w < start + t, (S w).Nonempty →
    Rep s.1 (OncePositive.poolView s.2.1) (S w) (M w)) ∧
  ∀ g : Fin 6, s.1.testBit g.val = true → ∃ j < t, G (start + j) = some g

lemma program_inv_step {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 6)} {start n t : ℕ} {s : State}
    (hv : Valid start A B n)
    (hcap : ∀ w, S w = ∅ → ReadCount start A B n w ≤ 1)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback S M A B G start n)
    (ht : t < n) (hinv : ProgramInv S M A B G start n t s) :
    ∃ q, Reach s q ∧ ProgramInv S M A B G start n (t+1) q := by
  obtain ⟨hhealthy, hzeros, hreps, hused⟩ := hinv
  obtain ⟨ha, hb, hab⟩ := hv t ht
  have hcap' : ∀ w, S w = ∅ → ReadCount start A B n w ≤ Capacity (start+n) w := by
    intro w hw
    apply (hcap w hw).trans
    unfold Capacity
    split_ifs <;> decide
  obtain ⟨rest, hids, _⟩ := available_step_decomp (fun w => S w = ∅) hv hcap' ht
  have hzero_input : (s.2.2 : Multiset ℕ) =
      contrib (S (A (start + t))) (M (A (start + t))) +
      contrib (S (B (start + t))) (M (B (start + t))) + project (fun w => S w = ∅) M rest := by
    rw [hzeros, hids, project_cons, project_cons]
    simp only [contrib, Multiset.add_assoc]
  have hunused : ∀ g : Fin 6, G (start + t) = some g → s.1.testBit g.val = false := by
    intro g hg
    cases hbit : s.1.testBit g.val with
    | false => rfl
    | true =>
      obtain ⟨j, hj, hjg⟩ := hused g hbit
      have heq := hgroups t ht j (by omega) g hg hjg
      omega
  obtain ⟨q, hreach, hhealth, hzero, hpres, hnew, huse⟩ :=
    hcallback t ht s (project (fun w => S w = ∅) M rest) hhealthy
      (hreps _ ha) (hreps _ hb) hzero_input hunused
  refine ⟨q, hreach, hhealth, ?_, ?_, ?_⟩
  · rw [Available, project_step (fun w => S w = ∅) M hids hab]
    have hne : start+t ≠ start+n := by omega
    simpa only [hne, and_false, ite_false, Multiset.add_zero, contrib] using hzero
  · intro w hw hSw
    by_cases hold : w < start+t
    · exact hpres _ _ (hreps w hold hSw)
    · have heq : w = start+t := by omega
      subst w
      exact hnew hSw
  · intro g hg
    rcases huse g hg with hg | hg
    · obtain ⟨j, hj, hjg⟩ := hused g hg
      exact ⟨j, by omega, hjg⟩
    · exact ⟨t, by omega, hg⟩

lemma program_induction_prefix {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 6)} {start n : ℕ} {s₀ : State}
    (hv : Valid start A B n) (hcap : ∀ w, S w = ∅ → ReadCount start A B n w ≤ 1)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback S M A B G start n)
    (hinit : ProgramInv S M A B G start n 0 s₀) :
    ∀ t ≤ n, ∃ s, Reach s₀ s ∧ ProgramInv S M A B G start n t s := by
  intro t
  induction t with
  | zero => intro _; exact ⟨s₀, Relation.ReflTransGen.refl, hinit⟩
  | succ t ih =>
    intro ht
    obtain ⟨s, hreach, hinv⟩ := ih (by omega)
    obtain ⟨q, hstep, hiq⟩ := program_inv_step hv hcap hgroups hcallback (by omega) hinv
    exact ⟨q, hreach.trans hstep, hiq⟩

lemma program_target_excluded {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 6)} {start n w : ℕ}
    (hsafe : ∀ s : State, Reach initial s → 56 ∉ s.2.2)
    (hv : Valid start A B n) (hcap : ∀ u, S u = ∅ → ReadCount start A B n u ≤ 1)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback S M A B G start n)
    (hinit : ProgramInv S M A B G start n 0 initial)
    (hw : w ∈ Available (fun u => S u = ∅) start (start+n) A B n)
    (hSw : S w = ∅) (hMw : M w = 56) : False := by
  obtain ⟨s, hr, hi⟩ := program_induction_prefix hv hcap hgroups hcallback hinit n (Nat.le_refl n)
  have hMne : M w ≠ 0 := by omega
  have hm := project_mem (fun u => S u = ∅) M hw hSw hMne
  rw [hMw] at hm
  have ht : 56 ∈ s.2.2 := by
    change 56 ∈ (s.2.2 : Multiset ℕ)
    rw [hi.2.1]
    exact hm
  exact hsafe s hr ht

end S200Simulation

namespace S200Simulation

open S200Geometry

def ProgramSemantics (S : ℕ → Finset (Fin 10)) (M A B : ℕ → ℕ)
    (G : ℕ → Option (Fin 6)) (Op : ℕ → Bool) (start n : ℕ) : Prop :=
  ∀ t < n,
    if Op (start + t) then
      S (start + t) = ∅ ∧ M (start + t) = M (A (start + t)) &&& M (B (start + t)) ∧
        (match G (start + t) with
        | none => S (A (start + t)) = ∅ ∧ S (B (start + t)) = ∅
        | some g =>
          (S (A (start + t)) = physicalPort g false ∧ S (B (start + t)) = physicalPort g true) ∨
          (S (A (start + t)) = physicalPort g true ∧ S (B (start + t)) = physicalPort g false))
    else G (start + t) = none ∧
      S (start + t) = S (A (start + t)) ∪ S (B (start + t)) ∧
      M (start + t) = M (A (start + t)) ||| M (B (start + t))

end S200Simulation

namespace S200Positive

open S200Resource OnceGeometry

lemma frame_preserves {s t : State}
    (hu : s.1 < 64) (hlen : s.2.1.length = 7) (hp : PoolsGood (poolView s.2.1))
    (ht : t.1 = s.1) (hps : t.2.1 = s.2.1 ∨ t.2.1 = (prune s).2.1) :
    t.1 < 64 ∧ t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep s.1 (poolView s.2.1) T n → Rep t.1 (poolView t.2.1) T n) := by
  refine ⟨by simpa only [ht] using hu, ?_⟩
  rcases hps with he | he
  · rw [he, ht]
    exact ⟨hlen, hp, fun _ _ h => h⟩
  · rw [he, ht]
    exact ⟨prune_pools_length s, poolsGood_prune hp, fun _ _ h => rep_prune hp h⟩

lemma zero_binary_positive_state {s : State} (a b : ℕ) (isAnd : Bool) (rest : Multiset ℕ)
    (hu : s.1 < 64) (hlen : s.2.1.length = 7) (hp : PoolsGood (poolView s.2.1))
    (hz : (s.2.2 : Multiset ℕ) =
      ZeroTransitions.token a + ZeroTransitions.token b + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      t.1 = s.1 ∧
      (t.2.2 : Multiset ℕ) =
        ZeroTransitions.token (if isAnd then a &&& b else a ||| b) + rest ∧
      t.1 < 64 ∧ t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep s.1 (poolView s.2.1) T n → Rep t.1 (poolView t.2.1) T n) := by
  obtain ⟨t, hr, hz', ht, hps⟩ := ZeroTransitions.zero_binary a b isAnd rest hz
  exact ⟨t, hr, ht, hz', frame_preserves hu hlen hp ht hps⟩

end S200Positive

namespace S200Simulation
open S200Resource S200Geometry S200Positive

lemma lift_token_step {s : State} {S : Finset (Fin 10)} {m k : ℕ} {rest : Multiset ℕ}
    (hs : Healthy s) (hS : S.Nonempty) (hm : Rep s.1 (poolView s.2.1) S m)
    (hk : k < 64) (hz : (s.2.2 : Multiset ℕ) = OnceResource.TokenMap.token k + rest) :
    ∃ q, LocalResult s q S (m ||| k) rest none := by
  have hne : S ≠ ∅ := hS.ne_empty
  by_cases hk0 : k = 0
  · subst k
    refine ⟨s, Relation.ReflTransGen.refl, hs, ?_, (fun _ _ h => h), ?_, ?_⟩
    · simpa [contrib, OnceResource.TokenMap.token, hne] using hz
    · intro _
      simpa using hm
    · exact fun _ h => Or.inl h
  · have hmem : k ∈ s.2.2 := by
      have hm' : k ∈ (s.2.2 : Multiset ℕ) := by rw [hz]; simp [OnceResource.TokenMap.token, hk0]
      exact hm'
    obtain ⟨q, hr, hu, hqz, hl, hp, hpres, hrep⟩ :=
      positive_lift_step hs.2.1 hs.2.2 hm hS hk hmem
    refine ⟨q, hr, ⟨by simpa [hu] using hs.1, hl, hp⟩, ?_, hpres,
      (fun _ => hrep), ?_⟩
    · rw [hqz, ← Multiset.coe_erase, hz]
      simp [contrib, hne, OnceResource.TokenMap.token, hk0]
    · intro g hg
      exact Or.inl (hu ▸ hg)

lemma or_local {s : State} {S T : Finset (Fin 10)} {a b : ℕ} {rest : Multiset ℕ}
    (hs : Healthy s) (ha : S.Nonempty → Rep s.1 (poolView s.2.1) S a)
    (hb : T.Nonempty → Rep s.1 (poolView s.2.1) T b)
    (hab : a < 64 ∧ b < 64)
    (hz : (s.2.2 : Multiset ℕ) = contrib S a + contrib T b + rest) :
    ∃ q, LocalResult s q (S ∪ T) (a ||| b) rest none := by
  by_cases hS : S = ∅
  · subst S
    by_cases hT : T = ∅
    · subst T
      have hz' : (s.2.2 : Multiset ℕ) =
          ZeroTransitions.token a + ZeroTransitions.token b + rest := by
        simpa [contrib, ZeroTransitions.token, OnceResource.TokenMap.token] using hz
      obtain ⟨q, hr, hu, hqz, hqu, hql, hqp, hpres⟩ :=
        zero_binary_positive_state a b false rest hs.1 hs.2.1 hs.2.2 hz'
      refine ⟨q, hr, ⟨hqu, hql, hqp⟩, ?_, hpres, ?_, ?_⟩
      · simpa [contrib, ZeroTransitions.token, OnceResource.TokenMap.token] using hqz
      · simp
      · intro g hg
        exact Or.inl (hu ▸ hg)
    · have hTn : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
      have hz' : (s.2.2 : Multiset ℕ) = OnceResource.TokenMap.token a + rest := by
        simpa [contrib, hT] using hz
      obtain ⟨q, hq⟩ := lift_token_step hs hTn (hb hTn) hab.1 hz'
      refine ⟨q, ?_⟩
      simpa [Nat.or_comm] using hq
  · have hSn : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    by_cases hT : T = ∅
    · subst T
      have hz' : (s.2.2 : Multiset ℕ) = OnceResource.TokenMap.token b + rest := by
        simpa [contrib, hS] using hz
      obtain ⟨q, hq⟩ := lift_token_step hs hSn (ha hSn) hab.2 hz'
      exact ⟨q, by simpa using hq⟩
    · have hTn : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
      have hST : S ∪ T ≠ ∅ := (hSn.mono Finset.subset_union_left).ne_empty
      refine ⟨s, Relation.ReflTransGen.refl, hs, ?_, (fun _ _ h => h), ?_, ?_⟩
      · simpa [contrib, hS, hT, hST] using hz
      · intro _
        exact rep_or hs.2.2 (ha hSn) (hb hTn)
      · exact fun _ h => Or.inl h

lemma marked_group {used : ℕ} {g h : Fin 6}
    (ht : (used ||| (1 <<< g.val)).testBit h.val = true) :
    used.testBit h.val = true ∨ g = h := by
  rw [Nat.testBit_or, Bool.or_eq_true] at ht
  rcases ht with ht | ht
  · exact Or.inl ht
  · right
    have hsingle := OnceResource.testBit_singleton_iff.mp ht
    exact Fin.ext hsingle

lemma pure_local {s : State} {g : Fin 6} {a b : ℕ} {rest : Multiset ℕ}
    (hs : Healthy s)
    (ha : if g.val < 4 then Rep s.1 (poolView s.2.1) (physicalPort g false) a else a = 63)
    (hb : Rep s.1 (poolView s.2.1) (physicalPort g true) b)
    (hk : a &&& b < 64) (hunused : s.1.testBit g.val = false)
    (hz : (s.2.2 : Multiset ℕ) = rest) :
    ∃ q, LocalResult s q ∅ (a &&& b) rest (some g) := by
  by_cases hk0 : a &&& b = 0
  · refine ⟨s, Relation.ReflTransGen.refl, hs, ?_, (fun _ _ h => h), ?_, ?_⟩
    · simpa [contrib, OnceResource.TokenMap.token, hk0] using hz
    · simp
    · exact fun _ h => Or.inl h
  · let q := prune (s.1 ||| (1 <<< g.val), s.2.1, insertZero (a &&& b) s.2.2 )
    obtain ⟨hr, hu, hl, hp, hpres⟩ := positive_group_step hs.1 hs.2.2 ha hb hunused hk hk0
    refine ⟨q, Relation.ReflTransGen.single hr, ⟨hu, hl, hp⟩, ?_, hpres, ?_, ?_⟩
    · change (insertZero (a &&& b) s.2.2 : Multiset ℕ) = _
      rw [ZeroTransitions.coe_insertZero, hz]
      simp [contrib, OnceResource.TokenMap.token, hk0]
    · simp
    · intro h hh
      change (s.1 ||| (1 <<< g.val)).testBit h.val = true at hh
      rcases marked_group (g := g) hh with hh | hh
      · exact Or.inl hh
      · exact Or.inr (congrArg some hh)

lemma zero_local {s : State} {a b : ℕ} {rest : Multiset ℕ}
    (hs : Healthy s)
    (hz : (s.2.2 : Multiset ℕ) = OnceResource.TokenMap.token a + OnceResource.TokenMap.token b + rest) :
    ∃ q, LocalResult s q ∅ (a &&& b) rest none := by
  obtain ⟨q, hr, hu, hqz, hqu, hql, hqp, hpres⟩ :=
    zero_binary_positive_state a b true rest hs.1 hs.2.1 hs.2.2 hz
  refine ⟨q, hr, ⟨hqu, hql, hqp⟩, ?_, hpres, ?_, ?_⟩
  · exact hqz
  · simp
  · intro g hg
    exact Or.inl (hu ▸ hg)

end S200Simulation

namespace S200Simulation
open S200Resource S200Geometry S200Positive

lemma gate_local {s : State} {S T U : Finset (Fin 10)} {a b c : Nat}
    {rest : Multiset Nat} (op : Bool) (group : Option (Fin 6))
    (hs : Healthy s) (ha : S.Nonempty → Rep s.1 (poolView s.2.1) S a)
    (hb : T.Nonempty → Rep s.1 (poolView s.2.1) T b)
    (hfullA : S = {3, 6, 7} → a = 63)
    (hfullB : T = {3, 6, 7} → b = 63)
    (hm : a < 64 ∧ b < 64 ∧ c < 64)
    (hz : (s.2.2 : Multiset Nat) = contrib S a + contrib T b + rest)
    (hunused : ∀ g : Fin 6, group = some g → s.1.testBit g.val = false)
    (hsem : if op then
      U = ∅ ∧ c = a &&& b ∧
        (match group with
        | none => S = ∅ ∧ T = ∅
        | some g => (S = physicalPort g false ∧ T = physicalPort g true) ∨
          (S = physicalPort g true ∧ T = physicalPort g false))
      else group = none ∧ U = S ∪ T ∧ c = a ||| b) :
    ∃ q, LocalResult s q U c rest group := by
  cases op with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hsem
    obtain ⟨rfl, rfl, rfl⟩ := hsem
    exact or_local hs ha hb ⟨hm.1, hm.2.1⟩ hz
  | true =>
    simp only [↓reduceIte] at hsem
    obtain ⟨rfl, rfl, hports⟩ := hsem
    cases group with
    | none =>
      obtain ⟨rfl, rfl⟩ := hports
      exact zero_local hs (by simpa [contrib] using hz)
    | some g =>
      have hu := hunused g rfl
      have hl : (physicalPort g false).Nonempty := by fin_cases g <;> decide
      have hr : (physicalPort g true).Nonempty := by fin_cases g <;> decide
      have hdirty : ¬g.val < 4 → physicalPort g false = {3, 6, 7} := by
        intro hg
        fin_cases g <;> simp_all [physicalPort]
      rcases hports with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hz' : (s.2.2 : Multiset Nat) = rest := by
          simpa [contrib, hl.ne_empty, hr.ne_empty] using hz
        apply pure_local hs ?_ (hb hr) hm.2.2 hu hz'
        split
        · exact ha hl
        · exact hfullA (hdirty ‹¬g.val < 4›)
      · have hz' : (s.2.2 : Multiset Nat) = rest := by
          simpa [contrib, hl.ne_empty, hr.ne_empty] using hz
        have hleft : if g.val < 4 then
            Rep s.1 (poolView s.2.1) (physicalPort g false) b else b = 63 := by
          split
          · exact hb hl
          · exact hfullB (hdirty ‹¬g.val < 4›)
        obtain ⟨q, hq⟩ := pure_local hs hleft (ha hr)
          (by simpa [Nat.and_comm] using hm.2.2) hu hz'
        exact ⟨q, by simpa [Nat.and_comm] using hq⟩

lemma semantic_callback {S : Nat → Finset (Fin 10)} {M A B : Nat → Nat}
    {G : Nat → Option (Fin 6)} {Op : Nat → Bool} {start n : Nat}
    (hm : ∀ w, M w < 64)
    (hfull : ∀ w, S w = {3, 6, 7} → M w = 63)
    (hsem : ProgramSemantics S M A B G Op start n) :
    ProgramCallback S M A B G start n := by
  intro t ht s rest hs ha hb hz hgroups
  generalize hg : G (start + t) = group at hgroups ⊢
  cases group with
  | none =>
    exact gate_local (Op (start + t)) none hs ha hb (hfull _) (hfull _)
      ⟨hm _, hm _, hm _⟩ hz hgroups (by simpa [hg] using hsem t ht)
  | some g =>
    exact gate_local (Op (start + t)) (some g) hs ha hb (hfull _) (hfull _)
      ⟨hm _, hm _, hm _⟩ hz hgroups (by simpa [hg] using hsem t ht)

end S200Simulation



namespace DAGBridge.DagTools

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gop : Bool → Bool → Bool → Bool
  | true, a, b => a && b
  | false, a, b => a || b

lemma gop_true (a b : Bool) : gop true a b = (a && b) := rfl

lemma gop_false (a b : Bool) : gop false a b = (a || b) := rfl

abbrev Dag := List (Bool × ℕ × ℕ)

def tag (D : Dag) (j : ℕ) : Bool := (D.getD j (false, 0, 0)).1

def opA (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.1

def opB (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.2

def wstep (w : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  w ++ [gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]

def wl (D : Dag) (w : List Bool) : List Bool := D.foldl wstep w

def val (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wl D (List.ofFn x)).getD w false

def Strict (n : ℕ) (D : Dag) : Prop :=
  ∀ j, j < D.length → opA D j < n + j ∧ opB D j < n + j ∧ opA D j ≠ opB D j

def readers (D : Dag) (w : ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => opA D j = w ∨ opB D j = w)

def fanout (D : Dag) (w : ℕ) : ℕ := (readers D w).card

def Live (n : ℕ) (D : Dag) : Prop := ∀ w, w + 1 < n + D.length → 1 ≤ fanout D w

def StrictLive (n : ℕ) (D : Dag) : Prop := Strict n D ∧ Live n D ∧ D ≠ []

def outW (n : ℕ) (D : Dag) : ℕ := n + D.length - 1

def single {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i = v)

def supp (n : ℕ) (D : Dag) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => val D (single v) w = true)

def surplusOn (D : Dag) (K : Finset ℕ) : ℕ := ∑ w ∈ K, (fanout D w - 1)

def inner (n : ℕ) (D : Dag) : Finset ℕ := Finset.range (n + D.length - 1)

def totalSurplus (n : ℕ) (D : Dag) : ℕ := surplusOn D (inner n D)

def Bplus (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => (supp n D w).Nonempty))

def Bzero (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => ¬ (supp n D w).Nonempty))

def branchW (n : ℕ) (D : Dag) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => 2 ≤ fanout D w)

def eligSet (n : ℕ) (D : Dag) : Finset (Fin n) := (branchW n D).biUnion (supp n D)

def ineligSet (n : ℕ) (D : Dag) : Finset (Fin n) := Finset.univ \ eligSet n D

def units (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (inner n D).sigma (fun w => Finset.range (fanout D w - 1))

def unitsPlus (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => (supp n D u.1).Nonempty)

def arcs (D : Dag) : Finset (ℕ × Bool) := Finset.range D.length ×ˢ Finset.univ

def src (D : Dag) (e : ℕ × Bool) : ℕ := if e.2 = true then opB D e.1 else opA D e.1

def exitArcs (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (ℕ × Bool) :=
  (arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∉ K)

def merges (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => n + j ∈ K ∧ opA D j ∈ K ∧ opB D j ∈ K)

def sources (n : ℕ) (K : Finset ℕ) : Finset ℕ := K.filter (fun w => w < n)

def carrierT (n : ℕ) (D : Dag) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => (supp n D w ∩ T).Nonempty)

def carrierDiff (n : ℕ) (D : Dag) (x y : Fin n) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)

def PureBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v}

def reservedUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ))

def residualUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  unitsPlus n D \ reservedUnits n D b

lemma tag_eq (D : Dag) (j : ℕ) (h : j < D.length) : tag D j = (D[j]).1 := by
  simp [tag, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma opA_eq (D : Dag) (j : ℕ) (h : j < D.length) : opA D j = (D[j]).2.1 := by
  simp [opA, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma opB_eq (D : Dag) (j : ℕ) (h : j < D.length) : opB D j = (D[j]).2.2 := by
  simp [opB, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma wl_cons (g : Bool × ℕ × ℕ) (D : Dag) (w : List Bool) :
    wl (g :: D) w = wl D (wstep w g) := rfl

lemma wl_append (D E : Dag) (w : List Bool) : wl (D ++ E) w = wl E (wl D w) := by
  simp [wl, List.foldl_append]

lemma wstep_length (w : List Bool) (g : Bool × ℕ × ℕ) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

lemma wl_length (D : Dag) : ∀ w : List Bool, (wl D w).length = w.length + D.length := by
  induction D with
  | nil => intro w; simp [wl]
  | cons g D ih => intro w; rw [wl_cons, ih, wstep_length]; simp; omega

lemma wstep_getD_lt (w : List Bool) (g : Bool × ℕ × ℕ) (i : ℕ) (h : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma wl_getD_lt (D : Dag) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wl D w).getD i false = w.getD i false := by
  induction D with
  | nil => intro w i _; rfl
  | cons g D ih =>
    intro w i h
    rw [wl_cons, ih _ _ (by rw [wstep_length]; omega), wstep_getD_lt _ _ _ h]

lemma getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma wstep_getD_last (w : List Bool) (g : Bool × ℕ × ℕ) :
    (wstep w g).getD w.length false = gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false) := by
  simp [wstep, List.getD_eq_getElem?_getD]

lemma wl_getD_gate (D : Dag) (w : List Bool) (j : ℕ) (hj : j < D.length) :
    (wl D w).getD (w.length + j) false =
      gop (tag D j) ((wl (D.take j) w).getD (opA D j) false)
        ((wl (D.take j) w).getD (opB D j) false) := by
  have hsplit : D = D.take j ++ D[j] :: D.drop (j + 1) := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  rw [tag_eq D j hj, opA_eq D j hj, opB_eq D j hj]
  conv_lhs => rw [hsplit, wl_append, wl_cons]
  rw [wl_getD_lt _ _ _ (by rw [wstep_length, hlen]; omega), ← hlen, wstep_getD_last]

lemma wl_take_getD (D : Dag) (w : List Bool) (j i : ℕ) (hi : i < w.length + j)
    (hj : j ≤ D.length) :
    (wl (D.take j) w).getD i false = (wl D w).getD i false := by
  have hsplit : D = D.take j ++ D.drop j := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  conv_rhs => rw [hsplit, wl_append]
  rw [wl_getD_lt (D.drop j) (wl (D.take j) w) i (by rw [hlen]; exact hi)]

lemma val_input (D : Dag) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    val D x i = x ⟨i, h⟩ := by
  unfold val
  rw [wl_getD_lt _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

lemma val_ge (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (h : n + D.length ≤ w) :
    val D x w = false := by
  unfold val
  exact getD_ge _ _ (by rw [wl_length]; simpa using h)

lemma val_take (D : Dag) {n : ℕ} (x : Fin n → Bool) (k w : ℕ) (hw : w < n + k)
    (hk : k ≤ D.length) : val (D.take k) x w = val D x w := by
  unfold val
  exact wl_take_getD D _ k w (by simpa using hw) hk

lemma val_gate {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (j : ℕ)
    (hj : j < D.length) :
    val D x (n + j) = gop (tag D j) (val D x (opA D j)) (val D x (opB D j)) := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  have h := wl_getD_gate D (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold val
  rw [h, wl_take_getD D _ j _ (by simpa using ha) hj.le,
    wl_take_getD D _ j _ (by simpa using hb) hj.le]

lemma val_unique {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (f : ℕ → Bool)
    (hin : ∀ i (h : i < n), f i = x ⟨i, h⟩)
    (hg : ∀ j, j < D.length → f (n + j) = gop (tag D j) (f (opA D j)) (f (opB D j))) :
    ∀ w, w < n + D.length → val D x w = f w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · rw [val_input D x w hn, hin w hn]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      obtain ⟨ha, hb, -⟩ := hS j hj
      rw [val_gate hS x j hj, hg j hj, ih _ ha (by omega), ih _ hb (by omega)]


variable {n : ℕ} {D : Dag}

lemma mem_supp {v : Fin n} {w : ℕ} : v ∈ supp n D w ↔ val D (single v) w = true := by
  simp [supp]

lemma val_mono (hS : Strict n D) (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) : val D x w = true → val D y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input D x w hn, val_input D y w hn]; exact hxy _
    · by_cases hw : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        rw [val_gate hS x j hj, val_gate hS y j hj]
        have h1 := ih _ ha
        have h2 := ih _ hb
        cases tag D j <;>
          simp only [gop_true, gop_false, Bool.and_eq_true, Bool.or_eq_true] <;> tauto
      · rw [val_ge D x w (by omega)]; simp

lemma supp_input (D : Dag) (i : Fin n) : supp n D i.val = {i} := by
  ext v
  rw [mem_supp, val_input D (single v) i.val i.isLt]
  simp [single, eq_comm]

lemma supp_ge (D : Dag) (w : ℕ) (h : n + D.length ≤ w) : supp n D w = ∅ := by
  ext v
  simp [mem_supp, val_ge D (single v) w h]

lemma supp_gate (hS : Strict n D) (j : ℕ) (hj : j < D.length) :
    supp n D (n + j) = if tag D j = true then supp n D (opA D j) ∩ supp n D (opB D j)
      else supp n D (opA D j) ∪ supp n D (opB D j) := by
  ext v
  rw [mem_supp, val_gate hS _ j hj]
  cases tag D j <;> simp [mem_supp, gop]

end DAGBridge.DagTools

namespace OnceResourceBudget

open PEqualNP.Outside.L_meta_2590.DAGBridge.DagTools

variable {n : ℕ} {D : Dag}

lemma zero_reader_inner (hS : Strict n D) {j w : ℕ} (hj : j < D.length)
    (he : supp n D w = ∅) (hr : opA D j = w ∨ opB D j = w) :
    w ∈ (inner n D).filter (fun u => ¬(supp n D u).Nonempty) := by
  have hw : w < n + j := by
    obtain ⟨ha, hb, _⟩ := hS j hj
    rcases hr with hr | hr <;> omega
  apply Finset.mem_filter.mpr
  constructor
  · simp only [inner, Finset.mem_range]
    omega
  · simp [he]

lemma zero_branch_inner (hS : Strict n D) {w : ℕ} (he : supp n D w = ∅)
    (hf : 2 ≤ fanout D w) :
    w ∈ (inner n D).filter (fun u => ¬(supp n D u).Nonempty) := by
  have hp : 0 < (readers D w).card := by change 0 < fanout D w; omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hp
  obtain ⟨hj, hr⟩ := Finset.mem_filter.mp hj
  exact zero_reader_inner hS (Finset.mem_range.mp hj) he hr

lemma zero_fanout_le_two (hS : Strict n D) (hB : Bzero n D ≤ 1)
    {w : ℕ} (he : supp n D w = ∅) : fanout D w ≤ 2 := by
  by_cases hf : 2 ≤ fanout D w
  · have hsum : fanout D w - 1 ≤ Bzero n D := by
      unfold Bzero surplusOn
      exact Finset.single_le_sum (f := fun u => fanout D u - 1)
        (fun _ _ => Nat.zero_le _) (zero_branch_inner hS he hf)
    omega
  · omega

lemma zero_branch_unique (hS : Strict n D) (hB : Bzero n D ≤ 1)
    {a b : ℕ} (ha : supp n D a = ∅) (hb : supp n D b = ∅)
    (hfa : 2 ≤ fanout D a) (hfb : 2 ≤ fanout D b) : a = b := by
  by_contra hne
  have hsub : ({a, b} : Finset ℕ) ⊆
      (inner n D).filter (fun u => ¬(supp n D u).Nonempty) := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact zero_branch_inner hS ha hfa
    · have hwb : w = b := Finset.mem_singleton.mp hw
      subst w
      exact zero_branch_inner hS hb hfb
  have hsum := Finset.sum_le_sum_of_subset (f := fun w => fanout D w - 1) hsub
  rw [Finset.sum_pair hne] at hsum
  unfold Bzero surplusOn at hB
  omega

lemma exists_fork_id (hS : Strict n D) (hB : Bzero n D ≤ 1) :
    ∃ fork : ℕ, ∀ w, supp n D w = ∅ →
      fanout D w ≤ if w = fork then 2 else 1 := by
  classical
  by_cases hb : ∃ b, supp n D b = ∅ ∧ 2 ≤ fanout D b
  · obtain ⟨b, hb, hfb⟩ := hb
    refine ⟨b, ?_⟩
    intro w hw
    by_cases hwb : w = b
    · simp only [hwb, ite_true]
      exact zero_fanout_le_two hS hB hb
    · simp only [hwb, ite_false]
      by_contra hbad
      have hwf : 2 ≤ fanout D w := by omega
      exact hwb (zero_branch_unique hS hB hw hb hwf hfb)
  · refine ⟨0, ?_⟩
    intro w hw
    have hf : fanout D w ≤ 1 := by
      by_contra hbad
      exact hb ⟨w, hw, by omega⟩
    split_ifs <;> omega

lemma readers_card_le_cap {fork : ℕ}
    (hcap : ∀ w, supp n D w = ∅ → fanout D w ≤ if w = fork then 2 else 1)
    {w : ℕ} (hw : supp n D w = ∅) :
    (readers D w).card ≤ if w = fork then 2 else 1 := hcap w hw

lemma zero_reader_pair_eq (hS : Strict n D) (hB : Bzero n D ≤ 1)
    {w j k l : ℕ} (hw : supp n D w = ∅)
    (hj : j < D.length) (hk : k < D.length) (hl : l < D.length)
    (rj : opA D j = w ∨ opB D j = w)
    (rk : opA D k = w ∨ opB D k = w)
    (rl : opA D l = w ∨ opB D l = w) : j = k ∨ j = l ∨ k = l := by
  by_contra h
  push Not at h
  have hsub : ({j, k, l} : Finset ℕ) ⊆ readers D w := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, rj⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, rk⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hl, rl⟩
  have hcard := Finset.card_le_card hsub
  have hthree : ({j, k, l} : Finset ℕ).card = 3 := by simp [h.1, h.2.1, h.2.2]
  rw [hthree] at hcard
  have htwo := zero_fanout_le_two hS hB hw
  change (readers D w).card ≤ 2 at htwo
  omega

end OnceResourceBudget

namespace OnceActualSchedule

open DAGBridge.DagTools OnceResource.IndexCopies

def start (g : ℕ) : ℕ := 10 + g + 1

def remaining (D : Dag) (g : ℕ) : ℕ := D.length - g - 1

def sourceA (D : Dag) (w : ℕ) : ℕ := opA D (w - 10)

def sourceB (D : Dag) (w : ℕ) : ℕ := opB D (w - 10)

abbrev Zero (D : Dag) (w : ℕ) : Prop := supp 10 D w = ∅

def ids (D : Dag) (g fork t : ℕ) : Multiset ℕ :=
  Available (Zero D) (start g) fork (sourceA D) (sourceB D) t

lemma continuation_index (g t : ℕ) : start g + t - 10 = g + 1 + t := by
  unfold start
  omega

lemma continuation_valid {D : Dag} (hS : Strict 10 D) (g : ℕ) :
    Valid (start g) (sourceA D) (sourceB D) (remaining D g) := by
  intro t ht
  have hj : g + 1 + t < D.length := by unfold remaining at ht; omega
  have hs := hS (g + 1 + t) hj
  have hout : 10 + (g + 1 + t) = start g + t := by unfold start; omega
  simpa only [sourceA, sourceB, continuation_index, hout] using hs

lemma continuation_readCount_le_fanout (D : Dag) (g w : ℕ) :
    ReadCount (start g) (sourceA D) (sourceB D) (remaining D g) w ≤ fanout D w := by
  unfold ReadCount fanout
  apply Finset.card_le_card_of_injOn (fun j => g + 1 + j)
  · intro j hj
    obtain ⟨hj, hr⟩ := Finset.mem_filter.mp hj
    have hjt := Finset.mem_range.mp hj
    have hjD : g + 1 + j < D.length := by unfold remaining at hjt; omega
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hjD, ?_⟩
    simpa only [sourceA, sourceB, continuation_index] using hr
  · intro i _ j _ heq
    change g + 1 + i = g + 1 + j at heq
    omega

lemma exists_continuation_fork {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D ≤ 1)
    (g : ℕ) :
    ∃ fork : ℕ, ∀ w, Zero D w →
      ReadCount (start g) (sourceA D) (sourceB D) (remaining D g) w ≤ Capacity fork w := by
  obtain ⟨fork, hcap⟩ := OnceResourceBudget.exists_fork_id hS hB
  refine ⟨fork, ?_⟩
  intro w hw
  exact (continuation_readCount_le_fanout D g w).trans (hcap w hw)

lemma actual_sources_available {D : Dag} (hS : Strict 10 D) {g fork t : ℕ}
    (hcap : ∀ w, Zero D w →
      ReadCount (start g) (sourceA D) (sourceB D) (remaining D g) w ≤ Capacity fork w)
    (ht : t < remaining D g) :
    opA D (g + 1 + t) ∈ ids D g fork t ∧
      opB D (g + 1 + t) ∈ Drop (Zero D) (opA D (g + 1 + t)) (ids D g fork t) := by
  have hs := sources_available (Zero D) (continuation_valid hS g) hcap ht
  simpa only [ids, sourceA, sourceB, continuation_index] using hs

lemma actual_available_step_decomp {D : Dag} (hS : Strict 10 D) {g fork t : ℕ}
    (hcap : ∀ w, Zero D w →
      ReadCount (start g) (sourceA D) (sourceB D) (remaining D g) w ≤ Capacity fork w)
    (ht : t < remaining D g) :
    ∃ rest : Multiset ℕ,
      ids D g fork t = opA D (g + 1 + t) ::ₘ opB D (g + 1 + t) ::ₘ rest ∧
      ids D g fork (t + 1) =
        (start g + t) ::ₘ
          (if Zero D (start g + t) ∧ start g + t = fork then
            (start g + t) ::ₘ
              (Retain (Zero D) (opA D (g + 1 + t)) + Retain (Zero D) (opB D (g + 1 + t)) + rest)
          else Retain (Zero D) (opA D (g + 1 + t)) + Retain (Zero D) (opB D (g + 1 + t)) + rest) := by
  have hs := available_step_decomp (Zero D) (continuation_valid hS g) hcap ht
  simpa only [ids, sourceA, sourceB, continuation_index] using hs

lemma actual_id_count {D : Dag} (hS : Strict 10 D) (g fork t w : ℕ)
    (ht : t ≤ remaining D g) :
    (ids D g fork t).count w =
      if w < start g + t then
        if Zero D w then Capacity fork w - ReadCount (start g) (sourceA D) (sourceB D) t w else 1
      else 0 := by
  exact count_available (Zero D) (continuation_valid hS g) t ht w

lemma actual_extra_count (D : Dag) (g fork t : ℕ) :
    ExtraCount (Zero D) (start g) fork t = if Zero D fork ∧ fork < start g + t then 1 else 0 := by
  exact extraCount_eq (Zero D) (start g) fork t

lemma exists_actual_sources {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D ≤ 1) (g : ℕ) :
    ∃ fork : ℕ,
      (∀ w, Zero D w →
        ReadCount (start g) (sourceA D) (sourceB D) (remaining D g) w ≤ Capacity fork w) ∧
      ∀ t < remaining D g,
        opA D (g + 1 + t) ∈ ids D g fork t ∧
          opB D (g + 1 + t) ∈ Drop (Zero D) (opA D (g + 1 + t)) (ids D g fork t) := by
  obtain ⟨fork, hcap⟩ := exists_continuation_fork hS hB g
  exact ⟨fork, hcap, fun _ ht => actual_sources_available hS hcap ht⟩

end OnceActualSchedule

namespace OnceActualSchedule

open DAGBridge.DagTools OnceResource.IndexCopies

lemma final_fanout_zero {D : Dag} (hS : Strict 10 D) : fanout D (outW 10 D) = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨hj, hr⟩ := Finset.mem_filter.mp hj
  have hjD := Finset.mem_range.mp hj
  obtain ⟨ha, hb, _⟩ := hS j hjD
  unfold outW at hr
  rcases hr with hr | hr <;> omega

lemma final_readCount_zero {D : Dag} (hS : Strict 10 D) (g : ℕ) :
    ReadCount (start g) (sourceA D) (sourceB D) (remaining D g) (outW 10 D) = 0 := by
  have hle := continuation_readCount_le_fanout D g (outW 10 D)
  rw [final_fanout_zero hS] at hle
  omega

lemma final_output_count {D : Dag} (hS : Strict 10 D) {g : ℕ}
    (hg : g < D.length) (fork : ℕ) :
    (ids D g fork (remaining D g)).count (outW 10 D) = Copies (Zero D) fork (outW 10 D) := by
  rw [actual_id_count hS g fork (remaining D g) (outW 10 D) (Nat.le_refl _)]
  have hbound : outW 10 D < start g + remaining D g := by
    unfold outW start remaining
    omega
  rw [ite_eq_left hbound, final_readCount_zero hS g]
  simp only [Copies, Nat.sub_zero]

lemma final_output_available {D : Dag} (hS : Strict 10 D) {g : ℕ}
    (hg : g < D.length) (fork : ℕ) :
    outW 10 D ∈ ids D g fork (remaining D g) := by
  apply Multiset.count_pos.mp
  rw [final_output_count hS hg fork]
  unfold Copies Capacity
  split_ifs <;> decide

end OnceActualSchedule

namespace OnceGeometry

open PEqualNP.Outside.L_meta_2590.DAGBridge.DagTools

def rowInput (r : Fin 6) : Fin 10 → Bool := fun v => decide (v ∈ rowSet r)

def wireMask (D : Dag) (w : ℕ) : ℕ := mask (fun r => val D (rowInput r) w)

lemma wireMask_lt (D : Dag) (w : ℕ) : wireMask D w < 64 := mask_lt _

lemma wireMask_input (D : Dag) (v : Fin 10) : wireMask D v.val = rawMask {v} := by
  unfold wireMask rawMask
  congr 1
  funext r
  rw [val_input D _ v.val v.isLt]
  simp [rowInput, Finset.Nonempty]

lemma wireMask_gate {D : Dag} (hS : Strict 10 D) {j : ℕ} (hj : j < D.length) :
    wireMask D (10 + j) = if tag D j then
      wireMask D (opA D j) &&& wireMask D (opB D j)
      else wireMask D (opA D j) ||| wireMask D (opB D j) := by
  have hfun : (fun r => val D (rowInput r) (10 + j)) =
      (fun r => gop (tag D j) (val D (rowInput r) (opA D j)) (val D (rowInput r) (opB D j))) := by
    funext r
    exact val_gate hS _ j hj
  unfold wireMask
  rw [hfun]
  cases tag D j <;> simp only [gop, Bool.false_eq_true, ite_false, ite_true, mask_or, mask_and]

lemma support_row_true {D : Dag} (hS : Strict 10 D) {w : ℕ} {r : Fin 6}
    (hh : (supp 10 D w ∩ rowSet r).Nonempty) : val D (rowInput r) w = true := by
  obtain ⟨v, hv⟩ := hh
  obtain ⟨hvs, hvE⟩ := Finset.mem_inter.mp hv
  apply val_mono hS (single v) (rowInput r) ?_ w (mem_supp.mp hvs)
  intro u hu
  have huv : u = v := by simpa [single] using hu
  subst u
  exact decide_eq_true hvE

lemma wireMask_support_lower {D : Dag} (hS : Strict 10 D) (w : ℕ) :
    rawMask (supp 10 D w) &&& wireMask D w = rawMask (supp 10 D w) := by
  unfold rawMask wireMask
  rw [← mask_and]
  congr 1
  funext r
  by_cases hh : (supp 10 D w ∩ rowSet r).Nonempty
  · simp only [decide_eq_true hh, support_row_true hS hh, Bool.and_self]
  · simp [hh]

lemma wireMask_correct {D : Dag} {w : ℕ}
    (hc : ∀ x : Fin 10 → Bool, val D x w = edgeFn x) : wireMask D w = 56 := by
  unfold wireMask
  have hh : (fun r => val D (rowInput r) w) = (fun r => edgeFn (rowInput r)) := by
    funext r
    exact hc _
  rw [hh]
  exact petersen_mask

lemma dirty_row_hits : ∀ r : Fin 6,
    (({3, 6, 7} : Finset (Fin 10)) ∩ rowSet r).Nonempty ∧
    (({2, 8, 9} : Finset (Fin 10)) ∩ rowSet r).Nonempty := by decide

lemma dirty_wire_mask {D : Dag} (hS : Strict 10 D) {j : ℕ} (hj : j < D.length)
    (ht : tag D j = true)
    (ha : supp 10 D (opA D j) = {3, 6, 7})
    (hb : supp 10 D (opB D j) = {2, 8, 9}) : wireMask D (10 + j) = 63 := by
  have hh : (fun r => val D (rowInput r) (10 + j)) = (fun _ => true) := by
    funext r
    rw [val_gate hS _ j hj, ht, gop_true]
    have h1 := support_row_true hS (show (supp 10 D (opA D j) ∩ rowSet r).Nonempty by
      rw [ha]; exact (dirty_row_hits r).1)
    have h2 := support_row_true hS (show (supp 10 D (opB D j) ∩ rowSet r).Nonempty by
      rw [hb]; exact (dirty_row_hits r).2)
    rw [h1, h2]
    rfl
  unfold wireMask
  rw [hh]
  decide

end OnceGeometry

namespace S200Geometry
open OnceGeometry DAGBridge.DagTools
lemma dirty_left_mask {D : Dag} (hS : Strict 10 D) {w : ℕ}
    (hw : supp 10 D w = {3, 6, 7}) : wireMask D w = 63 := by
  have hfun : (fun r => val D (rowInput r) w) = (fun _ : Fin 6 => true) := by
    funext r
    apply support_row_true hS
    rw [hw]
    fin_cases r <;> decide
  unfold wireMask
  rw [hfun]
  decide

end S200Geometry

namespace S200Simulation

open S200Resource S200Positive OnceGeometry
open OnceResource.IndexCopies OnceResource.TokenMap

lemma initial_program_inv (S : ℕ → Finset (Fin 10)) (M A B : ℕ → ℕ)
    (G : ℕ → Option (Fin 6)) {start n : ℕ}
    (hsupport : ∀ w < start, (S w).Nonempty)
    (hraw : ∀ w < start, M w = rawMask (S w)) :
    ProgramInv S M A B G start n 0 initial := by
  have hi : Healthy initial := ⟨by decide, rfl, poolsGood_replicate_one⟩
  refine ⟨hi, ?_, ?_, ?_⟩
  · have hf : ¬start+n < start := by omega
    have he : (Multiset.range start).filter (fun w => S w = ∅ ∧ M w ≠ 0) = 0 := by
      apply Multiset.filter_eq_nil.mpr
      intro w hw h
      exact (hsupport w (Multiset.mem_range.mp hw)).ne_empty h.1
    simp [Available, Initial, hf, project, he, initial]
  · intro w hw _
    rw [hraw w (by omega)]
    exact rep_raw hi.2.2 _
  · intro g hg
    simpa [initial] using hg

end S200Simulation

namespace S200Budget

open DAGBridge.DagTools OnceResource.IndexCopies OnceActualSchedule

lemma zero_fanout_le_one {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D = 0)
    {w : ℕ} (hz : supp 10 D w = ∅) : fanout D w ≤ 1 := by
  by_cases hf : fanout D w ≤ 1
  · exact hf
  · have htwo : 2 ≤ fanout D w := by omega
    have hi := OnceResourceBudget.zero_branch_inner hS hz htwo
    have hm : w ∈ (inner 10 D).filter (fun w => ¬(supp 10 D w).Nonempty) := by
      exact hi
    have hs := Finset.single_le_sum (fun x _ => Nat.zero_le (fanout D x - 1)) hm
    change fanout D w - 1 ≤ Bzero 10 D at hs
    rw [hB] at hs
    omega

lemma continuation_capacity {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D = 0)
    (g : ℕ) : ∀ w, supp 10 D w = ∅ →
      ReadCount (start g) (sourceA D) (sourceB D) (remaining D g) w ≤ 1 := by
  intro w hw
  exact (continuation_readCount_le_fanout D g w).trans (zero_fanout_le_one hS hB hw)

end S200Budget

namespace S200ActualSchedule

open DAGBridge.DagTools OnceActualSchedule OnceResource.IndexCopies

lemma full_valid {D : Dag} (hS : Strict 10 D) :
    Valid 10 (sourceA D) (sourceB D) D.length := by
  intro t ht
  simpa only [sourceA, sourceB, Nat.add_sub_cancel_left] using hS t ht

lemma full_readCount (D : Dag) (w : ℕ) :
    ReadCount 10 (sourceA D) (sourceB D) D.length w = fanout D w := by
  simp only [ReadCount, Readers, fanout, readers, sourceA, sourceB, Nat.add_sub_cancel_left]

lemma full_capacity {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D = 0) :
    ∀ w, supp 10 D w = ∅ → ReadCount 10 (sourceA D) (sourceB D) D.length w ≤ 1 := by
  intro w hw
  rw [full_readCount]
  exact S200Budget.zero_fanout_le_one hS hB hw

lemma final_available {D : Dag} (hS : Strict 10 D) :
    outW 10 D ∈ Available (fun w => supp 10 D w = ∅) 10 (10+D.length)
      (sourceA D) (sourceB D) D.length := by
  apply Multiset.count_pos.mp
  rw [count_available _ (full_valid hS) _ (Nat.le_refl _) _, full_readCount,
    final_fanout_zero hS]
  have hlt : outW 10 D < 10+D.length := by unfold outW; omega
  have hne : outW 10 D ≠ 10+D.length := by omega
  simp [hlt, Capacity, hne]

end S200ActualSchedule

namespace S200Geometry

open OnceGeometry DAGBridge.DagTools

lemma input_raw (D : Dag) (i : Fin 10) :
    wireMask D i.val = rawMask (supp 10 D i.val) := by
  rw [supp_input]
  unfold wireMask rawMask
  apply congrArg mask
  funext r
  rw [val_input D (rowInput r) i.val i.isLt]
  simp only [rowInput, decide_eq_decide]
  constructor
  · intro h
    exact ⟨i, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self i, h⟩⟩
  · rintro ⟨v, hv⟩
    obtain ⟨hv, hr⟩ := Finset.mem_inter.mp hv
    have he : v = i := Finset.mem_singleton.mp hv
    simpa only [he] using hr

end S200Geometry

namespace S200Simulation

open S200Resource S200Positive OnceGeometry OnceActualSchedule
open DAGBridge.DagTools

lemma actual_target_exclusion_of_safe
    (hsafe : ∀ s, Reach initial s → 56 ∉ s.2.2) {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D = 0)
    {G : ℕ → Option (Fin 6)}
    (hgroups : GroupUnique G 10 D.length)
    (hsem : ProgramSemantics (supp 10 D) (wireMask D) (sourceA D) (sourceB D) G
      (fun w => tag D (w - 10)) 10 D.length) :
    ¬ (supp 10 D (outW 10 D) = ∅ ∧ wireMask D (outW 10 D) = 56) := by
  intro hout
  have hinit : ProgramInv (supp 10 D) (wireMask D) (sourceA D) (sourceB D) G
      10 D.length 0 initial := by
    apply initial_program_inv (supp 10 D) (wireMask D) (sourceA D) (sourceB D) G
    · intro w hw
      have h := supp_input D (⟨w, hw⟩ : Fin 10)
      rw [h]
      exact Finset.singleton_nonempty _
    · intro w hw
      exact S200Geometry.input_raw D ⟨w, hw⟩
  exact program_target_excluded hsafe
    (S200ActualSchedule.full_valid hS) (S200ActualSchedule.full_capacity hS hB)
    hgroups (semantic_callback (wireMask_lt D) (fun _ hw => S200Geometry.dirty_left_mask hS hw) hsem)
    hinit (S200ActualSchedule.final_available hS) hout.1 hout.2

end S200Simulation


namespace ResourceCertificate

def search {α β : Type} [BEq α] (lt : α → α → Bool)
    (xs : Array β) (decode : β → α) (needle : α) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if h : mid < xs.size then
          if decode xs[mid] == needle then true
          else if lt needle (decode xs[mid]) then
            search lt xs decode needle fuel lo mid
          else search lt xs decode needle fuel (mid + 1) hi
        else false
      else false

lemma search_sound {α β : Type} [BEq α] [LawfulBEq α]
    (lt : α → α → Bool) (xs : Array β) (decode : β → α)
    (needle : α) (fuel lo hi : Nat)
    (hsearch : search lt xs decode needle fuel lo hi = true) :
    needle ∈ xs.toList.map decode := by
  induction fuel generalizing lo hi with
  | zero => simp [search] at hsearch
  | succ fuel ih =>
      simp only [search] at hsearch
      split at hsearch
      next hlt =>
        split at hsearch
        next hmid =>
          split at hsearch
          next heq =>
            exact List.mem_map.mpr
              ⟨xs[(lo + hi) / 2], Array.getElem_mem_toList hmid, eq_of_beq heq⟩
          next hne =>
            split at hsearch
            next => exact ih _ _ hsearch
            next => exact ih _ _ hsearch
        next => cases hsearch
      next => cases hsearch

lemma reachable_mem {α : Type} (states : List α) (next : α → List α)
    (contains : α → Bool)
    (hcontains : ∀ s, contains s = true → s ∈ states)
    (hclosed : states.all (fun s => (next s).all contains) = true)
    {start finish : α} (hstart : contains start = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    finish ∈ states := by
  have step : ∀ a ∈ states, ∀ b ∈ next a, b ∈ states := by
    intro a ha b hb
    exact hcontains b (List.all_eq_true.mp (List.all_eq_true.mp hclosed a ha) b hb)
  induction hreach with
  | refl => exact hcontains start hstart
  | @tail b c hab hbc ih => exact step b ih c hbc

lemma reachable_safe {α : Type} (states : List α) (next : α → List α)
    (contains safe : α → Bool)
    (hcontains : ∀ s, contains s = true → s ∈ states)
    (hclosed : states.all (fun s => (next s).all contains) = true)
    (hsafe : states.all safe = true)
    {start finish : α} (hstart : contains start = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    safe finish = true := by
  exact List.all_eq_true.mp hsafe finish
    (reachable_mem states next contains hcontains hclosed hstart hreach)

lemma array_reachable_safe {α β : Type} (codes : Array β) (decode : β → α)
    (next : α → List α) (contains safe : α → Bool)
    (hcontains : ∀ s, contains s = true → s ∈ codes.toList.map decode)
    (hclosed : codes.all (fun c => (next (decode c)).all contains) = true)
    (hsafe : codes.all (fun c => safe (decode c)) = true)
    {start finish : α} (hstart : contains start = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    safe finish = true := by
  apply reachable_safe (codes.toList.map decode) next contains safe hcontains
      ?_ ?_ hstart hreach
  · simpa only [List.all_map, Function.comp_def, Array.all_toList] using hclosed
  · simpa only [List.all_map, Function.comp_def, Array.all_toList] using hsafe

lemma search_reachable_safe {α β : Type} [BEq α] [LawfulBEq α]
    (lt : α → α → Bool) (codes : Array β) (decode : β → α)
    (fuel : Nat) (next : α → List α) (safe : α → Bool)
    (hclosed : codes.all (fun c => (next (decode c)).all
      (fun s => search lt codes decode s fuel 0 codes.size)) = true)
    (hsafe : codes.all (fun c => safe (decode c)) = true)
    {start finish : α}
    (hstart : search lt codes decode start fuel 0 codes.size = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    safe finish = true := by
  exact array_reachable_safe codes decode next
    (fun s => search lt codes decode s fuel 0 codes.size) safe
    (fun s hs => search_sound lt codes decode s fuel 0 codes.size hs)
    hclosed hsafe hstart hreach

end ResourceCertificate

namespace ResourceCertificate

def searchIndex {α : Type} [BEq α] (lt : α → α → Bool)
    (get : Nat → α) (bound : Nat) (needle : α) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if mid < bound then
          if get mid == needle then true
          else if lt needle (get mid) then
            searchIndex lt get bound needle fuel lo mid
          else searchIndex lt get bound needle fuel (mid + 1) hi
        else false
      else false

lemma searchIndex_sound {α : Type} [BEq α] [LawfulBEq α]
    (lt : α → α → Bool) (get : Nat → α) (bound : Nat)
    (needle : α) (fuel lo hi : Nat)
    (hsearch : searchIndex lt get bound needle fuel lo hi = true) :
    ∃ i < bound, get i = needle := by
  induction fuel generalizing lo hi with
  | zero => simp [searchIndex] at hsearch
  | succ fuel ih =>
      simp only [searchIndex] at hsearch
      split at hsearch
      next hlt =>
        split at hsearch
        next hmid =>
          split at hsearch
          next heq => exact ⟨(lo + hi) / 2, hmid, eq_of_beq heq⟩
          next hne =>
            split at hsearch
            next => exact ih _ _ hsearch
            next => exact ih _ _ hsearch
        next => cases hsearch
      next => cases hsearch

lemma searchIndex_mem {α : Type} [BEq α] [LawfulBEq α]
    (lt : α → α → Bool) (get : Nat → α) (bound : Nat)
    (needle : α) (fuel lo hi : Nat)
    (hsearch : searchIndex lt get bound needle fuel lo hi = true) :
    needle ∈ (List.range bound).map get := by
  obtain ⟨i, hi, heq⟩ := searchIndex_sound lt get bound needle fuel lo hi hsearch
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, heq⟩

lemma index_reachable_safe {α : Type} (get : Nat → α) (bound : Nat)
    (next : α → List α) (contains safe : α → Bool)
    (hcontains : ∀ s, contains s = true → ∃ i < bound, get i = s)
    (hclosed : (List.range bound).all
      (fun i => (next (get i)).all contains) = true)
    (hsafe : (List.range bound).all (fun i => safe (get i)) = true)
    {start finish : α} (hstart : contains start = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    safe finish = true := by
  apply reachable_safe ((List.range bound).map get) next contains safe ?_
      ?_ ?_ hstart hreach
  · intro s hs
    obtain ⟨i, hi, heq⟩ := hcontains s hs
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, heq⟩
  · simpa only [List.all_map, Function.comp_def] using hclosed
  · simpa only [List.all_map, Function.comp_def] using hsafe

lemma searchIndex_reachable_safe {α : Type} [BEq α] [LawfulBEq α]
    (lt : α → α → Bool) (get : Nat → α) (bound fuel : Nat)
    (next : α → List α) (safe : α → Bool)
    (hclosed : (List.range bound).all (fun i => (next (get i)).all
      (fun s => searchIndex lt get bound s fuel 0 bound)) = true)
    (hsafe : (List.range bound).all (fun i => safe (get i)) = true)
    {start finish : α}
    (hstart : searchIndex lt get bound start fuel 0 bound = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    safe finish = true := by
  exact index_reachable_safe get bound next
    (fun s => searchIndex lt get bound s fuel 0 bound) safe
    (fun s hs => searchIndex_sound lt get bound s fuel 0 bound hs)
    hclosed hsafe hstart hreach

end ResourceCertificate

namespace ResourceCertificate

lemma chunked_all (checked : Nat → Bool) (bound width count : Nat)
    (hwidth : 0 < width) (hbound : bound ≤ count * width)
    (hchunks : ∀ k < count, (List.range width).all
      (fun j => if k * width + j < bound then checked (k * width + j) else true) = true) :
    (List.range bound).all checked = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hibound : i < bound := List.mem_range.mp hi
  have hk : i / width < count :=
    (Nat.div_lt_iff_lt_mul hwidth).mpr (Nat.lt_of_lt_of_le hibound hbound)
  have hj : i % width < width := Nat.mod_lt _ hwidth
  have hsum : i / width * width + i % width = i := by
    rw [Nat.mul_comm, Nat.div_add_mod]
  have h := List.all_eq_true.mp (hchunks (i / width) hk)
    (i % width) (List.mem_range.mpr hj)
  simpa only [hsum, ite_eq_left hibound] using h

lemma all_and_parts {α : Type} (xs : List α) (p q : α → Bool)
    (h : xs.all (fun a => p a && q a) = true) :
    xs.all p = true ∧ xs.all q = true := by
  constructor
  · apply List.all_eq_true.mpr
    intro a ha
    exact (Bool.and_eq_true_iff.mp (List.all_eq_true.mp h a ha)).1
  · apply List.all_eq_true.mpr
    intro a ha
    exact (Bool.and_eq_true_iff.mp (List.all_eq_true.mp h a ha)).2

lemma chunked_index_reachable_safe {α : Type}
    (get : Nat → α) (bound width count : Nat)
    (next : α → List α) (contains safe : α → Bool)
    (hwidth : 0 < width) (hbound : bound ≤ count * width)
    (hcontains : ∀ s, contains s = true → ∃ i < bound, get i = s)
    (hchunks : ∀ k < count, (List.range width).all (fun j =>
      if k * width + j < bound then
        safe (get (k * width + j)) && (next (get (k * width + j))).all contains
      else true) = true)
    {start finish : α} (hstart : contains start = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    safe finish = true := by
  have hall := chunked_all (fun i => safe (get i) && (next (get i)).all contains)
    bound width count hwidth hbound hchunks
  obtain ⟨hsafe, hclosed⟩ := all_and_parts (List.range bound)
    (fun i => safe (get i)) (fun i => (next (get i)).all contains) hall
  exact index_reachable_safe get bound next contains safe hcontains hclosed hsafe hstart hreach

lemma chunked_searchIndex_reachable_safe {α : Type} [BEq α] [LawfulBEq α]
    (lt : α → α → Bool) (get : Nat → α) (bound width count fuel : Nat)
    (next : α → List α) (safe : α → Bool)
    (hwidth : 0 < width) (hbound : bound ≤ count * width)
    (hchunks : ∀ k < count, (List.range width).all (fun j =>
      if k * width + j < bound then
        safe (get (k * width + j)) && (next (get (k * width + j))).all
          (fun s => searchIndex lt get bound s fuel 0 bound)
      else true) = true)
    {start finish : α}
    (hstart : searchIndex lt get bound start fuel 0 bound = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    safe finish = true := by
  exact chunked_index_reachable_safe get bound width count next
    (fun s => searchIndex lt get bound s fuel 0 bound) safe hwidth hbound
    (fun s hs => searchIndex_sound lt get bound s fuel 0 bound hs)
    hchunks hstart hreach

end ResourceCertificate



namespace S18Structural.DagTools

def gop : Bool → Bool → Bool → Bool
  | true, a, b => a && b
  | false, a, b => a || b

abbrev Dag := List (Bool × ℕ × ℕ)

def wstep (w : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  w ++ [gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]

def wl (D : Dag) (w : List Bool) : List Bool := D.foldl wstep w

def val (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wl D (List.ofFn x)).getD w false

def outW (n : ℕ) (D : Dag) : ℕ := n + D.length - 1

def single {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i = v)

def supp (n : ℕ) (D : Dag) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => val D (single v) w = true)

variable {n : ℕ} {D : Dag}

lemma mem_supp {v : Fin n} {w : ℕ} : v ∈ supp n D w ↔ val D (single v) w = true := by
  simp [supp]

def sem_Edge {n : ℕ} (G : Fin n → Fin n → Prop) (x : Fin n → Bool) : Prop :=
  ∃ u v : Fin n, G u v ∧ x u = true ∧ x v = true

def sem_Comp (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) : Prop :=
  ∀ x : Fin n → Bool, val D x (outW n D) = true ↔ sem_Edge G x

def petersenAdj (x y : Fin 10) : Prop :=
  (([50, 69, 138, 276, 521, 385, 770, 548, 104, 208] : List Nat).getD x.val 0).testBit y.val = true

lemma h3_out_empty {D : Dag} (hC : sem_Comp 10 petersenAdj D) :
    supp 10 D (outW 10 D) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hh := (hC (single v)).mp (mem_supp.mp hv)
  have hf : ∀ v : Fin 10, ¬ sem_Edge petersenAdj (single v) := by
    unfold sem_Edge petersenAdj single
    decide +kernel
  exact hf v hh

lemma h3_six_rows : ∀ r : Fin 6,
    decide (3 ≤ r.val) = true ↔
    sem_Edge petersenAdj (PEqualNP.Outside.L_meta_2590.OnceGeometry.rowInput r) := by
  unfold PEqualNP.Outside.L_meta_2590.OnceGeometry.rowInput
    PEqualNP.Outside.L_meta_2590.OnceGeometry.rowSet sem_Edge petersenAdj
  decide +kernel

lemma h3_output_mask {D : Dag} (hC : sem_Comp 10 petersenAdj D) :
    PEqualNP.Outside.L_meta_2590.OnceGeometry.wireMask D (outW 10 D) = 56 := by
  have hh : (fun r => val D (PEqualNP.Outside.L_meta_2590.OnceGeometry.rowInput r) (outW 10 D)) =
      (fun r : Fin 6 => decide (3 ≤ r.val)) := by
    funext r
    apply Bool.eq_iff_iff.mpr
    exact (hC _).trans (h3_six_rows r).symm
  change PEqualNP.Outside.L_meta_2590.OnceGeometry.mask
    (fun r => val D (PEqualNP.Outside.L_meta_2590.OnceGeometry.rowInput r) (outW 10 D)) = 56
  rw [hh]
  decide +kernel


end S18Structural.DagTools


namespace S50Resource

abbrev State := Nat × List Nat × List Nat

def layout (c : Fin 8) : Nat := c.val % 4

def groupCount (c : Fin 8) : Nat := if layout c = 0 then 7 else 6

def active (c : Fin 8) (g : Nat) : Bool := decide (g < groupCount c)

def isFilter (c : Fin 8) (g : Nat) : Bool :=
  if layout c = 0 then decide (4 ≤ g) else decide (g = 5)

def leafLoc (c : Fin 8) (i : Nat) : Nat :=
  if c.val < 4 then match i with | 0 => 4 | 1 => 6 | _ => 5
  else match i with | 0 => 5 | 1 => 4 | _ => 6

def leafBase (c : Fin 8) (i : Nat) : Nat :=
  if c.val < 4 then match i with | 0 => 9 | 1 => 20 | _ => 34
  else match i with | 0 => 10 | 1 => 17 | _ => 36

def pairLeft (c : Fin 8) : Nat := if layout c = 3 then 1 else 0

def pairRight (c : Fin 8) : Nat := if layout c = 1 then 1 else 2

def remaining (c : Fin 8) : Nat := 3 - layout c

def portLocs (c : Fin 8) (g : Nat) (right : Bool) : List Nat :=
  if g < 4 then
    if right then (if g = 0 then [1, 2, 3] else [g + 3]) else [g]
  else if layout c = 0 then
    if right then [leafLoc c (g - 4)] else []
  else if g = 4 then [leafLoc c (if right then pairRight c else pairLeft c)]
  else if g = 5 then (if right then [leafLoc c (remaining c)] else [])
  else []

def base (c : Fin 8) (g : Nat) (right : Bool) : Nat :=
  if g < 4 then
    if right then
      if c.val < 4 then match g with | 0 => 0 | 1 => 17 | 2 => 10 | _ => 36
      else match g with | 0 => 0 | 1 => 9 | 2 => 34 | _ => 20
    else 0
  else if layout c = 0 then
    if right then leafBase c (g - 4) else 0
  else if g = 4 then leafBase c (if right then pairRight c else pairLeft c)
  else if g = 5 then (if right then leafBase c (remaining c) else 0)
  else 0

def values (bits : Nat) : List Nat := (List.range 64).filter bits.testBit

def pairMasks (op : Nat → Nat → Nat) (a b : Nat) : Nat :=
  (values a).foldl (fun acc x =>
    (values b).foldl (fun acc y => acc ||| (1 <<< op x y)) acc) 0

def mergePools (a b : Nat) : Nat := pairMasks (· ||| ·) a b

def addCarrier (pool k : Nat) : Nat := pool ||| mergePools pool (1 <<< k)

def sourcePool (ps : List Nat) (raw : Nat) (locs : List Nat) : Nat :=
  locs.foldl (fun acc loc => mergePools acc (ps.getD loc 1)) (1 <<< raw)

def sidePool (c : Fin 8) (ps : List Nat) (g : Nat) (right : Bool) : Nat :=
  sourcePool ps (base c g right) (portLocs c g right)

def live (c : Fin 8) (used loc : Nat) : Bool :=
  (List.range 7).any fun g => active c g && !used.testBit g &&
    ((portLocs c g false).contains loc || (portLocs c g true).contains loc)

def prune (c : Fin 8) (s : State) : State :=
  (s.1, (List.range 7).map (fun i =>
    if live c s.1 i then s.2.1.getD i 1 else 1), s.2.2)

def sortedInsert (k : Nat) : List Nat → List Nat
  | [] => [k]
  | x :: xs => if k ≤ x then k :: x :: xs else x :: sortedInsert k xs

def zeroSort : List Nat → List Nat
  | [] => []
  | x :: xs => sortedInsert x (zeroSort xs)

def insertZero (k : Nat) (zs : List Nat) : List Nat := zeroSort (k :: zs)

def groupNext (c : Fin 8) (s : State) : List State :=
  (List.range 7).flatMap fun g =>
    if active c g && !isFilter c g && !s.1.testBit g then
      (values (pairMasks (· &&& ·) (sidePool c s.2.1 g false) (sidePool c s.2.1 g true))).filterMap
        fun k => if k = 0 then none else
          some (prune c (s.1 ||| (1 <<< g), s.2.1, insertZero k s.2.2))
    else []

def filterNext (c : Fin 8) (s : State) : List State :=
  (List.range 7).flatMap fun g =>
    if active c g && isFilter c g && !s.1.testBit g then
      s.2.2.flatMap fun k => (values (sidePool c s.2.1 g true)).filterMap fun carrier =>
        let result := k &&& carrier
        if result = 0 then none else
          some (prune c (s.1 ||| (1 <<< g), s.2.1, insertZero result (s.2.2.erase k)))
    else []

def liftNext (c : Fin 8) (s : State) : List State :=
  s.2.2.flatMap fun k => (List.range 7).filterMap fun loc =>
    if live c s.1 loc then
      let old := s.2.1.getD loc 1
      let new := addCarrier old k
      if new = old then none else
        some (prune c (s.1, s.2.1.set loc new, s.2.2.erase k))
    else none

def discardNext (c : Fin 8) (s : State) : List State :=
  s.2.2.map fun k => prune c (s.1, s.2.1, s.2.2.erase k)

def combineNext (c : Fin 8) (s : State) : List State :=
  s.2.2.flatMap fun a => (s.2.2.erase a).flatMap fun b =>
    [a &&& b, a ||| b].filterMap fun k => if k = 0 then none else
      some (prune c (s.1, s.2.1, insertZero k ((s.2.2.erase a).erase b)))

def successors (c : Fin 8) (s : State) : List State :=
  groupNext c s ++ filterNext c s ++ liftNext c s ++ discardNext c s ++ combineNext c s

-- Bit 7 records the distinguished dirty gate already used to create the seed.
def initial : State := (128, List.replicate 7 1, [63])

def listLess : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then listLess as bs else decide (a < b)

def stateLess (a b : State) : Bool :=
  if a.1 ≠ b.1 then decide (a.1 < b.1)
  else if a.2.1 ≠ b.2.1 then listLess a.2.1 b.2.1
  else listLess a.2.2 b.2.2

def safe (s : State) : Bool := !s.2.2.contains 56

abbrev CaseState := Fin 8 × State

def caseSuccessors (s : CaseState) : List CaseState :=
  (successors s.1 s.2).map (fun t => (s.1, t))

def caseLess (a b : CaseState) : Bool :=
  if a.1 ≠ b.1 then decide (a.1.val < b.1.val) else stateLess a.2 b.2

def caseSafe (s : CaseState) : Bool := safe s.2

lemma case_reachable (c : Fin 8) {s t : State}
    (h : Relation.ReflTransGen (fun a b => b ∈ successors c a) s t) :
    Relation.ReflTransGen (fun a b => b ∈ caseSuccessors a) (c, s) (c, t) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b d hbd hstep ih =>
    exact ih.tail (List.mem_map.mpr ⟨d, hstep, rfl⟩)

end S50Resource

namespace S50Resource

def packedPool0 : Nat := 0x80000000000000010000001000000001000000040000000100000001000000010000000000100001000000000002000100000000000100010000000000000401000000000000020100000000000001010000000000000011000000000000000500000000000000030000000000000001

def packedPool1 : Nat := 0x8000000000020001800000000001000180000000000002018000000000000101800000000000000380000000000000010000001100000001000000100000001100000010000000010000000500000001000000040000000500000004000000010000000100000001000000000011000100000000001000110000000000100001000000000002000300000000000200010000000000010001000000000000050100000000000004050000000000000401000000000000020300000000000002010000000000000101000000000000001100000000000000050000000000000001

def packedPool2 : Nat := 0x8000000400000001800000010000000180000000000004018000000000000101800000000000000580000000000000010000001100000001000000100000001100000010000000010000000400000005000000040000000100000001000000010000000000110001000000000010001100000000001000010000000000030001000000000002000300000000000200010000000000010001000000000000040500000000000004010000000000000301000000000000020300000000000002010000000000000101000000000000001100000000000000030000000000000001

def packedPool3 : Nat := 0x8000001000000001800000010000000180000000001000018000000000010001800000000000001180000000000000010000001000000011000000100000000100000005000000010000000400000005000000040000000100000001000000010000000000100011000000000010000100000000000300010000000000020003000000000002000100000000000100010000000000000501000000000000040500000000000004010000000000000301000000000000020300000000000002010000000000000101000000000000000500000000000000030000000000000001

def packedPool4 : Nat := 0x80000010000000018000000400000001800000010000000180000000001000018000000000000401800000000000001180000000000000058000000000000001000000110000000100000010000000110000001000000001000000050000000100000004000000050000000400000001000000010000000100000000001000110000000000100001000000000002000100000000000100010000000000000405000000000000040100000000000002010000000000000101000000000000001100000000000000050000000000000001

def packedPool5 : Nat := 0x80000010000000018000000000100001800000000002000180000000000100018000000000000201800000000000001180000000000000038000000000000001000000100000001100000010000000010000000400000001000000010000000100000000001100010000000000100011000000000010000100000000000300010000000000020003000000000002000100000000000100010000000000000401000000000000020300000000000002010000000000000101000000000000001100000000000000030000000000000001

def packedPool6 : Nat := 0x80000004000000018000000000020001800000000000040180000000000002018000000000000101800000000000000580000000000000038000000000000001000000100000000100000004000000050000000400000001000000010000000100000000001000010000000000020003000000000002000100000000000100010000000000000501000000000000040500000000000004010000000000000301000000000000020300000000000002010000000000000101000000000000000500000000000000030000000000000001

def packedPoolLookup (loc : Nat) : Nat :=
  match loc with
  | 0 => packedPool0
  | 1 => packedPool1
  | 2 => packedPool2
  | 3 => packedPool3
  | 4 => packedPool4
  | 5 => packedPool5
  | _ => packedPool6

def packedZeros : Nat := 0x3f4091022408101440450104029009402100440090014000

def poolLookup (loc i : Nat) : Nat :=
  (packedPoolLookup loc >>> (64 * i)) &&& 18446744073709551615

def zeroLookup (i : Nat) : List Nat :=
  let code := (packedZeros >>> (14 * i)) &&& 16383
  (List.range (code &&& 3)).map (fun j => (code >>> (2 + 6 * j)) &&& 63)

def poolSlot (code loc : Nat) : Nat :=
  match loc with
  | 0 => (code >>> 10) &&& 15
  | 1 => (code >>> 14) &&& 31
  | 2 => (code >>> 19) &&& 31
  | 3 => (code >>> 24) &&& 31
  | 4 => (code >>> 29) &&& 31
  | 5 => (code >>> 34) &&& 31
  | _ => (code >>> 39) &&& 31

def decode (code : Nat) : CaseState :=
  (⟨code % 8, Nat.mod_lt _ (by decide)⟩, ((code >>> 3) &&& 127) + 128,
    (List.range 7).map (fun i => poolLookup i (poolSlot code i)),
    zeroLookup ((code >>> 44) &&& 15))

def block0 : Nat := 0x20008000000400008000008000008000100000008002000000008050000000008000000000008000000004c0480000009800480001e0000048004000000048088000000048c0000000004800000000004800001600304000001604c04000001698004000001b0000400001f6000040004016000040088016000040c000160000400000160000400000000180280000070000280000a0000028001800000028038000000028600000000028000000000028000000b01820000000b18020000000c80020000007b000200000a0b00020001800b00020038000b00020600000b00020000000b0002000000050001800000b00001800010000001800200000001805800000001880000000001800000000001800000005a01000000006c01000000055801000000b058010000100058010002000058010058000058010800000058010000000058010000000003400000000058000000000b00000000016000000000240000000004800000000090000000000d00000000000000000000000

def block1 : Nat := 0xa0301100000e0030110001c0003011005000003011070000003011000000003011000000000250000000003010000000068010000000e000100000120000100002c0000010006800000010090000000010000000000010000000000c0a80000030000a80000600000a8000c000000a80180000000a84000000000a80000000000a8000000b010a00000002010a0000000b0c0a000000020c0a0000000c000a0000003b000a0000060b000a0000c00b000a0018000b000a0400000b000a0000000b000a00000003000a00000032000a00000602000a0000c002000a00180002000a04000002000a00000002000a000000008009800000100009800040000009800800000009810000000009800000000009800000005849000000001049000000005c0900000000d8090000001058090000400058090008000058090100000058090000000058090000000014090000000090090000001010090000400010090008000010090100000010090000000010090000000001480000000010080

def block2 : Nat := 0xb04220000000884220000000b80220000002b00220000020b00220010000b00220200000b00220000000b00220000000900220000002880220000020880220010000880220200000880220000000880220000000002e00000000040200000000880200000011000200000180000200003c00000200078000000200b00000000200000000000200000000008148000000100148000040000148000800000148300000000148000000000148000016000d4000000e000d4000001600814000000e00814000001610014000000e10014000001700014000005600014000081600014030001600014000001600014000000f00014000004e00014000080e00014030000e00014000000e00014000000048011800000a0001180000e0000118001c00000118050000000118700000000118000000000118000000059d10000000031d100000000681100000004d811000000a0581100000e0058110001c000581100500000581107000000581100000000581100000000381100000004b0110

def block3 : Nat := 0x7b000210000a0b00021001800b00021038000b00021600000b00021000000b0002100000050001900000b00001900010000001900200000001905800000001980000000001900000000001900000005a01100000006c01100000055801100000b058011000100058011002000058011058000058011800000058011000000058011000000003401000000058001000000b00001000016000001000240000001004800000001090000000001d0000000000100000000000100000003c248000000800248000160000248003800000248070000000248a00000000248000000000248000016002a40000011002a4000001603c24000001103c24000001680024000001180024000001a000240000176000240003816000240070016000240a00016000240000016000240000013000240000171000240003811000240070011000240a00011000240000011000240000000004228000002000228000020000228010000000228200000000228000000000228000000b00a20000000880a20

def block4 : Nat := 0x580910000000380910000006b00910000004b009100000e03009100000a030091002c00030091001c0003009106800003009105000003009190000003009170000003009100000003009109000001409109000009009109000101009109040001009109800001009119000001009109000001009100024000248109000000148100024003008109000001008100024068008109000020008100024e0000810900040000810002c0000081002e400000810682400000819002400000810002400000810900800000810910000000810b000000008159000000008109000000008100000004c0490000009800490001e0000049004000000049088000000049c0000000004900000000004900001600304100001604c04100001698004100001b0000410001f6000041004016000041088016000041c000160000410000160000410000000180290000070000290000a0000029001800000029038000000029600000000029000000000029000000b01821000000b18021000000c80021

def block5 : Nat := 0x4900000000a90900000000a90480000000a94380000000a90380000000a9038000b010a10900002010a1038000b0c0a109000020c0a1038000c000a1038003b000a1038060b000a1038c00b000a1048000b000a1438000b000a1038000b000a10900003000a10900032000a10900602000a1090c002000a10a80002000a14900002000a10900002000a100000068009900000048009909000008009905800008009900000e00009900000a000099090001000099058001000099002c00000099001c00000099090400000099058400000099098000000099190000000099090000000099068000000099060000000099158000000099058000000099050000000099900000000099700000000099000000000099000000032491000000059c91000000031c9105800005849109000001049100000006809105800005c0910000004d80910580000d809100000a058091058001058091001c00058091058400058091060000058091158000058091058000058091050000058091700000058091

def block6 : Nat := 0x40100d10004010100d11000010100d10000010100d10000161080d100000e1080d10000170080d10008160080d13000160080d10000160080d100000f0080d100080e0080d130000e0080d100000e0080d10000000100c90002400080c90001e00080c90000002000c90002401000c90001e01000c90002800000c9000a400000c93002400000c90002400000c90002000000c90009e00000c93001e00000c90001e00000c90000800000c90010000000c95000000000c90000000000c90000040014c10001f6000cc100024e000cc10000040100c10001f60080c100024e0080c10000042000c10001f61000c100024e1000c10001f70000c10002160000c10009f60000c13001f60000c10001f60000c100024f0000c100028e0000c1000a4e0000c130024e0000c100024e0000c10000840000c10010040000c15000040000c10000040000c109000000c0a903800000c0a90900030000a90380030000a90900600000a90380600000a9090c000000a9038c000000a90a80000000a9

def block7 : Nat := 0x11000101000180000101003c00000101078000000101b0000000010100000000010100000000c0e90000600000e9000c000000e94000000000e90000000000e9000003b010e10000042010e10000032010e1000003b0c0e100000420c0e100000320c0e1000003c000e1000063b000e1000c03b000e1400003b000e1000003b000e10000043000e10000033000e10000062000e10000642000e1000c042000e14000042000e10000042000e10000632000e1000c032000e14000032000e10000032000e10000001000d90000000800d90008000000d90004000000d93000000000d91000000000d90000000000d900000e030cd1000016008cd100000e008cd10000010584d10000040104d10000010104d100000105c0d10000010d80d10004010580d11000010580d10000010580d100000e0340d100000e1300d100000f0300d100080e0300d130000e0300d100000e0300d10000040140d10000010140d10000040900d10000010900d10000050100d10004040100d11000040100d1

def block8 : Nat := 0x100058012002000058012058000058012800000058012000000058012000000003402000000058002000000b00002000016000002000240000002004800000002090000000002d0000000000200000000000200000003c149000000800149000160000149003800000149070000000149a0000000014900000000014900001600294100001100294100001603c14100001103c14100001680014100001180014100001a000141000176000141003816000141070016000141a00016000141000016000141000013000141000171000141003811000141070011000141a00011000141000011000141000000004129000002000129000020000129010000000129200000000129000000000129000000b00921000000880921000000b04121000000884121000000b80121000002b00121000020b00121010000b00121200000b00121000000b00121000000900121000002880121000020880121010000880121200000880121000000880121000000002d01000000040101000000880101

def block9 : Nat := 0xc800010092104800010092004800010092000240002c82004800001482000240040082004800010082000240880082004800200082000251000082004804000082000300000082003e40000082078240000082b0024000008200024000008200488000008200540000008202480000008250480000008200480000008200000004c04a00000098004a0001e000004a00400000004a08800000004ac0000000004a00000000004a00001600304200001604c04200001698004200001b0000420001f6000042004016000042088016000042c0001600004200001600004200000001802a00000700002a0000a000002a00180000002a03800000002a60000000002a00000000002a000000b01822000000b18022000000c80022000007b000220000a0b00022001800b00022038000b00022600000b00022000000b0002200000050001a00000b00001a00010000001a00200000001a05800000001a80000000001a00000000001a00000005a01200000006c01200000055801200000b058012

def block10 : Nat := 0x3b000a20000a2b000a20000c0b000a20100a0b000a22000a0b000a20000a0b000a2000060b000a2018000b000a2400000b000a2000000b000a20002409000a20002428800a20002608800a20102408800a22002408800a20002408800a20000003000a20000042000a20000032000a20000802000a20000602000a20200002000a20180002000a25000002000a24000002000a20000002000a200000088009a00480008009a00200008009a00001100009a00480100009a00200100009a004c0000009a00c80000009a10480000009a00480000009a003c0000009a00240000009a00a00000009a10200000009a00200000009a07800000009ab0000000009a00000000009a000000042c9200200005849200480001049200200005c0920020000d809200200105809200240005809200a0000580921020000580920020000580920000008c0092000011040092003c00040092078000040092b00000040092000000040092004800014092004800090092004801010092004c00010092

def block11 : Nat := 0x1000000d80b20000000d80b20000008c40b20000009400b20000028c00b20100008c00b22000008c00b20000008c00b20000002140b20000000940b20000002900b20000012100b20080002100b21000002100b20000002100b20000010900b20080000900b21000000900b20000000900b2000000b840b2000002b040b2010000b040b2200000b040b2000000b040b20000009040b20000028840b20100008840b22000008840b20000008840b20000000100aa00000000c0aa0002400040aa0000a00040aa0000040000aa0000030000aa0002420000aa0000a20000aa0002600000aa0102400000aa2002400000aa0002400000aa0000c00000aa0100a00000aa2000a00000aa0000a00000aa0000800000aa0000600000aa0200000000aa0180000000aa5000000000aa4000000000aa0000000000aa0000002014a2000000b010a20000002010a20000a0b008a20002408808a20000002100a2000000b0c0a200000020c0a20000a0b040a20002408840a2000000c000a20000a0b800a2

def block12 : Nat := 0x38110400d20700110400d2a000110400d20000110400d200001683c0d200001183c0d200001a03c0d200381603c0d207001603c0d2a0001603c0d200001603c0d200001303c0d200381103c0d207001103c0d2a0001103c0d200001103c0d200024003c0ca0001e003c0ca0002408000ca0001e08000ca0002e00000ca003a400000ca0702400000caa002400000ca0002400000ca0002200000ca0039e00000ca0701e00000caa001e00000ca0001e00000ca0001f60028c20002510028c20001f603c0c200025103c0c20001f68000c20002518000c20001fa0000c20002360000c20039f60000c20701f60000c2a001f60000c20001f60000c20002530000c20002f10000c2003a510000c20702510000c2a002510000c20002510000c20000020000ba0000010000ba0100000000ba0080000000ba2000000000ba1000000000ba0000000000ba0000008c08b2000000b048b20000008848b20000000d84b20000002104b20000000904b20000000dc0b20000010d80b20080000d80b2

def block13 : Nat := 0x80000014a30000000014a00000000014a000016000d4200000e000d4200001600814200000e00814200001610014200000e10014200001700014200005600014200081600014230001600014200001600014200000f00014200004e00014200080e00014230000e00014200000e00014200000048011a00000a00011a0000e000011a001c0000011a05000000011a70000000011a00000000011a000000059d12000000031d120000000681120000004d811200000a0581120000e0058112001c000581120500000581127000000581120000000581120000000381120000004b011200000a0301120000e0030112001c0003011205000003011270000003011200000003011200000000250200000003010200000068010200000e000102000120000102002c000001020680000001029000000001020000000001020000008000da0038000000da0700000000daa000000000da0000000000da0000110428d200001603e8d200001103e8d20000110480d20000118400d20000130400d2

def block14 : Nat := 0x93c000000830c8000000083b9000000008309000000008300000004c04b00000098004b0001e000004b00400000004b08800000004bc0000000004b00000000004b00001600304300001604c04300001698004300001b0000430001f6000043004016000043088016000043c0001600004300001600004300000001802b00000700002b0000a000002b00180000002b03800000002b60000000002b00000000002b000000b01823000000b18023000000c80023000007b000230000a0b00023001800b00023038000b00023600000b00023000000b0002300000050001b00000b00001b00010000001b00200000001b05800000001b80000000001b00000000001b00000005a01300000006c01300000055801300000b058013000100058013002000058013058000058013800000058013000000058013000000003403000000058003000000b00003000016000003000240000003004800000003090000000003d0000000000300000000000300000000814a00000010014a00004000014a

def block15 : Nat := 0x900008840a3038000b800a3038002b000a3038020b000a3040000b000a3238000b000a3038000b000a30900009000a30900028800a30900208800a30a00008800a32900008800a30900008800a300000e6800a30001206800a30680006800a39000006800a30000006800a300480048009b00200048009b00480a00009b00200a00009b0048e000009b0020e000009b00580000009b05480000009b70480000009b00480000009b00280000009b05200000009b70200000009b00200000009b002000059c93004800031c930020000680930020004d809300200a0580930020e00580930028000580930520000580937020000580930020000580930048000380930048004b009300480a0300930048e0030093005800030093054800030093704800030093004800030093090000002c8300480000248309000004008300480003008309000088008300480068008309001100008300480e00008309018000008300492000008300600000008306c800000083904800000083004800000083

def block16 : Nat := 0x160000c30000130000c30001910000c30001710000c3003c110000c30038110000c3b000110000c3a000110000c30000110000c300480f0000c300484e0000c300500e0000c330480e0000c300480e0000c300000a0000bb0000e00000bb0500000000bb7000000000bb0000000000bb0000004d9cb30000006b1cb30000004b1cb30000004e80b300000a4d80b30000e04d80b30500004d80b37000004d80b30000004d80b30000006b80b30000004b80b30000007b00b300000a6b00b30000e06b00b30500006b00b37000006b00b30000006b00b300000a4b00b30000e04b00b30500004b00b37000004b00b30000004b00b30000000300ab0900000040ab0380000040ab00000e0000ab0900020000ab0380020000ab0001200000ab0900200000ab0380200000ab0a00000000ab2900000000ab0900000000ab0680000000ab0400000000ab2380000000ab0380000000ab9000000000ab0000000000ab0000006824a3038000b008a30900008808a30000006b00a3038000b040a3

def block17 : Nat := 0x118800e30000228800e32000028800e30000028800e300000e7000e300000f6800e300004e6800e330000e6800e300000e6800e30000171000e30000561000e33000161000e30000161000e300000f1000e300004e1000e330000e1000e300000e1000e30000000400cb00000003c0cb0048000080cb0040000080cb0000008800cb0000008000cb0048001000cb0040001000cb0001800000cb0001600000cb0048400000cb0040400000cb0050000000cb3048000000cb0048000000cb0044000000cb3040000000cb0040000000cb003c000000cb0038000000cbb000000000cba000000000cb0000000000cb000011002cc30000160028c30000110028c3004016000cc300480e000cc30000110400c300001603c0c300001103c0c30040160080c300480e0080c30000118800c30000168000c30000118000c30040161000c300480e1000c300001a0000c30040170000c30001760000c30040560000c30044160000c33040160000c30040160000c30038160000c3a000160000c3

def block18 : Nat := 0x60200123000c0020012301800020012340000020012300000020012300000008011b00000100011b00040000011b00800000011b10000000011b00000000011b00000005851300000001051300000005c1130000000d81130000010581130004000581130080000581131000000581130000000581130000000141130000000901130000010101130004000101130080000101131000000101130000000101130000000015030000000101030000002001030000040001030000800001030010000001030200000001035000000001030000000001030000000080eb0000000040eb0000400000eb0000200000eb3000000000eb2000000000eb0000000000eb00000e680ce3000016100ce300000e100ce3000002b008e30000118808e30000028808e300000e6880e30000161080e300000e1080e3000002b040e30000118840e30000028840e3000002b800e3000022b000e3200002b000e3000002b000e30000119000e30000029000e30000128800e30000318800e32000118800e3

def block19 : Nat := 0x6801600004490001600004400001600004400000004002c00001100002c00018000002c003c0000002c07800000002cb0000000002c00000000002c000000b02c24000000b40024000000d80024000011b00024000180b00024003c00b00024078000b00024b00000b00024000000b0002400000020001c00000400001c00008000001c00100000001c02000000001c50000000001c00000000001c000000059414000000064014000000258014000004058014000080058014001000058014020000058014500000058014000000058014000000003404000000058004000000b00004000016000004000240000004004800000004090000000004d0000000000400000000000400000000c12b00000300012b00006000012b000c0000012b01800000012b40000000012b00000000012b000000b01123000000201123000000b0c12300000020c123000000c00123000003b00123000060b00123000c00b00123018000b00123400000b00123000000b00123000000300123000003200123

def block20 : Nat := 0xac000000b008a40000003808a4000000b040a40000003840a4000000b800a4000002b000a4000020b000a4010000b000a4200000b000a4000000b000a40000004000a40000023800a40000203800a40100003800a42000003800a40000003800a400000018009c00000300009c00006000009c000c0000009c01800000009c40000000009c00000000009c0000000590940000000190940000000600940000001d8094000003058094000060058094000c00058094018000058094400000058094000000058094000000020094000000198094000003018094000060018094000c000180940180000180944000000180940000000180940000000018840000000180840000003800840000070000840000a000008400180000008403800000008460000000008400000000008400000003004c00000068004c00012000004c002c0000004c06800000004c90000000004c00000000004c000016002444000016030044000016680044000019000044000136000044002c16000044

def block21 : Nat := 0x88000000204c0000000020400000000020400000002414c00000048014c0000e000014c001c0000014c05000000014c70000000014c00000000014c000016001d4400000b001d4400001602414400000b02414400001648014400000b4801440000180001440000f6000144001c1600014405001600014470001600014400001600014400000d0001440000eb000144001c0b00014405000b00014470000b00014400000b00014400000008011c00000100011c00040000011c00800000011c10000000011c00000000011c00000005851400000002851400000005c1140000000d811400000105811400040005811400800005811410000005811400000005811400000002c1140000000a811400000102811400040002811400800002811410000002811400000002811400000000210400000002810400000050010400000b0001040001000001040020000001040580000001048000000001040000000001040000000040ac0000020000ac0000200000ac0100000000ac2000000000ac

def block22 : Nat := 0x500000058015000000058015000000003405000000058005000000b00005000016000005000240000005004800000005090000000005d0000000000500000000000500000000824c00000010024c00004000024c00080000024c30000000024c00000000024c000016000e44000014000e4400001600824400001400824400001610024400001410024400001700024400005600024400081600024430001600024400001600024400001500024400005400024400081400024430001400024400001400024400000003c22c00001000022c00016000022c00380000022c07000000022ca0000000022c00000000022c000000b02a24000000982a24000000b3c2240000009bc224000000d00224000010b00224000160b00224003800b00224070000b00224a00000b00224000000b00224000000a80224000010980224000160980224003800980224070000980224a0000098022400000098022400000000320400000004c2040000009802040000140002040001e0000204004000000204

def block23 : Nat := 0x480000208500024000188500480002808500024001808500480050008500024038008500480b0000850002470000850002a0000085001a40000085038240000085600240000085000240000085004900000085005c0000008505c80000008580480000008500480000008500000003004d00000068004d00012000004d002c0000004d06800000004d90000000004d00000000004d000016002445000016030045000016680045000019000045000136000045002c1600004506801600004590001600004500001600004500000004002d00001100002d00018000002d003c0000002d07800000002db0000000002d00000000002d000000b02c25000000b40025000000d80025000011b00025000180b00025003c00b00025078000b00025b00000b00025000000b0002500000020001d00000400001d00008000001d00100000001d02000000001d50000000001d00000000001d000000059415000000064015000000258015000004058015000080058015001000058015020000058015

def block24 : Nat := 0x102403800a52002403800a50002403800a500000038009d00000018009d00480008009d00100008009d00000700009d00000300009d00480100009d00100100009d004c0000009d00c80000009d10480000009d00480000009d00180000009d00140000009d00900000009d10100000009d00100000009d000c0000009d03800000009d01800000009d60000000009d40000000009d00000000009d00000001989500000005909500000001909500100005849500480002849500000006009500100005c0950000001d80950010000d8095000003058095001001058095001400058095009000058095101000058095001000058095000c0005809501800005809540000005809500000005809500480002c0950048000a8095004801028095004c0002809500c800028095104800028095004800028095000000020095000000398095000000198095000007018095000003018095001800018095000c00018095038000018095018000018095600000018095400000018095000000018095

def block25 : Nat := 0xac0b50000005a80b50000015280b50080005280b51000005280b50000005280b50000010a80b50080000a80b51000000a80b50000000a80b500000039c0b50000004180b50000023980b50100003980b52000003980b50000003980b5000000b840b5000002b040b5010000b040b5200000b040b5000000b040b50000004040b50000023840b50100003840b52000003840b50000003840b50000000280ad0002400040ad0001800040ad00000b0000ad0002420000ad0001820000ad0002600000ad0102400000ad2002400000ad0002400000ad0001a00000ad0101800000ad2001800000ad0001800000ad0001000000ad0580000000ad8000000000ad0000000000ad0000005020a5000180b008a50002403808a50000005280a5000180b040a50002403840a5000180b800a5000182b000a50001a0b000a5010180b000a5200180b000a5000180b000a500000b5000a50001005000a50580005000a58000005000a50000005000a50002404000a50002423800a50002603800a5

def block26 : Nat := 0x5000b5000e570000b5000e500000b5000e50000184800e50000f64800e50500164800e57000164800e50000164800e500000d4800e50000eb4800e505000b4800e570000b4800e500000b4800e50048000240cd002c000240cd0048004800cd002c004800cd0048e00000cd002ce00000cd0058000000cd0548000000cd7048000000cd0048000000cd0034000000cd052c000000cd702c000000cd002c000000cd002c16001cc500480b001cc5002c160240c500480b0240c5002c164800c500480b4800c5002c180000c5002cf60000c50034160000c5052c160000c5702c160000c5002c160000c500480d0000c50048eb0000c500580b0000c505480b0000c570480b0000c500480b0000c50000020000bd0000010000bd0100000000bd0080000000bd2000000000bd1000000000bd0000000000bd0000003988b5000000b048b50000003848b50000000d84b50000005284b50000000a84b50000000dc0b50000010d80b50080000d80b51000000d80b50000000d80b500000052c0b5

def block27 : Nat := 0x16000d45000014000d4500001600814500001400814500001610014500001410014500001700014500005600014500081600014530001600014500001600014500001500014500005400014500081400014530001400014500001400014500000003c12d00001000012d00016000012d00380000012d07000000012da0000000012d00000000012d000000b02925000000982925000000b3c1250000009bc125000000d00125000010b00125000160b00125003800b00125070000b00125a00000b00125000000b00125000000a80125000010980125000160980125003800980125070000980125a0000098012500000098012500000000310500000004c1050000009801050000140001050001e0000105004000000105088000000105c000000001050000000001050000000240ed0000e00000ed0500000000ed7000000000ed0000000000ed00000b501ce5000016481ce500000b481ce500000b5240e50000164a40e500000b4a40e500000b6000e500000d5000e50000eb5000e5

def block28 : Nat := 0x9000000008600000003004e00000068004e00012000004e002c0000004e06800000004e90000000004e00000000004e000016002446000016030046000016680046000019000046000136000046002c1600004606801600004690001600004600001600004600000004002e00001100002e00018000002e003c0000002e07800000002eb0000000002e00000000002e000000b02c26000000b40026000000d80026000011b00026000180b00026003c00b00026078000b00026b00000b00026000000b0002600000020001e00000400001e00008000001e00100000001e02000000001e50000000001e00000000001e000000059416000000064016000000258016000004058016000080058016001000058016020000058016500000058016000000058016000000003406000000058006000000b00006000016000006000240000006004800000006090000000006d0000000000600000000000600000000814d00000010014d00004000014d00080000014d30000000014d00000000014d

def block29 : Nat := 0x149800a60000109800a60001e09800a60001609800a60880009800a60700009800a6c000009800a6a000009800a60000009800a60900004000a60900023800a60900203800a60a00003800a62900003800a60900003800a609000018009e02000018009e09000300009e02000300009e09006000009e02006000009e090c0000009e020c0000009e0a800000009e49000000009e09000000009e03000000009e42000000009e02000000009e0200000590960900000190960200000600960200001d8096020003058096020060058096020c00058096030000058096420000058096020000058096090000020096090000198096090003018096090060018096090c000180960a800001809649000001809609000001809600480000308609000000188600480004c0860900000180860048009800860900003800860048140000860900070000860049e00000860900a000008600640000008608c800000086c048000000860048000000860918000000860b8000000086690000000086

def block30 : Nat := 0x48140080c60000073800c6002c161000c60048141000c6002c170000c6002c560000c60030160000c6302c160000c6002c160000c60048150000c60048540000c60050140000c63048140000c60048140000c60000a70000c60018070000c66000070000c60000070000c600000004c0ae00000003c0ae0900000040ae0780000040ae0000140000ae0000100000ae0900020000ae0780020000ae0001e00000ae0001600000ae0900200000ae0780200000ae0a00000000ae2900000000ae0900000000ae0880000000ae0800000000ae2780000000ae0780000000ae0700000000aec000000000aea000000000ae0000000000ae0000009830a6000000b028a60000009828a6078000b008a60900003808a60000009cc0a6000000b3c0a60000009bc0a6078000b040a60900003840a6000000d000a6078000b800a6000010b000a6078002b000a6000160b000a6078020b000a6080000b000a6278000b000a6078000b000a6070000b000a6a00000b000a6000000b000a6000000a800a6

def block31 : Nat := 0x273800e62000073800e60000073800e60000223800e62000023800e60000023800e60000171000e60000561000e63000161000e60000161000e60000151000e60000541000e63000141000e60000141000e60000001800de0000600000de000c000000de4000000000de0000000000de0000030590d60000070190d60000030190d60000030600d60000031d80d60000630580d6000c030580d64000030580d60000030580d60000070200d60000030200d60000071980d60000031980d60000090180d60000670180d6000c070180d64000070180d60000070180d60000630180d6000c030180d64000030180d60000030180d60000000180ce0048000080ce002c000080ce0000003800ce0048001000ce002c001000ce0000a00000ce0048400000ce002c400000ce0050000000ce3048000000ce0048000000ce0030000000ce302c000000ce002c000000ce0018000000ce6000000000ce0000000000ce0000070018c6002c16000cc6004814000cc60000070180c6002c160080c6

def block32 : Nat := 0x70000b00014600000b00014600000008011e00000100011e00040000011e00800000011e10000000011e00000000011e00000005851600000002851600000005c1160000000d811600000105811600040005811600800005811610000005811600000005811600000002c1160000000a811600000102811600040002811600800002811610000002811600000002811600000000210600000002810600000050010600000b0001060001000001060020000001060580000001068000000001060000000001060000000080ee0000000040ee0000400000ee0000200000ee3000000000ee2000000000ee0000000000ee000014980ce6000016100ce6000014100ce6000002b008e60000073808e60000023808e60000149880e60000161080e60000141080e6000002b040e60000073840e60000023840e6000002b800e6000022b000e6200002b000e6000002b000e6000014a000e60000159800e60000549800e63000149800e60000149800e60000074000e60000024000e60000083800e6

def block33 : Nat := 0x4002f00001100002f00018000002f003c0000002f07800000002fb0000000002f00000000002f000000b02c27000000b40027000000d80027000011b00027000180b00027003c00b00027078000b00027b00000b00027000000b0002700000020001f00000400001f00008000001f00100000001f02000000001f50000000001f00000000001f000000059417000000064017000000258017000004058017000080058017001000058017020000058017500000058017000000058017000000003407000000058007000000b00007000016000007000240000007004800000007090000000007d0000000000700000000000700000002414e00000048014e0000e000014e001c0000014e05000000014e70000000014e00000000014e000016001d4600000b001d4600001602414600000b02414600001648014600000b4801460000180001460000f6000146001c1600014605001600014670001600014600001600014600000d0001460000eb000146001c0b00014605000b000146

def block34 : Nat := 0x9000000009f08800000009f02800000009f12000000009f02000000009fc0000000009f00000000009f00000004f09702000005849709000002849702000005c0970200000d80970200010580970204000580970280000580971200000580970200000580970000009cc09700001404c09700400004c09708800004c097c0000004c09700000004c09709000002c0970900000a809709000102809709040002809709800002809719000002809709000002809700024000308709000000208700024004c08709000002808700024098008709000050008700025400008709000b000087000320000087004240000087088240000087c002400000870002400000870901000000870920000000870c000000008789000000008709000000008700000003004f00000068004f00012000004f002c0000004f06800000004f90000000004f00000000004f000016002447000016030047000016680047000019000047000136000047002c16000047068016000047900016000047000016000047

def block35 : Nat := 0xb3e8b70000009be8b70000009d40b7000000acc0b70000109cc0b70038009cc0b70700009cc0b7a000009cc0b70000009cc0b7000000d3c0b7000010b3c0b7003800b3c0b7070000b3c0b7a00000b3c0b7000000b3c0b7000000abc0b70000109bc0b70038009bc0b70700009bc0b7a000009bc0b70000009bc0b700024003c0af00018003c0af0002500000af0001900000af0002e00000af003a400000af0702400000afa002400000af0002400000af0001c00000af0039800000af0701800000afa001800000af0001800000af000180b028a70002409828a7000180b3c0a70002409bc0a7000180d000a7000190b000a70001c0b000a7003980b000a7070180b000a7a00180b000a7000180b000a7000240a800a70002509800a70002e09800a7003a409800a70702409800a7a002409800a70002409800a700000098009f09000008009f02000008009f00001400009f09000100009f02000100009f00400000009f09040000009f02040000009f09800000009f19000000009f

def block36 : Nat := 0x1200080cf0000005000cf0000004800cf0002401000cf0001201000cf0002800000cf000a400000cf3002400000cf0002400000cf0001400000cf0009200000cf3001200000cf0001200000cf0001000000cf0000e00000cf0020000000cf001c000000cf8000000000cf7000000000cf0000000000cf00000b0020c7000016001cc700000b001cc7000136000cc7000254000cc700000b0280c70000160240c700000b0240c70001360080c70002540080c700000b5000c70000164800c700000b4800c70001361000c70002541000c70000180000c70001370000c70001560000c70009360000c73001360000c70001360000c70000f60000c7001c160000c77000160000c70000160000c70002550000c70002940000c7000a540000c73002540000c70002540000c700000d0000c700010b0000c70000eb0000c700200b0000c7001c0b0000c780000b0000c770000b0000c700000b0000c70000100000bf0038000000bf0700000000bfa000000000bf0000000000bf0000009ce8b7

def block37 : Nat := 0x198117000003018117000060018117000c000181170180000181174000000181170000000181170000000019070000000181070000003801070000070001070000a00001070018000001070380000001076000000001070000000001070000001000df0000000800df0008000000df0004000000df3000000000df1000000000df0000000000df00001404ccd7000016008cd7000014008cd70000010584d700000b0284d70000010284d700000105c0d70000010d80d70004010580d71000010580d70000010580d70000140500d700001414c0d700001504c0d700081404c0d730001404c0d700001404c0d700000b02c0d700000102c0d700000b0a80d70000010a80d700000c0280d700040b0280d710000b0280d700000b0280d70004010280d71000010280d70000010280d70000161080d70000141080d70000170080d70008160080d73000160080d70000160080d70000150080d70008140080d73000140080d70000140080d70000000280cf0000000240cf0002400080cf

def block38 : Nat := 0x412f00000200012f00002000012f01000000012f20000000012f00000000012f000000b00927000000380927000000b04127000000384127000000b80127000002b00127000020b00127010000b00127200000b00127000000b0012700000040012700000238012700002038012701000038012720000038012700000038012700000018011f00000300011f00006000011f000c0000011f01800000011f40000000011f00000000011f0000000591170000000191170000000601170000001d8117000003058117000060058117000c00058117018000058117400000058117000000058117000000020117

def blockLookup (k : Nat) : Nat := (if k < 19 then (if k < 9 then (if k < 4 then (if k < 2 then (if k < 1 then block0 else block1) else (if k < 3 then block2 else block3)) else (if k < 6 then (if k < 5 then block4 else block5) else (if k < 7 then block6 else (if k < 8 then block7 else block8)))) else (if k < 14 then (if k < 11 then (if k < 10 then block9 else block10) else (if k < 12 then block11 else (if k < 13 then block12 else block13))) else (if k < 16 then (if k < 15 then block14 else block15) else (if k < 17 then block16 else (if k < 18 then block17 else block18))))) else (if k < 29 then (if k < 24 then (if k < 21 then (if k < 20 then block19 else block20) else (if k < 22 then block21 else (if k < 23 then block22 else block23))) else (if k < 26 then (if k < 25 then block24 else block25) else (if k < 27 then block26 else (if k < 28 then block27 else block28)))) else (if k < 34 then (if k < 31 then (if k < 30 then block29 else block30) else (if k < 32 then block31 else (if k < 33 then block32 else block33))) else (if k < 36 then (if k < 35 then block34 else block35) else (if k < 37 then block36 else (if k < 38 then block37 else block38))))))

def getCode (i : Nat) : Nat :=
  (blockLookup (i / 64) >>> (48 * (i % 64))) &&& 281474976710655

def getState (i : Nat) : CaseState := decode (getCode i)

def contains (s : CaseState) : Bool :=
  ResourceCertificate.searchIndex caseLess getState 2472 s 13 0 2472

def checked (i : Nat) : Bool := caseSafe (getState i) && (caseSuccessors (getState i)).all contains

def chunkCheck (k : Nat) : Bool :=
  (List.range 64).all (fun j => if k * 64 + j < 2472 then checked (k * 64 + j) else true)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk0_closed : chunkCheck 0 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk1_closed : chunkCheck 1 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk2_closed : chunkCheck 2 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk3_closed : chunkCheck 3 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk4_closed : chunkCheck 4 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk5_closed : chunkCheck 5 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk6_closed : chunkCheck 6 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk7_closed : chunkCheck 7 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk8_closed : chunkCheck 8 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk9_closed : chunkCheck 9 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk10_closed : chunkCheck 10 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk11_closed : chunkCheck 11 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk12_closed : chunkCheck 12 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk13_closed : chunkCheck 13 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk14_closed : chunkCheck 14 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk15_closed : chunkCheck 15 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk16_closed : chunkCheck 16 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk17_closed : chunkCheck 17 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk18_closed : chunkCheck 18 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk19_closed : chunkCheck 19 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk20_closed : chunkCheck 20 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk21_closed : chunkCheck 21 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk22_closed : chunkCheck 22 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk23_closed : chunkCheck 23 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk24_closed : chunkCheck 24 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk25_closed : chunkCheck 25 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk26_closed : chunkCheck 26 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk27_closed : chunkCheck 27 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk28_closed : chunkCheck 28 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk29_closed : chunkCheck 29 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk30_closed : chunkCheck 30 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk31_closed : chunkCheck 31 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk32_closed : chunkCheck 32 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk33_closed : chunkCheck 33 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk34_closed : chunkCheck 34 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk35_closed : chunkCheck 35 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk36_closed : chunkCheck 36 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk37_closed : chunkCheck 37 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk38_closed : chunkCheck 38 = true := by decide +kernel

lemma all_chunks_checked : (List.range 39).all chunkCheck = true := by
  change ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38] : List Nat).all chunkCheck = true
  simp only [List.all_cons, List.all_nil, chunk0_closed, chunk1_closed, chunk2_closed, chunk3_closed, chunk4_closed, chunk5_closed, chunk6_closed, chunk7_closed, chunk8_closed, chunk9_closed, chunk10_closed, chunk11_closed, chunk12_closed, chunk13_closed, chunk14_closed, chunk15_closed, chunk16_closed, chunk17_closed, chunk18_closed, chunk19_closed, chunk20_closed, chunk21_closed, chunk22_closed, chunk23_closed, chunk24_closed, chunk25_closed, chunk26_closed, chunk27_closed, chunk28_closed, chunk29_closed, chunk30_closed, chunk31_closed, chunk32_closed, chunk33_closed, chunk34_closed, chunk35_closed, chunk36_closed, chunk37_closed, chunk38_closed, Bool.and_self]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma initial_contains : ∀ c : Fin 8, contains (c, initial) = true := by decide +kernel

lemma reachable_safe (c : Fin 8) {finish : State}
    (hreach : Relation.ReflTransGen (fun a b => b ∈ successors c a) initial finish) :
    safe finish = true := by
  apply ResourceCertificate.chunked_searchIndex_reachable_safe caseLess getState
    2472 64 39 13 caseSuccessors caseSafe (by decide) (by decide) ?_ (initial_contains c) (case_reachable c hreach)
  intro k hk
  change chunkCheck k = true
  exact List.all_eq_true.mp all_chunks_checked k (List.mem_range.mpr hk)

lemma reachable_no_target (c : Fin 8) {finish : State}
    (hreach : Relation.ReflTransGen (fun a b => b ∈ successors c a) initial finish) :
    56 ∉ finish.2.2 := by
  simpa [safe] using reachable_safe c hreach

end S50Resource


namespace S50Geometry

open S50Resource

def leafSupport (c : Fin 8) (i : Nat) : Finset (Fin 10) :=
  if c.val < 4 then match i with | 0 => {2} | 1 => {8} | _ => {9}
  else match i with | 0 => {3} | 1 => {6} | _ => {7}

def physicalPort (c : Fin 8) (g : Fin 7) (right : Bool) : Finset (Fin 10) :=
  if g.val < 4 then
    if right then
      if c.val < 4 then match g.val with
        | 0 => {1, 4, 5} | 1 => {6} | 2 => {3} | _ => {7}
      else match g.val with
        | 0 => {1, 4, 5} | 1 => {2} | 2 => {9} | _ => {8}
    else match g.val with | 0 => {0} | 1 => {1} | 2 => {4} | _ => {5}
  else if layout c = 0 then
    if right then leafSupport c (g.val - 4) else ∅
  else if g.val = 4 then leafSupport c (if right then pairRight c else pairLeft c)
  else if g.val = 5 then (if right then leafSupport c (remaining c) else ∅)
  else ∅

def dirtyLeft (c : Fin 8) : Finset (Fin 10) :=
  if c.val < 4 then {1, 3, 4, 5, 6, 7} else {1, 2, 4, 5, 8, 9}

def dirtyRight (c : Fin 8) : Finset (Fin 10) :=
  if c.val < 4 then {2, 8, 9} else {3, 6, 7}

end S50Geometry


namespace S50Geometry

open OnceGeometry S50Resource

def locations (c : Fin 8) (g : Fin 7) (b : Bool) : Finset (Fin 7) :=
  Finset.univ.filter (fun i => i.val ∈ portLocs c g.val b)

lemma port_class : ∀ (c : Fin 8) (g : Fin 7) (b : Bool) (v : Fin 10),
    v ∈ physicalPort c g b → vertexClass v ∈ locations c g b := by decide

lemma support_class {c : Fin 8} {S : Finset (Fin 10)} {g : Fin 7} {b : Bool}
    (hS : S ⊆ physicalPort c g b) {v : Fin 10} (hv : v ∈ S) :
    vertexClass v ∈ locations c g b := port_class c g b v (hS hv)

lemma portLocs_active : ∀ (c : Fin 8) (g : Fin 7) (b : Bool),
    portLocs c g.val b ≠ [] → active c g.val = true := by decide

lemma portLocs_bound (c : Fin 8) (g : Fin 7) (b : Bool) {loc : ℕ}
    (h : loc ∈ portLocs c g.val b) : loc < 7 := by
  fin_cases c <;> fin_cases g <;> cases b <;>
    simp_all [portLocs, layout, leafLoc, pairLeft, pairRight, remaining] <;> omega

lemma port_locations_live {c : Fin 8} {used : ℕ} {g : Fin 7}
    (hg : used.testBit g.val = false) (b : Bool) {loc : Fin 7}
    (hl : loc ∈ locations c g b) : live c used loc.val = true := by
  have hm : loc.val ∈ portLocs c g.val b := by simpa [locations] using hl
  have ha := portLocs_active c g b (fun he => by simp [he] at hm)
  apply List.any_eq_true.mpr
  refine ⟨g.val, List.mem_range.mpr g.isLt, ?_⟩
  cases b <;> simp [ha, hg, hm]

lemma raw_port : ∀ (c : Fin 8) (g : Fin 7) (b : Bool),
    rawMask (physicalPort c g b) = base c g.val b := by decide

lemma base_lt : ∀ (c : Fin 8) (g : Fin 7) (b : Bool), base c g.val b < 64 := by decide

end S50Geometry

namespace S50Resource

lemma prune_getD_of_live {c : Fin 8} {s : State} {loc : ℕ}
    (hloc : loc < 7) (hlive : live c s.1 loc = true) :
    (prune c s).2.1.getD loc 1 = s.2.1.getD loc 1 := by
  simp [prune, List.getD_eq_getElem?_getD, List.getElem?_range hloc, hlive]

lemma prune_pools_length (c : Fin 8) (s : State) : (prune c s).2.1.length = 7 := by simp [prune]

lemma prune_port_getD {c : Fin 8} {s : State} {g : Fin 7} {b : Bool} {loc : Fin 7}
    (hg : s.1.testBit g.val = false) (hl : loc ∈ S50Geometry.locations c g b) :
    (prune c s).2.1.getD loc.val 1 = s.2.1.getD loc.val 1 :=
  prune_getD_of_live loc.isLt (S50Geometry.port_locations_live hg b hl)

end S50Resource


namespace S50Positive

open S50Resource OnceGeometry

abbrev Pools := OncePositive.Pools
abbrev or7 := OncePositive.or7
abbrev PoolsGood := OncePositive.PoolsGood
abbrev Witness := OncePositive.Witness
abbrev liftPool := OncePositive.liftPool
abbrev poolView := OncePositive.poolView

lemma or7_or (f h : Fin 7 → ℕ) : or7 (fun i => f i ||| h i) = or7 f ||| or7 h :=
  OncePositive.or7_or f h

lemma or7_update (f : Fin 7 → ℕ) (loc : Fin 7) (k : ℕ) :
    or7 (Function.update f loc (f loc ||| k)) = or7 f ||| k :=
  OncePositive.or7_update f loc k

lemma or7_filtered {L : Finset (Fin 7)} {f : Fin 7 → ℕ}
    (hf : ∀ i, i ∉ L → f i = 0) :
    or7 f = or7 (fun i => if i ∈ L then f i else 0) :=
  OncePositive.or7_filtered hf

def Rep (c : Fin 8) (used : ℕ) (P : Pools) (S : Finset (Fin 10)) (m : ℕ) : Prop :=
  ∀ (g : Fin 7) (b : Bool), used.testBit g.val = false → S ⊆ S50Geometry.physicalPort c g b →
    ∃ f, Witness P (S50Geometry.locations c g b) f ∧ m = rawMask S ||| or7 f

variable {c : Fin 8}

lemma rep_raw (c : Fin 8) {used : ℕ} {P : Pools} (hp : PoolsGood P) (S : Finset (Fin 10)) :
    Rep c used P S (rawMask S) := by
  intro g b _ _
  refine ⟨fun _ => 0, ?_, ?_⟩
  · exact fun i => ⟨(hp i).1, fun _ => rfl⟩
  · simp [or7, OncePositive.or7]

lemma rep_or {used : ℕ} {P : Pools} (hp : PoolsGood P)
    {S T : Finset (Fin 10)} {a b : ℕ} (ha : Rep c used P S a) (hb : Rep c used P T b) :
    Rep c used P (S ∪ T) (a ||| b) := by
  intro g side hu hST
  have hS : S ⊆ S50Geometry.physicalPort c g side := fun v hv => hST (Finset.mem_union_left _ hv)
  have hT : T ⊆ S50Geometry.physicalPort c g side := fun v hv => hST (Finset.mem_union_right _ hv)
  obtain ⟨f, hf, ha⟩ := ha g side hu hS
  obtain ⟨h, hh, hb⟩ := hb g side hu hT
  refine ⟨fun i => f i ||| h i, ?_, ?_⟩
  · intro i
    refine ⟨(hp i).2 _ (hf i).1 _ (hh i).1, ?_⟩
    intro hi
    change f i ||| h i = 0
    rw [(hf i).2 hi, (hh i).2 hi]
    rfl
  · rw [ha, hb, rawMask_union, or7_or]
    ac_rfl

lemma rep_mono {used : ℕ} {P Q : Pools} {S : Finset (Fin 10)} {m : ℕ}
    (hPQ : ∀ i x, x ∈ values (P i) → x ∈ values (Q i))
    (h : Rep c used P S m) : Rep c used Q S m := by
  intro g b hg hS
  obtain ⟨f, hf, hm⟩ := h g b hg hS
  exact ⟨f, fun i => ⟨hPQ i _ (hf i).1, (hf i).2⟩, hm⟩

lemma liftPool_mono (P : Pools) (loc : Fin 7) (k : ℕ) :
    ∀ i x, x ∈ values (P i) → x ∈ values (liftPool P loc k i) :=
  OncePositive.liftPool_mono P loc k

lemma poolsGood_lift {P : Pools} (hp : PoolsGood P) (loc : Fin 7) {k : ℕ} (hk : k < 64) :
    PoolsGood (liftPool P loc k) := OncePositive.poolsGood_lift hp loc hk

lemma rep_lift {used : ℕ} {P : Pools} {S : Finset (Fin 10)} {m k : ℕ}
    (h : Rep c used P S m) (hk : k < 64) {v : Fin 10} (hv : v ∈ S) :
    Rep c used (liftPool P (vertexClass v) k) S (m ||| k) := by
  intro g b hg hS
  have hvL := S50Geometry.support_class hS hv
  obtain ⟨f, hf, hm⟩ := h g b hg hS
  refine ⟨Function.update f (vertexClass v) (f (vertexClass v) ||| k), ?_, ?_⟩
  · intro i
    by_cases hi : i = vertexClass v
    · subst i
      constructor
      · simpa [liftPool, OncePositive.liftPool] using OnceResource.mem_addCarrier_or (hf (vertexClass v)).1 hk
      · intro hnot
        exact False.elim (hnot hvL)
    · simpa [liftPool, OncePositive.liftPool, Function.update_apply, hi] using hf i
  · rw [or7_update, hm]
    ac_rfl

lemma rep_restrict_pools {old new : ℕ} {P Q : Pools} {S : Finset (Fin 10)} {m : ℕ}
    (hgroups : ∀ g : Fin 7, new.testBit g.val = false → old.testBit g.val = false)
    (hzero : ∀ i, 0 ∈ values (Q i))
    (hpools : ∀ (g : Fin 7) (b : Bool), new.testBit g.val = false →
      ∀ i ∈ S50Geometry.locations c g b, Q i = P i)
    (h : Rep c old P S m) : Rep c new Q S m := by
  intro g b hg hS
  obtain ⟨f, hf, hm⟩ := h g b (hgroups g hg) hS
  refine ⟨f, ?_, hm⟩
  intro i
  refine ⟨?_, (hf i).2⟩
  by_cases hi : i ∈ S50Geometry.locations c g b
  · rw [hpools g b hg i hi]
    exact (hf i).1
  · rw [(hf i).2 hi]
    exact hzero i

lemma poolView_prune c (s : State) (i : Fin 7) :
    poolView (prune c s).2.1 i = if live c s.1 i.val then poolView s.2.1 i else 1 := by
  simp [poolView, OncePositive.poolView, prune, List.getD_eq_getElem?_getD]

lemma mem_values_one_iff {x : ℕ} : x ∈ values 1 ↔ x = 0 := by
  rw [show (x ∈ values 1) ↔ x < 64 ∧ (1 : ℕ).testBit x = true from OnceResource.mem_values_iff,
    Nat.testBit_one_eq_true_iff_self_eq_zero]
  constructor
  · exact And.right
  · intro h; subst x; exact ⟨by decide, rfl⟩

lemma one_pool_good :
    0 ∈ values 1 ∧ ∀ a ∈ values 1, ∀ b ∈ values 1, a ||| b ∈ values 1 := by
  constructor
  · exact mem_values_one_iff.mpr rfl
  · intro a ha b hb
    obtain rfl := mem_values_one_iff.mp ha
    obtain rfl := mem_values_one_iff.mp hb
    exact mem_values_one_iff.mpr rfl

lemma poolsGood_prune {s : State} (hp : PoolsGood (poolView s.2.1)) :
    PoolsGood (poolView (prune c s).2.1) := by
  intro i
  rw [poolView_prune]
  split
  · exact hp i
  · exact one_pool_good

lemma rep_prune {s : State} {S : Finset (Fin 10)} {m : ℕ}
    (hp : PoolsGood (poolView s.2.1)) (h : Rep c s.1 (poolView s.2.1) S m) :
    Rep c (prune c s).1 (poolView (prune c s).2.1) S m := by
  apply rep_restrict_pools (fun _ hg => hg) (fun i => (poolsGood_prune hp i).1) ?_ h
  intro g b hg i hi
  rw [poolView_prune, S50Geometry.port_locations_live hg b hi]
  rfl

lemma unused_of_or_unused {used extra i : ℕ}
    (h : (used ||| extra).testBit i = false) : used.testBit i = false := by
  rw [Nat.testBit_or] at h
  exact (Bool.or_eq_false_iff.mp h).1

lemma mark_used_lt {used : ℕ} (hu : used < 256) (g : Fin 7) :
    used ||| (1 <<< g.val) < 256 := by
  have hg : (1 <<< g.val : ℕ) < 256 := by fin_cases g <;> decide
  exact Nat.or_lt_two_pow (n := 8) hu hg

lemma rep_mark {used : ℕ} {P : Pools} {S : Finset (Fin 10)} {m : ℕ}
    (h : Rep c used P S m) (g : Fin 7) : Rep c (used ||| (1 <<< g.val)) P S m := by
  intro g' b hg hS
  exact h g' b (unused_of_or_unused hg) hS

lemma rep_mark_prune {used : ℕ} {ps : List ℕ} {S : Finset (Fin 10)} {m : ℕ}
    (hp : PoolsGood (poolView ps)) (h : Rep c used (poolView ps) S m)
    (g : Fin 7) (zs : List ℕ) :
    Rep c (used ||| (1 <<< g.val))
      (poolView (prune c (used ||| (1 <<< g.val), ps, zs)).2.1) S m := by
  exact rep_prune (c := c) (s := (used ||| (1 <<< g.val), ps, zs)) hp (rep_mark h g)

lemma poolView_set {ps : List ℕ} (hlen : ps.length = 7) (loc : Fin 7) (k : ℕ) :
    poolView (ps.set loc.val (addCarrier (ps.getD loc.val 1) k)) =
      liftPool (poolView ps) loc k := by
  funext i
  by_cases hi : i = loc
  · subst i
    have hb : loc.val < ps.length := by simpa only [hlen] using loc.isLt
    simp [poolView, OncePositive.poolView, liftPool, OncePositive.liftPool,
      List.getD_eq_getElem?_getD, List.getElem?_set_self hb]
    rfl
  · have hne : loc.val ≠ i.val := fun h => hi (Fin.ext h.symm)
    simp [poolView, OncePositive.poolView, liftPool, OncePositive.liftPool, hi,
      List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma poolsGood_set {ps : List ℕ} (hlen : ps.length = 7)
    (hp : PoolsGood (poolView ps)) (loc : Fin 7) {k : ℕ} (hk : k < 64) :
    PoolsGood (poolView (ps.set loc.val (addCarrier (ps.getD loc.val 1) k))) := by
  rw [poolView_set hlen]
  exact poolsGood_lift hp loc hk

lemma poolView_replicate_one : poolView (List.replicate 7 1) = fun _ => 1 := by
  funext i
  fin_cases i <;> rfl

lemma poolsGood_replicate_one : PoolsGood (poolView (List.replicate 7 1)) := by
  rw [poolView_replicate_one]
  exact fun _ => one_pool_good


lemma merge_mem {p q a b : ℕ} (ha : a ∈ values p) (hb : b ∈ values q) :
    a ||| b ∈ values (mergePools p q) := OncePositive.merge_mem ha hb

lemma fold_source_mem (ps : List ℕ) (locs : List ℕ) (f : ℕ → ℕ)
    {pool raw : ℕ} (hraw : raw ∈ values pool)
    (hf : ∀ i ∈ locs, f i ∈ values (ps.getD i 1)) :
    locs.foldl (fun acc i => acc ||| f i) raw ∈
      values (locs.foldl (fun acc i => mergePools acc (ps.getD i 1)) pool) := by
  induction locs generalizing pool raw with
  | nil => exact hraw
  | cons i locs ih =>
    simp only [List.foldl_cons]
    apply ih (merge_mem hraw (hf i (by simp)))
    intro j hj
    exact hf j (by simp [hj])

lemma sourcePool_mem (ps : List ℕ) (locs : List ℕ) (f : ℕ → ℕ)
    {raw : ℕ} (hraw : raw < 64)
    (hf : ∀ i ∈ locs, f i ∈ values (ps.getD i 1)) :
    locs.foldl (fun acc i => acc ||| f i) raw ∈ values (sourcePool ps raw locs) :=
  fold_source_mem ps locs f (OnceResource.mem_singleton hraw) hf

def evalAt (f : Fin 7 → ℕ) (i : ℕ) : ℕ := if h : i < 7 then f ⟨i, h⟩ else 0

lemma source_value (c : Fin 8) (g : Fin 7) (b : Bool) (r : ℕ) (f : Fin 7 → ℕ) :
    (portLocs c g.val b).foldl (fun acc i => acc ||| evalAt f i) r =
      r ||| or7 (fun i => if i ∈ S50Geometry.locations c g b then f i else 0) := by
  fin_cases c <;> fin_cases g <;> cases b <;>
    simp [portLocs, layout, leafLoc, pairLeft, pairRight, remaining,
      evalAt, S50Geometry.locations, or7, OncePositive.or7, Nat.or_assoc, Nat.or_comm, Nat.or_left_comm]

lemma sidePool_membership (c : Fin 8) (ps : List ℕ) (g : Fin 7) (b : Bool) (f : Fin 7 → ℕ)
    (hf : ∀ i, f i ∈ values (poolView ps i)) :
    rawMask (S50Geometry.physicalPort c g b) |||
      or7 (fun i => if i ∈ S50Geometry.locations c g b then f i else 0) ∈
      values (sidePool c ps g.val b) := by
  have hm := sourcePool_mem ps (portLocs c g.val b) (evalAt f)
    (S50Geometry.base_lt c g b) (fun i hi => ?_)
  · rw [source_value] at hm
    simpa only [sidePool, S50Geometry.raw_port] using hm
  · have hib := S50Geometry.portLocs_bound c g b hi
    simpa [evalAt, hib, poolView, OncePositive.poolView] using hf ⟨i, hib⟩

lemma rep_port_mem {used : ℕ} {ps : List ℕ} {g : Fin 7} {b : Bool} {m : ℕ}
    (h : Rep c used (poolView ps) (S50Geometry.physicalPort c g b) m)
    (hu : used.testBit g.val = false) : m ∈ values (sidePool c ps g.val b) := by
  obtain ⟨f, hf, hm⟩ := h g b hu (Finset.Subset.refl _)
  rw [hm, or7_filtered (fun i => (hf i).2)]
  exact sidePool_membership c ps g b f (fun i => (hf i).1)

lemma group_candidate {used : ℕ} {ps : List ℕ} {g : Fin 7} {a b : ℕ}
    (ha : Rep c used (poolView ps) (S50Geometry.physicalPort c g false) a)
    (hb : Rep c used (poolView ps) (S50Geometry.physicalPort c g true) b)
    (hu : used.testBit g.val = false) (hab : a &&& b < 64) :
    a &&& b ∈ values (pairMasks (· &&& ·) (sidePool c ps g.val false) (sidePool c ps g.val true)) :=
  OnceResource.mem_pairMasks (rep_port_mem ha hu) (rep_port_mem hb hu) hab

lemma filter_candidate {used : ℕ} {ps : List ℕ} {g : Fin 7} {m : ℕ}
    (h : Rep c used (poolView ps) (S50Geometry.physicalPort c g true) m)
    (hu : used.testBit g.val = false) : m ∈ values (sidePool c ps g.val true) :=
  rep_port_mem h hu

end S50Positive


namespace S50Resource

lemma sortedInsert_perm (k : ℕ) (xs : List ℕ) :
    List.Perm (sortedInsert k xs) (k :: xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
      simp only [sortedInsert]
      split
      · exact List.Perm.refl _
      · exact (List.Perm.cons x ih).trans (List.Perm.swap _ _ _)

lemma zeroSort_perm (xs : List ℕ) : List.Perm (zeroSort xs) xs := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
      exact (sortedInsert_perm x (zeroSort xs)).trans (List.Perm.cons x ih)

lemma insertZero_perm (k : ℕ) (xs : List ℕ) :
    List.Perm (insertZero k xs) (k :: xs) :=
  zeroSort_perm (k :: xs)

lemma mem_sortedInsert (a k : ℕ) (xs : List ℕ) :
    a ∈ sortedInsert k xs ↔ a = k ∨ a ∈ xs := by
  rw [(sortedInsert_perm k xs).mem_iff, List.mem_cons]

lemma mem_zeroSort (a : ℕ) (xs : List ℕ) :
    a ∈ zeroSort xs ↔ a ∈ xs :=
  (zeroSort_perm xs).mem_iff

lemma mem_insertZero (a k : ℕ) (xs : List ℕ) :
    a ∈ insertZero k xs ↔ a = k ∨ a ∈ xs := by
  rw [(insertZero_perm k xs).mem_iff, List.mem_cons]

lemma sortedInsert_length (k : ℕ) (xs : List ℕ) :
    (sortedInsert k xs).length = xs.length + 1 := by
  simpa only [List.length_cons] using (sortedInsert_perm k xs).length_eq

lemma zeroSort_length (xs : List ℕ) : (zeroSort xs).length = xs.length :=
  (zeroSort_perm xs).length_eq

lemma insertZero_length (k : ℕ) (xs : List ℕ) :
    (insertZero k xs).length = xs.length + 1 := by
  simpa only [List.length_cons] using (insertZero_perm k xs).length_eq

variable {c : Fin 8}

lemma prune_used (s : State) : (prune c s).1 = s.1 := rfl

lemma prune_zeros (s : State) : (prune c s).2.2 = s.2.2 := rfl

lemma prune_pool_getD (s : State) (i : ℕ) (hi : i < 7) :
    (prune c s).2.1.getD i 1 = if live c s.1 i then s.2.1.getD i 1 else 1 := by
  change ((List.range 7).map (fun j =>
    if live c s.1 j then s.2.1.getD j 1 else 1)).getD i 1 = _
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]

lemma prune_idempotent (s : State) : prune c (prune c s) = prune c s := by
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  change (List.range 7).map (fun i =>
    if live c s.1 i then (prune c s).2.1.getD i 1 else 1) =
      (List.range 7).map (fun i => if live c s.1 i then s.2.1.getD i 1 else 1)
  apply List.map_congr_left
  intro i hi
  rw [prune_pool_getD s i (List.mem_range.mp hi)]
  split <;> rfl

lemma prune_pools_congr (s t : State) (hused : s.1 = t.1)
    (hpools : s.2.1 = t.2.1) : (prune c s).2.1 = (prune c t).2.1 := by
  change (List.range 7).map (fun i => if live c s.1 i then s.2.1.getD i 1 else 1) =
    (List.range 7).map (fun i => if live c t.1 i then t.2.1.getD i 1 else 1)
  rw [hused, hpools]

variable {c : Fin 8}

lemma filterNext_mem_successors {s t : State} (h : t ∈ filterNext c s) :
    t ∈ successors c s := by
  simp only [successors, List.mem_append, h, true_or, or_true]

lemma groupNext_mem_successors {s t : State} (h : t ∈ groupNext c s) :
    t ∈ successors c s := by
  simp only [successors, List.mem_append, h, true_or]

lemma liftNext_mem_successors {s t : State} (h : t ∈ liftNext c s) :
    t ∈ successors c s := by
  simp only [successors, List.mem_append, h, true_or, or_true]

lemma discardNext_mem_successors {s t : State} (h : t ∈ discardNext c s) :
    t ∈ successors c s := by
  simp only [successors, List.mem_append, h, true_or, or_true]

lemma combineNext_mem_successors {s t : State} (h : t ∈ combineNext c s) :
    t ∈ successors c s := by
  simp only [successors, List.mem_append, h, or_true]

lemma group_successor {s : State} {g k : Nat}
    (hg : g < 7) (hactive : active c g = true) (hfilter : isFilter c g = false)
    (hunused : s.1.testBit g = false)
    (hk : k ∈ values (pairMasks (· &&& ·) (sidePool c s.2.1 g false) (sidePool c s.2.1 g true)))
    (hkn : k ≠ 0) :
    prune c (s.1 ||| (1 <<< g), s.2.1, insertZero k s.2.2) ∈ successors c s := by
  apply groupNext_mem_successors
  apply List.mem_flatMap.mpr
  refine ⟨g, List.mem_range.mpr hg, ?_⟩
  simp only [hactive, hfilter, hunused, Bool.not_false, Bool.true_and, ↓reduceIte]
  apply List.mem_filterMap.mpr
  exact ⟨k, hk, by simp [hkn]⟩

lemma filter_successor {s : State} {g k carrier : Nat}
    (hg : g < 7) (hactive : active c g = true) (hfilter : isFilter c g = true)
    (hunused : s.1.testBit g = false) (hk : k ∈ s.2.2)
    (hc : carrier ∈ values (sidePool c s.2.1 g true))
    (hresult : k &&& carrier ≠ 0) :
    prune c (s.1 ||| (1 <<< g), s.2.1, insertZero (k &&& carrier) (s.2.2.erase k)) ∈
      successors c s := by
  apply filterNext_mem_successors
  apply List.mem_flatMap.mpr
  refine ⟨g, List.mem_range.mpr hg, ?_⟩
  simp only [hactive, hfilter, hunused, Bool.not_false, Bool.true_and, ↓reduceIte]
  apply List.mem_flatMap.mpr
  refine ⟨k, hk, ?_⟩
  apply List.mem_filterMap.mpr
  exact ⟨carrier, hc, by simp [hresult]⟩

lemma lift_successor {s : State} {k loc : ℕ}
    (hk : k ∈ s.2.2) (hloc : loc < 7) (hlive : live c s.1 loc = true)
    (hchange : addCarrier (s.2.1.getD loc 1) k ≠ s.2.1.getD loc 1) :
    prune c (s.1, s.2.1.set loc (addCarrier (s.2.1.getD loc 1) k),
      s.2.2.erase k) ∈ successors c s := by
  apply liftNext_mem_successors
  apply List.mem_flatMap.mpr
  refine ⟨k, hk, ?_⟩
  apply List.mem_filterMap.mpr
  exact ⟨loc, List.mem_range.mpr hloc, by simp only [hlive, hchange, ↓reduceIte]⟩

lemma discard_successor {s : State} {k : ℕ} (hk : k ∈ s.2.2) :
    prune c (s.1, s.2.1, s.2.2.erase k) ∈ successors c s := by
  apply discardNext_mem_successors
  exact List.mem_map.mpr ⟨k, hk, rfl⟩

lemma combine_successor {s : State} {a b k : ℕ}
    (ha : a ∈ s.2.2) (hb : b ∈ s.2.2.erase a)
    (hk : k = a &&& b ∨ k = a ||| b) (hkn : k ≠ 0) :
    prune c (s.1, s.2.1, insertZero k ((s.2.2.erase a).erase b)) ∈ successors c s := by
  apply combineNext_mem_successors
  apply List.mem_flatMap.mpr
  refine ⟨a, ha, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨b, hb, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨k, ?_, by simp [hkn]⟩
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using hk

lemma reachable_of_eq_or_successor {s t : State}
    (h : t = s ∨ t ∈ successors c s) :
    Relation.ReflTransGen (fun a b : State => b ∈ successors c a) s t := by
  rcases h with rfl | h
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single h

namespace ZeroTransitions

variable {c : Fin 8}

def token (k : ℕ) : Multiset ℕ := if k = 0 then 0 else {k}

lemma mem_of_zero_eq {zs : List ℕ} {a : ℕ} {rest : Multiset ℕ}
    (hz : (zs : Multiset ℕ) = {a} + rest) : a ∈ zs := by
  change a ∈ (zs : Multiset ℕ)
  rw [hz]
  simp

lemma erase_of_zero_eq {zs : List ℕ} {a : ℕ} {rest : Multiset ℕ}
    (hz : (zs : Multiset ℕ) = {a} + rest) :
    (zs.erase a : Multiset ℕ) = rest := by
  change (zs : Multiset ℕ).erase a = rest
  rw [hz]
  simp

lemma coe_insertZero (k : ℕ) (zs : List ℕ) :
    (insertZero k zs : Multiset ℕ) = {k} + (zs : Multiset ℕ) := by
  change (insertZero k zs : Multiset ℕ) = ((k :: zs : List ℕ) : Multiset ℕ)
  exact Quot.sound (insertZero_perm k zs)

lemma discard_one {s : State} {a : ℕ} {rest : Multiset ℕ}
    (hz : (s.2.2 : Multiset ℕ) = {a} + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors c p) s t ∧
      (t.2.2 : Multiset ℕ) = rest ∧ t.1 = s.1 ∧
      t.2.1 = (prune c s).2.1 := by
  refine ⟨prune c (s.1, s.2.1, s.2.2.erase a),
    Relation.ReflTransGen.single (discard_successor (mem_of_zero_eq hz)),
    erase_of_zero_eq hz, rfl, rfl⟩

lemma discard_two {s : State} {a b : ℕ} {rest : Multiset ℕ}
    (hz : (s.2.2 : Multiset ℕ) = {a} + {b} + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors c p) s t ∧
      (t.2.2 : Multiset ℕ) = rest ∧ t.1 = s.1 ∧
      t.2.1 = (prune c s).2.1 := by
  have hz' : (s.2.2 : Multiset ℕ) = {a} + ({b} + rest) := by
    simpa only [Multiset.add_assoc] using hz
  have ha := mem_of_zero_eq hz'
  have hz1 := erase_of_zero_eq hz'
  have hb := mem_of_zero_eq hz1
  have hz2 := erase_of_zero_eq hz1
  let t1 : State := prune c (s.1, s.2.1, s.2.2.erase a)
  let t2 : State := prune c (s.1, s.2.1, (s.2.2.erase a).erase b)
  have h1 : t1 ∈ successors c s := discard_successor ha
  have h2 : t2 ∈ successors c t1 := by
    have hh := discard_successor (c := c) (s := t1) (k := b) hb
    change prune c (prune c (s.1, s.2.1, (s.2.2.erase a).erase b)) ∈
      successors c t1 at hh
    rw [prune_idempotent] at hh
    exact hh
  exact ⟨t2, (Relation.ReflTransGen.single h1).trans (Relation.ReflTransGen.single h2),
    hz2, rfl, rfl⟩

lemma combine_nonzero {s : State} {a b k : ℕ} {rest : Multiset ℕ}
    (hz : (s.2.2 : Multiset ℕ) = {a} + {b} + rest)
    (hop : k = a &&& b ∨ k = a ||| b) (hk : k ≠ 0) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors c p) s t ∧
      (t.2.2 : Multiset ℕ) = {k} + rest ∧ t.1 = s.1 ∧
      t.2.1 = (prune c s).2.1 := by
  have hz' : (s.2.2 : Multiset ℕ) = {a} + ({b} + rest) := by
    simpa only [Multiset.add_assoc] using hz
  have ha := mem_of_zero_eq hz'
  have hz1 := erase_of_zero_eq hz'
  have hb := mem_of_zero_eq hz1
  have hz2 := erase_of_zero_eq hz1
  refine ⟨prune c (s.1, s.2.1, insertZero k ((s.2.2.erase a).erase b)),
    Relation.ReflTransGen.single (combine_successor ha hb hop hk), ?_, rfl, rfl⟩
  change (insertZero k ((s.2.2.erase a).erase b) : Multiset ℕ) = {k} + rest
  rw [coe_insertZero, hz2]

lemma zero_binary {s : State} (a b : ℕ) (isAnd : Bool) (rest : Multiset ℕ)
    (hz : (s.2.2 : Multiset ℕ) = token a + token b + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors c p) s t ∧
      (t.2.2 : Multiset ℕ) = token (if isAnd then a &&& b else a ||| b) + rest ∧
      t.1 = s.1 ∧
      (t.2.1 = s.2.1 ∨ t.2.1 = (prune c s).2.1) := by
  by_cases ha : a = 0
  · subst a
    cases isAnd
    · refine ⟨s, Relation.ReflTransGen.refl, ?_, rfl, Or.inl rfl⟩
      simpa [token] using hz
    · by_cases hb : b = 0
      · subst b
        refine ⟨s, Relation.ReflTransGen.refl, ?_, rfl, Or.inl rfl⟩
        simpa [token] using hz
      · have hz' : (s.2.2 : Multiset ℕ) = {b} + rest := by simpa [token, hb] using hz
        obtain ⟨t, hr, ht, hu, hp⟩ := discard_one (c := c) hz'
        exact ⟨t, hr, by simpa [token] using ht, hu, Or.inr hp⟩
  · by_cases hb : b = 0
    · subst b
      cases isAnd
      · refine ⟨s, Relation.ReflTransGen.refl, ?_, rfl, Or.inl rfl⟩
        simpa [token] using hz
      · have hz' : (s.2.2 : Multiset ℕ) = {a} + rest := by simpa [token, ha] using hz
        obtain ⟨t, hr, ht, hu, hp⟩ := discard_one (c := c) hz'
        exact ⟨t, hr, by simpa [token] using ht, hu, Or.inr hp⟩
    · have hz' : (s.2.2 : Multiset ℕ) = {a} + {b} + rest := by
        simpa [token, ha, hb] using hz
      let k := if isAnd then a &&& b else a ||| b
      by_cases hk : k = 0
      · obtain ⟨t, hr, ht, hu, hp⟩ := discard_two (c := c) hz'
        refine ⟨t, hr, ?_, hu, Or.inr hp⟩
        change (t.2.2 : Multiset ℕ) = token k + rest
        rw [hk]
        simpa [token] using ht
      · have hop : k = a &&& b ∨ k = a ||| b := by cases isAnd <;> simp [k]
        obtain ⟨t, hr, ht, hu, hp⟩ := combine_nonzero (c := c) hz' hop hk
        refine ⟨t, hr, ?_, hu, Or.inr hp⟩
        change (t.2.2 : Multiset ℕ) = token k + rest
        simpa [token, hk] using ht

end ZeroTransitions

end S50Resource


namespace S50Resource

variable {c : Fin 8}

lemma set_getD_self (xs : List ℕ) (i d : ℕ) : xs.set i (xs.getD i d) = xs := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact congrArg (List.cons x) (ih i)

lemma lift_successor_or_discard {s : State} {k loc : ℕ}
    (hk : k ∈ s.2.2) (hloc : loc < 7) (hlive : live c s.1 loc = true) :
    prune c (s.1, s.2.1.set loc (addCarrier (s.2.1.getD loc 1) k), s.2.2.erase k) ∈ successors c s := by
  by_cases hchange : addCarrier (s.2.1.getD loc 1) k = s.2.1.getD loc 1
  · rw [hchange, set_getD_self]
    exact discard_successor hk
  · exact lift_successor hk hloc hlive hchange

lemma lift_step_reachable {s : State} {k loc : ℕ}
    (hk : k ∈ s.2.2) (hloc : loc < 7) (hlive : live c s.1 loc = true) :
    Relation.ReflTransGen (fun a b : State => b ∈ successors c a) s
      (prune c (s.1, s.2.1.set loc (addCarrier (s.2.1.getD loc 1) k), s.2.2.erase k)) :=
  Relation.ReflTransGen.single (lift_successor_or_discard hk hloc hlive)

end S50Resource

namespace S50Positive

open S50Resource OnceGeometry

variable {c : Fin 8}

lemma rep_of_dead_class {used : ℕ} {P : Pools} {S : Finset (Fin 10)} {v : Fin 10}
    (hv : v ∈ S) (hd : live c used (vertexClass v).val = false) (m : ℕ) :
    Rep c used P S m := by
  intro g b hg hS
  have hl := S50Geometry.port_locations_live hg b (S50Geometry.support_class hS hv)
  simp [hd] at hl

lemma positive_lift_step {s : State} {S : Finset (Fin 10)} {m k : ℕ}
    (hlen : s.2.1.length = 7) (hp : PoolsGood (poolView s.2.1))
    (h : Rep c s.1 (poolView s.2.1) S m) (hs : S.Nonempty)
    (hk : k < 64) (hmem : k ∈ s.2.2) :
    ∃ t : State,
      Relation.ReflTransGen (fun a b : State => b ∈ successors c a) s t ∧
      t.1 = s.1 ∧ t.2.2 = s.2.2.erase k ∧
      t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep c s.1 (poolView s.2.1) T n → Rep c t.1 (poolView t.2.1) T n) ∧
      Rep c t.1 (poolView t.2.1) S (m ||| k) := by
  obtain ⟨v, hv⟩ := hs
  by_cases hl : live c s.1 (vertexClass v).val = true
  · let q : State := (s.1,
        s.2.1.set (vertexClass v).val (addCarrier (s.2.1.getD (vertexClass v).val 1) k),
        s.2.2.erase k)
    have hqgood : PoolsGood (poolView q.2.1) := poolsGood_set hlen hp (vertexClass v) hk
    refine ⟨prune c q, lift_step_reachable hmem (vertexClass v).isLt hl, rfl, rfl,
      prune_pools_length c q, poolsGood_prune hqgood, ?_, ?_⟩
    · intro T n hT
      apply rep_prune (c := c) (s := q) hqgood
      change Rep c s.1 (poolView (s.2.1.set (vertexClass v).val
        (addCarrier (s.2.1.getD (vertexClass v).val 1) k))) T n
      rw [poolView_set hlen]
      exact rep_mono (liftPool_mono _ _ _) hT
    · apply rep_prune (c := c) (s := q) hqgood
      change Rep c s.1 (poolView (s.2.1.set (vertexClass v).val
        (addCarrier (s.2.1.getD (vertexClass v).val 1) k))) S (m ||| k)
      rw [poolView_set hlen]
      exact rep_lift h hk hv
  · have hd : live c s.1 (vertexClass v).val = false := Bool.eq_false_of_not_eq_true hl
    let q : State := (s.1, s.2.1, s.2.2.erase k)
    refine ⟨prune c q, Relation.ReflTransGen.single (discard_successor hmem), rfl, rfl,
      prune_pools_length c q, poolsGood_prune hp, ?_, ?_⟩
    · intro T n hT
      exact rep_prune (c := c) (s := q) hp hT
    · exact rep_of_dead_class hv hd _

lemma positive_group_step {s : State} {g : Fin 7} {a b : ℕ}
    (hu : s.1 < 256) (hp : PoolsGood (poolView s.2.1))
    (hactive : active c g.val = true) (hfilter : isFilter c g.val = false)
    (ha : Rep c s.1 (poolView s.2.1) (S50Geometry.physicalPort c g false) a)
    (hb : Rep c s.1 (poolView s.2.1) (S50Geometry.physicalPort c g true) b)
    (hg : s.1.testBit g.val = false) (hab : a &&& b < 64) (hne : a &&& b ≠ 0) :
    let t := prune c (s.1 ||| (1 <<< g.val), s.2.1, insertZero (a &&& b) s.2.2)
    t ∈ successors c s ∧ t.1 < 256 ∧ t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep c s.1 (poolView s.2.1) T n → Rep c t.1 (poolView t.2.1) T n) := by
  dsimp only
  have hc := group_candidate ha hb hg hab
  refine ⟨group_successor g.isLt hactive hfilter hg hc hne, mark_used_lt hu g,
    prune_pools_length c _, poolsGood_prune hp, ?_⟩
  intro T n hT
  exact rep_mark_prune hp hT g _

lemma positive_filter_step {s : State} {g : Fin 7} {k carrier : ℕ}
    (hu : s.1 < 256) (hp : PoolsGood (poolView s.2.1))
    (hactive : active c g.val = true) (hfilter : isFilter c g.val = true)
    (hmem : k ∈ s.2.2)
    (hcarrier : Rep c s.1 (poolView s.2.1) (S50Geometry.physicalPort c g true) carrier)
    (hg : s.1.testBit g.val = false) (hne : k &&& carrier ≠ 0) :
    let t := prune c (s.1 ||| (1 <<< g.val), s.2.1, insertZero (k &&& carrier) (s.2.2.erase k))
    t ∈ successors c s ∧ t.1 < 256 ∧ t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep c s.1 (poolView s.2.1) T n → Rep c t.1 (poolView t.2.1) T n) := by
  dsimp only
  have hc := filter_candidate hcarrier hg
  refine ⟨filter_successor g.isLt hactive hfilter hg hmem hc hne, mark_used_lt hu g,
    prune_pools_length c _, poolsGood_prune hp, ?_⟩
  intro T n hT
  exact rep_mark_prune hp hT g _

end S50Positive


namespace S50Geometry

open S50Resource

lemma physical_right_nonempty : ∀ (c : Fin 8) (g : Fin 7),
    active c g.val = true → (physicalPort c g true).Nonempty := by decide

lemma physical_left_nonempty : ∀ (c : Fin 8) (g : Fin 7),
    active c g.val = true → isFilter c g.val = false →
      (physicalPort c g false).Nonempty := by decide

lemma filter_left_empty : ∀ (c : Fin 8) (g : Fin 7),
    isFilter c g.val = true → physicalPort c g false = ∅ := by decide

lemma physical_disjoint : ∀ (c : Fin 8) (g : Fin 7),
    physicalPort c g false ∩ physicalPort c g true = ∅ := by decide

end S50Geometry


namespace S50Simulation

open S50Resource S50Positive
open OnceResource.IndexCopies OnceResource.TokenMap

abbrev Reach (c : Fin 8) (s t : State) : Prop :=
  Relation.ReflTransGen (fun a b : State => b ∈ successors c a) s t

def contrib (S : Finset (Fin 10)) (m : ℕ) : Multiset ℕ :=
  if S = ∅ then OnceResource.TokenMap.token m else 0

def Healthy (s : State) : Prop :=
  s.1 < 256 ∧ s.2.1.length = 7 ∧ OncePositive.PoolsGood (OncePositive.poolView s.2.1)

def Preserves (c : Fin 8) (s t : State) : Prop :=
  ∀ T m, S50Positive.Rep c s.1 (OncePositive.poolView s.2.1) T m →
    S50Positive.Rep c t.1 (OncePositive.poolView t.2.1) T m

def LocalResult (c : Fin 8) (s q : State) (S : Finset (Fin 10)) (m : ℕ)
    (rest : Multiset ℕ) (group : Option (Fin 7)) : Prop :=
  Reach c s q ∧ Healthy q ∧ (q.2.2 : Multiset ℕ) = contrib S m + rest ∧
  Preserves c s q ∧ (S.Nonempty → Rep c q.1 (OncePositive.poolView q.2.1) S m) ∧
  (∀ g : Fin 7, q.1.testBit g.val = true → s.1.testBit g.val = true ∨ group = some g)

def ProgramCallback (c : Fin 8) (S : ℕ → Finset (Fin 10)) (M A B : ℕ → ℕ)
    (G : ℕ → Option (Fin 7)) (start n : ℕ) : Prop :=
  ∀ t < n, ∀ (s : State) (rest : Multiset ℕ), Healthy s →
    ((S (A (start + t))).Nonempty →
      Rep c s.1 (OncePositive.poolView s.2.1) (S (A (start + t))) (M (A (start + t)))) →
    ((S (B (start + t))).Nonempty →
      Rep c s.1 (OncePositive.poolView s.2.1) (S (B (start + t))) (M (B (start + t)))) →
    (s.2.2 : Multiset ℕ) = contrib (S (A (start + t))) (M (A (start + t))) +
      contrib (S (B (start + t))) (M (B (start + t))) + rest →
    (∀ g : Fin 7, G (start + t) = some g → s.1.testBit g.val = false) →
    ∃ q, LocalResult c s q (S (start + t)) (M (start + t)) rest (G (start + t))

def GroupUnique (G : ℕ → Option (Fin 7)) (start n : ℕ) : Prop :=
  ∀ i < n, ∀ j < n, ∀ g : Fin 7,
    G (start + i) = some g → G (start + j) = some g → i = j

def ProgramInv (c : Fin 8) (S : ℕ → Finset (Fin 10)) (M A B : ℕ → ℕ)
    (G : ℕ → Option (Fin 7)) (start n t : ℕ) (s : State) : Prop :=
  Healthy s ∧ (s.2.2 : Multiset ℕ) =
    project (fun w => S w = ∅) M (Available (fun w => S w = ∅) start (start+n) A B t) ∧
  (∀ w < start + t, (S w).Nonempty →
    Rep c s.1 (OncePositive.poolView s.2.1) (S w) (M w)) ∧
  ∀ g : Fin 7, s.1.testBit g.val = true → ∃ j < t, G (start + j) = some g

lemma program_inv_step {c : Fin 8} {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 7)} {start n t : ℕ} {s : State}
    (hv : Valid start A B n)
    (hcap : ∀ w, S w = ∅ → ReadCount start A B n w ≤ 1)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback c S M A B G start n)
    (ht : t < n) (hinv : ProgramInv c S M A B G start n t s) :
    ∃ q, Reach c s q ∧ ProgramInv c S M A B G start n (t+1) q := by
  obtain ⟨hhealthy, hzeros, hreps, hused⟩ := hinv
  obtain ⟨ha, hb, hab⟩ := hv t ht
  have hcap' : ∀ w, S w = ∅ → ReadCount start A B n w ≤ Capacity (start+n) w := by
    intro w hw
    apply (hcap w hw).trans
    unfold Capacity
    split_ifs <;> decide
  obtain ⟨rest, hids, _⟩ := available_step_decomp (fun w => S w = ∅) hv hcap' ht
  have hzero_input : (s.2.2 : Multiset ℕ) =
      contrib (S (A (start + t))) (M (A (start + t))) +
      contrib (S (B (start + t))) (M (B (start + t))) + project (fun w => S w = ∅) M rest := by
    rw [hzeros, hids, project_cons, project_cons]
    simp only [contrib, Multiset.add_assoc]
  have hunused : ∀ g : Fin 7, G (start + t) = some g → s.1.testBit g.val = false := by
    intro g hg
    cases hbit : s.1.testBit g.val with
    | false => rfl
    | true =>
      obtain ⟨j, hj, hjg⟩ := hused g hbit
      have heq := hgroups t ht j (by omega) g hg hjg
      omega
  obtain ⟨q, hreach, hhealth, hzero, hpres, hnew, huse⟩ :=
    hcallback t ht s (project (fun w => S w = ∅) M rest) hhealthy
      (hreps _ ha) (hreps _ hb) hzero_input hunused
  refine ⟨q, hreach, hhealth, ?_, ?_, ?_⟩
  · rw [Available, project_step (fun w => S w = ∅) M hids hab]
    have hne : start+t ≠ start+n := by omega
    simpa only [hne, and_false, ite_false, Multiset.add_zero, contrib] using hzero
  · intro w hw hSw
    by_cases hold : w < start+t
    · exact hpres _ _ (hreps w hold hSw)
    · have heq : w = start+t := by omega
      subst w
      exact hnew hSw
  · intro g hg
    rcases huse g hg with hg | hg
    · obtain ⟨j, hj, hjg⟩ := hused g hg
      exact ⟨j, by omega, hjg⟩
    · exact ⟨t, by omega, hg⟩

lemma program_induction_prefix {c : Fin 8} {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 7)} {start n : ℕ} {s₀ : State}
    (hv : Valid start A B n) (hcap : ∀ w, S w = ∅ → ReadCount start A B n w ≤ 1)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback c S M A B G start n)
    (hinit : ProgramInv c S M A B G start n 0 s₀) :
    ∀ t ≤ n, ∃ s, Reach c s₀ s ∧ ProgramInv c S M A B G start n t s := by
  intro t
  induction t with
  | zero => intro _; exact ⟨s₀, Relation.ReflTransGen.refl, hinit⟩
  | succ t ih =>
    intro ht
    obtain ⟨s, hreach, hinv⟩ := ih (by omega)
    obtain ⟨q, hstep, hiq⟩ := program_inv_step hv hcap hgroups hcallback (by omega) hinv
    exact ⟨q, hreach.trans hstep, hiq⟩

lemma program_target_excluded {c : Fin 8} {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 7)} {start n w : ℕ}
    (hsafe : ∀ s : State, Reach c initial s → 56 ∉ s.2.2)
    (hv : Valid start A B n) (hcap : ∀ u, S u = ∅ → ReadCount start A B n u ≤ 1)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback c S M A B G start n)
    (hinit : ProgramInv c S M A B G start n 0 initial)
    (hw : w ∈ Available (fun u => S u = ∅) start (start+n) A B n)
    (hSw : S w = ∅) (hMw : M w = 56) : False := by
  obtain ⟨s, hr, hi⟩ := program_induction_prefix hv hcap hgroups hcallback hinit n (Nat.le_refl n)
  have hMne : M w ≠ 0 := by omega
  have hm := project_mem (fun u => S u = ∅) M hw hSw hMne
  rw [hMw] at hm
  have ht : 56 ∈ s.2.2 := by
    change 56 ∈ (s.2.2 : Multiset ℕ)
    rw [hi.2.1]
    exact hm
  exact hsafe s hr ht

end S50Simulation


namespace S50Simulation

open S50Geometry

def ProgramSemantics (c : Fin 8) (S : ℕ → Finset (Fin 10)) (M A B : ℕ → ℕ)
    (G : ℕ → Option (Fin 7)) (Op : ℕ → Bool) (start n : ℕ) : Prop :=
  ∀ t < n,
    if Op (start + t) then
      S (start + t) = ∅ ∧ M (start + t) = M (A (start + t)) &&& M (B (start + t)) ∧
        (match G (start + t) with
        | none => S (A (start + t)) = ∅ ∧ S (B (start + t)) = ∅
        | some g =>
          S50Resource.active c g.val = true ∧ (( S (A (start + t)) = physicalPort c g false ∧ S (B (start + t)) = physicalPort c g true) ∨
          (S (A (start + t)) = physicalPort c g true ∧ S (B (start + t)) = physicalPort c g false)))
    else G (start + t) = none ∧
      S (start + t) = S (A (start + t)) ∪ S (B (start + t)) ∧
      M (start + t) = M (A (start + t)) ||| M (B (start + t))

end S50Simulation


namespace S50Simulation

open S50Resource S50Positive OnceGeometry
open OnceResource.IndexCopies OnceResource.TokenMap

lemma initial_program_inv (c : Fin 8) (S : ℕ → Finset (Fin 10)) (M A B : ℕ → ℕ)
    (G : ℕ → Option (Fin 7)) {start n seed : ℕ}
    (hseed : seed < start) (hSseed : S seed = ∅) (hMseed : M seed = 63)
    (hother : ∀ w < start, S w = ∅ → w ≠ seed → M w = 0)
    (hpositive : ∀ w < start, (S w).Nonempty → M w = rawMask (S w)) :
    ProgramInv c S M A B G start n 0 initial := by
  have hi : Healthy initial := ⟨by decide, rfl, poolsGood_replicate_one⟩
  refine ⟨hi, ?_, ?_, ?_⟩
  · have hMne : M seed ≠ 0 := by omega
    have hf : start+n ≠ seed := by omega
    have hproj := project_initial (fun w => S w = ∅) M
      (fork := start+n) hseed hSseed hMne hother
    rw [Available, hproj, hMseed]
    simp [initial, hf]
  · intro w hw hSw
    rw [hpositive w (by omega) hSw]
    exact rep_raw c hi.2.2 _
  · intro g hg
    have hn : (128 : ℕ).testBit g.val = false := by fin_cases g <;> decide
    change (128 : ℕ).testBit g.val = true at hg
    rw [hn] at hg
    contradiction

end S50Simulation


namespace OnceGeometry

open DAGBridge.DagTools

lemma before_seed_raw_of_zero_and {D : Dag} (hS : Strict 10 D) {g : ℕ}
    (hg : g ≤ D.length)
    (hzero : ∀ j, j < g → tag D j = true →
      supp 10 D (10+j) = ∅ ∧
      rawMask (supp 10 D (opA D j)) &&& rawMask (supp 10 D (opB D j)) = 0) :
    ∀ w, w < 10+g → wireMask D w = rawMask (supp 10 D w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hi : w < 10
    · exact S200Geometry.input_raw D (⟨w,hi⟩ : Fin 10)
    · let j := w - 10
      have hj : j < g := by dsimp [j]; omega
      have hjD : j < D.length := lt_of_lt_of_le hj hg
      have he : 10+j = w := by dsimp [j]; omega
      obtain ⟨ha,hb,_⟩ := hS j hjD
      have hma := ih (opA D j) (by omega) (by omega)
      have hmb := ih (opB D j) (by omega) (by omega)
      have hs := supp_gate hS j hjD
      have hm := wireMask_gate hS hjD
      have hh : wireMask D (10+j) = rawMask (supp 10 D (10+j)) := by
        rw [hm,hma,hmb]
        cases ht : tag D j with
        | false =>
          simp only [ht, Bool.false_eq_true, ite_false] at hs ⊢
          rw [hs,rawMask_union]
        | true =>
          obtain ⟨hz,hr⟩ := hzero j hj ht
          simp only [ht,ite_true,hz,rawMask_empty,hr]
      simpa only [he] using hh

lemma seed_support_lower {D : Dag} (hS : Strict 10 D) (w : ℕ) :
    rawMask (supp 10 D w) &&& wireMask D w = rawMask (supp 10 D w) := by
  unfold rawMask wireMask
  rw [← mask_and]
  congr 1
  funext r
  by_cases hh : (supp 10 D w ∩ rowSet r).Nonempty
  · simp only [decide_eq_true hh, support_row_true hS hh, Bool.and_self]
  · simp [hh]

lemma wireMask_eq_63_of_raw_eq_63 {D : Dag} (hS : Strict 10 D) {w : ℕ}
    (hraw : rawMask (supp 10 D w) = 63) : wireMask D w = 63 := by
  have hh := seed_support_lower hS w
  rw [hraw] at hh
  have hm := wireMask_lt D w
  have ht : ∀ k : Fin 64, 63 &&& k.val = k.val := by decide
  rw [ht ⟨wireMask D w,hm⟩] at hh
  exact hh

lemma dirty_seed_mask_of_raw {D : Dag} (hS : Strict 10 D) {g : ℕ}
    (hg : g < D.length) (ht : tag D g = true)
    (ha : rawMask (supp 10 D (opA D g)) = 63)
    (hb : rawMask (supp 10 D (opB D g)) = 63) : wireMask D (10+g) = 63 := by
  calc
    wireMask D (10+g) = 63 &&& 63 := by
      simp only [wireMask_gate hS hg,ht,ite_true,wireMask_eq_63_of_raw_eq_63 hS ha,
        wireMask_eq_63_of_raw_eq_63 hS hb]
    _ = 63 := by decide

end OnceGeometry


namespace S50Positive

open S50Resource OnceGeometry

variable {c : Fin 8}

lemma frame_preserves {s t : State}
    (hu : s.1 < 256) (hlen : s.2.1.length = 7) (hp : PoolsGood (poolView s.2.1))
    (ht : t.1 = s.1) (hps : t.2.1 = s.2.1 ∨ t.2.1 = (prune c s).2.1) :
    t.1 < 256 ∧ t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep c s.1 (poolView s.2.1) T n → Rep c t.1 (poolView t.2.1) T n) := by
  refine ⟨by simpa only [ht] using hu, ?_⟩
  rcases hps with he | he
  · rw [he, ht]
    exact ⟨hlen, hp, fun _ _ h => h⟩
  · rw [he, ht]
    exact ⟨prune_pools_length c s, poolsGood_prune hp, fun _ _ h => rep_prune hp h⟩

lemma zero_binary_positive_state {s : State} (a b : ℕ) (isAnd : Bool) (rest : Multiset ℕ)
    (hu : s.1 < 256) (hlen : s.2.1.length = 7) (hp : PoolsGood (poolView s.2.1))
    (hz : (s.2.2 : Multiset ℕ) =
      ZeroTransitions.token a + ZeroTransitions.token b + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors c p) s t ∧
      t.1 = s.1 ∧
      (t.2.2 : Multiset ℕ) =
        ZeroTransitions.token (if isAnd then a &&& b else a ||| b) + rest ∧
      t.1 < 256 ∧ t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep c s.1 (poolView s.2.1) T n → Rep c t.1 (poolView t.2.1) T n) := by
  obtain ⟨t, hr, hz', ht, hps⟩ := ZeroTransitions.zero_binary (c := c) a b isAnd rest hz
  exact ⟨t, hr, ht, hz', frame_preserves hu hlen hp ht hps⟩

end S50Positive

namespace S50Simulation
open S50Resource S50Geometry S50Positive

variable {c : Fin 8}

lemma lift_token_step {s : State} {S : Finset (Fin 10)} {m k : ℕ} {rest : Multiset ℕ}
    (hs : Healthy s) (hS : S.Nonempty) (hm : Rep c s.1 (poolView s.2.1) S m)
    (hk : k < 64) (hz : (s.2.2 : Multiset ℕ) = OnceResource.TokenMap.token k + rest) :
    ∃ q, LocalResult c s q S (m ||| k) rest none := by
  have hne : S ≠ ∅ := hS.ne_empty
  by_cases hk0 : k = 0
  · subst k
    refine ⟨s, Relation.ReflTransGen.refl, hs, ?_, (fun _ _ h => h), ?_, ?_⟩
    · simpa [contrib, OnceResource.TokenMap.token, hne] using hz
    · intro _
      simpa using hm
    · exact fun _ h => Or.inl h
  · have hmem : k ∈ s.2.2 := by
      have hm' : k ∈ (s.2.2 : Multiset ℕ) := by rw [hz]; simp [OnceResource.TokenMap.token, hk0]
      exact hm'
    obtain ⟨q, hr, hu, hqz, hl, hp, hpres, hrep⟩ :=
      positive_lift_step hs.2.1 hs.2.2 hm hS hk hmem
    refine ⟨q, hr, ⟨by simpa [hu] using hs.1, hl, hp⟩, ?_, hpres,
      (fun _ => hrep), ?_⟩
    · rw [hqz, ← Multiset.coe_erase, hz]
      simp [contrib, hne, OnceResource.TokenMap.token, hk0]
    · intro g hg
      exact Or.inl (hu ▸ hg)

lemma or_local {s : State} {S T : Finset (Fin 10)} {a b : ℕ} {rest : Multiset ℕ}
    (hs : Healthy s) (ha : S.Nonempty → Rep c s.1 (poolView s.2.1) S a)
    (hb : T.Nonempty → Rep c s.1 (poolView s.2.1) T b)
    (hab : a < 64 ∧ b < 64)
    (hz : (s.2.2 : Multiset ℕ) = contrib S a + contrib T b + rest) :
    ∃ q, LocalResult c s q (S ∪ T) (a ||| b) rest none := by
  by_cases hS : S = ∅
  · subst S
    by_cases hT : T = ∅
    · subst T
      have hz' : (s.2.2 : Multiset ℕ) =
          ZeroTransitions.token a + ZeroTransitions.token b + rest := by
        simpa [contrib, ZeroTransitions.token, OnceResource.TokenMap.token] using hz
      obtain ⟨q, hr, hu, hqz, hqu, hql, hqp, hpres⟩ :=
        zero_binary_positive_state a b false rest hs.1 hs.2.1 hs.2.2 hz'
      refine ⟨q, hr, ⟨hqu, hql, hqp⟩, ?_, hpres, ?_, ?_⟩
      · simpa [contrib, ZeroTransitions.token, OnceResource.TokenMap.token] using hqz
      · simp
      · intro g hg
        exact Or.inl (hu ▸ hg)
    · have hTn : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
      have hz' : (s.2.2 : Multiset ℕ) = OnceResource.TokenMap.token a + rest := by
        simpa [contrib, hT] using hz
      obtain ⟨q, hq⟩ := lift_token_step hs hTn (hb hTn) hab.1 hz'
      refine ⟨q, ?_⟩
      simpa [Nat.or_comm] using hq
  · have hSn : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    by_cases hT : T = ∅
    · subst T
      have hz' : (s.2.2 : Multiset ℕ) = OnceResource.TokenMap.token b + rest := by
        simpa [contrib, hS] using hz
      obtain ⟨q, hq⟩ := lift_token_step hs hSn (ha hSn) hab.2 hz'
      exact ⟨q, by simpa using hq⟩
    · have hTn : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
      have hST : S ∪ T ≠ ∅ := (hSn.mono Finset.subset_union_left).ne_empty
      refine ⟨s, Relation.ReflTransGen.refl, hs, ?_, (fun _ _ h => h), ?_, ?_⟩
      · simpa [contrib, hS, hT, hST] using hz
      · intro _
        exact rep_or hs.2.2 (ha hSn) (hb hTn)
      · exact fun _ h => Or.inl h

lemma marked_group {used : ℕ} {g h : Fin 7}
    (ht : (used ||| (1 <<< g.val)).testBit h.val = true) :
    used.testBit h.val = true ∨ g = h := by
  rw [Nat.testBit_or, Bool.or_eq_true] at ht
  rcases ht with ht | ht
  · exact Or.inl ht
  · right
    have hsingle := OnceResource.testBit_singleton_iff.mp ht
    exact Fin.ext hsingle

lemma pure_local {s : State} {g : Fin 7} {a b : ℕ} {rest : Multiset ℕ}
    (hs : Healthy s) (hactive : active c g.val = true) (hfilter : isFilter c g.val = false)
    (ha : Rep c s.1 (poolView s.2.1) (physicalPort c g false) a)
    (hb : Rep c s.1 (poolView s.2.1) (physicalPort c g true) b)
    (hk : a &&& b < 64) (hunused : s.1.testBit g.val = false)
    (hz : (s.2.2 : Multiset ℕ) = rest) :
    ∃ q, LocalResult c s q ∅ (a &&& b) rest (some g) := by
  by_cases hk0 : a &&& b = 0
  · refine ⟨s, Relation.ReflTransGen.refl, hs, ?_, (fun _ _ h => h), ?_, ?_⟩
    · simpa [contrib, OnceResource.TokenMap.token, hk0] using hz
    · simp
    · exact fun _ h => Or.inl h
  · let q := prune c (s.1 ||| (1 <<< g.val), s.2.1, insertZero (a &&& b) s.2.2 )
    obtain ⟨hr, hu, hl, hp, hpres⟩ := positive_group_step hs.1 hs.2.2 hactive hfilter ha hb hunused hk hk0
    refine ⟨q, Relation.ReflTransGen.single hr, ⟨hu, hl, hp⟩, ?_, hpres, ?_, ?_⟩
    · change (insertZero (a &&& b) s.2.2 : Multiset ℕ) = _
      rw [ZeroTransitions.coe_insertZero, hz]
      simp [contrib, OnceResource.TokenMap.token, hk0]
    · simp
    · intro h hh
      change (s.1 ||| (1 <<< g.val)).testBit h.val = true at hh
      rcases marked_group (g := g) hh with hh | hh
      · exact Or.inl hh
      · exact Or.inr (congrArg some hh)

lemma zero_local {s : State} {a b : ℕ} {rest : Multiset ℕ}
    (hs : Healthy s)
    (hz : (s.2.2 : Multiset ℕ) = OnceResource.TokenMap.token a + OnceResource.TokenMap.token b + rest) :
    ∃ q, LocalResult c s q ∅ (a &&& b) rest none := by
  obtain ⟨q, hr, hu, hqz, hqu, hql, hqp, hpres⟩ :=
    zero_binary_positive_state a b true rest hs.1 hs.2.1 hs.2.2 hz
  refine ⟨q, hr, ⟨hqu, hql, hqp⟩, ?_, hpres, ?_, ?_⟩
  · exact hqz
  · simp
  · intro g hg
    exact Or.inl (hu ▸ hg)

end S50Simulation

namespace S50Simulation

open S50Resource S50Geometry S50Positive

lemma filter_local {c : Fin 8} {g : Fin 7} {s : State} {k carrier : ℕ} {rest : Multiset ℕ}
    (hs : Healthy s)
    (hactive : active c g.val = true) (hfilter : isFilter c g.val = true)
    (hb : Rep c s.1 (poolView s.2.1) (physicalPort c g true) carrier)
    (hunused : s.1.testBit g.val = false)
    (hz : (s.2.2 : Multiset ℕ) = OnceResource.TokenMap.token k + rest) :
    ∃ q, LocalResult c s q ∅ (k &&& carrier) rest (some g) := by
  by_cases hk : k = 0
  · subst k
    refine ⟨s, Relation.ReflTransGen.refl, hs, ?_, (fun _ _ h => h), ?_, ?_⟩
    · simpa [contrib, OnceResource.TokenMap.token] using hz
    · simp
    · exact fun _ h => Or.inl h
  · have hz' : (s.2.2 : Multiset ℕ) = {k} + rest := by
      simpa [OnceResource.TokenMap.token, hk] using hz
    by_cases hresult : k &&& carrier = 0
    · obtain ⟨q, hr, hqz, hu, hpool⟩ := ZeroTransitions.discard_one (c := c) hz'
      obtain ⟨hqu, hql, hgood, hpres⟩ :=
        frame_preserves hs.1 hs.2.1 hs.2.2 hu (Or.inr hpool)
      refine ⟨q, hr, ⟨hqu, hql, hgood⟩, ?_, hpres, ?_, ?_⟩
      · simpa [contrib, OnceResource.TokenMap.token, hresult] using hqz
      · simp
      · intro g hg
        exact Or.inl (hu ▸ hg)
    · have hmem := ZeroTransitions.mem_of_zero_eq hz'
      let q : State := prune c (s.1 ||| (1 <<< g.val), s.2.1,
        insertZero (k &&& carrier) (s.2.2.erase k))
      obtain ⟨hr, hu, hl, hp, hpres⟩ :=
        positive_filter_step hs.1 hs.2.2 hactive hfilter hmem hb hunused hresult
      refine ⟨q, Relation.ReflTransGen.single hr, ⟨hu, hl, hp⟩, ?_, hpres, ?_, ?_⟩
      · change (insertZero (k &&& carrier) (s.2.2.erase k) : Multiset ℕ) = _
        rw [ZeroTransitions.coe_insertZero, ZeroTransitions.erase_of_zero_eq hz']
        simp [contrib, OnceResource.TokenMap.token, hresult]
      · simp
      · intro h hh
        rcases marked_group (used := s.1) (g := g) (h := h) hh with hh | hh
        · exact Or.inl hh
        · exact Or.inr (congrArg some hh)

end S50Simulation

namespace S50Simulation
open S50Resource S50Geometry S50Positive

variable {c : Fin 8}

lemma gate_local {s : State} {S T U : Finset (Fin 10)} {a b z : Nat}
    {rest : Multiset Nat} (op : Bool) (group : Option (Fin 7))
    (hs : Healthy s) (ha : S.Nonempty → Rep c s.1 (poolView s.2.1) S a)
    (hb : T.Nonempty → Rep c s.1 (poolView s.2.1) T b)
    (hm : a < 64 ∧ b < 64 ∧ z < 64)
    (hz : (s.2.2 : Multiset Nat) = contrib S a + contrib T b + rest)
    (hunused : ∀ g : Fin 7, group = some g → s.1.testBit g.val = false)
    (hsem : if op then
      U = ∅ ∧ z = a &&& b ∧
        (match group with
        | none => S = ∅ ∧ T = ∅
        | some g => active c g.val = true ∧
          ((S = physicalPort c g false ∧ T = physicalPort c g true) ∨
          (S = physicalPort c g true ∧ T = physicalPort c g false)))
      else group = none ∧ U = S ∪ T ∧ z = a ||| b) :
    ∃ q, LocalResult c s q U z rest group := by
  cases op with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hsem
    obtain ⟨rfl, rfl, rfl⟩ := hsem
    exact or_local hs ha hb ⟨hm.1, hm.2.1⟩ hz
  | true =>
    simp only [↓reduceIte] at hsem
    obtain ⟨rfl, rfl, hports⟩ := hsem
    cases group with
    | none =>
      obtain ⟨rfl, rfl⟩ := hports
      exact zero_local hs (by simpa [contrib] using hz)
    | some g =>
      obtain ⟨hactive, hports⟩ := hports
      have hu := hunused g rfl
      have hr := physical_right_nonempty c g hactive
      cases hf : isFilter c g.val with
      | false =>
        have hl := physical_left_nonempty c g hactive hf
        rcases hports with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have hz' : (s.2.2 : Multiset Nat) = rest := by
            simpa [contrib, hl.ne_empty, hr.ne_empty] using hz
          exact pure_local hs hactive hf (ha hl) (hb hr) hm.2.2 hu hz'
        · have hz' : (s.2.2 : Multiset Nat) = rest := by
            simpa [contrib, hl.ne_empty, hr.ne_empty] using hz
          obtain ⟨q, hq⟩ := pure_local hs hactive hf (hb hl) (ha hr)
            (by simpa [Nat.and_comm] using hm.2.2) hu hz'
          exact ⟨q, by simpa [Nat.and_comm] using hq⟩
      | true =>
        have hl := filter_left_empty c g hf
        rcases hports with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have hz' : (s.2.2 : Multiset Nat) = OnceResource.TokenMap.token a + rest := by
            simpa [contrib, hl, hr.ne_empty] using hz
          exact filter_local hs hactive hf (hb hr) hu hz'
        · have hz' : (s.2.2 : Multiset Nat) = OnceResource.TokenMap.token b + rest := by
            simpa [contrib, hl, hr.ne_empty] using hz
          obtain ⟨q, hq⟩ := filter_local hs hactive hf (ha hr) hu hz'
          exact ⟨q, by simpa [Nat.and_comm] using hq⟩

lemma semantic_callback {S : Nat → Finset (Fin 10)} {M A B : Nat → Nat}
    {G : Nat → Option (Fin 7)} {Op : Nat → Bool} {start n : Nat}
    (hm : ∀ w, M w < 64) (hsem : ProgramSemantics c S M A B G Op start n) :
    ProgramCallback c S M A B G start n := by
  intro t ht s rest hs ha hb hz hgroups
  generalize hg : G (start + t) = group at hgroups ⊢
  cases group with
  | none =>
    exact gate_local (Op (start + t)) none hs ha hb
      ⟨hm _, hm _, hm _⟩ hz hgroups (by simpa [hg] using hsem t ht)
  | some g =>
    exact gate_local (Op (start + t)) (some g) hs ha hb
      ⟨hm _, hm _, hm _⟩ hz hgroups (by simpa [hg] using hsem t ht)

end S50Simulation


namespace S50Simulation

open S50Resource S50Positive OnceGeometry OnceActualSchedule
open DAGBridge.DagTools

def DirtySeed (D : Dag) (g : ℕ) : Prop :=
  supp 10 D (10+g) = ∅ ∧ rawMask (supp 10 D (opA D g)) = 63 ∧
    rawMask (supp 10 D (opB D g)) = 63

def BeforeSeed (D : Dag) (g : ℕ) : Prop :=
  ∀ j, j < g → tag D j = true → supp 10 D (10+j) = ∅ ∧
    rawMask (supp 10 D (opA D j)) &&& rawMask (supp 10 D (opB D j)) = 0

lemma actual_target_exclusion (c : Fin 8) {D : Dag}
    (hS : Strict 10 D) (hB : Bzero 10 D = 0)
    {g : ℕ} (hg : g < D.length) (ht : tag D g = true)
    (hdirty : DirtySeed D g) (hbefore : BeforeSeed D g)
    {G : ℕ → Option (Fin 7)}
    (hgroups : GroupUnique G (start g) (remaining D g))
    (hsem : ProgramSemantics c (supp 10 D) (wireMask D) (sourceA D) (sourceB D) G
      (fun w => tag D (w - 10)) (start g) (remaining D g)) :
    ¬ (supp 10 D (outW 10 D) = ∅ ∧ wireMask D (outW 10 D) = 56) := by
  intro hout
  have hm := dirty_seed_mask_of_raw hS hg ht hdirty.2.1 hdirty.2.2
  have hinit : ProgramInv c (supp 10 D) (wireMask D) (sourceA D) (sourceB D) G
      (start g) (remaining D g) 0 initial := by
    apply initial_program_inv c (supp 10 D) (wireMask D) (sourceA D) (sourceB D) G
      (seed := 10+g) (by unfold start; omega) hdirty.1 hm
    · intro w hw hz hne
      have he := before_seed_raw_of_zero_and hS (Nat.le_of_lt hg) hbefore w
        (by unfold start at hw; omega)
      simpa only [hz,rawMask_empty] using he
    · intro w hw hpos
      have hne : w ≠ 10+g := by intro heq; subst w; exact hpos.ne_empty hdirty.1
      apply before_seed_raw_of_zero_and hS (Nat.le_of_lt hg) hbefore
      unfold start at hw
      omega
  exact program_target_excluded (fun _ hr => reachable_no_target c hr)
    (continuation_valid hS g) (S200Budget.continuation_capacity hS hB g)
    hgroups (semantic_callback (c := c) (wireMask_lt D) hsem) hinit
    (final_output_available hS hg (start g + remaining D g)) hout.1 hout.2

end S50Simulation


namespace S50ActualLabels

noncomputable def label (active : Fin 7 → Bool) (gate : Fin 7 → ℕ) (j : ℕ) :
    Option (Fin 7) := by
  classical
  exact if h : ∃ g : Fin 7, active g = true ∧ j = gate g then
    some (Classical.choose h) else none

lemma label_some_iff {active : Fin 7 → Bool} {gate : Fin 7 → ℕ}
    (hinj : ∀ a b, active a = true → active b = true → gate a = gate b → a = b)
    (j : ℕ) (g : Fin 7) :
    label active gate j = some g ↔ active g = true ∧ j = gate g := by
  classical
  unfold label
  split_ifs with h
  · constructor
    · intro he
      have he' : Classical.choose h = g := Option.some.inj he
      exact he' ▸ Classical.choose_spec h
    · rintro ⟨ha, he⟩
      have he' : Classical.choose h = g := hinj _ _ (Classical.choose_spec h).1 ha
        ((Classical.choose_spec h).2.symm.trans he)
      rw [he']
  · constructor
    · intro he
      cases he
    · intro he
      exact False.elim (h ⟨g, he⟩)

lemma label_none_iff (active : Fin 7 → Bool) (gate : Fin 7 → ℕ) (j : ℕ) :
    label active gate j = none ↔ ∀ g : Fin 7, active g = true → j ≠ gate g := by
  classical
  unfold label
  split_ifs with h
  · constructor
    · intro he
      cases he
    · intro he
      exact False.elim (he (Classical.choose h) (Classical.choose_spec h).1
        (Classical.choose_spec h).2)
  · constructor
    · intro _ g ha he
      exact h ⟨g, ha, he⟩
    · intro _
      rfl

lemma label_unique {active : Fin 7 → Bool} {gate : Fin 7 → ℕ}
    (hinj : ∀ a b, active a = true → active b = true → gate a = gate b → a = b)
    {j k : ℕ} {g : Fin 7} (hj : label active gate j = some g)
    (hk : label active gate k = some g) : j = k :=
  ((label_some_iff hinj j g).mp hj).2.trans ((label_some_iff hinj k g).mp hk).2.symm

lemma seed_label_none {active : Fin 7 → Bool} {gate : Fin 7 → ℕ} {seed : ℕ}
    (hsep : ∀ g, active g = true → gate g ≠ seed) :
    label active gate seed = none := by
  apply (label_none_iff active gate seed).mpr
  intro g hg he
  exact hsep g hg he.symm

lemma continuation_unique {active : Fin 7 → Bool} {gate : Fin 7 → ℕ}
    (hinj : ∀ a b, active a = true → active b = true → gate a = gate b → a = b)
    (seed j k : ℕ) (g : Fin 7)
    (hj : label active gate (seed + 1 + j) = some g)
    (hk : label active gate (seed + 1 + k) = some g) : j = k := by
  have he := label_unique hinj hj hk
  omega

end S50ActualLabels

namespace S50ActualLabels

open DAGBridge.DagTools OnceGeometry

abbrev groupActive (c : Fin 8) (g : Fin 7) : Bool := S50Resource.active c g.val

def PortsAt (c : Fin 8) (D : Dag) (j : ℕ) (g : Fin 7) : Prop :=
  (supp 10 D (opA D j) = S50Geometry.physicalPort c g false ∧
   supp 10 D (opB D j) = S50Geometry.physicalPort c g true) ∨
  (supp 10 D (opA D j) = S50Geometry.physicalPort c g true ∧
   supp 10 D (opB D j) = S50Geometry.physicalPort c g false)

def Classified (c : Fin 8) (D : Dag) (seed : ℕ) (gate : Fin 7 → ℕ) : Prop :=
  ∀ j, j < D.length → tag D j = true →
    j = seed ∨ (∃ k : Fin 7, groupActive c k = true ∧ j = gate k) ∨
      (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅)

set_option maxRecDepth 4096 in
lemma port_geometry : ∀ (c : Fin 8) (g : Fin 7),
    S50Geometry.physicalPort c g false ∩ S50Geometry.physicalPort c g true = ∅ ∧
    rawMask (S50Geometry.physicalPort c g false) &&&
      rawMask (S50Geometry.physicalPort c g true) = 0 := by decide +kernel

set_option maxRecDepth 4096 in
lemma dirty_geometry : ∀ c : Fin 8,
    S50Geometry.dirtyLeft c ∩ S50Geometry.dirtyRight c = ∅ ∧
    rawMask (S50Geometry.dirtyLeft c) = 63 ∧ rawMask (S50Geometry.dirtyRight c) = 63 := by
  decide +kernel

lemma and_zero_of_ports {c : Fin 8} {D : Dag} (hS : Strict 10 D)
    {j : ℕ} (hj : j < D.length) (ht : tag D j = true) {g : Fin 7}
    (hp : PortsAt c D j g) :
    supp 10 D (10+j) = ∅ ∧
    rawMask (supp 10 D (opA D j)) &&& rawMask (supp 10 D (opB D j)) = 0 := by
  have hs := supp_gate hS j hj
  simp only [ht, ite_true] at hs
  obtain ⟨hd,hm⟩ := port_geometry c g
  rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact ⟨by simpa only [ha,hb,hd] using hs, by simpa only [ha,hb] using hm⟩
  · constructor
    · simpa only [ha,hb,Finset.inter_comm (S50Geometry.physicalPort c g true)
        (S50Geometry.physicalPort c g false),hd] using hs
    · simpa only [ha,hb,Nat.and_comm] using hm

lemma before_seed_zero {c : Fin 8} {D : Dag} (hS : Strict 10 D) {seed : ℕ}
    (hseed : seed < D.length) {gate : Fin 7 → ℕ}
    (hports : ∀ g, groupActive c g = true → PortsAt c D (gate g) g)
    (htypes : Classified c D seed gate) :
    ∀ j, j < seed → tag D j = true →
      supp 10 D (10+j) = ∅ ∧
      rawMask (supp 10 D (opA D j)) &&& rawMask (supp 10 D (opB D j)) = 0 := by
  intro j hj ht
  have hjD := lt_trans hj hseed
  rcases htypes j hjD ht with he | ⟨g,hg,he⟩ | ⟨ha,hb⟩
  · omega
  · exact and_zero_of_ports hS hjD ht (he ▸ hports g hg)
  · have hs := supp_gate hS j hjD
    simp only [ht,ite_true,ha,hb,Finset.empty_inter] at hs
    exact ⟨hs, by simp only [ha,rawMask_empty,Nat.zero_and]⟩

end S50ActualLabels

namespace S50ActualLabels

open DAGBridge.DagTools OnceGeometry

lemma label_semantics {c : Fin 8} {D : Dag} (hS : Strict 10 D) {seed : ℕ}
    {gate : Fin 7 → ℕ}
    (hinj : ∀ a b, groupActive c a = true → groupActive c b = true →
      gate a = gate b → a = b)
    (hvalid : ∀ g, groupActive c g = true → gate g < D.length ∧ tag D (gate g) = true)
    (hports : ∀ g, groupActive c g = true → PortsAt c D (gate g) g)
    (htypes : Classified c D seed gate) (j : ℕ) (hj : j < D.length) (hne : j ≠ seed) :
    if tag D j then
      supp 10 D (10+j) = ∅ ∧
      wireMask D (10+j) = wireMask D (opA D j) &&& wireMask D (opB D j) ∧
      (match label (groupActive c) gate j with
      | none => supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅
      | some g => groupActive c g = true ∧ PortsAt c D j g)
    else label (groupActive c) gate j = none ∧
      supp 10 D (10+j) = supp 10 D (opA D j) ∪ supp 10 D (opB D j) ∧
      wireMask D (10+j) = wireMask D (opA D j) ||| wireMask D (opB D j) := by
  classical
  have hm := wireMask_gate hS hj
  have hs := supp_gate hS j hj
  cases ht : tag D j with
  | false =>
    simp only [ht, Bool.false_eq_true, ↓reduceIte] at hm hs ⊢
    refine ⟨(label_none_iff (groupActive c) gate j).mpr ?_, hs, hm⟩
    intro g hg he
    have hh := (hvalid g hg).2
    rw [← he,ht] at hh
    cases hh
  | true =>
    simp only [ht, ↓reduceIte] at hm hs ⊢
    cases hl : label (groupActive c) gate j with
    | none =>
      have hz : supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅ := by
        rcases htypes j hj ht with he | ⟨g,hg,he⟩ | hz
        · exact False.elim (hne he)
        · exact False.elim ((label_none_iff (groupActive c) gate j).mp hl g hg he)
        · exact hz
      refine ⟨?_,hm,hz⟩
      simpa only [hz.1,Finset.empty_inter] using hs
    | some g =>
      obtain ⟨hg,he⟩ := (label_some_iff hinj j g).mp hl
      have hp := hports g hg
      rw [← he] at hp
      exact ⟨(and_zero_of_ports hS hj ht hp).1,hm,hg,hp⟩

open S50Simulation OnceActualSchedule

noncomputable def wireLabel (c : Fin 8) (gate : Fin 7 → ℕ) (w : ℕ) : Option (Fin 7) :=
  label (groupActive c) gate (w - 10)

lemma actual_group_unique {c : Fin 8} {D : Dag} {seed : ℕ} {gate : Fin 7 → ℕ}
    (hinj : ∀ a b, groupActive c a = true → groupActive c b = true →
      gate a = gate b → a = b) :
    GroupUnique (wireLabel c gate) (start seed) (remaining D seed) := by
  intro i hi j hj g hgi hgj
  have he := label_unique hinj hgi hgj
  change start seed + i - 10 = start seed + j - 10 at he
  unfold start at he
  omega

lemma actual_program_semantics {c : Fin 8} {D : Dag} (hS : Strict 10 D) {seed : ℕ}
    {gate : Fin 7 → ℕ}
    (hinj : ∀ a b, groupActive c a = true → groupActive c b = true →
      gate a = gate b → a = b)
    (hvalid : ∀ g, groupActive c g = true → gate g < D.length ∧ tag D (gate g) = true)
    (hports : ∀ g, groupActive c g = true → PortsAt c D (gate g) g)
    (htypes : Classified c D seed gate) :
    ProgramSemantics c (supp 10 D) (wireMask D) (sourceA D) (sourceB D)
      (wireLabel c gate) (fun w => tag D (w-10)) (start seed) (remaining D seed) := by
  intro t ht
  have hj : seed + 1 + t < D.length := by unfold remaining at ht; omega
  have hne : seed + 1 + t ≠ seed := by omega
  have hh := label_semantics hS hinj hvalid hports htypes (seed+1+t) hj hne
  simpa only [sourceA,sourceB,wireLabel,continuation_index,PortsAt,groupActive,
    show start seed + t = 10 + (seed+1+t) by unfold start; omega,
    Nat.add_sub_cancel_left] using hh

lemma dirty_seed_of_ports {c : Fin 8} {D : Dag} (hS : Strict 10 D) {seed : ℕ}
    (hg : seed < D.length) (ht : tag D seed = true)
    (hp : (supp 10 D (opA D seed) = S50Geometry.dirtyLeft c ∧
           supp 10 D (opB D seed) = S50Geometry.dirtyRight c) ∨
          (supp 10 D (opA D seed) = S50Geometry.dirtyRight c ∧
           supp 10 D (opB D seed) = S50Geometry.dirtyLeft c)) :
    supp 10 D (10+seed) = ∅ ∧ rawMask (supp 10 D (opA D seed)) = 63 ∧
      rawMask (supp 10 D (opB D seed)) = 63 := by
  obtain ⟨hd,ha,hb⟩ := dirty_geometry c
  have hs := supp_gate hS seed hg
  simp only [ht,ite_true] at hs
  rcases hp with ⟨hA,hB⟩ | ⟨hA,hB⟩
  · exact ⟨by simpa only [hA,hB,hd] using hs, by simpa only [hA] using ha,
      by simpa only [hB] using hb⟩
  · refine ⟨?_,?_,?_⟩
    · simpa only [hA,hB,Finset.inter_comm (S50Geometry.dirtyRight c)
        (S50Geometry.dirtyLeft c),hd] using hs
    · simpa only [hA] using hb
    · simpa only [hB] using ha

end S50ActualLabels

namespace S50ActualLabels

open DAGBridge.DagTools OnceGeometry S50Simulation

lemma active_gate_target_exclusion (c : Fin 8) {D : Dag} (hS : Strict 10 D)
    (hB : Bzero 10 D = 0) {seed : ℕ} (hg : seed < D.length) (ht : tag D seed = true)
    (hdirty : (supp 10 D (opA D seed) = S50Geometry.dirtyLeft c ∧
               supp 10 D (opB D seed) = S50Geometry.dirtyRight c) ∨
              (supp 10 D (opA D seed) = S50Geometry.dirtyRight c ∧
               supp 10 D (opB D seed) = S50Geometry.dirtyLeft c))
    {gate : Fin 7 → ℕ}
    (hinj : ∀ a b, groupActive c a = true → groupActive c b = true →
      gate a = gate b → a = b)
    (hvalid : ∀ g, groupActive c g = true → gate g < D.length ∧ tag D (gate g) = true)
    (hports : ∀ g, groupActive c g = true → PortsAt c D (gate g) g)
    (htypes : Classified c D seed gate) :
    ¬ (supp 10 D (outW 10 D) = ∅ ∧ wireMask D (outW 10 D) = 56) := by
  exact S50Simulation.actual_target_exclusion c hS hB hg ht
    (dirty_seed_of_ports hS hg ht hdirty) (before_seed_zero hS hg hports htypes)
    (actual_group_unique hinj) (actual_program_semantics hS hinj hvalid hports htypes)

lemma active_gate_petersen_exclusion (c : Fin 8) {D : Dag} (hS : Strict 10 D)
    (hC : S18Structural.DagTools.sem_Comp 10 S18Structural.DagTools.petersenAdj D)
    (hB : Bzero 10 D = 0) {seed : ℕ} (hg : seed < D.length) (ht : tag D seed = true)
    (hdirty : (supp 10 D (opA D seed) = S50Geometry.dirtyLeft c ∧
               supp 10 D (opB D seed) = S50Geometry.dirtyRight c) ∨
              (supp 10 D (opA D seed) = S50Geometry.dirtyRight c ∧
               supp 10 D (opB D seed) = S50Geometry.dirtyLeft c))
    {gate : Fin 7 → ℕ}
    (hinj : ∀ a b, groupActive c a = true → groupActive c b = true →
      gate a = gate b → a = b)
    (hvalid : ∀ g, groupActive c g = true → gate g < D.length ∧ tag D (gate g) = true)
    (hports : ∀ g, groupActive c g = true → PortsAt c D (gate g) g)
    (htypes : Classified c D seed gate) : False := by
  exact active_gate_target_exclusion c hS hB hg ht hdirty hinj hvalid hports htypes
    ⟨S18Structural.DagTools.h3_out_empty hC, S18Structural.DagTools.h3_output_mask hC⟩

end S50ActualLabels

end PEqualNP.Outside.L_meta_2590
