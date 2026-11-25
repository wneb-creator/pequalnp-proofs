import Mathlib
import PEqualNP.Defs

-- The base lowerDag verifier engine is adapted from lean/PEqualNP/Outside/L_meta_8503.lean
-- in this repository, extended with a monotone lowerDagMono verifier, an unlimited-NOT
-- binary-gate BinEngine verifier, and the split-mode certificates for L-meta-11086.

namespace PEqualNP.Outside.L_meta_12087_aux

abbrev Forest := Nat → Nat × Nat

def unpack (packed width index : Nat) : Nat :=
  (packed >>> (width * index)) &&& ((1 <<< width) - 1)

def decodeNode (parentWidth width packed index : Nat) : Nat × Nat :=
  let entry := unpack packed width index
  (entry &&& ((1 <<< parentWidth) - 1), entry >>> parentWidth)

def treeBlock (start count : Nat) (check : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ next i => check i && next (i + 1)) count) start

theorem treeBlock_at {start count i : Nat} {check : Nat → Bool}
    (h : treeBlock start count check = true) (lo : start ≤ i) (hi : i < start + count) :
    check i = true := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
    change (check start && treeBlock (start + 1) count check) = true at h
    rcases Bool.and_eq_true_iff.mp h with ⟨here, rest⟩
    by_cases eq : i = start
    · simpa [eq] using here
    · exact ih rest (by omega) (by omega)

abbrev Word := Nat
abbrev RowState := Nat × List Word × List (Word × Word × Word)
abbrev CutCheck := RowState → Bool

def rootWords (base : List Word) (token : Nat) : List Word :=
  List.rec (motive := fun _ => Nat → List Word) (fun _ => [])
    (fun word _ next bits =>
      let tail := next (bits >>> 1)
      if bits &&& 1 == 0 then tail else word :: tail) base token

def rootState (base : List Word) (fuel token : Nat) : RowState :=
  (fuel, rootWords base token, [])

def insertWord (w : Word) (ws : List Word) : List Word :=
  List.rec [w] (fun a tail next => if w ≤ a then w :: a :: tail else a :: next) ws

abbrev Bound := Nat × List Word × Nat × Word

def maskFlat (mask word : Nat) : Bool :=
  let v := word &&& mask
  v == 0 || v == mask

def flatCount (mask : Nat) (words : List Word) : Nat :=
  List.rec 0 (fun word _ count => if maskFlat mask word then count + 1 else count) words

def AvailableWord (mask : Nat) (bank : List Word) (word : Word) : Prop :=
  word = 0 ∨ word = mask ∨ word ∈ bank

theorem restrictWord (mask : Nat) (word : Word) : word &&& mask &&& mask = word &&& mask := by
  simp

def AgreesAt (i j : Nat) (word : Word) : Prop :=
  word.testBit i = word.testBit j

def properWord (mask word : Word) : Prop := word ≠ 0 ∧ word ≠ mask

def binWord (isOr : Bool) (a b : Word) : Word :=
  if isOr then a ||| b else a &&& b

variable {mask : Nat} {target : Word}

def LiveWord (mask : Nat) (target : Word) : Nat → Nat → Finset (Word) → Prop
  | 0,t,S => t=0 ∧ S={target} ∧ properWord mask target
  | k+1,t,S =>
    (∃ (u : Nat) (U : Finset (Word)) (a : Word), t=u+1 ∧ S=insert a U ∧ properWord mask a ∧
      (mask ^^^ a) ∉ insert a U ∧ LiveWord mask target k u (insert ((mask ^^^ a)) U)) ∨
    (∃ (U : Finset (Word)) (a b : Word) (d : Bool), S=insert a (insert b U) ∧ properWord mask a ∧ properWord mask b ∧ a ≠ b ∧
      binWord d a b ∉ insert a (insert b U) ∧ LiveWord mask target k t (insert (binWord d a b) U))
theorem LiveWord.stop {target : Word} (hp : properWord mask target) : LiveWord mask target 0 0 {target} := ⟨rfl,rfl,hp⟩
theorem LiveWord.unary {target : Word} {k t : Nat} {U : Finset (Word)} {a : Word} (ha : properWord mask a)
    (hfresh : (mask ^^^ a) ∉ insert a U) (tail : LiveWord mask target k t (insert ((mask ^^^ a)) U)) :
    LiveWord mask target (k+1) (t+1) (insert a U) :=
  Or.inl ⟨t,U,a,rfl,rfl,ha,hfresh,tail⟩
theorem LiveWord.binary {target : Word} {k t : Nat} {U : Finset (Word)} {a b : Word} {d : Bool}
    (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
    (hfresh : binWord d a b ∉ insert a (insert b U)) (tail : LiveWord mask target k t (insert (binWord d a b) U)) :
    LiveWord mask target (k+1) t (insert a (insert b U)) :=
  Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hfresh,tail⟩
theorem LiveWord.ind {target : Word} {motive : ∀ (k t : Nat) (S : Finset (Word)), LiveWord mask target k t S → Prop}
    (stop : ∀ (hp : properWord mask target), motive 0 0 {target} (LiveWord.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset (Word)} {a : Word} (ha : properWord mask a)
      (hfresh : (mask ^^^ a) ∉ insert a U) (tail : LiveWord mask target k t (insert ((mask ^^^ a)) U)),
      motive k t (insert ((mask ^^^ a)) U) tail → motive (k+1) (t+1) (insert a U) (LiveWord.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset (Word)} {a b : Word} {d : Bool}
      (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
      (hfresh : binWord d a b ∉ insert a (insert b U)) (tail : LiveWord mask target k t (insert (binWord d a b) U)),
      motive k t (insert (binWord d a b) U) tail →
      motive (k+1) t (insert a (insert b U)) (LiveWord.binary ha hb hab hfresh tail))
    {k t : Nat} {S : Finset (Word)} (h : LiveWord mask target k t S) : motive k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)

def wordRep (mask : Nat) (ws : List Word) (w : Word) : Prop :=
  w ∈ ws ∨ ¬properWord mask w



def Masked (mask word : Nat) : Prop := word &&& mask = word

theorem insertWordMem {x w : Word} {ws : List Word} :
    x ∈ insertWord w ws ↔ x = w ∨ x ∈ ws := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change x ∈ (if w ≤ a then w :: a :: tail else a :: insertWord w tail) ↔ _
    split <;> simp [ih, or_assoc, or_left_comm]

theorem insertWordNodup {w : Word} {ws : List Word} (nd : ws.Nodup) (fresh : w ∉ ws) :
    (insertWord w ws).Nodup := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change (if w ≤ a then w :: a :: tail else a :: insertWord w tail).Nodup
    split
    · exact List.nodup_cons.mpr ⟨fresh, nd⟩
    have hn := List.nodup_cons.mp nd
    have hnot : w ≠ a ∧ w ∉ tail := by simpa using fresh
    exact List.nodup_cons.mpr ⟨by simp [insertWordMem, hnot.1.symm, hn.1], ih hn.2 hnot.2⟩

theorem insertWordSet (w : Word) (ws : List Word) :
    (insertWord w ws).toFinset = insert w ws.toFinset := by
  ext x
  simp [insertWordMem]

theorem eraseWordSet {ws : List Word} (nd : ws.Nodup) (w : Word) :
    (ws.erase w).toFinset = ws.toFinset.erase w := by
  ext x
  simp [nd.mem_erase_iff, and_comm]

def keepWord (save : Bool) (w : Word) (ws : List Word) : List Word :=
  if save then ws else ws.erase w

theorem keepNodup {ws : List Word} (nd : ws.Nodup) (save : Bool) (w : Word) :
    (keepWord save w ws).Nodup := by
  cases save
  · exact nd.erase _
  · exact nd

theorem keepSubset (save : Bool) (w : Word) (ws : List Word) :
    ∀ v ∈ keepWord save w ws, v ∈ ws := by
  cases save
  · exact fun _ h => List.mem_of_mem_erase h
  · exact fun _ h => h

theorem keepSet {ws : List Word} (nd : ws.Nodup) {w : Word} {U : Finset Word}
    (eq : ws.toFinset = insert w U) :
    (keepWord (decide (w ∈ U)) w ws).toFinset = U := by
  by_cases hw : w ∈ U
  · simp [keepWord, hw, eq, Finset.insert_eq_of_mem hw]
  · simp [keepWord, hw, eraseWordSet nd, eq]

theorem keepPairSet {ws : List Word} (nd : ws.Nodup) {a b : Word} {U : Finset Word}
    (ab : a ≠ b) (eq : ws.toFinset = insert a (insert b U)) :
    (keepWord (decide (b ∈ U)) b (keepWord (decide (a ∈ U)) a ws)).toFinset = U := by
  have x : decide (a ∈ insert b U) = decide (a ∈ U) := by simp [ab]
  have h := keepSet nd eq
  rw [x] at h
  exact keepSet (keepNodup nd _ _) h

theorem getWord {ws : List Word} {x : Word} (h : x ∈ ws) :
    ws.getD (ws.idxOf x) 0 = x := by
  have inb := List.idxOf_lt_length_iff.mpr h
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inb] using
    List.getElem_idxOf inb


theorem rootWordSublist (base : List Word) (token : Nat) : (rootWords base token).Sublist base := by
  induction base generalizing token with
  | nil => exact List.Sublist.slnil
  | cons w ws ih =>
    change (if token &&& 1 == 0 then rootWords ws (token >>> 1)
      else w :: rootWords ws (token >>> 1)).Sublist (w :: ws)
    split
    · exact (ih _).cons _
    · exact (ih _).cons₂ _

theorem rootToken (base : List Word) (S : Finset Word) :
    ∃ token < 2 ^ base.length, (rootWords base token).toFinset = base.toFinset ∩ S := by
  induction base with
  | nil => exact ⟨0, by simp, by simp [rootWords]⟩
  | cons w ws ih =>
    obtain ⟨token, htoken, ih⟩ := ih
    let bit : Nat := if w ∈ S then 1 else 0
    have hbit : bit < 2 := by dsimp [bit]; split <;> decide
    let code := 2 * token + bit
    have low : code &&& 1 = bit := by
      rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      dsimp [code]
      omega
    have high : code >>> 1 = token := by
      rw [Nat.shiftRight_eq_div_pow]
      change code / 2 = token
      dsimp [code]
      omega
    refine ⟨code, ?_, ?_⟩
    · simp only [List.length_cons, pow_succ]
      dsimp [code]
      omega
    · change (if code &&& 1 == 0 then rootWords ws (code >>> 1)
        else w :: rootWords ws (code >>> 1)).toFinset = _
      rw [low, high]
      by_cases hw : w ∈ S
      · simp [bit, hw, ih]
      · simp [bit, hw, ih]

theorem positiveInMask {i : Nat} (mt : Masked mask target) (ht : target.testBit i = true) :
    mask.testBit i = true := by
  have h := congrArg (fun n : Nat => n.testBit i) mt
  simpa [Nat.testBit_and, ht] using h

variable {rows : Nat}

def fullMask (rows : Nat) : Nat := 2 ^ rows - 1

theorem notNat (v : BitVec rows) : (~~~v).toNat = fullMask rows ^^^ v.toNat := by
  rw [← BitVec.xor_allOnes, BitVec.toNat_xor, Nat.xor_comm, BitVec.toNat_allOnes]
  rfl

theorem toNatAvailable (bank : List (BitVec rows)) (i : Nat) :
    AvailableWord (fullMask rows) (bank.map BitVec.toNat) (bank.getD i 0).toNat := by
  rw [List.getD_eq_getElem?_getD]
  cases h : bank[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (Or.inr (List.mem_map_of_mem (List.mem_of_getElem? h)))

abbrev maskedFlat (m a : Word) : Prop := a &&& m = 0 ∨ a &&& m = m


def flatSet (m : Word) (s : Finset (Word)) := s.filter (maskedFlat m)
def visibleWords (m : Word) (s : Finset (Word)) := s.image fun w => w &&& m

theorem flIns {m a : Word} {s : Finset (Word)} (ha : a ∉ s) :
    (flatSet m (insert a s)).card = (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases f : maskedFlat m a <;> simp [flatSet,Finset.filter_insert,f,ha]

theorem flLe (m a : Word) (s : Finset (Word)) :
    (flatSet m (insert a s)).card ≤ (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases old : a ∈ s
  · rw [Finset.insert_eq_of_mem old]
    omega
  · rw [flIns old]

theorem prIns (m a : Word) (s : Finset (Word)) :
    visibleWords m (insert a s) = insert (a &&& m) (visibleWords m s) := Finset.image_insert ..

theorem cofNot {mask m : Nat} (sub : mask &&& m = m) (a : Word) :
    (mask ^^^ a) &&& m = m ^^^ (a &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h := congrArg (fun w : Nat => w.testBit i) sub
  simp only [Nat.testBit_and, Nat.testBit_xor] at h ⊢
  cases he : m.testBit i
  · simp
  · have hm : mask.testBit i = true := by simpa [he] using h
    simp [hm]

theorem cofBinary (m a b : Word) (d : Bool) :
    binWord d a b &&& m = binWord d (a &&& m) (b &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases d <;> simp only [binWord, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and, Nat.testBit_or] <;>
    cases m.testBit i <;> simp

theorem flNot {mask m : Nat} (sub : mask &&& m = m) (a : Word) :
    maskedFlat m (mask ^^^ a) ↔ maskedFlat m a := by
  unfold maskedFlat
  rw [cofNot sub]
  constructor <;> intro h
  · rcases h with h | h
    · right
      have hh := congrArg (fun v => m ^^^ v) h
      simpa [← Nat.xor_assoc] using hh
    · left
      have hh := congrArg (fun v => m ^^^ v) h
      simpa [← Nat.xor_assoc] using hh
  · rcases h with h | h <;> simp [h]

def projectedStock (m : Word) (s : Finset (Word)) := insert 0 (insert m (visibleWords m s))

theorem flatCountCard (mask : Nat) {words : List Word} (nodup : words.Nodup) :
    flatCount mask words = (flatSet mask words.toFinset).card := by
  induction words with
  | nil => rfl
  | cons w ws ih =>
    have nd := List.nodup_cons.mp nodup
    have fresh : w ∉ ws.toFinset := by simpa using nd.1
    have bool : maskFlat mask w = true ↔ maskedFlat mask w := by
      simp [maskFlat, maskedFlat]
    change (if maskFlat mask w then flatCount mask ws + 1 else flatCount mask ws) = _
    rw [List.toFinset_cons, flIns fresh, ih nd.2]
    by_cases h : maskedFlat mask w
    · simp [h, bool.mpr h]
    · have no : maskFlat mask w = false := Bool.eq_false_iff.mpr (fun ht => h (bool.mp ht))
      simp [h, no]

abbrev PointWire (rows : Nat) := Fin rows → Bool

def encodePoint (f : PointWire rows) : BitVec rows :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem encodeBit (f : PointWire rows) (i : Fin rows) :
    (encodePoint f).getLsbD i.val = f i := by
  simp only [encodePoint, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]

theorem encodeAnd (a b : PointWire rows) :
    encodePoint (fun i => a i && b i) = encodePoint a &&& encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]

theorem encodeOr (a b : PointWire rows) :
    encodePoint (fun i => a i || b i) = encodePoint a ||| encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]

def pointWord (f : PointWire rows) : Word := (encodePoint f).toNat

def relabel (sourceIndex : Fin rows → Fin rows) (word : Word) : Word :=
  pointWord fun i => word.testBit (sourceIndex i).val

theorem pointZero : pointWord (fun _ : Fin rows => false) = 0 := by
  have eq : encodePoint (fun _ : Fin rows => false) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i, hi⟩]
    simp
  simp [pointWord, eq]

theorem relabelZero (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex 0 = 0 := by
  simpa [relabel] using (pointZero (rows := rows))

theorem relabelAnd (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a &&& b) = relabel sourceIndex a &&& relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_and, pointWord, encodeAnd, BitVec.toNat_and]

theorem relabelOr (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a ||| b) = relabel sourceIndex a ||| relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_or, pointWord, encodeOr, BitVec.toNat_or]

theorem relabelXor (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a ^^^ b) = relabel sourceIndex a ^^^ relabel sourceIndex b := by
  have eq : encodePoint (fun i => (a ^^^ b).testBit (sourceIndex i).val) =
      encodePoint (fun i => a.testBit (sourceIndex i).val) ^^^
      encodePoint (fun i => b.testBit (sourceIndex i).val) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_xor, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
    exact Nat.testBit_xor ..
  simpa only [relabel, pointWord, BitVec.toNat_xor] using congrArg BitVec.toNat eq

theorem relabelBit (sourceIndex : Fin rows → Fin rows) (word : Word) (i : Fin rows) :
    (relabel sourceIndex word).testBit i.val = word.testBit (sourceIndex i).val :=
  encodeBit _ i

theorem relabelOutside (sourceIndex : Fin rows → Fin rows) (word i : Word) (h : rows ≤ i) :
    (relabel sourceIndex word).testBit i = false := by
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le (show (encodePoint _).toNat < 2 ^ rows from BitVec.isLt _)
    (Nat.pow_le_pow_right (by decide) h)

theorem relabelInj (sourceIndex : Fin rows → Fin rows) (onto : Function.Surjective sourceIndex)
    {a b : Word} (ba : Masked (fullMask rows) a) (bb : Masked (fullMask rows) b)
    (eq : relabel sourceIndex a = relabel sourceIndex b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · obtain ⟨j, h⟩ := onto ⟨i, inside⟩
    have bit := congrArg (fun w : Nat => w.testBit j.val) eq
    simpa only [relabelBit, h] using bit
  · have ea := congrArg (fun w : Nat => w.testBit i) ba
    have eb := congrArg (fun w : Nat => w.testBit i) bb
    simp only [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, inside, decide_false,
      Bool.and_false] at ea eb
    rw [← ea, ← eb]

namespace PackedRect

def full : ℕ := 22300745198530623141535718272648361505980415

def IsRect (R : ℕ → Prop) : Prop :=
  ∀ e i e' i' : ℕ, e < 12 → i < 12 → e' < 12 → i' < 12 →
    R (12 * e + i) → R (12 * e' + i') → R (12 * e + i')

def Part (zs : List ((ℕ → Prop) × ℕ)) : Prop :=
  (∀ z ∈ zs, IsRect z.1) ∧
  (∀ z ∈ zs, ∀ q, z.1 q → q < 144) ∧
  (zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False)) ∧
  (∀ q, q < 144 → ∃ z ∈ zs, z.1 q) ∧
  (∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true)

theorem Part.disj {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False) := h.2.2.1

theorem Part.sub {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true := h.2.2.2.2


end PackedRect

abbrev Witness := Word × Nat × Nat

def witnessWord (w : Witness) : Word := w.1

def essentialB (mask target : Word) (stock : List Word) (entry : Witness) : Bool :=
  let (w,p,n) := entry
  mask.testBit p && mask.testBit n && target.testBit p && !target.testBit n &&
    (w.testBit p != w.testBit n) &&
    stock.all (fun x => x == w || x.testBit p == x.testBit n)

def unpackWitnesses (stock : List Word) (codes : List Nat) : List Witness :=
  List.rec [] (fun code _ rest =>
    (stock.getD (code >>> 18) 0, (code >>> 9) &&& 511, code &&& 511) :: rest) codes

def DagAuto (mask goal : Word) (select : Fin rows → Fin rows) : Prop :=
  Function.Surjective select ∧ relabel select mask = mask ∧ relabel select goal = goal

abbrev WordMoveStep := List (Word × Nat) × List (Word × Nat)
abbrev WordMove := List WordMoveStep

def mixStep (m : WordMoveStep) (w : Word) : Word :=
  let left := List.rec 0 (fun (part,n) _ acc => ((w &&& part) <<< n) ||| acc) m.1
  let right := List.rec 0 (fun (part,n) _ acc => ((w &&& part) >>> n) ||| acc) m.2
  left ||| right

def BitLinear (f : Word → Word) : Prop :=
  ∀ w i, (f w).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (2 ^ j)).testBit i = true

theorem bitLinearZero : BitLinear (fun _ => 0) := by
  simp [BitLinear]

theorem bitLinearOr {f g : Word → Word} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f w ||| g w) := by
  intro w i
  change ((f w ||| g w).testBit i = true) ↔ _
  simp only [Nat.testBit_or, Bool.or_eq_true]
  rw [hf w i, hg w i]
  constructor
  · rintro (⟨j,hw,hj⟩ | ⟨j,hw,hj⟩)
    · exact ⟨j,hw,Or.inl hj⟩
    · exact ⟨j,hw,Or.inr hj⟩
  · rintro ⟨j,hw,hj | hj⟩
    · exact Or.inl ⟨j,hw,hj⟩
    · exact Or.inr ⟨j,hw,hj⟩

theorem bitLinearLeft (mask n : Nat) : BitLinear (fun w => (w &&& mask) <<< n) := by
  intro w i
  simp only [Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hw, hm⟩
    exact ⟨i-n,hw,h,rfl,hm⟩
  · rintro ⟨j,hw,h,rfl,hm⟩
    exact ⟨h,hw,hm⟩

theorem bitLinearRight (mask n : Nat) : BitLinear (fun w => (w &&& mask) >>> n) := by
  intro w i
  simp only [Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hw,hm⟩
    exact ⟨n+i,hw,rfl,hm⟩
  · rintro ⟨j,hw,rfl,hm⟩
    exact ⟨hw,hm⟩

theorem mixStepLinear (move : WordMoveStep) : BitLinear (mixStep move) := by
  obtain ⟨left, right⟩ := move
  unfold mixStep
  apply bitLinearOr
  · induction left with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearLeft part count) ih
  · induction right with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearRight part count) ih

def mixMove (move : WordMove) (w : Word) : Word :=
  (List.rec (motive := fun _ => Word → Word) id
    (fun step _ next w => next (mixStep step w)) move) w

theorem bitLinearId : BitLinear id := by
  intro w i
  change w.testBit i = true ↔ ∃ j, w.testBit j = true ∧ (2 ^ j).testBit i = true
  simp [Nat.testBit_two_pow]

theorem bitLinearComp {f g : Word → Word} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f (g w)) := by
  intro w i
  change (f (g w)).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (g (2 ^ j))).testBit i = true
  rw [hf]
  constructor
  · rintro ⟨j,gj,fj⟩
    obtain ⟨k,wk,gk⟩ := (hg w j).mp gj
    exact ⟨k,wk,(hf (g (2^k)) i).mpr ⟨j,gk,fj⟩⟩
  · rintro ⟨j,wj,h⟩
    obtain ⟨k,gk,fk⟩ := (hf (g (2^j)) i).mp h
    exact ⟨k,(hg w k).mpr ⟨j,wj,gk⟩,fk⟩

theorem mixMoveLinear (move : WordMove) : BitLinear (mixMove move) := by
  induction move with
  | nil => exact bitLinearId
  | cons op ops ih =>
    change BitLinear (fun w => mixMove ops (mixStep op w))
    exact bitLinearComp ih (mixStepLinear op)

def permuteAxes (axes : List Nat) (offset row : Nat) : Nat :=
  offset ^^^ (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun j _ next i => (if row.testBit i then 1 <<< j else 0) ||| next (i + 1)) axes) 0

theorem relabelLinear (select : Fin rows → Fin rows) : BitLinear (relabel select) := by
  intro w i
  by_cases inside : i < rows
  · let ii : Fin rows := ⟨i,inside⟩
    change (relabel select w).testBit ii.val = true ↔ _
    rw [relabelBit]
    constructor
    · intro h
      refine ⟨(select ii).val,h,?_⟩
      change (relabel select (2 ^ (select ii).val)).testBit ii.val = true
      rw [relabelBit, Nat.testBit_two_pow]
      simp
    · rintro ⟨j,h,bit⟩
      change (relabel select (2^j)).testBit ii.val = true at bit
      rw [relabelBit, Nat.testBit_two_pow, decide_eq_true_eq] at bit
      exact bit ▸ h
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]
    simp [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]

theorem wordMoveAgreement {select : Fin rows → Fin rows} {mask : Word} {move : WordMove}
    (bounded : Masked (fullMask rows) mask)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = relabel select (2 ^ i.val))
    {w : Word} (masked : Masked mask w) : mixMove move w = relabel select w := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [mixMoveLinear, relabelLinear]
  have source {j : Nat} (bit : w.testBit j = true) :
      mixMove move (2^j) = relabel select (2^j) := by
    have m : mask.testBit j = true := by
      have eq := congrArg (fun x : Nat => x.testBit j) masked
      simpa [Nat.testBit_and, bit] using eq
    have within : j < rows := by
      have eq := congrArg (fun x : Nat => x.testBit j) bounded
      simpa [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, m] using eq
    exact basis ⟨j,within⟩ m
  constructor <;> rintro ⟨j,hj,hi⟩
  · exact ⟨j,hj,by rwa [← source hj]⟩
  · exact ⟨j,hj,by rwa [source hj]⟩

theorem relabelBasis {select inverse : Fin rows → Fin rows}
    (left : ∀ i, inverse (select i) = i) :
    ∀ j : Fin rows, select (inverse j) = j →
      relabel select (2 ^ j.val) = 2 ^ (inverse j).val := by
  intro j right
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · let pos : Fin rows := ⟨i,inside⟩
    change (relabel select (2 ^ j.val)).testBit pos.val = _
    rw [relabelBit, Nat.testBit_two_pow, Nat.testBit_two_pow]
    apply (Bool.eq_iff_iff).mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro eq
      have e : j = select pos := Fin.ext eq
      rw [e,left]
    · intro eq
      have hp : inverse j = pos := Fin.ext eq
      rw [← hp, right]
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside), Nat.testBit_two_pow]
    have ne : (inverse j).val ≠ i := by have := (inverse j).isLt; omega
    simp [ne]

theorem dagAutoFromMove {select inverse : Fin rows → Fin rows} {mask goal : Word} {move : WordMove}
    (left : ∀ i, inverse (select i) = i)
    (right : ∀ i, select (inverse i) = i)
    (bm : Masked (fullMask rows) mask)
    (gm : Masked mask goal)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val)
    (sameMask : mixMove move mask = mask) (sameGoal : mixMove move goal = goal) :
    DagAuto mask goal select ∧ ∀ w, Masked mask w → mixMove move w = relabel select w := by
  have agree {w : Word} (hw : Masked mask w) : mixMove move w = relabel select w :=
    wordMoveAgreement bm (fun i h => (basis i h).trans (relabelBasis left i (right i)).symm) hw
  exact ⟨⟨fun i => ⟨inverse i,right i⟩,(agree (by simp [Masked])).symm.trans sameMask,
    (agree gm).symm.trans sameGoal⟩,fun _ h => agree h⟩

theorem maskedBelow {mask w : Word} (bm : Masked (fullMask rows) mask)
    (bw : Masked mask w) : Masked (fullMask rows) w := by
  unfold Masked at *
  rw [← bw, Nat.land_assoc, bm, bw]

theorem maskedTransfer {mask w : Word} {select : Fin rows → Fin rows}
    (same : relabel select mask = mask) (hw : Masked mask w) :
    Masked mask (relabel select w) := by
  unfold Masked at *
  rw [← same, ← relabelAnd, hw]

def dagForceWord {α : Type} (word : Word) (cont : Word → α) : α :=
  Nat.rec (cont 0) (fun k _ => cont (k + 1)) word

theorem dagForceWordEq {α : Type} (word : Word) (cont : Word → α) :
    dagForceWord word cont = cont word := by cases word <;> rfl

def dagForceWords (words : List Word) (cont : List Word → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Word → Bool) → Bool) (fun k => k [])
    (fun w _ next k => dagForceWord w (fun v => next (fun rest => k (v :: rest)))) words) cont

theorem dagForceWordsEq (words : List Word) (cont : List Word → Bool) :
    dagForceWords words cont = cont words := by
  induction words generalizing cont with
  | nil => rfl
  | cons w ws ih =>
    change dagForceWord w (fun v => dagForceWords ws (fun rest => cont (v :: rest))) = _
    rw [dagForceWordEq, ih]

abbrev DagLink := Nat × Nat
abbrev DagLinks := Nat → Nat → Option DagLink

def dagPartition (directed : Bool) (ws : List Word) : Word → Word → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      Nat.beq p 0 || Nat.beq n 0 ||
      dagForceWord (p &&& w) (fun up =>
        dagForceWord (n &&& w) (fun down =>
          rest up down &&
            dagForceWord (p ^^^ up) (fun offP =>
              dagForceWord (if directed then n else n ^^^ down) (rest offP))))) ws

theorem dagOffBits {v w : Word} {i : Nat} (bit : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor, Nat.testBit_and] at bit
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv, hw] at bit ⊢

theorem dagPartitionSound {directed : Bool} {ws : List Word} {positive negative : Word}
    (fail : dagPartition directed ws positive negative = false) :
    ∃ p n, positive.testBit p = true ∧ negative.testBit n = true ∧
      ∀ w ∈ ws, if directed then w.testBit p = true → w.testBit n = true
                  else w.testBit p = w.testBit n := by
  have nonempty {w : Word} (hn : w ≠ 0) : ∃ j, w.testBit j = true := by
    by_contra! all
    apply hn
    apply Nat.eq_of_testBit_eq
    intro i
    simp [all i]
  induction ws generalizing positive negative with
  | nil =>
    change (Nat.beq positive 0 || Nat.beq negative 0) = false at fail
    simp only [Bool.or_eq_false_iff] at fail
    obtain ⟨p,hp⟩ := nonempty (w := positive) (fun eq => by simp [eq] at fail)
    obtain ⟨n,hn⟩ := nonempty (w := negative) (fun eq => by simp [eq] at fail)
    exact ⟨p,n,hp,hn,by simp⟩
  | cons w ws ih =>
    change (Nat.beq positive 0 || Nat.beq negative 0 ||
      dagForceWord (positive &&& w) (fun up =>
        dagForceWord (negative &&& w) (fun down =>
          dagPartition directed ws up down &&
            dagForceWord (positive ^^^ up) (fun offP =>
              dagForceWord (if directed then negative else negative ^^^ down)
                (dagPartition directed ws offP))))) = false at fail
    simp only [dagForceWordEq, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p,n,hp,hn,agree⟩ := ih on
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hn
      refine ⟨p,n,hp.1,hn.1,?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | tail
      · simp [hp.2, hn.2]
      · exact agree _ tail
    · obtain ⟨p,n,hp,hn,agree⟩ := ih off
      have hp' := dagOffBits hp
      cases mode : directed
      · have hn' : negative.testBit n = true ∧ w.testBit n = false := by
          apply dagOffBits
          simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn'.1,?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2, hn'.2]
        · simpa [mode] using agree _ tail
      · have hn' : negative.testBit n = true := by simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn',?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2]
        · simpa [mode] using agree _ tail

abbrev DagSample := Nat × Nat
abbrev DagSignals := Word × Word
abbrev DagCounts := Word × Word × Word

def dagForceCache (tags : List DagSignals) (use : List DagSignals → Bool) : Bool :=
  (List.rec (motive := fun _ => (List DagSignals → Bool) → Bool) (fun k => k [])
    (fun tag _ next k =>
      dagForceWord tag.1 (fun up => dagForceWord tag.2 (fun down =>
        next (fun tail => k ((up,down)::tail))))) tags) use

theorem dagForceCacheEq (tags : List DagSignals) (use : List DagSignals → Bool) :
    dagForceCache tags use = use tags := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag rest ih =>
    obtain ⟨a,b⟩ := tag
    change dagForceWord a (fun up => dagForceWord b (fun down =>
      dagForceCache rest (fun tail => use ((up,down)::tail)))) = _
    simp only [dagForceWordEq, ih]

def dagSignalContrast (directed : Bool) (full : Word) (tag : DagSignals) : Word :=
  if directed then tag.1 &&& (tag.2 ^^^ full) else tag.1 ^^^ tag.2

def dagCountStep (acc : DagCounts) (column : Word) : DagCounts :=
  (acc.1 ||| column, acc.2.1 ||| (acc.1 &&& column), acc.2.2 ||| (acc.2.1 &&& column))

def dagCountSigns (directed : Bool) (full : Word) (tags : List DagSignals)
    (use : DagCounts → Bool) : Bool :=
  (List.rec (motive := fun _ => (DagCounts → Bool) → Bool) (fun k => k (0,0,0))
    (fun tag _ more k =>
      dagForceWord (dagSignalContrast directed full tag) (fun column =>
        more (fun acc =>
          dagForceWord (acc.1 ||| column) (fun once =>
            dagForceWord (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
              dagForceWord (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => k (once,twice,thrice)))))))
    tags) use

theorem dagCountSignsEq (directed : Bool) (full : Word) (tags : List DagSignals)
    (use : DagCounts → Bool) : dagCountSigns directed full tags use =
    use (tags.foldr (fun tag acc => dagCountStep acc (dagSignalContrast directed full tag)) (0,0,0)) := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag tags ih =>
    change dagForceWord (dagSignalContrast directed full tag) (fun column =>
      dagCountSigns directed full tags (fun acc =>
        dagForceWord (acc.1 ||| column) (fun once =>
          dagForceWord (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
            dagForceWord (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => use (once,twice,thrice)))))) = _
    simp only [dagForceWordEq, ih]
    rfl

def dagPairReject (mask goal : Word) (directed : Bool) (ws : List Word) (pairs : List Nat) : Bool :=
  pairs.any fun code =>
    let p := code &&& 511
    let n := code >>> 9
    goal.testBit p && mask.testBit n && !goal.testBit n &&
      ws.all (fun w => if directed then !(w.testBit p) || w.testBit n
                       else w.testBit p == w.testBit n)

abbrev DagTagged := Word × DagSignals

def dagTagBases (stock : List Word) (positive negative width : Nat) : List DagTagged :=
  (List.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun w _ next i => (w, unpack positive width i, unpack negative width i) :: next (i+1)) stock) 0

def dagTagRoot (bank : List DagTagged) (token : Nat) : List DagTagged :=
  (List.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun tag _ next k =>
      if Nat.beq (k &&& 1) 0 then next (k >>> 1) else tag :: next (k >>> 1)) bank) token

def dagTagKeep (keep : Bool) (w : Word) (bank : List DagTagged) : List DagTagged :=
  if keep then bank
  else List.rec [] (fun tag tail next => if Nat.beq tag.1 w then tail else tag :: next) bank

def dagTagInsert (tag : DagTagged) (bank : List DagTagged) : List DagTagged :=
  List.rec [tag] (fun old tail next => if Nat.ble tag.1 old.1 then tag :: old :: tail else old :: next) bank

def dagStateOK (mask : Word) (ws : List Word) : Bool :=
  (ws.dedup.length == ws.length) && ws.all (fun w => w &&& mask == w)

theorem dagStateOKSpec {mask : Word} {ws : List Word} (ok : dagStateOK mask ws = true) :
    ws.Nodup ∧ ∀ w ∈ ws, Masked mask w := by
  simp only [dagStateOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  exact ⟨List.nodup_iff_length_dedup_eq.mpr ok.1, ok.2⟩

theorem dagInsertLength (w : Word) (ws : List Word) :
    (insertWord w ws).length = ws.length + 1 := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    change (if w ≤ a then w :: a :: ws else a :: insertWord w ws).length = _
    split <;> simp [ih]

theorem dagKeepLength (keep : Bool) (w : Word) (ws : List Word) :
    ws.length - (if keep then 0 else 1) ≤ (keepWord keep w ws).length := by
  cases keep
  · exact List.le_length_erase
  · simp [keepWord]

theorem dagKeepMem {ws : List Word} {x w : Word} {keep : Bool}
    (nd : ws.Nodup) (h : w ∈ keepWord keep x ws) : w ∈ ws ∧ (keep = true ∨ w ≠ x) := by
  cases keep
  · simpa [keepWord, nd.mem_erase_iff, and_comm] using h
  · simpa [keepWord] using h

theorem dagKeepNodup {ws : List Word} (nd : ws.Nodup) (keep : Bool) (x : Word) :
    (keepWord keep x ws).Nodup := by
  cases keep
  · exact nd.erase x
  · exact nd

theorem readWordMasked {mask : Word} {ws : List Word}
    (all : ∀ w ∈ ws, Masked mask w) (i : Nat) : Masked mask (ws.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => simp [Masked]
  | some w => exact all w (List.mem_of_getElem? h)

def DagMovesOK (mask goal : Word) (width : Nat) (moves : Array WordMove) : Prop :=
  ∀ (i : Nat) (m : WordMove), moves[i]? = some m →
    ∃ select : Fin width → Fin width, DagAuto mask goal select ∧
      ∀ w, Masked mask w → mixMove m w = relabel select w

abbrev DagMoveRecord (width : Nat) := WordMove × (Fin width → Fin width) × (Fin width → Fin width)

def dagMoves (cert : List (DagMoveRecord width)) : Array WordMove := (cert.map Prod.fst).toArray

def dagMoveRecordProps {width : Nat} (mask goal : Word) (entry : DagMoveRecord width) : Prop :=
  let (move, select, inverse) := entry
  (∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal

def dagMoveRecordOK {width : Nat} (mask goal : Word) (entry : DagMoveRecord width) : Bool :=
  let (move, select, inverse) := entry
  decide ((∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal)

theorem dagMoveRecordSpec {width : Nat} {mask goal : Word} {entry : DagMoveRecord width}
    (ok : dagMoveRecordOK mask goal entry = true) : dagMoveRecordProps mask goal entry := by
  rcases entry with ⟨move,select,inverse⟩
  unfold dagMoveRecordProps
  exact of_decide_eq_true ok

theorem dagMovesOfCheck {width : Nat} {mask goal : Word} {cert : List (DagMoveRecord width)}
    (ok : cert.all (dagMoveRecordOK mask goal) = true) :
    DagMovesOK mask goal width (dagMoves cert) := by
  intro i m get
  simp only [dagMoves, List.getElem?_toArray, List.getElem?_map] at get
  cases e : cert[i]? with
  | none => simp [e] at get
  | some entry =>
    have eq : entry.1 = m := by simpa [e] using get
    rcases entry with ⟨move,select,inverse⟩
    obtain ⟨left,right,bm,gm,basis,mm,mg⟩ :=
      dagMoveRecordSpec (List.all_eq_true.mp ok _ (List.mem_of_getElem? e))
    subst m
    exact ⟨select, dagAutoFromMove left right bm gm basis mm mg⟩

def projectDAGStock (mask : Word) (source : List Word) (indices : List Nat) : List Word :=
  List.rec [] (fun i _ rest => (mask &&& source.getD i 0) :: rest) indices

theorem stockMaskedOfCheck {mask : Word} {stock : List Word}
    (h : stock.all (fun w => w &&& mask == w) = true) :
    ∀ w ∈ stock, Masked mask w := by
  intro w hw
  exact beq_iff_eq.mp (List.all_eq_true.mp h w hw)

def dagShift (mask : Word) (move : WordMove) (word : Word) : Word :=
  mixMove move (word &&& mask)

def dagShiftUnique (mask : Word) (move : WordMove) : Nat → Word → Bool :=
  Nat.rec (fun _ => true) (fun i next occupied =>
    if mask.testBit i then
      dagForceWord (mixMove move (2^i)) (fun col =>
        Nat.beq (col &&& occupied) 0 && dagForceWord (occupied ||| col) next)
    else next occupied)

theorem dagShiftLinear (mask : Word) (move : WordMove) : BitLinear (dagShift mask move) := by
  apply bitLinearComp (mixMoveLinear move)
  simpa using bitLinearRight mask 0

theorem dagShiftBasis (mask : Word) (move : WordMove) (i : Nat) :
    dagShift mask move (2 ^ i) = if mask.testBit i then mixMove move (2^i) else 0 := by
  have select : 2 ^ i &&& mask = if mask.testBit i then 2^i else 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases same : i = j
    · subst j
      simp only [Nat.testBit_and, Nat.testBit_two_pow, decide_true, Bool.true_and]
      cases mask.testBit i <;> simp
    · cases h : mask.testBit i <;> simp [Nat.testBit_and, Nat.testBit_two_pow, same, h]
  rw [dagShift, select]
  split
  · rfl
  · apply Nat.eq_of_testBit_eq
    intro j
    apply Bool.eq_iff_iff.mpr
    rw [mixMoveLinear]
    simp

theorem dagShiftUniqueSpec {mask : Word} {move : WordMove} {n : Nat} {occupied : Word}
    (ok : dagShiftUnique mask move n occupied = true) :
    (∀ j < n, ∀ b, (dagShift mask move (2^j)).testBit b = true → occupied.testBit b = false) ∧
    (∀ j < n, ∀ k < n, ∀ b, (dagShift mask move (2^j)).testBit b = true →
      (dagShift mask move (2^k)).testBit b = true → j = k) := by
  induction n generalizing occupied with
  | zero => simp
  | succ n ih =>
    let col := mixMove move (2^n)
    change (if mask.testBit n then dagForceWord col (fun w =>
      Nat.beq (w &&& occupied) 0 && dagForceWord (occupied ||| w) (dagShiftUnique mask move n))
      else dagShiftUnique mask move n occupied) = true at ok
    cases active : mask.testBit n
    · simp [active,dagForceWordEq] at ok
      obtain ⟨existing,unique⟩ := ih ok
      have dead : dagShift mask move (2^n) = 0 := by simp [dagShiftBasis,active]
      refine ⟨?_,?_⟩
      · intro j hj b h
        by_cases same : j = n
        · simp [same,dead] at h
        · exact existing j (by omega) b h
      · intro j hj k hk b a c
        by_cases e : j = n
        · simp [e,dead] at a
        by_cases e' : k = n
        · simp [e',dead] at c
        exact unique j (by omega) k (by omega) b a c
    · simp only [active,ite_true,dagForceWordEq,Bool.and_eq_true] at ok
      have disjoint := Nat.beq_eq.mp ok.1
      obtain ⟨existing,unique⟩ := ih ok.2
      have colEq : dagShift mask move (2^n) = col := by simp [dagShiftBasis,active,col]
      have old {j b : Nat} (hj : j < n) (h : (dagShift mask move (2^j)).testBit b = true) :
          occupied.testBit b = false ∧ col.testBit b = false := by
        simpa [Nat.testBit_or, Bool.or_eq_false_iff] using existing j hj b h
      refine ⟨?_,?_⟩
      · intro j hj b h
        by_cases same : j = n
        · rw [same,colEq] at h
          have bit := congrArg (fun w => Nat.testBit w b) disjoint
          simpa [Nat.testBit_and,h] using bit
        · exact (old (by omega) h).1
      · intro j hj k hk b a c
        by_cases e : j = n
        · by_cases e' : k = n
          · exact e.trans e'.symm
          · rw [e,colEq,(old (by omega) c).2] at a
            contradiction
        by_cases e' : k = n
        · rw [e',colEq,(old (by omega) a).2] at c
          contradiction
        exact unique j (by omega) k (by omega) b a c

theorem dagShiftGates {mask : Word} {move : WordMove} {width : Nat}
    (bounded : Masked (fullMask width) mask) (checked : dagShiftUnique mask move width 0 = true) :
    (∀ a b, dagShift mask move (a &&& b) = dagShift mask move a &&& dagShift mask move b) ∧
    (∀ a b, dagShift mask move (a ||| b) = dagShift mask move a ||| dagShift mask move b) ∧
    (∀ a b, dagShift mask move (a ^^^ b) = dagShift mask move a ^^^ dagShift mask move b) := by
  let f := dagShift mask move
  have lin := dagShiftLinear mask move
  have uniq {j k i : Nat} (hj : (f (2^j)).testBit i = true) (hk : (f (2^k)).testBit i = true) : j = k := by
    have within {m : Nat} (a : (f (2^m)).testBit i = true) : m < width := by
      by_contra! big
      have eq := congrArg (fun w => Nat.testBit w m) bounded
      have zero : mask.testBit m = false := by
        simpa [Masked,fullMask,Nat.testBit_and,Nat.testBit_two_pow_sub_one,show ¬m < width by omega] using eq.symm
      simp [f,dagShiftBasis,zero] at a
    exact (dagShiftUniqueSpec checked).2 j (within hj) k (within hk) i hj hk
  refine ⟨?_,?_,?_⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [Nat.testBit_and, Bool.and_eq_true, lin, lin, lin]
    constructor
    · rintro ⟨j,hj,h⟩
      rw [Nat.testBit_and, Bool.and_eq_true] at hj
      exact ⟨⟨j,hj.1,h⟩,⟨j,hj.2,h⟩⟩
    · rintro ⟨⟨j,hj,q⟩,⟨k,hk,r⟩⟩
      have same := uniq q r
      subst k
      exact ⟨j,by simp [Nat.testBit_and,hj,hk],q⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [lin (a ||| b) i, Nat.testBit_or, Bool.or_eq_true, lin a i, lin b i]
    simp only [Nat.testBit_or, Bool.or_eq_true]
    constructor
    · rintro ⟨j,(left | right),same⟩
      · exact Or.inl ⟨j,left,same⟩
      · exact Or.inr ⟨j,right,same⟩
    · rintro (⟨j,left,same⟩ | ⟨j,right,same⟩)
      · exact ⟨j,Or.inl left,same⟩
      · exact ⟨j,Or.inr right,same⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    have l := lin a i
    have r := lin b i
    have v := lin (a ^^^ b) i
    cases pa : (f a).testBit i <;> cases pb : (f b).testBit i
    · rw [Nat.testBit_xor,pa,pb]
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨j,hj,h⟩ := v.mp yes
      have disj : a.testBit j = true ∨ b.testBit j = true := by
        rw [Nat.testBit_xor] at hj
        cases aj : a.testBit j <;> cases bj : b.testBit j <;> simp [aj,bj] at hj ⊢
      rcases disj with da | db
      · have := l.mpr ⟨j,da,h⟩
        change (f a).testBit i = true at this
        simp [pa] at this
      · have := r.mpr ⟨j,db,h⟩
        change (f b).testBit i = true at this
        simp [pb] at this
    · rw [Nat.testBit_xor,pa,pb]
      apply v.mpr
      obtain ⟨j,hj,h⟩ := r.mp pb
      have notA : a.testBit j = false := Bool.eq_false_iff.mpr (fun yes => by
        have := l.mpr ⟨j,yes,h⟩
        change (f a).testBit i = true at this
        simp [pa] at this)
      exact ⟨j,by simp [Nat.testBit_xor,notA,hj],h⟩
    · rw [Nat.testBit_xor,pa,pb]
      apply v.mpr
      obtain ⟨j,hj,h⟩ := l.mp pa
      have notB : b.testBit j = false := Bool.eq_false_iff.mpr (fun yes => by
        have := r.mpr ⟨j,yes,h⟩
        change (f b).testBit i = true at this
        simp [pb] at this)
      exact ⟨j,by simp [Nat.testBit_xor,hj,notB],h⟩
    · rw [Nat.testBit_xor,pa,pb]
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨j,hj,h⟩ := v.mp yes
      obtain ⟨a',ha,q⟩ := l.mp pa
      obtain ⟨b',hb,r⟩ := r.mp pb
      have ea := uniq h q
      have eb := uniq h r
      rw [← ea] at ha
      rw [← eb] at hb
      simp [Nat.testBit_xor,ha,hb] at hj

def hcsGateVal {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    BitVec rows :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => args.foldr (· &&& ·) (BitVec.allOnes rows)
  | PEqualNP.CircuitLowerBounds.GateOp.or => args.foldr (· ||| ·) 0
  | PEqualNP.CircuitLowerBounds.GateOp.not => ~~~(args.headD 0)
  | _ => 0

def hcsStep {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    List (BitVec rows) :=
  bank ++ [hcsGateVal bank g]

theorem hcsGetDBit {rows : Nat} (bank : List (BitVec rows)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp

theorem hcsAndBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]

theorem hcsOrBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]

theorem hcsGateBit {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsAndBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsOrBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, BitVec.getLsbD_not, i.isLt,
      decide_true, Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons, List.headD_cons, hcsGetDBit]

theorem hcsFoldBits {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl hcsStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (hcsStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [hcsStep, List.map_append, List.map_cons, List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')), hstep]

def hcsCheckPow (p : Nat → Bool) : Nat → Nat → Bool
  | 0, s => p s
  | k + 1, s => hcsCheckPow p k s && hcsCheckPow p k (s + 2 ^ k)

theorem hcsCheckPow_spec {p : Nat → Bool} {k s i : Nat}
    (h : hcsCheckPow p k s = true) (lo : s ≤ i) (hi : i < s + 2 ^ k) : p i = true := by
  induction k generalizing s with
  | zero =>
    have e : i = s := by omega
    simpa [hcsCheckPow, e] using h
  | succ k ih =>
    simp only [hcsCheckPow, Bool.and_eq_true] at h
    by_cases hlt : i < s + 2 ^ k
    · exact ih h.1 lo hlt
    · exact ih h.2 (by omega) (by rw [Nat.pow_succ] at hi; omega)


-- ============================================================================
-- Extension: Monotone lowerDag (lowerDagMono) + Unlimited-NOT Engine (BinEngine)
-- ============================================================================

-- Part 1: Monotone (NOT-free, t = 0) lowerDag engine

def GateWordMono (mask : Nat) (bank : List Word) (out : Word) : Prop :=
  ∃ a b, AvailableWord mask bank a ∧ AvailableWord mask bank b ∧
    (out = a &&& b ∨ out = a ||| b)

theorem gateMonoOfAvailable {mask : Nat} {bank : List Word} {w : Word}
    (av : AvailableWord mask bank w) : GateWordMono mask bank w :=
  ⟨w, 0, av, Or.inl rfl, Or.inr (by simp)⟩

def maskFlatF (mask word : Word) : Bool :=
  dagForceWord (word &&& mask) (fun v => v == 0 || v == mask)

theorem maskFlatF_eq (mask word : Word) : maskFlatF mask word = maskFlat mask word := by
  simp [maskFlatF, maskFlat, dagForceWordEq]

def flatCountF (mask : Word) (words : List Word) : Nat :=
  List.rec 0 (fun word _ count => if maskFlatF mask word then count + 1 else count) words

theorem flatCountF_eq (mask : Word) (words : List Word) : flatCountF mask words = flatCount mask words := by
  induction words with
  | nil => rfl
  | cons w ws ih =>
    change (if maskFlatF mask w then flatCountF mask ws + 1 else flatCountF mask ws) =
      (if maskFlat mask w then flatCount mask ws + 1 else flatCount mask ws)
    rw [maskFlatF_eq, ih]

def dagBoundHeaderOK (target : Word) (bound : Bound) : Bool :=
  let (mask, _, _, goal) := bound
  (target &&& mask) == goal && goal != 0 && goal != mask

abbrev DagLinkList := Nat → List (Nat × Nat × Nat)

def dagUnpackLinksGo (data width tokenBits destBits tokMask destMask : Nat) : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, pos =>
      dagForceWord (unpack data width pos) (fun code =>
        dagForceWord (code &&& tokMask) (fun tk =>
          dagForceWord ((code >>> tokenBits) &&& destMask) (fun ds =>
            dagForceWord (code >>> (tokenBits + destBits)) (fun au =>
              (tk, ds, au) :: dagUnpackLinksGo data width tokenBits destBits tokMask destMask n (pos + 1)))))

def dagExtractLinks (index data indexWidth sizeBits tokenBits destBits autoBits : Nat) : DagLinkList :=
  fun parent =>
    dagForceWord (unpack index indexWidth parent) (fun entry =>
      dagForceWord (entry &&& fullMask sizeBits) (fun size =>
        dagForceWord (entry >>> sizeBits) (fun offset =>
          dagUnpackLinksGo data (tokenBits + destBits + autoBits) tokenBits destBits
            (fullMask tokenBits) (fullMask destBits) size offset)))

def dagFindLink : List (Nat × Nat × Nat) → Nat → Option DagLink
  | [], _ => none
  | (tk, ds, au) :: rest, token =>
      if Nat.beq tk token then some (ds, au) else dagFindLink rest token

def dagForceLinkList (ls : List (Nat × Nat × Nat)) (cont : List (Nat × Nat × Nat) → Bool) : Bool :=
  (List.rec (motive := fun _ => (List (Nat × Nat × Nat) → Bool) → Bool) (fun k => k [])
    (fun e _ next k =>
      dagForceWord e.1 (fun tk =>
        dagForceWord e.2.1 (fun ds =>
          dagForceWord e.2.2 (fun au =>
            next (fun rest => k ((tk, ds, au) :: rest)))))) ls) cont

theorem dagForceLinkListEq (ls : List (Nat × Nat × Nat)) (cont : List (Nat × Nat × Nat) → Bool) :
    dagForceLinkList ls cont = cont ls := by
  induction ls generalizing cont with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨tk, ds, au⟩ := e
    change dagForceWord tk (fun tk' => dagForceWord ds (fun ds' => dagForceWord au (fun au' =>
      dagForceLinkList es (fun rest => cont ((tk', ds', au') :: rest))))) = _
    rw [dagForceWordEq, dagForceWordEq, dagForceWordEq, ih]

-- Fast 256-bit stride packing + pre-validated sample pairs + 7-bit dagHighest7!
def dagHighest7 (value : Word) : Nat :=
  (Nat.rec (motive := fun _ => Word → Nat → Nat) (fun _ offset => offset)
    (fun i next w offset =>
      let shift := 1 <<< i
      dagForceWord (w >>> shift) (fun upper =>
        if Nat.beq upper 0 then next w offset else next upper (offset + shift))) 7) value 0

def dagSamplePairOK (mask goal : Word) (code : Nat) : Bool :=
  let p := code &&& 511
  let n := code >>> 9
  goal.testBit p && mask.testBit n && !goal.testBit n && Nat.blt p 256 && Nat.blt n 256

def dagSampleValid (mask goal : Word) (sample : DagSample) : Bool :=
  treeBlock 0 sample.2 (fun k => dagSamplePairOK mask goal (unpack sample.1 18 k))

def dagPackWords256 (ws : List Word) : Word :=
  List.rec 0 (fun w _ tail => (w &&& fullMask 256) ||| (tail <<< 256)) ws

def dagLaneMarks256 (n : Nat) : Word :=
  Nat.rec 0 (fun _ more => 1 ||| (more <<< 256)) n

def dagOmitted256 (aBit bBit : Word) (left right : Bool) : Word :=
  (if left then 0 else aBit) ||| (if right then 0 else bBit)

theorem dagPackBits256 {ws : List Word} {i row : Nat} (inside : i < ws.length) (width : row < 256) :
    (dagPackWords256 ws).testBit (256 * i + row) = (ws.getD i 0).testBit row := by
  induction ws generalizing i with
  | nil => simp at inside
  | cons w ws ih =>
    change ((w &&& fullMask 256) ||| (dagPackWords256 ws <<< 256)).testBit (256 * i + row) = _
    rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft]
    cases i with
    | zero =>
      rw [fullMask, Nat.testBit_two_pow_sub_one]
      simp [width, Nat.not_le.mpr width]
    | succ i =>
      have hi : i < ws.length := by simpa using inside
      have crossed : 256 ≤ 256 * i.succ + row := by omega
      have offset : 256 * i.succ + row - 256 = 256 * i + row := by omega
      have past : ¬ 256 * i.succ + row < 256 := by omega
      rw [fullMask, Nat.testBit_two_pow_sub_one]
      simp [crossed, offset, past, ih hi]

theorem dagMarkBits256 {length i : Nat} (inside : i < length) :
    (dagLaneMarks256 length).testBit (256 * i) = true := by
  induction length generalizing i with
  | zero => omega
  | succ length ih =>
    change (1 ||| (dagLaneMarks256 length <<< 256)).testBit (256 * i) = true
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp
    | succ i =>
      have hi : i < length := by omega
      have crossed : 256 ≤ 256 * i.succ := by omega
      have offset : 256 * i.succ - 256 = 256 * i := by omega
      simp [crossed, offset, ih hi]

def dagPackedPair256 (packed marks erased out : Word) (directed : Bool) (code : Nat) : Bool :=
  dagForceWord (code &&& 511) (fun p =>
    dagForceWord (code >>> 9) (fun n =>
      let gateOK := if directed then !out.testBit p || out.testBit n else out.testBit p == out.testBit n
      gateOK &&
        dagForceWord ((packed >>> p) &&& marks) (fun up =>
          dagForceWord ((packed >>> n) &&& marks) (fun down =>
            let contrast := if directed then up &&& (down ^^^ marks) else up ^^^ down
            Nat.beq (contrast &&& (marks ^^^ erased)) 0))))

theorem dagPackedPair256Sound {mask goal out : Word} {ws : List Word} {directed : Bool}
    {code a b : Nat} {left right : Bool}
    (nd : ws.Nodup) (pairOK : dagSamplePairOK mask goal code = true)
    (checked : dagPackedPair256 (dagPackWords256 ws) (dagLaneMarks256 ws.length)
      (dagOmitted256 (1 <<< (256 * a)) (1 <<< (256 * b)) left right) out directed code = true) :
    dagPairReject mask goal directed
      (out :: keepWord right (ws.getD b 0) (keepWord left (ws.getD a 0) ws)) [code] = true := by
  apply List.any_eq_true.mpr
  refine ⟨code, List.mem_cons_self, ?_⟩
  simp only [dagSamplePairOK, Bool.and_eq_true, Nat.blt_eq] at pairOK
  obtain ⟨⟨⟨⟨hp, hn⟩, neg⟩, wp⟩, wn⟩ := pairOK
  simp only [dagPackedPair256, dagForceWordEq, Bool.and_eq_true] at checked
  obtain ⟨output, closure⟩ := checked
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨
    Bool.and_eq_true_iff.mpr ⟨hp, hn⟩, neg⟩, List.all_eq_true.mpr ?_⟩
  intro w hw
  rcases List.mem_cons.mp hw with rfl | later
  · exact output
  have rightMem := dagKeepMem (dagKeepNodup nd left (ws.getD a 0)) later
  have leftMem := dagKeepMem nd rightMem.1
  obtain ⟨i, inside, eq⟩ := List.mem_iff_getElem.mp leftMem.1
  have atIndex : ws.getD i 0 = w := by
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside] using eq
  have omitted : (dagOmitted256 (1 <<< (256 * a)) (1 <<< (256 * b)) left right).testBit (256 * i) = false := by
    have cleared (j : Nat) (keep : Bool) (h : keep = true ∨ w ≠ ws.getD j 0) :
        (if keep then 0 else 1 <<< (256 * j)).testBit (256 * i) = false := by
      rcases h with yes | diff
      · simp [yes]
      · have ne : i ≠ j := fun same => diff (same ▸ atIndex).symm
        cases keep <;> simp [Nat.shiftLeft_eq, Nat.testBit_two_pow, show 256 * j ≠ 256 * i by omega]
    simp [dagOmitted256, Nat.testBit_or, cleared a left leftMem.2, cleared b right rightMem.2]
  let p := code &&& 511
  let n := code >>> 9
  let marks := dagLaneMarks256 ws.length
  let signal := dagPackWords256 ws
  have mark : marks.testBit (256 * i) = true := dagMarkBits256 inside
  have test {j : Nat} (within : j < 256) :
      ((signal >>> j) &&& marks).testBit (256 * i) = w.testBit j := by
    rw [Nat.testBit_and, Nat.testBit_shiftRight, mark, Bool.and_true,
      Nat.add_comm j, dagPackBits256 inside within, atIndex]
  have h := congrArg (fun word => Nat.testBit word (256 * i)) (Nat.beq_eq.mp closure)
  simp only [Nat.zero_testBit] at h
  change (((if directed then (signal >>> p &&& marks) &&& ((signal >>> n &&& marks) ^^^ marks)
      else (signal >>> p &&& marks) ^^^ (signal >>> n &&& marks)) &&&
    (marks ^^^ dagOmitted256 (1 <<< (256 * a)) (1 <<< (256 * b)) left right)).testBit (256 * i)) = false at h
  have pt := test (j := p) wp
  have nt := test (j := n) wn
  cases directed <;> cases px : w.testBit p <;> cases nx : w.testBit n <;>
    simp [px, nx, pt, nt, Nat.testBit_and, Nat.testBit_xor, mark, omitted, p, n] at h ⊢

def dagSampleKill256 (sample : DagSample) (full : Word) (counts : DagCounts)
    (xC yC outC packed marks aBit bBit out : Word) (directed ka kb : Bool) : Bool :=
  let dx := if ka then 0 else xC
  let dy := if kb then 0 else yC
  let rest := counts.2.2 ||| (counts.2.1 ^^^ (counts.2.1 &&& dx &&& dy)) |||
    (counts.1 ^^^ (counts.1 &&& (dx ||| dy)))
  dagForceWord ((rest ||| outC) ^^^ full) (fun missing =>
    if Nat.beq missing 0 then false
    else dagForceWord (dagHighest7 missing) (fun idx =>
      if Nat.blt idx sample.2 then
        dagForceWord (unpack sample.1 18 idx) (fun code =>
          dagPackedPair256 packed marks (dagOmitted256 aBit bBit ka kb) out directed code)
      else false))

def dagNodeBoundsGo (bounds : Array Bound) (dataPacked cutBits : Nat) : Nat → Nat → List Bound
  | 0, _ => []
  | n + 1, pos =>
      match bounds[unpack dataPacked cutBits pos]? with
      | none => dagNodeBoundsGo bounds dataPacked cutBits n (pos + 1)
      | some b => b :: dagNodeBoundsGo bounds dataPacked cutBits n (pos + 1)

theorem dagNodeBoundsGo_mem {bounds : Array Bound} {dataPacked cutBits : Nat} :
    ∀ cnt off b, b ∈ dagNodeBoundsGo bounds dataPacked cutBits cnt off → b ∈ bounds.toList := by
  intro cnt
  induction cnt with
  | zero => intro _ _ h; cases h
  | succ n ih =>
    intro off b h
    unfold dagNodeBoundsGo at h
    split at h
    · exact ih _ _ h
    next x hx =>
      rcases List.mem_cons.mp h with rfl | h
      · exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hx)
      · exact ih _ _ h

def dagNodeBounds (bounds : Array Bound) (idxPacked dataPacked indexWidth sizeBits cutBits i : Nat) : List Bound :=
  let entry := unpack idxPacked indexWidth i
  dagNodeBoundsGo bounds dataPacked cutBits (entry &&& fullMask sizeBits) (entry >>> sizeBits)

theorem dagNodeBounds_mem {bounds : Array Bound} {idxPacked dataPacked indexWidth sizeBits cutBits i : Nat} :
    ∀ b ∈ dagNodeBounds bounds idxPacked dataPacked indexWidth sizeBits cutBits i, b ∈ bounds.toList :=
  fun b h => dagNodeBoundsGo_mem _ _ b h

def normWord (mask w : Word) : Word :=
  if w < mask ^^^ w then w else mask ^^^ w

theorem xor_cancel_left (mask w : Word) : mask ^^^ (mask ^^^ w) = w := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem normWord_symm (mask w : Word) : normWord mask (mask ^^^ w) = normWord mask w := by
  unfold normWord
  rw [xor_cancel_left]
  by_cases h : w < mask ^^^ w
  · have h' : ¬(mask ^^^ w < w) := Nat.lt_asymm h
    simp [h, h']
  · by_cases h' : mask ^^^ w < w
    · simp [h, h']
    · have eq : w = mask ^^^ w := Nat.le_antisymm (Nat.le_of_not_lt h') (Nat.le_of_not_lt h)
      rw [if_neg h', if_neg h]; exact eq

theorem normWord_eq_or (mask w : Word) : normWord mask w = w ∨ normWord mask w = mask ^^^ w := by
  unfold normWord; split <;> simp

theorem normWord_idem (mask w : Word) : normWord mask (normWord mask w) = normWord mask w := by
  rcases normWord_eq_or mask w with h | h
  · rw [h, h]
  · rw [h, normWord_symm, h]

theorem normWord_zero (mask : Word) : normWord mask 0 = 0 := by
  unfold normWord
  rw [Nat.xor_zero]
  by_cases h : 0 < mask
  · rw [if_pos h]
  · have hm : mask = 0 := Nat.eq_zero_of_not_pos h
    rw [hm]; rfl

theorem normWord_mask (mask : Word) : normWord mask mask = 0 := by
  have h : normWord mask (mask ^^^ 0) = normWord mask 0 := normWord_symm mask 0
  rwa [Nat.xor_zero, normWord_zero] at h

theorem masked_xor {mask w : Word} (hw : Masked mask w) : Masked mask (mask ^^^ w) := by
  apply Nat.eq_of_testBit_eq; intro i
  have bit := congrArg (fun n : Nat => n.testBit i) hw
  simp only [Nat.testBit_and, Nat.testBit_xor] at bit ⊢
  cases hm : mask.testBit i <;> simp_all

theorem masked_norm {mask w : Word} (hw : Masked mask w) : Masked mask (normWord mask w) := by
  rcases normWord_eq_or mask w with h | h
  · rw [h]; exact hw
  · rw [h]; exact masked_xor hw

theorem proper_xor {mask w : Word} (hp : properWord mask w) : properWord mask (mask ^^^ w) := by
  refine ⟨?_, ?_⟩
  · intro h
    have := congrArg (fun x => mask ^^^ x) h
    rw [xor_cancel_left, Nat.xor_zero] at this
    exact hp.2 this
  · intro h
    have := congrArg (fun x => mask ^^^ x) h
    rw [xor_cancel_left, Nat.xor_self] at this
    exact hp.1 this

theorem proper_norm {mask w : Word} (hp : properWord mask w) : properWord mask (normWord mask w) := by
  rcases normWord_eq_or mask w with h | h
  · rw [h]; exact hp
  · rw [h]; exact proper_xor hp

theorem demorgan_and {mask a b : Word} (ma : Masked mask a) (mb : Masked mask b) :
    mask ^^^ (a &&& b) = (mask ^^^ a) ||| (mask ^^^ b) := by
  apply Nat.eq_of_testBit_eq; intro i
  have ba := congrArg (fun n : Nat => n.testBit i) ma
  have bb := congrArg (fun n : Nat => n.testBit i) mb
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] at ba bb ⊢
  cases hm : mask.testBit i <;> cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

theorem demorgan_or {mask a b : Word} (ma : Masked mask a) (mb : Masked mask b) :
    mask ^^^ (a ||| b) = (mask ^^^ a) &&& (mask ^^^ b) := by
  apply Nat.eq_of_testBit_eq; intro i
  have ba := congrArg (fun n : Nat => n.testBit i) ma
  have bb := congrArg (fun n : Nat => n.testBit i) mb
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] at ba bb ⊢
  cases hm : mask.testBit i <;> cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

theorem masked_and_self_xor {mask a : Word} (ma : Masked mask a) : a &&& (mask ^^^ a) = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  have ba := congrArg (fun n : Nat => n.testBit i) ma
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at ba ⊢
  cases hm : mask.testBit i <;> cases ha : a.testBit i <;> simp_all

theorem masked_or_self_xor {mask a : Word} (ma : Masked mask a) : a ||| (mask ^^^ a) = mask := by
  apply Nat.eq_of_testBit_eq; intro i
  have ba := congrArg (fun n : Nat => n.testBit i) ma
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] at ba ⊢
  cases hm : mask.testBit i <;> cases ha : a.testBit i <;> simp_all

theorem masked_or_mask {mask a : Word} (ma : Masked mask a) : a ||| mask = mask := by
  apply Nat.eq_of_testBit_eq; intro i
  have ba := congrArg (fun n : Nat => n.testBit i) ma
  simp only [Nat.testBit_and, Nat.testBit_or] at ba ⊢
  cases hm : mask.testBit i <;> cases ha : a.testBit i <;> simp_all

def AvBin (mask : Word) (bank : List Word) (w : Word) : Prop :=
  w = 0 ∨ w = mask ∨ w ∈ bank ∨ (mask ^^^ w) ∈ bank

theorem avBin_not {mask : Word} {bank : List Word} {w : Word}
    (h : AvBin mask bank w) : AvBin mask bank (mask ^^^ w) := by
  rcases h with rfl | hmask | hm | hm
  · exact Or.inr (Or.inl (Nat.xor_zero mask))
  · rw [hmask]; exact Or.inl (Nat.xor_self mask)
  · exact Or.inr (Or.inr (Or.inr (by rwa [xor_cancel_left])))
  · exact Or.inr (Or.inr (Or.inl hm))

theorem avBin_weaken {mask : Word} {small big : List Word} {w : Word}
    (sub : ∀ x ∈ small, AvBin mask big x) (av : AvBin mask small w) : AvBin mask big w := by
  rcases av with rfl | rfl | h | h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact sub w h
  · simpa [xor_cancel_left] using avBin_not (sub (mask ^^^ w) h)

theorem avBin_of_av {mask : Word} {bank : List Word} {w : Word}
    (h : AvailableWord mask bank w) : AvBin mask bank w := by
  rcases h with rfl | rfl | hm
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl hm))

theorem masked_avBin {mask : Word} {bank : List Word} {w : Word}
    (all : ∀ x ∈ bank, Masked mask x) (av : AvBin mask bank w) : Masked mask w := by
  rcases av with rfl | rfl | hm | hm
  · simp [Masked]
  · simp [Masked]
  · exact all _ hm
  · simpa [xor_cancel_left] using masked_xor (all _ hm)

def GateBin (mask : Word) (bank : List Word) (out : Word) : Prop :=
  ∃ a b, AvBin mask bank a ∧ AvBin mask bank b ∧ (out = a &&& b ∨ out = a ||| b)

theorem gateBin_weaken {mask : Word} {small big : List Word} {out : Word}
    (sub : ∀ x ∈ small, AvBin mask big x) (g : GateBin mask small out) : GateBin mask big out := by
  rcases g with ⟨a, b, ha, hb, eq⟩
  exact ⟨a, b, avBin_weaken sub ha, avBin_weaken sub hb, eq⟩

theorem masked_gateBin {mask : Word} {bank : List Word} {out : Word}
    (all : ∀ x ∈ bank, Masked mask x) (g : GateBin mask bank out) : Masked mask out := by
  rcases g with ⟨a, b, ha, hb, rfl | rfl⟩
  · have ma := masked_avBin all ha; have mb := masked_avBin all hb
    simp only [Masked] at ma mb ⊢; rw [Nat.land_assoc, mb]
  · have ma := masked_avBin all ha; have mb := masked_avBin all hb
    apply Nat.eq_of_testBit_eq; intro i
    have ba := congrArg (fun n : Nat => n.testBit i) ma
    have bb := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and, Nat.testBit_or] at ba bb ⊢
    cases hm : mask.testBit i <;> simp_all

def WordBuildsBin (mask : Word) (roots : List Word) : List Word → Prop
  | [] => True
  | w :: ws => GateBin mask roots w ∧ WordBuildsBin mask (w :: roots) ws

def BinLower (mask : Word) (roots : List Word) (target : Word) (minimum : Nat) : Prop :=
  ∀ values, WordBuildsBin mask roots values →
    AvBin mask (values ++ roots) target → minimum ≤ values.length

theorem buildsBin_weaken {mask : Word} {small big values : List Word}
    (supply : ∀ w ∈ small, AvBin mask big w) (build : WordBuildsBin mask small values) :
    WordBuildsBin mask big values := by
  induction values generalizing small big with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gateBin_weaken supply build.1, ih ?_ build.2⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
    · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hx)))) (supply _ hw)

theorem buildsBin_append {mask : Word} {roots first second : List Word}
    (left : WordBuildsBin mask roots first)
    (right : WordBuildsBin mask (first ++ roots) second) :
    WordBuildsBin mask roots (first ++ second) := by
  induction first generalizing roots with
  | nil => exact right
  | cons w ws ih =>
    refine ⟨left.1, ih left.2 ?_⟩
    exact buildsBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (by
      simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hx)))) right

-- Bridge: BinLower automatically implies Lower!
def binOp4 (mask : Word) (op : Nat) (a b : Word) : Word :=
  if op == 0 then a &&& b
  else if op == 1 then a ||| b
  else if op == 2 then a &&& (mask ^^^ b)
  else (mask ^^^ a) &&& b

def normBinOp4 (mask : Word) (op : Nat) (a b : Word) : Word :=
  normWord mask (binOp4 mask op a b)

def swapOp4 (op : Nat) : Nat :=
  if op == 2 then 3 else if op == 3 then 2 else op

theorem swapOp4_lt {op : Nat} (h : op < 4) : swapOp4 op < 4 := by
  unfold swapOp4
  split
  · decide
  · split
    · decide
    · exact h

theorem binOp4_swap (mask : Word) {op : Nat} (hop : op < 4) (a b : Word) :
    binOp4 mask (swapOp4 op) b a = binOp4 mask op a b := by
  have : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;>
    simp [binOp4, swapOp4, Nat.land_comm, Nat.lor_comm]

theorem normBinOp4_swap (mask : Word) {op : Nat} (hop : op < 4) (a b : Word) :
    normBinOp4 mask (swapOp4 op) b a = normBinOp4 mask op a b := by
  unfold normBinOp4; rw [binOp4_swap mask hop]

theorem gateBin_normBinOp4 {mask : Word} {bank : List Word} {op : Nat} {a b : Word}
    (hop : op < 4) (ma : Masked mask a) (mb : Masked mask b)
    (ha : AvBin mask bank a) (hb : AvBin mask bank b) :
    GateBin mask bank (normBinOp4 mask op a b) := by
  have hna := avBin_not ha
  have hnb := avBin_not hb
  have mna := masked_xor ma
  have mnb := masked_xor mb
  have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
  unfold normBinOp4
  rcases normWord_eq_or mask (binOp4 mask op a b) with heq | heq
  · rw [heq]
    rcases hcase with rfl | rfl | rfl | rfl
    · exact ⟨a, b, ha, hb, Or.inl rfl⟩
    · exact ⟨a, b, ha, hb, Or.inr rfl⟩
    · exact ⟨a, mask ^^^ b, ha, hnb, Or.inl rfl⟩
    · exact ⟨mask ^^^ a, b, hna, hb, Or.inl rfl⟩
  · rw [heq]
    rcases hcase with rfl | rfl | rfl | rfl
    · exact ⟨mask ^^^ a, mask ^^^ b, hna, hnb, Or.inr (demorgan_and ma mb)⟩
    · exact ⟨mask ^^^ a, mask ^^^ b, hna, hnb, Or.inl (demorgan_or ma mb)⟩
    · refine ⟨mask ^^^ a, b, hna, hb, Or.inr ?_⟩
      change mask ^^^ (a &&& (mask ^^^ b)) = (mask ^^^ a) ||| b
      rw [demorgan_and ma mnb, xor_cancel_left]
    · refine ⟨a, mask ^^^ b, ha, hnb, Or.inr ?_⟩
      change mask ^^^ ((mask ^^^ a) &&& b) = a ||| (mask ^^^ b)
      rw [demorgan_and mna mb, xor_cancel_left]

def LiveBin (mask target : Word) : Nat → Finset Word → Prop
  | 0, S => S = {normWord mask target} ∧ properWord mask target
  | k + 1, S =>
    ∃ (U : Finset Word) (a b : Word) (op : Nat),
      op < 4 ∧ S = insert a (insert b U) ∧
      properWord mask a ∧ properWord mask b ∧ a ≠ b ∧
      normWord mask a = a ∧ normWord mask b = b ∧
      normBinOp4 mask op a b ∉ insert a (insert b U) ∧
      LiveBin mask target k (insert (normBinOp4 mask op a b) U)

theorem LiveBin.stop {mask target : Word} (hp : properWord mask target) :
    LiveBin mask target 0 {normWord mask target} := ⟨rfl, hp⟩

theorem LiveBin.step {mask target : Word} {k : Nat} {U : Finset Word} {a b : Word} {op : Nat}
    (hop : op < 4) (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
    (na : normWord mask a = a) (nb : normWord mask b = b)
    (hfresh : normBinOp4 mask op a b ∉ insert a (insert b U))
    (tail : LiveBin mask target k (insert (normBinOp4 mask op a b) U)) :
    LiveBin mask target (k + 1) (insert a (insert b U)) :=
  ⟨U, a, b, op, hop, rfl, ha, hb, hab, na, nb, hfresh, tail⟩

theorem LiveBin.ind {mask target : Word}
    {motive : ∀ (k : Nat) (S : Finset Word), LiveBin mask target k S → Prop}
    (stop : ∀ (hp : properWord mask target), motive 0 {normWord mask target} (LiveBin.stop hp))
    (step : ∀ {k : Nat} {U : Finset Word} {a b : Word} {op : Nat}
      (hop : op < 4) (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
      (na : normWord mask a = a) (nb : normWord mask b = b)
      (hfresh : normBinOp4 mask op a b ∉ insert a (insert b U))
      (tail : LiveBin mask target k (insert (normBinOp4 mask op a b) U)),
      motive k (insert (normBinOp4 mask op a b) U) tail →
      motive (k + 1) (insert a (insert b U)) (LiveBin.step hop ha hb hab na nb hfresh tail))
    {k : Nat} {S : Finset Word} (h : LiveBin mask target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U, a, b, op, hop, rfl, ha, hb, hab, na, nb, hf, tail⟩ := h
    exact step hop ha hb hab na nb hf tail (ih tail)

theorem liveBinProps {mask target : Word} {k : Nat} {S : Finset Word}
    (h : LiveBin mask target k S) : ∀ a ∈ S, properWord mask a ∧ normWord mask a = a := by
  induction h using LiveBin.ind with
  | stop hp =>
    intro a ha
    rw [Finset.mem_singleton.mp ha]
    exact ⟨proper_norm hp, normWord_idem mask target⟩
  | step hop ha hb hab na nb hf tail ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨⟨ha, na⟩, ⟨hb, nb⟩, fun w hw => ih w (Finset.mem_insert_of_mem hw)⟩

theorem liveBinSize {mask target : Word} {k : Nat} {S : Finset Word}
    (h : LiveBin mask target k S) : S.card ≤ k + 1 := by
  induction h using LiveBin.ind with
  | stop => simp
  | @step k U a b op hop ha hb hab na nb hf tail ih =>
    have hu : normBinOp4 mask op a b ∉ U := fun hm =>
      hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    omega

def binWitness (mask : Word) (nws : List Word) (w : Word) : Prop :=
  ∃ op a b, op < 4 ∧ a ∈ nws ∧ b ∈ nws ∧ properWord mask a ∧ properWord mask b ∧
    normWord mask a = a ∧ normWord mask b = b ∧ a ≠ b ∧ w = normBinOp4 mask op a b

theorem classifyGateBin {mask : Word} {bank : List Word} {out : Word}
    (all : ∀ w ∈ bank, Masked mask w) (g : GateBin mask bank out) :
    wordRep mask (bank.map (normWord mask)) (normWord mask out) ∨
    binWitness mask (bank.map (normWord mask)) (normWord mask out) := by
  let nbank := bank.map (normWord mask)
  have c0 : wordRep mask nbank 0 := Or.inr fun h => h.1 rfl
  have cnorm (x : Word) (hx : AvBin mask bank x) :
      x = 0 ∨ x = mask ∨ (normWord mask x ∈ nbank ∧ properWord mask (normWord mask x)) := by
    by_cases hz : x = 0
    · exact Or.inl hz
    by_cases hm : x = mask
    · exact Or.inr (Or.inl hm)
    have hp : properWord mask x := ⟨hz, hm⟩
    refine Or.inr (Or.inr ⟨?_, proper_norm hp⟩)
    rcases (hx.resolve_left hz).resolve_left hm with hmem | hmem
    · exact List.mem_map_of_mem hmem
    · rw [← normWord_symm]; exact List.mem_map_of_mem hmem
  rcases g with ⟨a, b, ha, hb, eq⟩
  have ma := masked_avBin all ha
  have mb := masked_avBin all hb
  have trivial_word (w : Word) (hw : AvBin mask bank w) : wordRep mask nbank (normWord mask w) := by
    rcases cnorm w hw with rfl | rfl | ⟨hm, _⟩
    · rw [normWord_zero]; exact c0
    · rw [normWord_mask]; exact c0
    · exact Or.inl hm
  rcases cnorm a ha with rfl | rfl | ⟨hma, pa⟩
  · rcases eq with rfl | rfl
    · simp only [Nat.zero_and, normWord_zero]; exact Or.inl c0
    · simp only [Nat.zero_or]; exact Or.inl (trivial_word b hb)
  · rcases eq with rfl | rfl
    · rw [Nat.land_comm, mb]; exact Or.inl (trivial_word b hb)
    · rw [Nat.lor_comm, masked_or_mask mb, normWord_mask]; exact Or.inl c0
  rcases cnorm b hb with rfl | rfl | ⟨hmb, pb⟩
  · rcases eq with rfl | rfl
    · simp only [Nat.and_zero, normWord_zero]; exact Or.inl c0
    · simp only [Nat.or_zero]; exact Or.inl (trivial_word a ha)
  · rcases eq with rfl | rfl
    · rw [ma]; exact Or.inl (trivial_word a ha)
    · rw [masked_or_mask ma, normWord_mask]; exact Or.inl c0
  let na := normWord mask a
  let nb := normWord mask b
  have mna : Masked mask na := masked_norm ma
  have mnb : Masked mask nb := masked_norm mb
  by_cases same : na = nb
  · have hrel : b = a ∨ b = mask ^^^ a := by
      rcases normWord_eq_or mask a with ea | ea <;> rcases normWord_eq_or mask b with eb | eb
      · left; exact eb.symm.trans (same.symm.trans ea)
      · right
        have h1 : a = mask ^^^ b := ea.symm.trans (same.trans eb)
        have := congrArg (fun z => mask ^^^ z) h1
        rw [xor_cancel_left] at this; exact this.symm
      · right; exact eb.symm.trans (same.symm.trans ea)
      · left
        have h1 : mask ^^^ a = mask ^^^ b := ea.symm.trans (same.trans eb)
        have := congrArg (fun z => mask ^^^ z) h1
        rw [xor_cancel_left, xor_cancel_left] at this; exact this.symm
    rcases hrel with rfl | rfl <;> rcases eq with rfl | rfl
    · rw [Nat.and_self]; exact Or.inl (Or.inl hma)
    · rw [Nat.or_self]; exact Or.inl (Or.inl hma)
    · rw [masked_and_self_xor ma, normWord_zero]; exact Or.inl c0
    · rw [masked_or_self_xor ma, normWord_mask]; exact Or.inl c0
  -- General case: na ≠ nb, map all 8 sign/op combinations to op ∈ {0,1,2,3}!
  have ea : a = na ∨ a = mask ^^^ na := by
    rcases normWord_eq_or mask a with h | h
    · exact Or.inl h.symm
    · right; have := congrArg (fun z => mask ^^^ z) h; rw [xor_cancel_left] at this; exact this.symm
  have eb : b = nb ∨ b = mask ^^^ nb := by
    rcases normWord_eq_or mask b with h | h
    · exact Or.inl h.symm
    · right; have := congrArg (fun z => mask ^^^ z) h; rw [xor_cancel_left] at this; exact this.symm
  have mkWit (op : Nat) (hop : op < 4) (heq : normWord mask out = normBinOp4 mask op na nb) :
      binWitness mask nbank (normWord mask out) :=
    ⟨op, na, nb, hop, hma, hmb, pa, pb, normWord_idem mask a, normWord_idem mask b, same, heq⟩
  right
  rcases eq with hout | hout <;> rcases ea with hea | hea <;> rcases eb with heb | heb
  · exact mkWit 0 (by decide) (by rw [hout, hea, heb]; rfl)
  · exact mkWit 2 (by decide) (by rw [hout, hea, heb]; rfl)
  · exact mkWit 3 (by decide) (by rw [hout, hea, heb]; rfl)
  · exact mkWit 1 (by decide) (by rw [hout, hea, heb, ← demorgan_or mna mnb, normWord_symm]; rfl)
  · exact mkWit 1 (by decide) (by rw [hout, hea, heb]; rfl)
  · exact mkWit 3 (by decide) (by
      have h1 : mask ^^^ ((mask ^^^ na) &&& nb) = na ||| (mask ^^^ nb) := by
        rw [demorgan_and (masked_xor mna) mnb, xor_cancel_left]
      rw [hout, hea, heb, ← h1, normWord_symm]; rfl)
  · exact mkWit 2 (by decide) (by
      have h1 : mask ^^^ (na &&& (mask ^^^ nb)) = (mask ^^^ na) ||| nb := by
        rw [demorgan_and mna (masked_xor mnb), xor_cancel_left]
      rw [hout, hea, heb, ← h1, normWord_symm]; rfl)
  · exact mkWit 0 (by decide) (by rw [hout, hea, heb, ← demorgan_and mna mnb, normWord_symm]; rfl)

theorem pullBin {mask target : Word} {nws : List Word} {z : Word} {k : Nat} {S : Finset Word}
    (h : LiveBin mask target k S)
    (hz : wordRep mask nws z ∨ binWitness mask nws z) (sub : ∀ a ∈ S, a ∈ nws ++ [z]) :
    ∃ k' S', k' ≤ k + 1 ∧ LiveBin mask target k' S' ∧ ∀ a ∈ S', a ∈ nws := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ nws
    · refine ⟨k, S, by omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ nws ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := (liveBinProps h z hm).1
      rcases hz with hr | ⟨op, a, b, hop, ha, hb, pa, pb, na, nb, hab, eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (normBinOp4 mask op a b)
        have ht : LiveBin mask target k (insert (normBinOp4 mask op a b) U) := by
          simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ nws := by
          intro v hv
          obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hmem
        have hf : normBinOp4 mask op a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨k + 1, insert a (insert b U), Nat.le_refl _,
          LiveBin.step hop pa pb hab na nb hf ht, by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, S, by omega, h, ?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

theorem extractBinLive {mask target : Word} {roots values : List Word}
    (all : ∀ w ∈ roots, Masked mask w) (builds : WordBuildsBin mask roots values)
    (hit : AvBin mask (values ++ roots) target) (p : properWord mask target) :
    ∃ k S, k ≤ values.length ∧ LiveBin mask target k S ∧ ∀ w ∈ S, w ∈ roots.map (normWord mask) := by
  have hm : normWord mask target ∈ (values ++ roots).map (normWord mask) := by
    rcases (hit.resolve_left p.1).resolve_left p.2 with hmem | hmem
    · exact List.mem_map_of_mem hmem
    · rw [← normWord_symm]; exact List.mem_map_of_mem hmem
  induction values generalizing roots with
  | nil =>
    exact ⟨0, {normWord mask target}, Nat.zero_le _, LiveBin.stop p, by simpa using hm⟩
  | cons w ws ih =>
    have next : ∀ v ∈ w :: roots, Masked mask v := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact masked_gateBin all builds.1
      · exact all _ hv
    have ht : AvBin mask (ws ++ w :: roots) target := by
      rcases hit with rfl | rfl | hmem | hmem
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl (by simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hmem)))
      · exact Or.inr (Or.inr (Or.inr (by simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hmem)))
    have hm' : normWord mask target ∈ (ws ++ w :: roots).map (normWord mask) := by
      rcases (ht.resolve_left p.1).resolve_left p.2 with hmem | hmem
      · exact List.mem_map_of_mem hmem
      · rw [← normWord_symm]; exact List.mem_map_of_mem hmem
    obtain ⟨k, S, hk, live, sub⟩ := ih next builds.2 ht hm'
    have available : ∀ v ∈ S, v ∈ roots.map (normWord mask) ++ [normWord mask w] := by
      intro v h
      simpa [List.map_cons, or_comm] using sub v h
    obtain ⟨k', S', hk', hl, hsub⟩ := pullBin live (classifyGateBin all builds.1) available
    exact ⟨k', S', by simp only [List.length_cons]; omega, hl, hsub⟩

-- Agreement & Partition lemmas for LiveBin
theorem agreesNorm {i j mask w : Word} (m : AgreesAt i j mask) (hw : AgreesAt i j w) :
    AgreesAt i j (normWord mask w) := by
  rcases normWord_eq_or mask w with h | h
  · rw [h]; exact hw
  · rw [h]; simp only [AgreesAt, Nat.testBit_xor] at m hw ⊢; rw [m, hw]

theorem liveBinAgrees {mask target : Word} {i j k : Nat} {S : Finset Word}
    (h : LiveBin mask target k S) (m : AgreesAt i j mask)
    (all : ∀ w ∈ S, AgreesAt i j w) : AgreesAt i j target := by
  induction h using LiveBin.ind with
  | stop =>
    have hn := all _ (Finset.mem_singleton_self _)
    rcases normWord_eq_or mask target with h | h
    · rwa [h] at hn
    · rw [h] at hn
      change mask.testBit i = mask.testBit j at m
      change (mask ^^^ target).testBit i = (mask ^^^ target).testBit j at hn
      rw [Nat.testBit_xor, Nat.testBit_xor, m] at hn
      change target.testBit i = target.testBit j
      cases hmj : mask.testBit j <;> cases hti : target.testBit i <;> cases htj : target.testBit j <;> simp_all
  | @step k U a b op hop pa pb hab na nb hf tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · unfold normBinOp4
      apply agreesNorm m
      have aa : a.testBit i = a.testBit j := all a (Finset.mem_insert_self _ _)
      have bb : b.testBit i = b.testBit j := all b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      have mm : mask.testBit i = mask.testBit j := m
      have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl <;>
        simp [binOp4, AgreesAt, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, aa, bb, mm]
    · exact all _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))

theorem dagPartitionLiveBin {mask goal : Word} {ws : List Word} {k : Nat}
    (goalMask : Masked mask goal) (live : LiveBin mask goal k ws.toFinset) :
    dagPartition false ws goal (mask ^^^ goal) = true := by
  by_contra fail
  have openPair : dagPartition false ws goal (mask ^^^ goal) = false := by
    cases h : dagPartition false ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p, n, hp, hn, agree⟩ := dagPartitionSound openPair
  have pm := positiveInMask goalMask hp
  have nm : mask.testBit n = true ∧ goal.testBit n = false := by
    rw [Nat.testBit_xor] at hn
    have implied := fun ht : goal.testBit n = true => positiveInMask goalMask ht
    cases hm : mask.testBit n <;> cases ht : goal.testBit n <;> simp_all
  have same := liveBinAgrees live (pm.trans nm.1.symm) (fun w hw => by
    simpa [AgreesAt] using agree w (List.mem_toFinset.mp hw))
  simp [AgreesAt, hp, nm.2] at same

theorem dagPairsOpenBin {mask goal : Word} {ws : List Word} {pairs : List Nat} {k : Nat}
    (masked : Masked mask goal) (live : LiveBin mask goal k ws.toFinset) :
    dagPairReject mask goal false ws pairs = false := by
  apply Bool.eq_false_iff.mpr
  intro close
  obtain ⟨code, _, check⟩ := List.any_eq_true.mp close
  simp only [Bool.and_eq_true, Bool.not_eq_true, List.all_eq_true] at check
  obtain ⟨⟨⟨hp, mn⟩, hn⟩, bank⟩ := check
  have neg : goal.testBit (code >>> 9) = false := by simpa using hn
  have h := liveBinAgrees live ((positiveInMask masked hp).trans mn.symm) (fun w hw => by
    have pair := bank _ (List.mem_toFinset.mp hw)
    simpa [AgreesAt] using pair)
  simp [AgreesAt, hp, neg] at h

-- Essential witnesses, essentialLowerBin, maskedBuildBin, essentialLiftBin, boundClosesBin

theorem essentialRequiredBin {mask target : Word} {stock : List Word} {entry : Witness}
    {S : Finset Word} {k : Nat}
    (ok : essentialB mask target stock entry = true)
    (sub : ∀ w ∈ S, w ∈ stock.map (normWord mask)) (live : LiveBin mask target k S) :
    normWord mask (witnessWord entry) ∈ S := by
  obtain ⟨w, p, n⟩ := entry
  simp only [essentialB, Bool.and_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨mp, mn⟩, tp⟩, tn⟩, unequal⟩, rest⟩ := ok
  by_contra no
  have all : ∀ x ∈ S, AgreesAt p n x := by
    intro x hx
    obtain ⟨orig, omem, rfl⟩ := List.mem_map.mp (sub x hx)
    have horig : orig ≠ w := fun e => no (by simpa [witnessWord, e] using hx)
    have h := List.all_eq_true.mp rest orig omem
    have hag : AgreesAt p n orig := by simpa [horig, AgreesAt] using h
    exact agreesNorm (mp.trans mn.symm) hag
  have agree := liveBinAgrees live (mp.trans mn.symm) all
  have falseBit : target.testBit n = false := by simpa using tn
  simp [AgreesAt, tp, falseBit] at agree

theorem essentialWordsInBin {mask target : Word} {stock : List Word} {witnesses : List Witness}
    {S : Finset Word} {k : Nat}
    (ok : witnesses.all (essentialB mask target stock) = true)
    (sub : ∀ w ∈ S, w ∈ stock.map (normWord mask)) (live : LiveBin mask target k S) :
    (witnesses.map (fun e => normWord mask (witnessWord e))).toFinset ⊆ S := by
  intro w hw
  obtain ⟨entry, mem, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
  exact essentialRequiredBin (List.all_eq_true.mp ok entry mem) sub live

def buildableBin (m g : Word) : Nat → Finset Word → Prop
  | 0, s => g ∈ s ∨ (m ^^^ g) ∈ s
  | n + 1, s => buildableBin m g n s ∨
      ∃ a b, (a ∈ s ∨ m ^^^ a ∈ s) ∧ (b ∈ s ∨ m ^^^ b ∈ s) ∧
        ∃ d : Bool, buildableBin m g n (insert (binWord d a b) s)

theorem supplyPoolBin {m g : Word} {n : Nat} {s q : Finset Word}
    (sub : ∀ w ∈ s, w ∈ q ∨ m ^^^ w ∈ q) (h : buildableBin m g n s) : buildableBin m g n q := by
  induction n generalizing s q with
  | zero =>
    rcases h with h1 | h1
    · exact sub g h1
    · rcases sub (m ^^^ g) h1 with h2 | h2
      · exact Or.inr h2
      · rw [xor_cancel_left] at h2; exact Or.inl h2
  | succ n ih =>
    have subPair {x : Word} (hx : x ∈ s ∨ m ^^^ x ∈ s) : x ∈ q ∨ m ^^^ x ∈ q := by
      rcases hx with h1 | h1
      · exact sub x h1
      · rcases sub (m ^^^ x) h1 with h2 | h2
        · exact Or.inr h2
        · rw [xor_cancel_left] at h2; exact Or.inl h2
    rcases h with h | ⟨a, b, ha, hb, d, h⟩
    · exact Or.inl (ih sub h)
    · refine Or.inr ⟨a, b, subPair ha, subPair hb, d, ih ?_ h⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact Or.inl (Finset.mem_insert_self _ _)
      · rcases sub w hw with hq | hq
        · exact Or.inl (Finset.mem_insert_of_mem hq)
        · exact Or.inr (Finset.mem_insert_of_mem hq)

theorem buildableBinWords {mask goal n : Nat} {pool : Finset Word} {bank : List Word}
    (h : buildableBin mask goal n pool) (supply : ∀ w ∈ pool, AvBin mask bank w) :
    ∃ values, values.length ≤ n ∧ WordBuildsBin mask bank values ∧
      AvBin mask (values ++ bank) goal := by
  induction n generalizing pool bank with
  | zero =>
    refine ⟨[], Nat.le_refl _, trivial, ?_⟩
    rcases h with h1 | h1
    · exact supply goal h1
    · simpa [xor_cancel_left] using avBin_not (supply _ h1)
  | succ n ih =>
    have supPair {w : Word} (hw : w ∈ pool ∨ mask ^^^ w ∈ pool) : AvBin mask bank w := by
      rcases hw with h1 | h1
      · exact supply w h1
      · simpa [xor_cancel_left] using avBin_not (supply _ h1)
    rcases h with h | ⟨a, b, ha, hb, d, h⟩
    · obtain ⟨values, cap, build, hit⟩ := ih h supply
      exact ⟨values, by omega, build, hit⟩
    · let w := binWord d a b
      have g : GateBin mask bank w :=
        ⟨a, b, supPair ha, supPair hb, by cases d <;> simp [w, binWord]⟩
      have growing : ∀ v ∈ insert w pool, AvBin mask (w :: bank) v := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
        · exact avBin_weaken (fun _ hh => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hh)))) (supply _ hv)
      obtain ⟨values, budget, build, hit⟩ := ih h growing
      refine ⟨w :: values, by simp only [List.length_cons]; omega, ⟨g, build⟩, ?_⟩
      exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (by
        simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto)))) hit

theorem cofBinOp4 {mask m : Word} (sub : mask &&& m = m) {op : Nat} (hop : op < 4) (a b : Word) :
    binOp4 mask op a b &&& m = binOp4 m op (a &&& m) (b &&& m) := by
  have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
  rcases hcase with rfl | rfl | rfl | rfl
  · exact cofBinary m a b false
  · exact cofBinary m a b true
  · change (a &&& (mask ^^^ b)) &&& m = (a &&& m) &&& (m ^^^ (b &&& m))
    rw [← cofNot sub b]; exact cofBinary m a (mask ^^^ b) false
  · change ((mask ^^^ a) &&& b) &&& m = (m ^^^ (a &&& m)) &&& (b &&& m)
    rw [← cofNot sub a]; exact cofBinary m (mask ^^^ a) b false

theorem flNorm {mask m : Word} (sub : mask &&& m = m) (a : Word) :
    maskedFlat m (normWord mask a) ↔ maskedFlat m a := by
  rcases normWord_eq_or mask a with h | h
  · rw [h]
  · rw [h]; exact flNot sub a

theorem flBothOp4 {mask m : Word} (sub : mask &&& m = m) {op : Nat} (hop : op < 4) {a b : Word}
    (ha : maskedFlat m a) (hb : maskedFlat m b) : maskedFlat m (normBinOp4 mask op a b) := by
  rw [normBinOp4, flNorm sub]
  unfold maskedFlat at *
  rw [cofBinOp4 sub hop]
  have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
  rcases hcase with rfl | rfl | rfl | rfl <;>
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [binOp4, ha, hb]

theorem simpleBinOp4 {mask m : Word} (sub : mask &&& m = m) {op : Nat} (hop : op < 4) {a b : Word}
    (h : maskedFlat m a ∨ maskedFlat m b) :
    binOp4 mask op a b &&& m = 0 ∨ binOp4 mask op a b &&& m = m ∨
    binOp4 mask op a b &&& m = a &&& m ∨ binOp4 mask op a b &&& m = m ^^^ (a &&& m) ∨
    binOp4 mask op a b &&& m = b &&& m ∨ binOp4 mask op a b &&& m = m ^^^ (b &&& m) := by
  rw [cofBinOp4 sub hop]
  have top1 (x : Word) : m &&& (x &&& m) = x &&& m := by
    rw [Nat.land_comm x m, ← Nat.land_assoc]; simp
  have top2 (x : Word) : m ||| (x &&& m) = m := by rw [Nat.lor_comm]; exact masked_or_mask (restrictWord m x)
  have top3 (x : Word) : (m ^^^ (x &&& m)) &&& m = m ^^^ (x &&& m) :=
    masked_xor (restrictWord m x)
  have right1 (x : Word) : (x &&& m) &&& m = x &&& m := restrictWord m x
  have right2 (x : Word) : (x &&& m) ||| m = m := by rw [Nat.lor_comm, top2]
  have right3 (x : Word) : m &&& (m ^^^ (x &&& m)) = m ^^^ (x &&& m) := by
    rw [Nat.land_comm]; exact top3 x
  have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
  rcases hcase with rfl | rfl | rfl | rfl <;> rcases h with (ha | ha) | (hb | hb) <;>
    simp [binOp4, *, top1, top2, top3, right1, right2, right3]

theorem maskedBuildBin {mask goal : Word} {k : Nat} {s : Finset Word}
    (run : LiveBin mask goal k s) (m : Word) (submask : mask &&& m = m)
    (properGoal : ¬ maskedFlat m goal) :
    ∃ n, n + (flatSet m s).card ≤ k ∧ buildableBin m (goal &&& m) n (projectedStock m s) := by
  induction run using LiveBin.ind with
  | stop =>
    refine ⟨0, ?_, ?_⟩
    · have pgn : ¬ maskedFlat m (normWord mask goal) := by rwa [flNorm submask]
      simp only [flatSet, Finset.filter_singleton, pgn, ite_false, Finset.card_empty,
        Nat.add_zero, Nat.le_refl]
    · rcases normWord_eq_or mask goal with h | h
      · left; simp [projectedStock, visibleWords, h]
      · right; rw [← cofNot submask goal, ← h]; simp [projectedStock, visibleWords]
  | @step k u a b op hop pa pb ab na nb fresh tail ih =>
    let v := normBinOp4 mask op a b
    obtain ⟨n, cap, built⟩ := ih
    have nn : v ∉ u := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    change n + (flatSet m (insert v u)).card ≤ k at cap
    rw [flIns nn] at cap
    have ca := flLe m a (insert b u)
    have cb := flLe m b u
    have hv_rel : v &&& m = binOp4 mask op a b &&& m ∨
        v &&& m = m ^^^ (binOp4 mask op a b &&& m) := by
      rcases normWord_eq_or mask (binOp4 mask op a b) with h | h
      · left; simp [v, normBinOp4, h]
      · right; simp [v, normBinOp4, h, cofNot submask]
    by_cases simple : maskedFlat m a ∨ maskedFlat m b
    · have budget : n + (flatSet m (insert a (insert b u))).card ≤ k + 1 := by
        by_cases fa : maskedFlat m a <;> by_cases fb : maskedFlat m b <;>
          simp only [fa, fb, ite_true, ite_false] at ca cb simple
        all_goals first | have vf : maskedFlat m v := flBothOp4 submask hop fa fb; simp only [vf, ite_true] at cap; omega | omega | tauto
      refine ⟨n, budget, supplyPoolBin ?_ built⟩
      intro w hw
      simp only [projectedStock, prIns, Finset.mem_insert] at hw ⊢
      rcases hw with rfl | rfl | rfl | h
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr (Or.inl rfl))
      · have sc := simpleBinOp4 submask hop simple
        rcases hv_rel with e | e <;> rw [e]
        · rcases sc with c | c | c | c | c | c <;> rw [c]
          · exact Or.inl (Or.inl rfl)
          · exact Or.inl (Or.inr (Or.inl rfl))
          · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          · exact Or.inr (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        · rcases sc with c | c | c | c | c | c <;> rw [c]
          · exact Or.inl (Or.inr (Or.inl (Nat.xor_zero m)))
          · exact Or.inl (Or.inl (Nat.xor_self m))
          · exact Or.inr (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inl (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          · exact Or.inl (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · have fa : ¬maskedFlat m a := fun h => simple (Or.inl h)
      have fb : ¬maskedFlat m b := fun h => simple (Or.inr h)
      simp only [fa, fb, ite_false] at ca cb
      have ha_in : a &&& m ∈ projectedStock m (insert a (insert b u)) := by simp [projectedStock, prIns]
      have hb_in : b &&& m ∈ projectedStock m (insert a (insert b u)) := by simp [projectedStock, prIns]
      have hna_in : m ^^^ (m ^^^ (a &&& m)) ∈ projectedStock m (insert a (insert b u)) := by
        rwa [xor_cancel_left]
      have hnb_in : m ^^^ (m ^^^ (b &&& m)) ∈ projectedStock m (insert a (insert b u)) := by
        rwa [xor_cancel_left]
      have mkStep {a' b' : Word} {d : Bool}
          (ha' : a' ∈ projectedStock m (insert a (insert b u)) ∨ m ^^^ a' ∈ projectedStock m (insert a (insert b u)))
          (hb' : b' ∈ projectedStock m (insert a (insert b u)) ∨ m ^^^ b' ∈ projectedStock m (insert a (insert b u)))
          (heq : binOp4 mask op a b &&& m = binWord d a' b') :
          ∃ n', n' + (flatSet m (insert a (insert b u))).card ≤ k + 1 ∧
            buildableBin m (goal &&& m) n' (projectedStock m (insert a (insert b u))) := by
        refine ⟨n + 1, by omega, Or.inr ⟨a', b', ha', hb', d, supplyPoolBin ?_ built⟩⟩
        intro w hw
        simp only [projectedStock, prIns, Finset.mem_insert] at hw ⊢
        rcases hw with rfl | rfl | rfl | h
        · exact Or.inl (Or.inr (Or.inl rfl))
        · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
        · rcases hv_rel with e | e
          · exact Or.inl (Or.inl (e.trans heq))
          · exact Or.inr (by rw [e, xor_cancel_left]; exact Or.inl heq)
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
      have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl
      · exact mkStep (d := false) (Or.inl ha_in) (Or.inl hb_in) (cofBinOp4 (op := 0) submask (by decide) a b)
      · exact mkStep (d := true) (Or.inl ha_in) (Or.inl hb_in) (cofBinOp4 (op := 1) submask (by decide) a b)
      · exact mkStep (d := false) (Or.inl ha_in) (Or.inr hnb_in) (cofBinOp4 (op := 2) submask (by decide) a b)
      · exact mkStep (d := false) (Or.inr hna_in) (Or.inl hb_in) (cofBinOp4 (op := 3) submask (by decide) a b)

theorem essentialLiftBin {mask target : Word} {stock cutStock : List Word} {witnesses : List Witness}
    {minimum cut prior : Nat}
    (proper : properWord mask target)
    (masked : ∀ w ∈ stock, Masked mask w)
    (ok : witnesses.all (essentialB mask target stock) = true)
    (submask : mask &&& cut = cut)
    (cutProper : properWord cut (target &&& cut))
    (supplies : ∀ w ∈ stock, AvBin cut cutStock (w &&& cut))
    (known : BinLower cut cutStock (target &&& cut) prior)
    (bound : minimum ≤ prior + (flatSet cut (witnesses.map (fun e => normWord mask (witnessWord e))).toFinset).card) :
    BinLower mask stock target minimum := by
  intro values build hit
  obtain ⟨k, S, hk, live, sub⟩ := extractBinLive masked build hit proper
  have subW := essentialWordsInBin ok sub live
  have subFlat : flatSet cut (witnesses.map (fun e => normWord mask (witnessWord e))).toFinset ⊆ flatSet cut S :=
    Finset.filter_subset_filter _ subW
  have card := Finset.card_le_card subFlat
  have pf : ¬maskedFlat cut target := by simpa [maskedFlat, properWord] using cutProper
  obtain ⟨n, budget, built⟩ := maskedBuildBin live cut submask pf
  have starts : ∀ w ∈ projectedStock cut S, AvBin cut cutStock w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image] at hw
    rcases hw with rfl | rfl | ⟨x, hx, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · obtain ⟨orig, omem, rfl⟩ := List.mem_map.mp (sub x hx)
      rcases normWord_eq_or mask orig with e | e
      · rw [e]; exact supplies _ omem
      · rw [e, cofNot submask]; exact avBin_not (supplies _ omem)
  obtain ⟨ys, len, built', out⟩ := buildableBinWords built starts
  have lower := known ys built' out
  omega

def normWordFast (mask w : Word) : Word :=
  dagForceWord (mask ^^^ w) (fun c => if Nat.blt w c then w else c)

theorem normWordFast_eq (mask w : Word) : normWordFast mask w = normWord mask w := by
  simp [normWordFast, normWord, dagForceWordEq, Nat.blt_eq]

def normBinOp4Fast (mask op x y : Word) : Word :=
  normWordFast mask (binOp4 mask op x y)

theorem normBinOp4Fast_eq (mask op x y : Word) : normBinOp4Fast mask op x y = normBinOp4 mask op x y :=
  normWordFast_eq mask (binOp4 mask op x y)

def availableNormB (bank : List Word) (v : Word) : Bool :=
  v == 0 || bank.contains v

theorem availableNormB_spec {mask : Word} {orig bank : List Word} {w : Word}
    (mw : Masked mask w) (hbank : ∀ x ∈ bank, AvBin mask orig x)
    (h : availableNormB bank (normWord mask w) = true) : AvBin mask orig w := by
  simp only [availableNormB, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at h
  rcases h with hz | hm
  · rcases normWord_eq_or mask w with e | e
    · exact Or.inl (e.symm.trans hz)
    · have : mask ^^^ w = 0 := e.symm.trans hz
      have h1 : w = mask := by
        have h2 := congrArg (fun z => mask ^^^ z) this
        rw [xor_cancel_left, Nat.xor_zero] at h2
        exact h2
      exact Or.inr (Or.inl h1)
  · have hav := hbank _ hm
    rcases normWord_eq_or mask w with e | e
    · rwa [e] at hav
    · rw [e] at hav
      have := avBin_not hav
      rwa [xor_cancel_left] at this

def stockWordBinF (mask : Word) (nstock needed : List Word) (word : Word) : List Word :=
  dagForceWord (normWordFast mask (word &&& mask)) (fun v =>
    if availableNormB nstock v || needed.contains v then needed else v :: needed)

def recipeStartBinF (mask : Word) (nstock words : List Word) : List Word :=
  (List.rec (motive := fun _ => List Word → List Word) id
    (fun word _ next seen => next (stockWordBinF mask nstock seen word)) words) []

def recipeClosureBinF (mask : Word) (nstock : List Word) (history : List (Word × Word × Word))
    (start : List Word) : List Word :=
  List.rec (motive := fun _ => List Word → List Word) id
    (fun (out, a, b) _ next seen =>
      next (dagForceWord (normWordFast mask (out &&& mask)) (fun vo =>
        if seen.contains vo then
          stockWordBinF mask nstock (stockWordBinF mask nstock seen a) b else seen)))
    history start

def recipeGateBinNorm (mask : Word) (nbank : List Word) (v ma mb : Word) : Bool :=
  availableNormB nbank (normWordFast mask ma) && availableNormB nbank (normWordFast mask mb) &&
    (v == normWordFast mask (ma &&& mb) || v == normWordFast mask (ma ||| mb) ||
     v == normWordFast mask (ma &&& (mask ^^^ mb)) || v == normWordFast mask ((mask ^^^ ma) &&& mb))

theorem recipeGateBinNorm_spec {mask : Word} {orig nbank : List Word} {v ma mb : Word}
    (hma : Masked mask ma) (hmb : Masked mask mb)
    (hbank : ∀ x ∈ nbank, AvBin mask orig x)
    (h : recipeGateBinNorm mask nbank v ma mb = true) : GateBin mask orig v := by
  simp only [recipeGateBinNorm, normWordFast_eq, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨ha, hb⟩, eq⟩ := h
  have havA := availableNormB_spec hma hbank ha
  have havB := availableNormB_spec hmb hbank hb
  rcases eq with ((rfl | rfl) | rfl) | rfl
  · exact gateBin_normBinOp4 (op := 0) (by decide) hma hmb havA havB
  · exact gateBin_normBinOp4 (op := 1) (by decide) hma hmb havA havB
  · exact gateBin_normBinOp4 (op := 2) (by decide) hma hmb havA havB
  · exact gateBin_normBinOp4 (op := 3) (by decide) hma hmb havA havB

def replayRecipesBinF (mask : Word) (needed : List Word) : List (Word × Word × Word) → List Word → List Word
  | [], _ => []
  | (w, a, b) :: rs, nbank =>
      dagForceWord (normWordFast mask (w &&& mask)) (fun v =>
        if needed.contains v && !availableNormB nbank v then
          dagForceWord (a &&& mask) (fun ma =>
            dagForceWord (b &&& mask) (fun mb =>
              if recipeGateBinNorm mask nbank v ma mb then
                v :: replayRecipesBinF mask needed rs (v :: nbank)
              else replayRecipesBinF mask needed rs nbank))
        else replayRecipesBinF mask needed rs nbank)

theorem replayRecipesBinFBuilds (mask : Word) (needed : List Word) (recipes : List (Word × Word × Word))
    (orig nbank : List Word) (hbank : ∀ x ∈ nbank, AvBin mask orig x) :
    WordBuildsBin mask orig (replayRecipesBinF mask needed recipes nbank) ∧
      ∀ x ∈ replayRecipesBinF mask needed recipes nbank, x ∈ replayRecipesBinF mask needed recipes nbank := by
  refine ⟨?_, fun _ h => h⟩
  induction recipes generalizing orig nbank with
  | nil => trivial
  | cons recipe recipes ih =>
    obtain ⟨w, a, b⟩ := recipe
    change WordBuildsBin mask orig (dagForceWord (normWordFast mask (w &&& mask)) (fun v =>
      if needed.contains v && !availableNormB nbank v then
        dagForceWord (a &&& mask) (fun ma =>
          dagForceWord (b &&& mask) (fun mb =>
            if recipeGateBinNorm mask nbank v ma mb then
              v :: replayRecipesBinF mask needed recipes (v :: nbank)
            else replayRecipesBinF mask needed recipes nbank))
      else replayRecipesBinF mask needed recipes nbank))
    simp only [dagForceWordEq, normWordFast_eq]
    split
    · split
      · rename_i h1 h2
        refine ⟨recipeGateBinNorm_spec (restrictWord mask a) (restrictWord mask b) hbank h2, ?_⟩
        apply ih (normWord mask (w &&& mask) :: orig) (normWord mask (w &&& mask) :: nbank)
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
        · exact avBin_weaken (fun y hy => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hy)))) (hbank x hx)
      · exact ih orig nbank hbank
    · exact ih orig nbank hbank

def dagBoundClosesBinNoHdr (state : RowState) (bound : Bound) : Bool :=
  let (mask, nstock, lower, _) := bound
  let (fuel, ws, history) := state
  dagForceWord (fuel - flatCountF mask ws) (fun remaining =>
    if Nat.blt remaining lower then
      dagForceWords (recipeStartBinF mask nstock ws) (fun start =>
        if Nat.blt (start.length + remaining) lower then
          dagForceWords (recipeClosureBinF mask nstock history start) (fun needed =>
            if Nat.blt (needed.length + remaining) lower then
              dagForceWords (replayRecipesBinF mask needed history.reverse nstock) (fun replay =>
                Nat.blt (replay.length + remaining) lower &&
                  ws.all (fun w => dagForceWord (normWordFast mask (w &&& mask)) (fun v =>
                    availableNormB (replay ++ nstock) v)))
            else false)
        else false)
    else false)

def dagKnownClosesBinNoHdr (bounds : List Bound) (state : RowState) : Bool :=
  List.rec false (fun bound _ later => dagBoundClosesBinNoHdr state bound || later) bounds

def dagFilterForceBoundsBin (target : Word) (bounds : List Bound) (cont : List Bound → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Bound → Bool) → Bool) (fun k => k [])
    (fun b _ next k =>
      dagForceWord b.1 (fun m' =>
        dagForceWord b.2.2.2 (fun g' =>
          if (target &&& m') == g' && g' != 0 && g' != m' then
            dagForceWords (b.2.1.map (fun w => normWordFast m' w)) (fun nst' =>
              next (fun rest => k ((m', nst', b.2.2.1, g') :: rest)))
          else next k))) bounds) cont

theorem dagFilterForceBoundsBinEq (target : Word) (bounds : List Bound) (cont : List Bound → Bool) :
    dagFilterForceBoundsBin target bounds cont =
      cont ((bounds.filter (dagBoundHeaderOK target)).map (fun b => (b.1, b.2.1.map (normWord b.1), b.2.2.1, b.2.2.2))) := by
  induction bounds generalizing cont with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨m, st, lo, g⟩ := b
    change dagForceWord m (fun m' => dagForceWord g (fun g' =>
      if (target &&& m') == g' && g' != 0 && g' != m' then
        dagForceWords (st.map (fun w => normWordFast m' w)) (fun nst' =>
          dagFilterForceBoundsBin target bs (fun rest => cont ((m', nst', lo, g') :: rest)))
      else dagFilterForceBoundsBin target bs cont)) = _
    simp only [dagForceWordEq, dagForceWordsEq, List.filter_cons, dagBoundHeaderOK]
    have hm : st.map (fun w => normWordFast m w) = st.map (normWord m) := by
      congr 1; funext w; exact normWordFast_eq m w
    by_cases hc : ((target &&& m) == g && g != 0 && g != m) = true
    · simp only [hc, ite_true, hm, List.map_cons]; exact ih _
    · simp only [Bool.not_eq_true] at hc; simp only [hc, Bool.false_eq_true, ite_false]; exact ih _

def dagBoundClosesBinFast (target : Word) (state : RowState) (bound : Bound) : Bool :=
  let (mask, nstock, lower, goal) := bound
  let (fuel, ws, history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    dagForceWord (fuel - flatCountF mask ws) (fun remaining =>
      if Nat.blt remaining lower then
        dagForceWords (recipeStartBinF mask nstock ws) (fun start =>
          if Nat.blt (start.length + remaining) lower then
            dagForceWords (recipeClosureBinF mask nstock history start) (fun needed =>
              if Nat.blt (needed.length + remaining) lower then
                dagForceWords (replayRecipesBinF mask needed history.reverse nstock) (fun replay =>
                  Nat.blt (replay.length + remaining) lower &&
                    ws.all (fun w => dagForceWord (normWordFast mask (w &&& mask)) (fun v =>
                      availableNormB (replay ++ nstock) v)))
              else false)
          else false)
      else false)

-- BinLower bound-closing check (with normalized words and 4 ops)
def availableBinB (mask : Word) (bank : List Word) (w : Word) : Bool :=
  w == 0 || w == mask || bank.contains w || bank.contains (mask ^^^ w)

theorem availableBinB_spec {mask : Word} {bank : List Word} {v : Word} :
    availableBinB mask bank v = true ↔ AvBin mask bank v := by
  simp [availableBinB, AvBin, or_assoc]

def stockWordBin (mask : Word) (stock needed : List Word) (word : Word) : List Word :=
  let v := normWord mask (word &&& mask)
  if availableBinB mask stock v || needed.contains v then needed else v :: needed

def recipeStartBin (mask : Word) (stock words : List Word) : List Word :=
  (List.rec (motive := fun _ => List Word → List Word) id
    (fun word _ next seen => next (stockWordBin mask stock seen word)) words) []

def recipeClosureBin (mask : Word) (stock : List Word) (history : List (Word × Word × Word))
    (start : List Word) : List Word :=
  List.rec (motive := fun _ => List Word → List Word) id
    (fun (out, a, b) _ next seen =>
      next (if seen.contains (normWord mask (out &&& mask)) then
        stockWordBin mask stock (stockWordBin mask stock seen a) b else seen))
    history start

def recipeGateBin (mask : Word) (bank : List Word) (w a b : Word) : Bool :=
  availableBinB mask bank a && availableBinB mask bank b &&
    (w == normWord mask (a &&& b) || w == normWord mask (a ||| b) ||
     w == normWord mask (a &&& (mask ^^^ b)) || w == normWord mask ((mask ^^^ a) &&& b))

theorem recipeGateBin_spec {mask : Word} {bank : List Word} {v a b : Word}
    (ma : Masked mask a) (mb : Masked mask b)
    (h : recipeGateBin mask bank v a b = true) : GateBin mask bank v := by
  simp only [recipeGateBin, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, availableBinB_spec] at h
  obtain ⟨⟨ha, hb⟩, eq⟩ := h
  rcases eq with ((rfl | rfl) | rfl) | rfl
  · exact gateBin_normBinOp4 (op := 0) (by decide) ma mb ha hb
  · exact gateBin_normBinOp4 (op := 1) (by decide) ma mb ha hb
  · exact gateBin_normBinOp4 (op := 2) (by decide) ma mb ha hb
  · exact gateBin_normBinOp4 (op := 3) (by decide) ma mb ha hb

def replayRecipesBin (mask : Word) (needed : List Word) (recipes : List (Word × Word × Word))
    (bank : List Word) : List Word :=
  List.rec (motive := fun _ => List Word → List Word) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := normWord mask (w &&& mask)
      if needed.contains v && !availableBinB mask bank v &&
          recipeGateBin mask bank v (a &&& mask) (b &&& mask) then
        v :: next (v :: bank)
      else next bank) recipes bank

theorem replayRecipesBinBuilds (mask : Word) (needed : List Word) (recipes : List (Word × Word × Word))
    (bank : List Word) : WordBuildsBin mask bank (replayRecipesBin mask needed recipes bank) := by
  induction recipes generalizing bank with
  | nil => trivial
  | cons recipe recipes ih =>
    obtain ⟨w, a, b⟩ := recipe
    change WordBuildsBin mask bank
      (if needed.contains (normWord mask (w &&& mask)) && !availableBinB mask bank (normWord mask (w &&& mask)) &&
          recipeGateBin mask bank (normWord mask (w &&& mask)) (a &&& mask) (b &&& mask) then
        normWord mask (w &&& mask) :: replayRecipesBin mask needed recipes (normWord mask (w &&& mask) :: bank)
      else replayRecipesBin mask needed recipes bank)
    split
    · rename_i yes
      exact ⟨recipeGateBin_spec (restrictWord mask a) (restrictWord mask b) (Bool.and_eq_true_iff.mp yes).2, ih _⟩
    · exact ih _

def dagBoundClosesBin (target : Word) (state : RowState) (bound : Bound) : Bool :=
  let (mask, stock, lower, goal) := bound
  let (fuel, ws, history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    dagForceWord (fuel - flatCount mask ws) (fun remaining =>
      if Nat.blt remaining lower then
        dagForceWords (recipeStartBin mask stock ws) (fun start =>
          if Nat.blt (start.length + remaining) lower then
            dagForceWords (recipeClosureBin mask stock history start) (fun needed =>
              if Nat.blt (needed.length + remaining) lower then
                dagForceWords (replayRecipesBin mask needed history.reverse stock) (fun replay =>
                  decide (replay.length + remaining < lower) &&
                    ws.all (fun w => availableBinB mask (replay ++ stock) (w &&& mask)))
              else false)
          else false)
      else false)

def dagKnownClosesBin (target : Word) (bounds : List Bound) (state : RowState) : Bool :=
  List.rec false (fun bound _ later => dagBoundClosesBin target state bound || later) bounds

def KnownBin (bounds : List Bound) : Prop :=
  ∀ bound ∈ bounds, BinLower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1

theorem extendKnownBin {bound : Bound} {bounds : List Bound}
    (old : KnownBin bounds)
    (new : BinLower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1) :
    KnownBin (bound :: bounds) := by
  intro x h
  rcases List.mem_cons.mp h with rfl | h
  · exact new
  · exact old _ h

def BinViable (mask target : Word) (state : RowState) : Prop :=
  state.2.1.Nodup ∧ ∃ k, k ≤ state.1 ∧ LiveBin mask target k state.2.1.toFinset

theorem boundClosesBinSound {mask target : Word} {state : RowState} {bound : Bound}
    (known : BinLower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (submask : mask &&& bound.1 = bound.1)
    (viable : BinViable mask target state) :
    dagBoundClosesBin target state bound = false := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨cut, stock, minimum, goal⟩ := bound
  obtain ⟨nd, k, steps, live⟩ := viable
  change k ≤ fuel at steps
  change LiveBin mask target k ws.toFinset at live
  apply Bool.eq_false_iff.mpr
  intro hc
  let needed := recipeClosureBin cut stock history (recipeStartBin cut stock ws)
  let replay := replayRecipesBin cut needed history.reverse stock
  simp only [dagBoundClosesBin, dagForceWordEq, dagForceWordsEq, Nat.blt_eq,
    Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hc
  obtain ⟨⟨⟨goalEq, nonzero⟩, nonflat⟩, scan⟩ := hc
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  rcases Bool.and_eq_true_iff.mp scan with ⟨length, sources⟩
  simp only [decide_eq_true_eq] at length
  have hlen : replay.length + (fuel - flatCount cut ws) < minimum := length
  have pn : ¬maskedFlat cut target := by simpa [maskedFlat, goalEq] using And.intro nonzero nonflat
  obtain ⟨n, hn, build⟩ := maskedBuildBin live cut submask pn
  rw [← flatCountCard cut nd] at hn
  change n + flatCount cut ws ≤ k at hn
  have supply : ∀ w ∈ projectedStock cut ws.toFinset, AvBin cut (replay ++ stock) w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image,
      List.mem_toFinset] at hw
    rcases hw with rfl | rfl | ⟨v, hv, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact availableBinB_spec.mp (List.all_eq_true.mp sources v hv)
  obtain ⟨ys, hy, built, avail⟩ := buildableBinWords build supply
  have both := buildsBin_append (replayRecipesBinBuilds cut needed history.reverse stock) built
  have hit : AvBin cut ((replay ++ ys) ++ stock) goal := by
    rw [← goalEq]
    exact avBin_weaken (fun v hv => Or.inr (Or.inr (Or.inl (by
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using hv)))) avail
  have enough := known (replay ++ ys) both hit
  simp only [List.length_append] at enough
  omega

theorem knownClosesBinSound {mask target : Word} {bounds : List Bound} {state : RowState}
    (known : KnownBin bounds) (submask : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (viable : BinViable mask target state) :
    dagKnownClosesBin target bounds state = false := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (dagBoundClosesBin target state bound || dagKnownClosesBin target bounds state) = false
    rw [boundClosesBinSound (known _ List.mem_cons_self) (submask _ List.mem_cons_self) viable]
    exact ih (fun b hb => known b (List.mem_cons_of_mem _ hb))
      (fun b hb => submask b (List.mem_cons_of_mem _ hb))

theorem boundClosesBinFastSound {mask target : Word} {state : RowState} {bound : Bound}
    (known : BinLower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (submask : mask &&& bound.1 = bound.1)
    (viable : BinViable mask target state) :
    dagBoundClosesBinFast target state (bound.1, bound.2.1.map (normWord bound.1), bound.2.2.1, bound.2.2.2) = false := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨cut, stock, minimum, goal⟩ := bound
  obtain ⟨nd, k, steps, live⟩ := viable
  change k ≤ fuel at steps
  change LiveBin mask target k ws.toFinset at live
  apply Bool.eq_false_iff.mpr
  intro hc
  let nstock := stock.map (normWord cut)
  let needed := recipeClosureBinF cut nstock history (recipeStartBinF cut nstock ws)
  let replay := replayRecipesBinF cut needed history.reverse nstock
  simp only [dagBoundClosesBinFast, dagForceWordEq, dagForceWordsEq, flatCountF_eq, normWordFast_eq,
    Nat.blt_eq, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hc
  obtain ⟨⟨⟨goalEq, nonzero⟩, nonflat⟩, scan⟩ := hc
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  rcases Bool.and_eq_true_iff.mp scan with ⟨length, sources⟩
  have hlen : replay.length + (fuel - flatCount cut ws) < minimum := Nat.blt_eq.mp length
  have pn : ¬maskedFlat cut target := by simpa [maskedFlat, goalEq] using And.intro nonzero nonflat
  obtain ⟨n, hn, build⟩ := maskedBuildBin live cut submask pn
  rw [← flatCountCard cut nd] at hn
  change n + flatCount cut ws ≤ k at hn
  have hnst : ∀ x ∈ nstock, AvBin cut stock x := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    rcases normWord_eq_or cut s with e | e
    · rw [e]; exact Or.inr (Or.inr (Or.inl hs))
    · rw [e]; exact Or.inr (Or.inr (Or.inr (by rwa [xor_cancel_left])))
  have hrep := (replayRecipesBinFBuilds cut needed history.reverse stock nstock hnst).1
  have hbank : ∀ x ∈ replay ++ nstock, AvBin cut (replay ++ stock) x := by
    intro x hx
    rcases List.mem_append.mp hx with hr | hs
    · exact Or.inr (Or.inr (Or.inl (List.mem_append_left stock hr)))
    · exact avBin_weaken (fun y hy => Or.inr (Or.inr (Or.inl (List.mem_append_right replay hy)))) (hnst x hs)
  have supply : ∀ w ∈ projectedStock cut ws.toFinset, AvBin cut (replay ++ stock) w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image,
      List.mem_toFinset] at hw
    rcases hw with rfl | rfl | ⟨v, hv, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact availableNormB_spec (restrictWord cut v) hbank (List.all_eq_true.mp sources v hv)
  obtain ⟨ys, hy, built, avail⟩ := buildableBinWords build supply
  have both := buildsBin_append hrep built
  have hit : AvBin cut ((replay ++ ys) ++ stock) goal := by
    rw [← goalEq]
    exact avBin_weaken (fun v hv => Or.inr (Or.inr (Or.inl (by
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using hv)))) avail
  have enough := known (replay ++ ys) both hit
  simp only [List.length_append] at enough
  omega

theorem knownClosesBinNoHdrSound {mask target : Word} {bounds : List Bound} {state : RowState}
    (known : KnownBin bounds) (submask : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hdr : ∀ b ∈ bounds, dagBoundHeaderOK target b = true)
    (viable : BinViable mask target state) :
    dagKnownClosesBinNoHdr (bounds.map (fun b => (b.1, b.2.1.map (normWord b.1), b.2.2.1, b.2.2.2))) state = false := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (dagBoundClosesBinNoHdr state (bound.1, bound.2.1.map (normWord bound.1), bound.2.2.1, bound.2.2.2) ||
      dagKnownClosesBinNoHdr (bounds.map (fun b => (b.1, b.2.1.map (normWord b.1), b.2.2.1, b.2.2.2))) state) = false
    have h1 := boundClosesBinFastSound (known _ List.mem_cons_self) (submask _ List.mem_cons_self) viable
    have hh := hdr bound List.mem_cons_self
    have heq : dagBoundClosesBinNoHdr state (bound.1, bound.2.1.map (normWord bound.1), bound.2.2.1, bound.2.2.2) =
        dagBoundClosesBinFast target state (bound.1, bound.2.1.map (normWord bound.1), bound.2.2.1, bound.2.2.2) := by
      obtain ⟨f, ws, hist⟩ := state
      obtain ⟨m, st, lo, g⟩ := bound
      simp only [dagBoundHeaderOK] at hh
      simp only [dagBoundClosesBinNoHdr, dagBoundClosesBinFast, hh, Bool.true_and]
    rw [heq, h1]
    exact ih (fun b hb => known b (List.mem_cons_of_mem _ hb))
      (fun b hb => submask b (List.mem_cons_of_mem _ hb))
      (fun b hb => hdr b (List.mem_cons_of_mem _ hb))

-- Shift / Isomorphism lifting for BinLower (reuses dagShiftGates!)
theorem buildsBinMap {m n : Word} (f : Word → Word)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a, f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b, f (a &&& b) = f a &&& f b)
    (join : ∀ a b, f (a ||| b) = f a ||| f b)
    {roots bank : List Word}
    (supply : ∀ v ∈ roots, AvBin n bank (f v))
    {values : List Word} (h : WordBuildsBin m roots values) :
    WordBuildsBin n bank (values.map f) := by
  have av {bank roots : List Word} {v : Word}
      (src : ∀ v ∈ roots, AvBin n bank (f v))
      (h : AvBin m roots v) : AvBin n bank (f v) := by
    rcases h with rfl | rfl | hv | hv
    · exact Or.inl zero
    · exact Or.inr (Or.inl ones)
    · exact src _ hv
    · have h1 := src _ hv; rw [invert] at h1; simpa [xor_cancel_left] using avBin_not h1
  induction values generalizing roots bank with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨?_, ih ?_ h.2⟩
    · rcases h.1 with ⟨a, b, ha, hb, eq | eq⟩
      · exact ⟨f a, f b, av supply ha, av supply hb, Or.inl (eq ▸ meet a b)⟩
      · exact ⟨f a, f b, av supply ha, av supply hb, Or.inr (eq ▸ join a b)⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
      · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hx)))) (supply _ hw)

theorem lowerBinMap {m n : Word} (f : Word → Word)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a, f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b, f (a &&& b) = f a &&& f b)
    (join : ∀ a b, f (a ||| b) = f a ||| f b)
    {roots bank : List Word} {goal : Word} {minimum : Nat}
    (supply : ∀ v ∈ roots, AvBin n bank (f v))
    (bound : BinLower n bank (f goal) minimum) :
    BinLower m roots goal minimum := by
  intro values build hit
  suffices AvBin n (values.map f ++ bank) (f goal) by
    simpa using bound (values.map f) (buildsBinMap f zero ones invert meet join supply build) this
  rcases hit with rfl | rfl | mem | mem
  · exact Or.inl zero
  · exact Or.inr (Or.inl ones)
  · rcases List.mem_append.mp mem with hv | hr
    · exact Or.inr (Or.inr (Or.inl (List.mem_append_left _ (List.mem_map_of_mem hv))))
    · exact avBin_weaken (fun w hw => Or.inr (Or.inr (Or.inl (List.mem_append_right _ hw)))) (supply _ hr)
  · rcases List.mem_append.mp mem with hv | hr
    · have h1 : f (m ^^^ goal) ∈ values.map f ++ bank := List.mem_append_left _ (List.mem_map_of_mem hv)
      rw [invert] at h1
      exact Or.inr (Or.inr (Or.inr h1))
    · have h1 := supply _ hr
      rw [invert] at h1
      exact avBin_weaken (fun w hw => Or.inr (Or.inr (Or.inl (List.mem_append_right _ hw))))
        (by simpa [xor_cancel_left] using avBin_not h1)

theorem suppliesBinOfCheck {oldMask : Word} {old new : List Word} {rename : Word → Word}
    (h : new.all (fun w => availableBinB oldMask old (rename w)) = true) :
    ∀ w ∈ new, AvBin oldMask old (rename w) := by
  intro w hw
  exact availableBinB_spec.mp (List.all_eq_true.mp h w hw)

def dagShiftCheckBin (width mask goal oldMask oldGoal : Word) (stock old : List Word) (move : WordMove) : Bool :=
  Nat.beq (mask &&& fullMask width) mask && dagShiftUnique mask move width 0 &&
    Nat.beq (dagShift mask move mask) oldMask && Nat.beq (dagShift mask move goal) oldGoal &&
    stock.all (fun w => availableBinB oldMask old (dagShift mask move w))

theorem dagShiftLowerBin {width mask goal oldMask oldGoal : Word} {stock old : List Word} {min : Nat}
    (move : WordMove) (origin : BinLower oldMask old oldGoal min)
    (ok : dagShiftCheckBin width mask goal oldMask oldGoal stock old move = true) :
    BinLower mask stock goal min := by
  simp only [dagShiftCheckBin, Bool.and_eq_true, Nat.beq_eq] at ok
  obtain ⟨⟨⟨⟨bounded, unique⟩, masks⟩, goals⟩, supply⟩ := ok
  obtain ⟨andG, orG, xorG⟩ := dagShiftGates bounded unique
  have zero : dagShift mask move 0 = 0 := by
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr; rw [dagShiftLinear]; simp
  apply lowerBinMap (dagShift mask move) zero masks (fun w => by rw [xorG, masks]) andG orG (suppliesBinOfCheck supply)
  rwa [goals]

-- ============================================================================
-- Part 3: lowerDagBin (DAG certificate verifier for BinLower!)
-- ============================================================================

def gateTokenBin (a b op keep : Nat) : Nat := ((a * 64 + b) * 4 + op) * 4 + keep

theorem gateTokenBinFields {a b op keep : Nat} (hb : b < 64) (ho : op < 4) (hk : keep < 4) :
    gateTokenBin a b op keep % 4 = keep ∧
    gateTokenBin a b op keep / 4 % 4 = op ∧
    gateTokenBin a b op keep / (4 * 4 * 64) = a ∧
    gateTokenBin a b op keep / (4 * 4) % 64 = b := by
  unfold gateTokenBin; omega

def normStock (mask : Word) (stock : List Word) : List Word :=
  List.rec [] (fun w _ rest => insertWord (normWord mask w) rest) stock

theorem normStockSet (mask : Word) (stock : List Word) :
    (normStock mask stock).toFinset = (stock.map (normWord mask)).toFinset := by
  induction stock with
  | nil => simp [normStock]
  | cons w ws ih =>
    change (insertWord (normWord mask w) (normStock mask ws)).toFinset = _
    rw [insertWordSet, ih]; simp

def childStateBin (mask token : Nat) (state : RowState) : Option RowState :=
  let (fuel, ws, history) := state
  let keep := token % 4
  let op := (token / 4) % 4
  let a := token / (4 * 4 * 64)
  let b := (token / (4 * 4)) % 64
  if fuel == 0 || b ≥ ws.length || a ≥ b then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let w := normBinOp4 mask op x y
    if w == 0 || w == mask || ws.contains w then none
    else
      let rest := if keep.testBit 0 then ws else ws.erase x
      let rest := if keep.testBit 1 then rest else rest.erase y
      some (fuel - 1, insertWord w rest, (w, x, y) :: history)

def dagDirectChildBin (mask : Word) (state : RowState) (a b op keep x y out : Nat) : Option RowState :=
  let (fuel, ws, history) := state
  if fuel == 0 || b ≥ ws.length || a ≥ b then none
  else if out == 0 || out == mask || ws.contains out then none
  else
    let rest := keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
    some (fuel - 1, insertWord out rest, (out, x, y) :: history)

theorem dagDirectChildBinEq {mask a b op keep : Nat} {state : RowState}
    (hb : b < 64) (hop : op < 4) (hk : keep < 4) :
    let x := state.2.1.getD a 0
    let y := state.2.1.getD b 0
    dagDirectChildBin mask state a b op keep x y (normBinOp4 mask op x y) =
      childStateBin mask (gateTokenBin a b op keep) state := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨keepEq, opEq, aEq, bEq⟩ := gateTokenBinFields (a := a) hb hop hk
  simp only [childStateBin, dagDirectChildBin, keepWord, keepEq, opEq, aEq, bEq]

def dagTraceBin (mask : Word) (nstock : List Word) (fuel : Nat) (forest : Forest)
    (i : Nat) : Option RowState :=
  (Nat.rec (motive := fun _ => Nat → Option RowState) (fun _ => none)
    (fun _ previous j =>
      let (parent, token) := forest j
      if parent == 0 then
        if token < 2 ^ nstock.length then some (rootState nstock fuel token) else none
      else (previous (parent - 1)).bind (childStateBin mask token)) (fuel + 1)) i

def dagMoveWordsBin (mask : Word) (m : WordMove) (ws : List Word) : List Word :=
  List.rec [] (fun w _ next => insertWord (normWord mask (mixMove m w)) next) ws

theorem dagMoveSetBin {mask : Word} {m : WordMove} {ws : List Word} {select : Fin rows → Fin rows}
    (agree : ∀ w ∈ ws, mixMove m w = relabel select w) :
    (dagMoveWordsBin mask m ws).toFinset = ws.toFinset.image (fun w => normWord mask (relabel select w)) := by
  induction ws with
  | nil => simp [dagMoveWordsBin]
  | cons w ws ih =>
    change (insertWord (normWord mask (mixMove m w)) (dagMoveWordsBin mask m ws)).toFinset = _
    rw [insertWordSet, ih (fun u hu => agree _ (List.mem_cons_of_mem _ hu)),
      agree _ List.mem_cons_self, List.toFinset_cons, Finset.image_insert]

def dagRefBin (mask : Word) (count : Nat) (states : Nat → Option RowState)
    (moves : Array WordMove) (links : DagLinks) (parent token : Nat) (state : RowState) : Bool :=
  match links parent token with
  | none => false
  | some (destination, auto) =>
    Nat.blt destination count &&
      match states destination with
      | none => false
      | some saved =>
        saved.1 == state.1 &&
          if auto == 0 then saved.2.1 == state.2.1
          else match moves[auto - 1]? with
               | none => false
               | some m => saved.2.1 == dagMoveWordsBin mask m state.2.1

theorem liveBinMaskedImage {mask goal : Word} {select : Fin rows → Fin rows}
    (auto : DagAuto mask goal select) (maskBounds : Masked (fullMask rows) mask)
    {k : Nat} {S : Finset Word} (live : LiveBin mask goal k S)
    (masked : ∀ w ∈ S, Masked mask w) :
    LiveBin mask goal k (S.image (fun w => normWord mask (relabel select w))) := by
  let g := relabel select
  let f := fun w => normWord mask (g w)
  have hmask : g mask = mask := auto.2.1
  have hxor (w : Word) : g (mask ^^^ w) = mask ^^^ g w := by dsimp only [g]; rw [relabelXor, auto.2.1]
  have fnrm (w : Word) : f (normWord mask w) = f w := by
    rcases normWord_eq_or mask w with h | h
    · rw [h]
    · simp only [f, h, hxor, normWord_symm]
  have injG {a b : Word} (ma : Masked mask a) (mb : Masked mask b) : g a = g b → a = b :=
    relabelInj select auto.1 (maskedBelow maskBounds ma) (maskedBelow maskBounds mb)
  have injF {a b : Word} (ma : Masked mask a) (mb : Masked mask b)
      (na : normWord mask a = a) (nb : normWord mask b = b) (eq : f a = f b) : a = b := by
    have hrel : g a = g b ∨ g a = mask ^^^ g b := by
      rcases normWord_eq_or mask (g a) with ea | ea <;> rcases normWord_eq_or mask (g b) with eb | eb
      · left; exact ea.symm.trans (eq.trans eb)
      · right; exact ea.symm.trans (eq.trans eb)
      · right
        have h1 : mask ^^^ g a = g b := ea.symm.trans (eq.trans eb)
        have := congrArg (fun z => mask ^^^ z) h1; rw [xor_cancel_left] at this; exact this
      · left
        have h1 : mask ^^^ g a = mask ^^^ g b := ea.symm.trans (eq.trans eb)
        have := congrArg (fun z => mask ^^^ z) h1; rw [xor_cancel_left, xor_cancel_left] at this; exact this
    rcases hrel with h1 | h1
    · exact injG ma mb h1
    · rw [← hxor] at h1
      have h2 := injG ma (masked_xor mb) h1
      rw [← na, h2, normWord_symm, nb]
  have properF {a : Word} (ma : Masked mask a) (ha : properWord mask a) : properWord mask (f a) := by
    apply proper_norm
    exact ⟨fun eq => ha.1 (injG ma (by simp [Masked]) (eq.trans (relabelZero select).symm)),
      fun eq => ha.2 (injG ma (by simp [Masked]) (eq.trans hmask.symm))⟩
  have freshImage {T : Finset Word} {v : Word} (hv : v ∉ T) (mv : Masked mask v) (nv : normWord mask v = v)
      (ms : ∀ w ∈ T, Masked mask w) (ns : ∀ w ∈ T, normWord mask w = w) : f v ∉ T.image f := by
    intro hw
    obtain ⟨w, hs, eq⟩ := Finset.mem_image.mp hw
    exact hv (injF (ms w hs) mv (ns w hs) nv eq ▸ hs)
  have opImage {a b : Word} (ma : Masked mask a) (mb : Masked mask b) {op : Nat} (hop : op < 4) :
      ∃ op', op' < 4 ∧ f (normBinOp4 mask op a b) = normBinOp4 mask op' (f a) (f b) := by
    have mfa : Masked mask (f a) := masked_norm (maskedTransfer hmask ma)
    have mfb : Masked mask (f b) := masked_norm (maskedTransfer hmask mb)
    have ga_rel : g a = f a ∨ g a = mask ^^^ f a := by
      rcases normWord_eq_or mask (g a) with h | h
      · exact Or.inl h.symm
      · right; have := congrArg (fun z => mask ^^^ z) h; rw [xor_cancel_left] at this; exact this.symm
    have gb_rel : g b = f b ∨ g b = mask ^^^ f b := by
      rcases normWord_eq_or mask (g b) with h | h
      · exact Or.inl h.symm
      · right; have := congrArg (fun z => mask ^^^ z) h; rw [xor_cancel_left] at this; exact this.symm
    have hstep : f (normBinOp4 mask op a b) = normWord mask (binOp4 mask op (g a) (g b)) := by
      rw [normBinOp4, fnrm]
      have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl
      · simp [f, binOp4, g, relabelAnd]
      · simp [f, binOp4, g, relabelOr]
      · simp [f, binOp4, g, relabelAnd, hxor]
      · simp [f, binOp4, g, relabelAnd, hxor]
    rw [hstep]
    have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
    rcases hcase with rfl | rfl | rfl | rfl <;> rcases ga_rel with hga | hga <;> rcases gb_rel with hgb | hgb
    · exact ⟨0, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨2, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨3, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨1, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ f a) &&& (mask ^^^ f b)) = _; rw [← demorgan_or mfa mfb, normWord_symm]; rfl⟩
    · exact ⟨1, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨3, by decide, by
        rw [hga, hgb]; change normWord mask (f a ||| (mask ^^^ f b)) = _
        have h1 : mask ^^^ ((mask ^^^ f a) &&& f b) = f a ||| (mask ^^^ f b) := by
          rw [demorgan_and (masked_xor mfa) mfb, xor_cancel_left]
        rw [← h1, normWord_symm]; rfl⟩
    · exact ⟨2, by decide, by
        rw [hga, hgb]; change normWord mask ((mask ^^^ f a) ||| f b) = _
        have h1 : mask ^^^ (f a &&& (mask ^^^ f b)) = (mask ^^^ f a) ||| f b := by
          rw [demorgan_and mfa (masked_xor mfb), xor_cancel_left]
        rw [← h1, normWord_symm]; rfl⟩
    · exact ⟨0, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ f a) ||| (mask ^^^ f b)) = _; rw [← demorgan_and mfa mfb, normWord_symm]; rfl⟩
    · exact ⟨2, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨0, by decide, by rw [hga, hgb]; change normWord mask (f a &&& (mask ^^^ (mask ^^^ f b))) = _; rw [xor_cancel_left]; rfl⟩
    · exact ⟨1, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ f a) &&& (mask ^^^ f b)) = _; rw [← demorgan_or mfa mfb, normWord_symm]; rfl⟩
    · exact ⟨3, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ f a) &&& (mask ^^^ (mask ^^^ f b))) = _; rw [xor_cancel_left]; rfl⟩
    · exact ⟨3, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨1, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ f a) &&& (mask ^^^ f b)) = _; rw [← demorgan_or mfa mfb, normWord_symm]; rfl⟩
    · exact ⟨0, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ (mask ^^^ f a)) &&& f b) = _; rw [xor_cancel_left]; rfl⟩
    · exact ⟨2, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ (mask ^^^ f a)) &&& (mask ^^^ f b)) = _; rw [xor_cancel_left]; rfl⟩
  induction live using LiveBin.ind with
  | stop hp =>
    rw [Finset.image_singleton]
    have hfg : f (normWord mask goal) = normWord mask goal := by
      rw [fnrm]; simp only [f, g, auto.2.2]
    change LiveBin mask goal 0 {f (normWord mask goal)}
    rw [hfg]
    exact LiveBin.stop hp
  | @step k U a b op hop pa pb ab na nb fresh tail ih =>
    let v := normBinOp4 mask op a b
    have ma := masked a (Finset.mem_insert_self ..)
    have mb := masked b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have mv : Masked mask v := by
      apply masked_norm
      have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl
      · exact masked_gateBin (bank := [a, b]) (by simpa using And.intro ma mb)
          ⟨a, b, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inl rfl⟩
      · exact masked_gateBin (bank := [a, b]) (by simpa using And.intro ma mb)
          ⟨a, b, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inr rfl⟩
      · exact masked_gateBin (bank := [a, b]) (by simpa using And.intro ma mb)
          ⟨a, mask ^^^ b, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inr (by rw [xor_cancel_left]; simp))), Or.inl rfl⟩
      · exact masked_gateBin (bank := [a, b]) (by simpa using And.intro ma mb)
          ⟨mask ^^^ a, b, Or.inr (Or.inr (Or.inr (by rw [xor_cancel_left]; simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inl rfl⟩
    have hnew : ∀ w ∈ insert v U, Masked mask w := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU))
    have hns : ∀ w ∈ insert a (insert b U), normWord mask w = w := fun w hw =>
      (liveBinProps (LiveBin.step hop pa pb ab na nb fresh tail) w hw).2
    obtain ⟨op', hop', fve⟩ := opImage ma mb hop
    have ht := ih hnew
    have hf := freshImage fresh mv (normWord_idem mask _) masked hns
    change LiveBin mask goal (k + 1) ((insert a (insert b U)).image f)
    rw [Finset.image_insert] at ht
    change LiveBin mask goal k (insert (f v) (U.image f)) at ht
    rw [fve] at ht
    rw [Finset.image_insert, Finset.image_insert, fve] at hf
    rw [Finset.image_insert, Finset.image_insert]
    exact LiveBin.step hop' (properF ma pa) (properF mb pb)
      (fun h => ab (injF ma mb na nb h)) (normWord_idem mask _) (normWord_idem mask _) hf ht

theorem dagLinkedBin {mask goal : Word} {width count : Nat} {states : Nat → Option RowState}
    {moves : Array WordMove} {links : DagLinks} {parent token : Nat} {state : RowState}
    (bounds : Masked (fullMask width) mask)
    (valid : DagMovesOK mask goal width moves)
    (masked : ∀ w ∈ state.2.1, Masked mask w)
    (ok : dagRefBin mask count states moves links parent token state = true)
    {k : Nat} (live : LiveBin mask goal k state.2.1.toFinset) :
    ∃ i saved, i < count ∧ states i = some saved ∧ saved.1 = state.1 ∧
      LiveBin mask goal k saved.2.1.toFinset := by
  unfold dagRefBin at ok
  split at ok
  · contradiction
  next destination auto h =>
    have hd := Nat.blt_eq.mp (Bool.and_eq_true_iff.mp ok).1
    have finish := (Bool.and_eq_true_iff.mp ok).2
    cases eq : states destination with
    | none => simp [eq] at finish
    | some saved =>
      simp only [eq, Bool.and_eq_true, beq_iff_eq] at finish
      refine ⟨destination, saved, hd, eq, finish.1, ?_⟩
      have last := finish.2
      split at last
      · have same : saved.2.1 = state.2.1 := beq_iff_eq.mp last
        rwa [same]
      · split at last
        · contradiction
        next m hm =>
          obtain ⟨select, hauto, agree⟩ := valid _ _ hm
          have same : saved.2.1 = dagMoveWordsBin mask m state.2.1 := beq_iff_eq.mp last
          rw [same, dagMoveSetBin (fun w hw => agree w (masked w hw))]
          exact liveBinMaskedImage hauto bounds live (fun w hw => masked _ (List.mem_toFinset.mp hw))

def dagLocalBinFast (mask goal ngoal negGoal : Word) (cut : CutCheck) (state : RowState) : Bool :=
  let (fuel, ws, _) := state
  ws.length > fuel + 1 ||
    (!ws.contains ngoal &&
      (fuel == 0 || cut state || !dagPartition false ws goal negGoal))

def dagLocalBin (mask goal : Word) (cut : CutCheck) (state : RowState) : Bool :=
  let (fuel, ws, _) := state
  ws.length > fuel + 1 ||
    (!ws.contains (normWord mask goal) &&
      (fuel == 0 || cut state || !dagPartition false ws goal (mask ^^^ goal)))

theorem dagLocalBinFast_eq (mask goal : Word) (cut : CutCheck) (state : RowState) :
    dagLocalBinFast mask goal (normWord mask goal) (mask ^^^ goal) cut state =
      dagLocalBin mask goal cut state := rfl

theorem dagLocalBinOpen {mask goal : Word} {cut : CutCheck} {state : RowState}
    (masked : Masked mask goal) (viable : BinViable mask goal state) (noCut : cut state = false) :
    dagLocalBin mask goal cut state = false := by
  obtain ⟨fuel, ws, history⟩ := state
  have ⟨nd, k, cap, live⟩ := viable
  change k ≤ fuel at cap
  have card := liveBinSize live
  rw [List.toFinset_card_of_nodup nd] at card
  change ws.length ≤ k + 1 at card
  have fit : ¬ ws.length > fuel + 1 := by omega
  by_cases hz : fuel = 0
  · have kz : k = 0 := by omega
    subst k
    obtain ⟨eq, _⟩ := live
    have hm : normWord mask goal ∈ ws := List.mem_toFinset.mp (by rw [eq]; simp)
    simp [dagLocalBin, fit, hm]
  have sep := dagPartitionLiveBin masked live
  simp [dagLocalBin, fit, hz, sep, noCut]

def dagSizeFloorBin (n keep : Nat) : Nat :=
  (n - (if keep.testBit 0 then 0 else 1) - (if keep.testBit 1 then 0 else 1)) + 1

def dagTooWideBin (n fuel token : Nat) : Bool :=
  dagSizeFloorBin n (token % 4) > (fuel - 1) + 1

theorem dagWideChildBin {mask token : Nat} {state child : RowState}
    (eval : childStateBin mask token state = some child)
    (wide : dagTooWideBin state.2.1.length state.1 token = true) :
    child.2.1.length > child.1 + 1 := by
  obtain ⟨fuel, ws, history⟩ := state
  let keep := token % 4
  let op := token / 4 % 4
  let i := token / (4 * 4 * 64)
  let j := token / (4 * 4) % 64
  let x := ws.getD i 0
  let y := ws.getD j 0
  let z := normBinOp4 mask op x y
  let a := keep.testBit 0
  let b := keep.testBit 1
  let rest := keepWord b y (keepWord a x ws)
  let bad : Bool := fuel == 0 || j ≥ ws.length || i ≥ j
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z, x, y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb, hs] at eval
  have eq : (fuel - 1, insertWord z rest, (z, x, y) :: history) = child := by simpa [hb, hs] using eval
  rw [← eq]
  change (insertWord z rest).length > fuel - 1 + 1
  rw [dagInsertLength]
  have h1 := dagKeepLength a x ws
  have h2 := dagKeepLength b y (keepWord a x ws)
  have h : ws.length - (if a then 0 else 1) - (if b then 0 else 1) + 1 > fuel - 1 + 1 :=
    of_decide_eq_true wide
  dsimp only [rest]
  omega

def dagTagStepBin (mask full token : Word) (bank : List DagTagged) : List DagTagged :=
  let keep := token % 4
  let op := token / 4 % 4
  let x := bank.getD (token / (4 * 4 * 64)) (0, 0, 0)
  let y := bank.getD (token / (4 * 4) % 64) (0, 0, 0)
  let raw := binOp4 mask op x.1 y.1
  let comp := mask ^^^ raw
  let up0 := binOp4 full op x.2.1 y.2.1
  let dn0 := binOp4 full op x.2.2 y.2.2
  let tag := if raw < comp then (raw, up0, dn0) else (comp, full ^^^ up0, full ^^^ dn0)
  dagTagInsert tag (dagTagKeep (keep.testBit 1) y.1 (dagTagKeep (keep.testBit 0) x.1 bank))

def dagTraceTagsBin (mask width : Word) (root : List DagTagged) (fuel : Nat) (forest : Forest)
    (i : Nat) : List DagSignals :=
  let tags := (Nat.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun _ previous j =>
      let (parent, token) := forest j
      if Nat.beq parent 0 then dagTagRoot root token
      else dagTagStepBin mask (fullMask width) token (previous (parent - 1))) (fuel + 1)) i
  List.rec [] (fun tag _ rest => tag.2 :: rest) tags

def dagCheckChildrenBin (mask goal : Word) (cut : CutCheck)
    (reference : Nat → RowState → Bool) (state : RowState) (sample : DagSample) (tags : List DagSignals) : Bool :=
  let n := state.2.1.length
  dagForceWord (normWordFast mask goal) (fun ngoal =>
  dagForceWord (mask ^^^ goal) (fun negGoal =>
  (n ≤ 64) && !state.2.1.contains ngoal &&
  dagForceWord (dagPackWords256 state.2.1) (fun packed =>
    dagForceWord (dagLaneMarks256 n) (fun marks =>
      dagForceCache tags (fun tags =>
    dagForceWord (fullMask sample.2) (fun full =>
      dagCountSigns false full tags (fun normal =>
        treeBlock 0 n (fun a =>
          dagForceWord (state.2.1.getD a 0) (fun x =>
            dagForceWord (1 <<< (256 * a)) (fun aBit =>
              let xs := tags.getD a (0, 0)
              dagForceWord (dagSignalContrast false full xs) (fun xC =>
                treeBlock (a + 1) (n - (a + 1)) (fun b =>
                  dagForceWord (state.2.1.getD b 0) (fun y =>
                    dagForceWord (1 <<< (256 * b)) (fun bBit =>
                      let ys := tags.getD b (0, 0)
                      dagForceWord (dagSignalContrast false full ys) (fun yC =>
                        treeBlock 0 4 (fun op =>
                          dagForceWord (normBinOp4Fast mask op x y) (fun out =>
                            if out == 0 || out == mask || state.2.1.contains out then true else
                            dagForceWord (binOp4 full op xs.1 ys.1) (fun up =>
                              dagForceWord (binOp4 full op xs.2 ys.2) (fun down =>
                                dagForceWord (dagSignalContrast false full (up, down)) (fun outC =>
                                  treeBlock 0 4 (fun keep =>
                                    let ka := keep.testBit 0
                                    let kb := keep.testBit 1
                                    let nAfter := n - (if ka then 0 else 1) - (if kb then 0 else 1) + 1
                                    if Nat.blt state.1 nAfter then true
                                    else if dagSampleKill256 sample full normal xC yC outC packed marks aBit bBit out false ka kb then true
                                    else match dagDirectChildBin mask state a b op keep x y out with
                                    | none => true
                                    | some (fuel, ws, history) => dagForceWords ws (fun forced =>
                                      let child := (fuel, forced, history)
                                      let token := gateTokenBin a b op keep
                                      reference token child || dagLocalBinFast mask goal ngoal negGoal cut child))))))))))))))))))))))

theorem dagEarlyOpenBin256 {mask goal a b op keep out : Nat} {state child : RowState}
    {sample : DagSample} (full : Word) (counts : DagCounts) (xC yC outC : Word)
    (masked : Masked mask goal) (viable : BinViable mask goal child)
    (parent : state.2.1.Nodup) (svalid : dagSampleValid mask goal sample = true)
    (eval : dagDirectChildBin mask state a b op keep
      (state.2.1.getD a 0) (state.2.1.getD b 0) out = some child) :
    dagSampleKill256 sample full counts xC yC outC
      (dagPackWords256 state.2.1) (dagLaneMarks256 state.2.1.length)
      (1 <<< (256 * a)) (1 <<< (256 * b)) out false (keep.testBit 0) (keep.testBit 1) = false := by
  obtain ⟨fuel, ws, history⟩ := state
  let x := ws.getD a 0
  let y := ws.getD b 0
  apply Bool.eq_false_iff.mpr
  intro closed
  unfold dagSampleKill256 at closed
  simp only [dagForceWordEq] at closed
  generalize hmiss :
    (((counts.2.2 ||| (counts.2.1 ^^^ (counts.2.1 &&& (if keep.testBit 0 then 0 else xC) &&& (if keep.testBit 1 then 0 else yC))) |||
       (counts.1 ^^^ (counts.1 &&& ((if keep.testBit 0 then 0 else xC) ||| (if keep.testBit 1 then 0 else yC))))) ||| outC) ^^^ full) = missing at closed
  by_cases hm : Nat.beq missing 0 = true
  · simp only [hm, ite_true] at closed; cases closed
  · simp only [Bool.not_eq_true] at hm
    simp only [hm, Bool.false_eq_true, ite_false] at closed
    by_cases hlt : Nat.blt (dagHighest7 missing) sample.2 = true
    · simp only [hlt, ite_true] at closed
      have hidx : dagHighest7 missing < sample.2 := Nat.blt_eq.mp hlt
      have pairOK := treeBlock_at svalid (Nat.zero_le _) (by simpa using hidx)
      have closed' := dagPackedPair256Sound parent pairOK closed
      let bad : Bool := fuel == 0 || b ≥ ws.length || a ≥ b
      let stale : Bool := out == 0 || out == mask || ws.contains out
      let bank := keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
      change (if bad then none else if stale then none else
        some (fuel - 1, insertWord out bank, (out, x, y) :: history)) = some child at eval
      by_cases h : bad = true
      · simp [h] at eval
      by_cases h' : stale = true
      · simp [h, h'] at eval
      have eq : (fuel - 1, insertWord out bank, (out, x, y) :: history) = child := by simpa [h, h'] using eval
      subst child
      obtain ⟨nd, k, cap, live⟩ := viable
      have same : (out :: bank).toFinset = (insertWord out bank).toFinset := by
        ext w
        simp only [List.mem_toFinset, List.mem_cons, insertWordMem]
      have refuses := dagPairsOpenBin (pairs := [unpack sample.1 18 (dagHighest7 missing)]) masked
        (show LiveBin mask goal k (out :: bank).toFinset by rwa [same])
      exact Bool.noConfusion (closed'.symm.trans refuses)
    · simp only [Bool.not_eq_true] at hlt
      simp only [hlt, Bool.false_eq_true, ite_false] at closed

theorem dagChildAtBin {mask goal : Word} {cut : CutCheck} {ref : Nat → RowState → Bool}
    {state child : RowState} {sample : DagSample} {tags : List DagSignals} {a b op keep : Nat}
    (checked : dagCheckChildrenBin mask goal cut ref state sample tags = true)
    (svalid : dagSampleValid mask goal sample = true)
    (ha : a < state.2.1.length) (hab : a < b) (hb : b < state.2.1.length) (hop : op < 4) (hk : keep < 4)
    (eval : childStateBin mask (gateTokenBin a b op keep) state = some child)
    (masked : Masked mask goal) (viable : BinViable mask goal child) (nd : state.2.1.Nodup)
    (openChild : dagLocalBin mask goal cut child = false) :
    ref (gateTokenBin a b op keep) child = true := by
  have narrow : Nat.blt state.1 (state.2.1.length - (if keep.testBit 0 then 0 else 1) - (if keep.testBit 1 then 0 else 1) + 1) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hlt : state.1 < state.2.1.length - (if keep.testBit 0 then 0 else 1) - (if keep.testBit 1 then 0 else 1) + 1 := Nat.blt_eq.mp h
    have hb64 : b < 64 := by
      simp only [dagCheckChildrenBin, dagForceWordEq, dagForceCacheEq, dagCountSignsEq, normWordFast_eq,
        Bool.and_eq_true, decide_eq_true_eq] at checked
      omega
    obtain ⟨ke, _, _, _⟩ := gateTokenBinFields (a := a) hb64 hop hk
    have hpos : 0 < state.1 := by
      rcases state with ⟨sf, sws, shist⟩
      by_contra! hz
      have h0 : sf = 0 := by omega
      subst h0
      simp [childStateBin] at eval
    have hwide : dagTooWideBin state.2.1.length state.1 (gateTokenBin a b op keep) = true := by
      simp only [dagTooWideBin, dagSizeFloorBin, ke, decide_eq_true_eq]
      omega
    have tooMany := dagWideChildBin eval hwide
    obtain ⟨f, w, path⟩ := child
    simp [dagLocalBin, tooMany] at openChild
  simp only [dagCheckChildrenBin, dagForceCacheEq, dagForceWordEq, dagCountSignsEq, normWordFast_eq, normBinOp4Fast_eq,
    Bool.and_eq_true, decide_eq_true_eq] at checked
  have width := checked.1.1
  have atA := treeBlock_at checked.2 (i := a) (Nat.zero_le _) (by simpa using ha)
  have atB := treeBlock_at atA (i := b) (by omega) (by omega)
  have atOp := treeBlock_at atB (i := op) (Nat.zero_le _) (by simpa using hop)
  have fields := dagDirectChildBinEq (mask := mask) (state := state) (a := a) (b := b) (op := op)
    (keep := keep) (by omega) hop hk
  have direct := fields.trans eval
  have notStale : (normBinOp4 mask op (state.2.1.getD a 0) (state.2.1.getD b 0) == 0 ||
      normBinOp4 mask op (state.2.1.getD a 0) (state.2.1.getD b 0) == mask ||
      state.2.1.contains (normBinOp4 mask op (state.2.1.getD a 0) (state.2.1.getD b 0))) = false := by
    apply Bool.eq_false_iff.mpr
    intro hs
    rcases state with ⟨f, ws, hist⟩
    dsimp only [dagDirectChildBin] at hs direct
    by_cases hbad : (f == 0 || b ≥ ws.length || a ≥ b) = true
    · simp only [hbad, ite_true] at direct; cases direct
    · simp only [Bool.not_eq_true] at hbad
      simp only [hbad, Bool.false_eq_true, ite_false, hs, ite_true] at direct
      cases direct
  simp only [notStale, Bool.false_eq_true, ite_false] at atOp
  have atKeep := treeBlock_at atOp (i := keep) (Nat.zero_le _) (by simpa using hk)
  have early := fun full counts xC yC outC => dagEarlyOpenBin256 full counts xC yC outC masked viable nd svalid direct
  rcases child with ⟨fuel, ws, history⟩
  simpa only [narrow, Bool.false_eq_true, ite_false, fields, eval, dagForceWordsEq, early,
    dagLocalBinFast_eq, openChild, Bool.or_false] using atKeep

def HasChildBin (mask : Nat) (state child : RowState) : Prop :=
  ∃ a b op keep, a < state.2.1.length ∧ a < b ∧ b < state.2.1.length ∧ op < 4 ∧ keep < 4 ∧
    childStateBin mask (gateTokenBin a b op keep) state = some child

theorem binaryChildBin {mask fuel a b op : Nat} {ws : List Word}
    {history : List (Word × Word × Word)} {x y : Word} {keep : Nat}
    (hop : op < 4) (hab : a < b) (hb : b < ws.length) (hb64 : b < 64)
    (hf : fuel ≠ 0) (hk : keep < 4)
    (hx : ws.getD a 0 = x) (hy : ws.getD b 0 = y)
    (p : properWord mask (normBinOp4 mask op x y)) (fresh : normBinOp4 mask op x y ∉ ws) :
    childStateBin mask (gateTokenBin a b op keep) (fuel, ws, history) =
      some (fuel - 1, insertWord (normBinOp4 mask op x y)
        (keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)),
        (normBinOp4 mask op x y, x, y) :: history) := by
  obtain ⟨ke, ope, aa, bb⟩ := gateTokenBinFields (a := a) hb64 hop hk
  simp only [childStateBin, ke, ope, aa, bb, hx, hy]
  simp_all [Nat.not_le_of_lt hab, Nat.not_le_of_lt hb, keepWord, properWord]

theorem stepProgressBin {mask fuel k op : Nat} {x y target : Word} {U : Finset Word}
    {ws : List Word} {history : List (Word × Word × Word)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel) (hop : op < 4)
    (he : ws.toFinset = insert x (insert y U)) (xy : x ≠ y)
    (ordered : ws.idxOf x < ws.idxOf y) (fresh : normBinOp4 mask op x y ∉ insert x (insert y U))
    (tail : LiveBin mask target k (insert (normBinOp4 mask op x y) U)) :
    ∃ child, HasChildBin mask (fuel, ws, history) child ∧ BinViable mask target child := by
  let a := ws.idxOf x
  let b := ws.idxOf y
  have xm : x ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ym : y ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ha : a < ws.length := List.idxOf_lt_length_iff.mpr xm
  have hb : b < ws.length := List.idxOf_lt_length_iff.mpr ym
  have hab : a < b := ordered
  have hx : ws.getD a 0 = x := getWord xm
  have hy : ws.getD b 0 = y := getWord ym
  let v := normBinOp4 mask op x y
  have p := (liveBinProps tail v (Finset.mem_insert_self _ _)).1
  let saveX := decide (x ∈ U)
  let saveY := decide (y ∈ U)
  let keep := (if saveX then 1 else 0) + (if saveY then 2 else 0)
  have fields : keep < 4 ∧ keep.testBit 0 = saveX ∧ keep.testBit 1 = saveY := by
    unfold keep; cases saveX <;> cases saveY <;> decide
  obtain ⟨keepLt, bx, by'⟩ := fields
  have fn : v ∉ ws := by simpa [← List.mem_toFinset, he] using fresh
  let rest := keepWord saveY y (keepWord saveX x ws)
  let child : RowState := (fuel - 1, insertWord v rest, (v, x, y) :: history)
  refine ⟨child, ⟨a, b, op, keep, ha, hab, hb, hop, keepLt, ?_⟩, ?_⟩
  · have eq := binaryChildBin (fuel := fuel) (history := history) hop hab hb (by omega) (by omega) keepLt hx hy p fn
    rw [bx, by'] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup (keepNodup nd saveX x) saveY y)
      (fun h => fn (keepSubset saveX x ws _ (keepSubset saveY y _ _ h))), k, by change k ≤ fuel - 1; omega, ?_⟩
    change LiveBin mask target k (insertWord v rest).toFinset
    rw [insertWordSet, keepPairSet nd xy he]
    exact tail

theorem wordProgressBin {mask target : Word} {state : RowState}
    (width : state.2.1.length ≤ 64) (h : BinViable mask target state) :
    normWord mask target ∈ state.2.1 ∨ ∃ child, HasChildBin mask state child ∧ BinViable mask target child := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨nd, k, cap, live⟩ := h
  cases k with
  | zero =>
    obtain ⟨eq, _⟩ := live
    left
    change ws.toFinset = {normWord mask target} at eq
    rw [← List.mem_toFinset, eq]; simp
  | succ k =>
    right
    obtain ⟨U, x, y, op, hop, eq, px, py, xy, nx, ny, fresh, tail⟩ := live
    have xm : x ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have ym : y ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have diff : ws.idxOf x ≠ ws.idxOf y := by
      intro same; apply xy; rw [← getWord xm, same, getWord ym]
    by_cases hord : ws.idxOf x < ws.idxOf y
    · exact stepProgressBin nd width cap hop eq xy hord fresh tail
    · have eq' : ws.toFinset = insert y (insert x U) := by rw [eq, Finset.insert_comm]
      have fresh' : normBinOp4 mask (swapOp4 op) y x ∉ insert y (insert x U) := by
        rw [normBinOp4_swap mask hop, Finset.insert_comm]; exact fresh
      have tail' : LiveBin mask target k (insert (normBinOp4 mask (swapOp4 op) y x) U) := by
        rw [normBinOp4_swap mask hop]; exact tail
      exact stepProgressBin nd width cap (swapOp4_lt hop) eq' xy.symm (by omega) fresh' tail'

theorem childStateBinData {mask token : Nat} {state child : RowState}
    (eval : childStateBin mask token state = some child)
    (masked : ∀ w ∈ state.2.1, Masked mask w) :
    child.1 < state.1 ∧ ∀ w ∈ child.2.1, Masked mask w := by
  obtain ⟨fuel, ws, history⟩ := state
  let keep := token % 4
  let op := token / 4 % 4
  let a := token / (4 * 4 * 64)
  let b := token / (4 * 4) % 64
  let x := ws.getD a 0
  let y := ws.getD b 0
  let z := normBinOp4 mask op x y
  let rest := keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
  let bad : Bool := fuel == 0 || b ≥ ws.length || a ≥ b
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z, x, y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb, hs] at eval
  have eq : (fuel - 1, insertWord z rest, (z, x, y) :: history) = child := by simpa [hb, hs] using eval
  subst child
  have pos : 0 < fuel := by
    by_contra! h
    have he : fuel = 0 := by omega
    simp [bad, he] at hb
  refine ⟨by dsimp; omega, ?_⟩
  have mx : Masked mask x := readWordMasked masked a
  have my : Masked mask y := readWordMasked masked b
  have hm : Masked mask z := by
    apply masked_norm
    unfold binOp4
    split
    · exact masked_gateBin (bank := [x, y]) (by simpa using And.intro mx my)
        ⟨x, y, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inl rfl⟩
    split
    · exact masked_gateBin (bank := [x, y]) (by simpa using And.intro mx my)
        ⟨x, y, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inr rfl⟩
    split
    · exact masked_gateBin (bank := [x, y]) (by simpa using And.intro mx my)
        ⟨x, mask ^^^ y, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inr (by rw [xor_cancel_left]; simp))), Or.inl rfl⟩
    · exact masked_gateBin (bank := [x, y]) (by simpa using And.intro mx my)
        ⟨mask ^^^ x, y, Or.inr (Or.inr (Or.inr (by rw [xor_cancel_left]; simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inl rfl⟩
  intro w hw
  rcases insertWordMem.mp hw with rfl | other
  · exact hm
  · apply masked w
    apply keepSubset (keep.testBit 0) x ws w
    exact keepSubset (keep.testBit 1) y _ w other

def dagCheckNodeBin (mask goal : Word) (nodeBounds : Nat → List Bound)
    (count : Nat) (states : Nat → Option RowState) (moves : Array WordMove) (linkList : DagLinkList)
    (sample : DagSample) (tags : Nat → List DagSignals) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, history) =>
    dagForceWord goal (fun goal' =>
      dagFilterForceBoundsBin goal' (nodeBounds i) (fun activeBounds =>
        dagForceLinkList (linkList (i + 1)) (fun nlinks =>
          dagForceWords ws (fun forced =>
            dagStateOK mask forced && dagCheckChildrenBin mask goal' (dagKnownClosesBinNoHdr activeBounds)
              (dagRefBin mask count states moves (fun _ tok => dagFindLink nlinks tok) 0)
              (fuel, forced, history) sample (tags i)))))

def dagAllowedRootBin (mask : Word) (witnesses : List Witness) (ws : List Word) : Bool :=
  witnesses.all (fun entry => ws.contains (normWord mask (witnessWord entry)))

def dagCheckRootsBin (mask goal : Word) (cut : CutCheck)
    (witnesses : List Witness) (reference : Nat → RowState → Bool) (nstock : List Word)
    (fuel : Nat) : Bool :=
  treeBlock 0 (2 ^ nstock.length) fun token =>
    let state := rootState nstock fuel token
    !dagAllowedRootBin mask witnesses state.2.1 || dagLocalBin mask goal cut state || reference token state

theorem dagAllNodesBin {mask goal : Word} {width fuel count : Nat}
    {nstock : List Word} {nodeBounds : Nat → List Bound} {forest : Forest} {moves : Array WordMove}
    {linkList : DagLinkList} {sample : DagSample} {tags : Nat → List DagSignals}
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal)
    (svalid : dagSampleValid mask goal sample = true)
    (cutSound : ∀ i s, BinViable mask goal s →
      dagKnownClosesBinNoHdr (((nodeBounds i).filter (dagBoundHeaderOK goal)).map
        (fun b => (b.1, b.2.1.map (normWord b.1), b.2.2.1, b.2.2.2))) s = false)
    (autos : DagMovesOK mask goal width moves)
    (verified : treeBlock 0 count (dagCheckNodeBin mask goal nodeBounds count
      (dagTraceBin mask nstock fuel forest) moves linkList sample tags) = true) :
    ∀ cap i saved, i < count → dagTraceBin mask nstock fuel forest i = some saved →
      saved.1 = cap → ∀ k, k ≤ cap → ¬LiveBin mask goal k saved.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i s iBound stateEq sFuel k kBound live
    rcases s with ⟨remaining, words, history⟩
    let s : RowState := (remaining, words, history)
    let states := dagTraceBin mask nstock fuel forest
    change states i = some s at stateEq
    have checked := treeBlock_at verified (Nat.zero_le i) (by simpa using iBound)
    change dagCheckNodeBin mask goal nodeBounds count states moves linkList sample tags i = true at checked
    simp only [dagCheckNodeBin, stateEq, dagForceWordEq, dagFilterForceBoundsBinEq, dagForceLinkListEq,
      dagForceWordsEq, Bool.and_eq_true] at checked
    obtain ⟨nd, masked⟩ := dagStateOKSpec checked.1
    have ok := checked.2
    have viable : BinViable mask goal s := ⟨nd, k, sFuel ▸ kBound, live⟩
    have scanned := ok
    simp only [dagCheckChildrenBin, dagForceWordEq, normWordFast_eq, Bool.and_eq_true, decide_eq_true_eq] at scanned
    have wide := scanned.1.1
    have absent := scanned.1.2
    rcases wordProgressBin wide viable with hit | ⟨child, possible, cv⟩
    · simpa [hit] using absent
    obtain ⟨a, b, op, keep, ha, hab, hb, hop, hk, eval⟩ := possible
    have r := dagChildAtBin ok svalid ha hab hb hop hk eval goalMask cv nd
      (dagLocalBinOpen goalMask cv (cutSound i _ cv))
    have ⟨less, cm⟩ := childStateBinData eval masked
    have below : child.1 < cap := sFuel ▸ less
    obtain ⟨_, k', fits, clive⟩ := cv
    obtain ⟨j, dest, bound, restore, fuelEq, tail⟩ := dagLinkedBin maskBounds autos cm r clive
    exact ih child.1 below j dest bound restore fuelEq k' fits tail

theorem lowerDagBin {mask goal : Word} {width fuel count : Nat}
    {stock : List Word} {forest : Forest} {moves : Array WordMove} {linkList : DagLinkList}
    {sample : DagSample} {tags : Nat → List DagSignals}
    {bounds : List Bound} {nodeBounds : Nat → List Bound} {witnesses : List Witness}
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal) (proper : properWord mask goal)
    (svalid : dagSampleValid mask goal sample = true)
    (autos : DagMovesOK mask goal width moves)
    (stockMasked : ∀ w ∈ stock, Masked mask w)
    (nstockNd : (normStock mask stock).Nodup)
    (essential : witnesses.all (essentialB mask goal stock) = true)
    (known : KnownBin bounds) (submasks : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (nodeSub : ∀ i b, b ∈ nodeBounds i → b ∈ bounds)
    (rootCheck : dagCheckRootsBin mask goal (dagKnownClosesBin goal bounds) witnesses
      (dagRefBin mask count (dagTraceBin mask (normStock mask stock) fuel forest) moves
        (fun p tok => dagFindLink (linkList p) tok) 0)
      (normStock mask stock) fuel = true)
    (nodeCheck : treeBlock 0 count (dagCheckNodeBin mask goal nodeBounds
      count (dagTraceBin mask (normStock mask stock) fuel forest) moves linkList sample tags) = true) :
    BinLower mask stock goal (fuel + 1) := by
  intro values build hit
  by_contra! small
  obtain ⟨k, S, hk, live, sub⟩ := extractBinLive stockMasked build hit proper
  let nstock := normStock mask stock
  have included : S ⊆ nstock.toFinset := by
    intro w hw
    rw [normStockSet, List.mem_toFinset]
    exact sub w hw
  obtain ⟨token, tokenBound, eq⟩ := rootToken nstock S
  rw [Finset.inter_eq_right.mpr included] at eq
  let state := rootState nstock fuel token
  have eq' : state.2.1.toFinset = S := eq
  have v : BinViable mask goal state := by
    refine ⟨(rootWordSublist nstock token).nodup nstockNd, k, ?_, ?_⟩
    · change k ≤ fuel; omega
    · rwa [eq']
  have cutOpen (s : RowState) (h : BinViable mask goal s) : dagKnownClosesBin goal bounds s = false :=
    knownClosesBinSound known submasks h
  have nodeCutOpen (i : Nat) (s : RowState) (h : BinViable mask goal s) :
      dagKnownClosesBinNoHdr (((nodeBounds i).filter (dagBoundHeaderOK goal)).map
        (fun b => (b.1, b.2.1.map (normWord b.1), b.2.2.1, b.2.2.2))) s = false :=
    knownClosesBinNoHdrSound
      (fun b hb => known b (nodeSub i b (List.mem_filter.mp hb).1))
      (fun b hb => submasks b (nodeSub i b (List.mem_filter.mp hb).1))
      (fun b hb => (List.mem_filter.mp hb).2) h
  have openRoot := dagLocalBinOpen goalMask v (cutOpen _ v)
  have allowed : dagAllowedRootBin mask witnesses state.2.1 = true := by
    apply List.all_eq_true.mpr
    intro entry mem
    apply List.contains_iff_mem.mpr
    rw [← List.mem_toFinset, eq']
    exact essentialRequiredBin (List.all_eq_true.mp essential entry mem) sub live
  have checked := treeBlock_at rootCheck (Nat.zero_le token) (by simpa using tokenBound)
  change (!dagAllowedRootBin mask witnesses state.2.1 || dagLocalBin mask goal (dagKnownClosesBin goal bounds) state ||
    dagRefBin mask count (dagTraceBin mask nstock fuel forest) moves
      (fun p tok => dagFindLink (linkList p) tok) 0 token state) = true at checked
  simp only [allowed, openRoot, Bool.not_true, Bool.false_or] at checked
  have finish := dagAllNodesBin maskBounds goalMask svalid nodeCutOpen autos nodeCheck
  have fits : k ≤ fuel := by omega
  have still : LiveBin mask goal k state.2.1.toFinset := by rwa [eq']
  have nstockMasked : ∀ w ∈ nstock, Masked mask w := by
    intro w hw
    have h1 : w ∈ nstock.toFinset := List.mem_toFinset.mpr hw
    rw [normStockSet, List.mem_toFinset] at h1
    obtain ⟨orig, omem, rfl⟩ := List.mem_map.mp h1
    exact masked_norm (stockMasked orig omem)
  have stateMask : ∀ w ∈ state.2.1, Masked mask w := by
    intro w hw
    exact nstockMasked _ ((rootWordSublist nstock token).subset hw)
  obtain ⟨i, s, hi, restore, cap, plan⟩ := dagLinkedBin maskBounds autos stateMask checked still
  exact finish fuel i s hi restore cap k fits plan

-- ============================================================================
-- Part 4: Split HasCircuitSize bridge (0 NOTs -> MonoLower, >= 1 NOT -> BinLower)
-- ============================================================================

theorem hcsGateWordMono {rows : Nat} (bank : List (BitVec rows))
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or)
    (hlen : g.inputs.length ≤ 2) :
    GateWordMono (fullMask rows) (bank.map BitVec.toNat) (hcsGateVal bank g).toNat := by
  obtain ⟨op, ins⟩ := g
  have zeroAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) 0 := Or.inl rfl
  have maskAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) (fullMask rows) := Or.inr (Or.inl rfl)
  rcases hop with rfl | rfl
  · cases ins with
    | nil => exact gateMonoOfAvailable (by simpa [hcsGateVal, fullMask] using maskAv)
    | cons a t =>
      cases t with
      | nil => exact gateMonoOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inl (by simp [hcsGateVal, BitVec.toNat_and])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact gateMonoOfAvailable (by simpa [hcsGateVal] using zeroAv)
    | cons a t =>
      cases t with
      | nil => exact gateMonoOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inr (by simp [hcsGateVal, BitVec.toNat_or])⟩
        | cons c t => simp at hlen

def isNotOp : PEqualNP.CircuitLowerBounds.GateOp → Bool
  | PEqualNP.CircuitLowerBounds.GateOp.not => true
  | _ => false

def countNonNot : List PEqualNP.CircuitLowerBounds.Gate → Nat
  | [] => 0
  | g :: rest => (if isNotOp g.op then 0 else 1) + countNonNot rest

theorem countNonNot_le_sub {gs : List PEqualNP.CircuitLowerBounds.Gate}
    (h : ∃ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) :
    countNonNot gs + 1 ≤ gs.length := by
  induction gs with
  | nil => obtain ⟨_, hm, _⟩ := h; simp at hm
  | cons g gs ih =>
    have hle : ∀ l, countNonNot l ≤ l.length := by
      intro l; induction l with
      | nil => simp [countNonNot]
      | cons x xs ihx => simp only [countNonNot, List.length_cons]; cases isNotOp x.op <;> simp <;> omega
    obtain ⟨g', hm, hop⟩ := h
    rcases List.mem_cons.mp hm with rfl | hm
    · simp only [countNonNot, hop, isNotOp, ite_true, Nat.zero_add, List.length_cons]
      have := hle gs; omega
    · have := ih ⟨g', hm, hop⟩
      simp only [countNonNot, List.length_cons]
      cases isNotOp g.op <;> simp <;> omega

theorem hcsBuildsBin {rows : Nat} (raw : List (BitVec rows)) (bank : List Word)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (sub0 : ∀ v ∈ raw, AvBin (fullMask rows) bank v.toNat)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    ∃ vs, vs.length ≤ countNonNot gs ∧ WordBuildsBin (fullMask rows) bank vs ∧
      ∀ v ∈ gs.foldl hcsStep raw, AvBin (fullMask rows) (vs ++ bank) v.toNat := by
  induction gs generalizing raw bank with
  | nil => exact ⟨[], Nat.le_refl _, trivial, fun v hv => sub0 v hv⟩
  | cons g gs ih =>
    let v := hcsGateVal raw g
    have hg := hfan g List.mem_cons_self
    have hop := hg.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    have avRaw (i : Nat) : AvBin (fullMask rows) bank (raw.getD i 0).toNat := by
      rw [List.getD_eq_getElem?_getD]
      cases h : raw[i]? with
      | none => exact Or.inl rfl
      | some a => exact sub0 a (List.mem_of_getElem? h)
    rcases hop with h_and | h_or | h_not
    · have gm : GateWordMono (fullMask rows) (raw.map BitVec.toNat) v.toNat :=
        hcsGateWordMono raw g (Or.inl h_and) hg.2
      have gbin : GateBin (fullMask rows) bank v.toNat := by
        rcases gm with ⟨a, b, ha, hb, eq⟩
        exact ⟨a, b, avBin_weaken (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact sub0 y hy) (avBin_of_av ha),
          avBin_weaken (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact sub0 y hy) (avBin_of_av hb), eq⟩
      have sub1 : ∀ u ∈ hcsStep raw g, AvBin (fullMask rows) (v.toNat :: bank) u.toNat := by
        intro u hu
        simp only [hcsStep, List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hx)))) (sub0 u hu)
        · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
      obtain ⟨xs, len, built, reach⟩ := ih (hcsStep raw g) (v.toNat :: bank) sub1 (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
      refine ⟨v.toNat :: xs, ?_, ⟨gbin, built⟩, fun u hu => ?_⟩
      · simp only [countNonNot, h_and, isNotOp, Bool.false_eq_true, ite_false, List.length_cons]; omega
      · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (by
          simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hx)))) (reach u hu)
    · have gm : GateWordMono (fullMask rows) (raw.map BitVec.toNat) v.toNat :=
        hcsGateWordMono raw g (Or.inr h_or) hg.2
      have gbin : GateBin (fullMask rows) bank v.toNat := by
        rcases gm with ⟨a, b, ha, hb, eq⟩
        exact ⟨a, b, avBin_weaken (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact sub0 y hy) (avBin_of_av ha),
          avBin_weaken (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact sub0 y hy) (avBin_of_av hb), eq⟩
      have sub1 : ∀ u ∈ hcsStep raw g, AvBin (fullMask rows) (v.toNat :: bank) u.toNat := by
        intro u hu
        simp only [hcsStep, List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hx)))) (sub0 u hu)
        · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
      obtain ⟨xs, len, built, reach⟩ := ih (hcsStep raw g) (v.toNat :: bank) sub1 (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
      refine ⟨v.toNat :: xs, ?_, ⟨gbin, built⟩, fun u hu => ?_⟩
      · simp only [countNonNot, h_or, isNotOp, Bool.false_eq_true, ite_false, List.length_cons]; omega
      · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (by
          simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hx)))) (reach u hu)
    · have hv : AvBin (fullMask rows) bank v.toNat := by
        obtain ⟨op, ins⟩ := g
        simp only at h_not; subst op
        cases ins with
        | nil =>
          have : v.toNat = fullMask rows ^^^ 0 := by simpa [v, hcsGateVal] using notNat (0 : BitVec rows)
          rw [this]; exact avBin_not (Or.inl rfl)
        | cons a _ =>
          have : v.toNat = fullMask rows ^^^ (raw.getD a 0).toNat := by
            simpa [v, hcsGateVal] using notNat (raw.getD a 0)
          rw [this]; exact avBin_not (avRaw a)
      have sub1 : ∀ u ∈ hcsStep raw g, AvBin (fullMask rows) bank u.toNat := by
        intro u hu
        simp only [hcsStep, List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · exact sub0 u hu
        · exact hv
      obtain ⟨xs, len, built, reach⟩ := ih (hcsStep raw g) bank sub1 (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
      refine ⟨xs, ?_, built, reach⟩
      simp only [countNonNot, h_not, isNotOp, ite_true, Nat.zero_add]; exact len

theorem hcsBinLowerEq {m1 m2 g1 g2 min : Nat} {b1 b2 : List Word}
    (hm : m1 = m2) (hb : b1 = b2) (hg : g1 = g2)
    (h : BinLower m1 b1 g1 min) : BinLower m2 b2 g2 min := by
  subst hm; subst hb; subst hg; exact h

def ms0 : WordMoveStep := ([(0x9999999999999999999999999999999999999999999999999999999999999999, 0), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x4444444444444444444444444444444444444444444444444444444444444444, 1)])
def ms1 : WordMoveStep := ([(0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0x5050505050505050505050505050505050505050505050505050505050505050, 3)])
def ms2 : WordMoveStep := ([(0xaaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555, 0), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0x5555555500000000555555550000000055555555000000005555555500000000, 31)])
def ms3 : WordMoveStep := ([(0xaa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55, 0), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0x5500550055005500550055005500550055005500550055005500550055005500, 7)])
def ms4 : WordMoveStep := ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])
def ms5 : WordMoveStep := ([(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 8)], [(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 8)])
def ms6 : WordMoveStep := ([(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 16)], [(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 16)])
def ms7 : WordMoveStep := ([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)])
def ms8 : WordMoveStep := ([(0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333, 0), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x3333333300000000333333330000000033333333000000003333333300000000, 30)])
def ms9 : WordMoveStep := ([(0xf0f0f0f00f0f0f0ff0f0f0f00f0f0f0ff0f0f0f00f0f0f0ff0f0f0f00f0f0f0f, 0), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000, 28)])
def ms10 : WordMoveStep := ([(0xffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff, 0), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xffff000000000000ffff000000000000ffff000000000000ffff00000000, 16)])
def ms11 : WordMoveStep := ([(0x5555555555555555555555555555555555555555555555555555555555555555, 1)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 1)])
def ms12 : WordMoveStep := ([(0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333, 0), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x3333000033330000333300003333000033330000333300003333000033330000, 14)])
def ms13 : WordMoveStep := ([(0xf0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0f, 0), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000, 12)])
def sBase : List Word := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def sGoal : Word := 0xfe80e880fe008000
def s0M : Word := 0xaa000000aa00
abbrev s0G : Word := sGoal &&& s0M
abbrev s0W : List Word := projectDAGStock s0M sBase [1, 2, 5]
def s0F : Bound := (s0M, s0W, 4, s0G)
def s0E := unpackWitnesses s0W [7693, 269835, 546315]
abbrev s0N : List Word := normStock s0M s0W
def s0C : List Bound := []
def s0S : DagSample := (0x122d048ac120f148b41a2d148ac162b0683c160f, 9)
def s0L : DagLinkList := dagExtractLinks 0x9 0x7 2 1 3 1 1
def s0D : Forest := fun i => decodeNode 1 4 0xe i
def s0T := dagTraceTagsBin s0M 9 (dagTagBases s0N 0x4c11843 0x7ebdbd7 9) 3 s0D
def s0St := dagTraceBin s0M s0N 3 s0D
def s0Mv := dagMoves ([] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0A : DagMovesOK s0M s0G 256 s0Mv := dagMovesOfCheck (by decide +kernel)
def s0NB : Nat → List Bound := dagNodeBounds s0C.toArray 0 0 2 1 1
def s0Ck := dagCheckNodeBin s0M s0G s0NB 1 s0St s0Mv s0L s0S s0T
def s0RA (token : Nat) : Bool :=
  let s := rootState s0N 3 token
  !dagAllowedRootBin s0M s0E s.2.1 || dagLocalBin s0M s0G (dagKnownClosesBin s0G s0C) s ||
  dagRefBin s0M 1 s0St s0Mv (fun p tok => dagFindLink (s0L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0RB0 : treeBlock 0 8 s0RA = true := by decide +kernel
theorem s0RV : treeBlock 0 8 s0RA = true := s0RB0
theorem s0R : dagCheckRootsBin s0M s0G (dagKnownClosesBin s0G s0C) s0E (dagRefBin s0M 1 s0St s0Mv (fun p tok => dagFindLink (s0L p) tok) 0) s0N 3 = true := s0RV
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Bl0 : treeBlock 0 1 s0Ck = true := by decide +kernel
theorem s0Bk : treeBlock 0 1 s0Ck = true := s0Bl0
theorem s0K : KnownBin s0C := (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Bin : BinLower s0M s0W s0G 4 := by
  apply lowerDagBin _ _ _ _ s0A _ _ _ s0K _ (fun _ b hb => dagNodeBounds_mem b hb) s0R s0Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s0C, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s1M : Word := 0xf0000000f000
abbrev s1G : Word := sGoal &&& s1M
abbrev s1W : List Word := projectDAGStock s1M sBase [0, 1, 5]
def s1F : Bound := (s1M, s1W, 4, s1G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Bin : BinLower s1M s1W s1G 4 := dagShiftLowerBin (width := 256) [ms0, ms1] s0Bin (by decide +kernel)
def s2M : Word := 0xcc000000cc00
abbrev s2G : Word := sGoal &&& s2M
abbrev s2W : List Word := projectDAGStock s2M sBase [0, 2, 5]
def s2F : Bound := (s2M, s2W, 4, s2G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Bin : BinLower s2M s2W s2G 4 := dagShiftLowerBin (width := 256) [ms0] s0Bin (by decide +kernel)
def s3M : Word := 0xff0000000000
abbrev s3G : Word := sGoal &&& s3M
abbrev s3W : List Word := projectDAGStock s3M sBase [0, 1, 2]
def s3F : Bound := (s3M, s3W, 4, s3G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s3Bin : BinLower s3M s3W s3G 4 := dagShiftLowerBin (width := 256) [ms0, ms1, ms2, ms3, ms4, ms5, ms6] s0Bin (by decide +kernel)
def s4M : Word := 0xff000000ff00
abbrev s4G : Word := sGoal &&& s4M
abbrev s4W : List Word := projectDAGStock s4M sBase [0, 1, 2, 5]
def s4F : Bound := (s4M, s4W, 7, s4G)
def s4E := unpackWitnesses s4W [7694, 269837, 531979, 808459]
abbrev s4N : List Word := normStock s4M s4W
def s4C : List Bound := [s1F, s2F, s0F, s3F]
def s4S : DagSample := (0x140b8182e060b4100f040ac102d150b81c2e148b4180f160b8122d148ac142b0503c122b068b4120f160b4542b0683c162b0703c160f, 24)
def s4L : DagLinkList := dagExtractLinks 0x884422101789e02c01 0x6c480a048d21299c230483a0706d09119d21b320460406ca60dd0a1b994272206e2409c080b8000f 9 4 12 3 4
def s4D : Forest := fun i => decodeNode 3 15 0x18910091c1d2836406c805c8078 i
def s4T := dagTraceTagsBin s4M 24 (dagTagBases s4N 0xc320002490a0080d1410424b 0xff6632fcf9e89e9f557d57cf 24) 6 s4D
def s4St := dagTraceBin s4M s4N 6 s4D
def s4Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 3, 4, 5, 6, 7] 0 i.val)
def s4Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 3, 4, 5, 6, 7] 0 i.val)
def s4Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 2, 0, 3, 4, 5, 6, 7] 0 i.val)
def s4Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 0, 1, 3, 4, 5, 6, 7] 0 i.val)
def s4Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 5, 1, 3, 4, 2, 6, 7] 0 i.val)
def s4Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 5, 3, 4, 1, 6, 7] 0 i.val)
def s4Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 5, 0, 3, 4, 2, 6, 7] 0 i.val)
def s4Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 0, 5, 3, 4, 1, 6, 7] 0 i.val)
def s4Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 5, 0, 3, 4, 1, 6, 7] 0 i.val)
def s4Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 5, 0, 3, 4, 1, 6, 7] 0 i.val)
def s4Mp5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 3, 4, 5, 6, 7] 0 i.val)
def s4Mi5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 3, 4, 5, 6, 7] 0 i.val)
def s4Mp6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 5, 3, 4, 2, 6, 7] 0 i.val)
def s4Mi6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 5, 3, 4, 2, 6, 7] 0 i.val)
def s4Mp7 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 5, 3, 4, 2, 6, 7] 0 i.val)
def s4Mi7 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 5, 3, 4, 2, 6, 7] 0 i.val)
def s4Mv := dagMoves ([([ms7], s4Mp0, s4Mi0), ([ms1, ms0], s4Mp1, s4Mi1), ([ms7, ms8], s4Mp2, s4Mi2), ([ms1, ms0, ms8], s4Mp3, s4Mi3), ([ms1, ms8], s4Mp4, s4Mi4), ([ms0], s4Mp5, s4Mi5), ([ms9], s4Mp6, s4Mi6), ([ms0, ms9], s4Mp7, s4Mi7)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4A : DagMovesOK s4M s4G 256 s4Mv := dagMovesOfCheck (by decide +kernel)
def s4NB : Nat → List Bound := dagNodeBounds s4C.toArray 0x1a2d58a309204 0x1088688688 7 3 3
def s4Ck := dagCheckNodeBin s4M s4G s4NB 7 s4St s4Mv s4L s4S s4T
def s4RA (token : Nat) : Bool :=
  let s := rootState s4N 6 token
  !dagAllowedRootBin s4M s4E s.2.1 || dagLocalBin s4M s4G (dagKnownClosesBin s4G s4C) s ||
  dagRefBin s4M 7 s4St s4Mv (fun p tok => dagFindLink (s4L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4RB0 : treeBlock 0 16 s4RA = true := by decide +kernel
theorem s4RV : treeBlock 0 16 s4RA = true := s4RB0
theorem s4R : dagCheckRootsBin s4M s4G (dagKnownClosesBin s4G s4C) s4E (dagRefBin s4M 7 s4St s4Mv (fun p tok => dagFindLink (s4L p) tok) 0) s4N 6 = true := s4RV
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Bl0 : treeBlock 0 7 s4Ck = true := by decide +kernel
theorem s4Bk : treeBlock 0 7 s4Ck = true := s4Bl0
theorem s4K : KnownBin s4C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) s3Bin) s0Bin) s2Bin) s1Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Bin : BinLower s4M s4W s4G 7 := by
  apply lowerDagBin _ _ _ _ s4A _ _ _ s4K _ (fun _ b hb => dagNodeBounds_mem b hb) s4R s4Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s4C, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s5M : Word := 0xf000f0000000000
abbrev s5G : Word := sGoal &&& s5M
abbrev s5W : List Word := projectDAGStock s5M sBase [0, 1, 4]
def s5F : Bound := (s5M, s5W, 4, s5G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s5Bin : BinLower s5M s5W s5G 4 := dagShiftLowerBin (width := 256) [ms0, ms1, ms10, ms11, ms6] s0Bin (by decide +kernel)
def s6M : Word := 0x3300330000000000
abbrev s6G : Word := sGoal &&& s6M
abbrev s6W : List Word := projectDAGStock s6M sBase [0, 2, 4]
def s6F : Bound := (s6M, s6W, 4, s6G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Bin : BinLower s6M s6W s6G 4 := dagShiftLowerBin (width := 256) [ms0, ms10, ms11, ms6] s0Bin (by decide +kernel)
def s7M : Word := 0x5500550000000000
abbrev s7G : Word := sGoal &&& s7M
abbrev s7W : List Word := projectDAGStock s7M sBase [1, 2, 4]
def s7F : Bound := (s7M, s7W, 4, s7G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Bin : BinLower s7M s7W s7G 4 := dagShiftLowerBin (width := 256) [ms10, ms11, ms6] s0Bin (by decide +kernel)
def s8M : Word := 0xff00ff0000000000
abbrev s8G : Word := sGoal &&& s8M
abbrev s8W : List Word := projectDAGStock s8M sBase [0, 1, 2, 4]
def s8F : Bound := (s8M, s8W, 7, s8G)
def s8E := unpackWitnesses s8W [22058, 284201, 547369, 815657]
abbrev s8N : List Word := normStock s8M s8W
def s8C : List Bound := [s5F, s6F, s7F, s3F]
def s8S : DagSample := (0x1c0bc503c1c0b8503a140e4502e140b4502b1c0e870391c0f0543a148e4542e148b4583c160b8522b160b4542b, 20)
def s8L : DagLinkList := dagExtractLinks 0x884420300789e02c01 0x68300a09912109e4193444208864cc13990210303e04064a60cd0a1999423220662408c08098000f 9 4 12 3 4
def s8D : Forest := fun i => decodeNode 3 15 0x10614131a19203e4064804c8078 i
def s8T := dagTraceTagsBin s8M 20 (dagTagBases s8N 0x74b584a6b219d85a706f 0xfff5bffebefffe55f1ff 20) 6 s8D
def s8St := dagTraceBin s8M s8N 6 s8D
def s8Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 3, 4, 5, 6, 7] 0 i.val)
def s8Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 3, 4, 5, 6, 7] 0 i.val)
def s8Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 2, 0, 3, 4, 5, 6, 7] 0 i.val)
def s8Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 0, 1, 3, 4, 5, 6, 7] 0 i.val)
def s8Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 1, 3, 2, 5, 6, 7] 0 i.val)
def s8Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 4, 3, 1, 5, 6, 7] 0 i.val)
def s8Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 4, 0, 3, 2, 5, 6, 7] 0 i.val)
def s8Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 0, 4, 3, 1, 5, 6, 7] 0 i.val)
def s8Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 4, 0, 3, 1, 5, 6, 7] 0 i.val)
def s8Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 4, 0, 3, 1, 5, 6, 7] 0 i.val)
def s8Mp5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 3, 4, 5, 6, 7] 0 i.val)
def s8Mi5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 3, 4, 5, 6, 7] 0 i.val)
def s8Mp6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 4, 3, 2, 5, 6, 7] 0 i.val)
def s8Mi6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 4, 3, 2, 5, 6, 7] 0 i.val)
def s8Mp7 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 4, 3, 2, 5, 6, 7] 0 i.val)
def s8Mi7 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 4, 3, 2, 5, 6, 7] 0 i.val)
def s8Mv := dagMoves ([([ms7], s8Mp0, s8Mi0), ([ms1, ms0], s8Mp1, s8Mi1), ([ms7, ms12], s8Mp2, s8Mi2), ([ms1, ms0, ms12], s8Mp3, s8Mi3), ([ms1, ms12], s8Mp4, s8Mi4), ([ms0], s8Mp5, s8Mi5), ([ms13], s8Mp6, s8Mi6), ([ms0, ms13], s8Mp7, s8Mi7)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8A : DagMovesOK s8M s8G 256 s8Mv := dagMovesOfCheck (by decide +kernel)
def s8NB : Nat → List Bound := dagNodeBounds s8C.toArray 0x16ac4a9105204 0x1042688688 7 3 3
def s8Ck := dagCheckNodeBin s8M s8G s8NB 7 s8St s8Mv s8L s8S s8T
def s8RA (token : Nat) : Bool :=
  let s := rootState s8N 6 token
  !dagAllowedRootBin s8M s8E s.2.1 || dagLocalBin s8M s8G (dagKnownClosesBin s8G s8C) s ||
  dagRefBin s8M 7 s8St s8Mv (fun p tok => dagFindLink (s8L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8RB0 : treeBlock 0 16 s8RA = true := by decide +kernel
theorem s8RV : treeBlock 0 16 s8RA = true := s8RB0
theorem s8R : dagCheckRootsBin s8M s8G (dagKnownClosesBin s8G s8C) s8E (dagRefBin s8M 7 s8St s8Mv (fun p tok => dagFindLink (s8L p) tok) 0) s8N 6 = true := s8RV
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8Bl0 : treeBlock 0 7 s8Ck = true := by decide +kernel
theorem s8Bk : treeBlock 0 7 s8Ck = true := s8Bl0
theorem s8K : KnownBin s8C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) s3Bin) s7Bin) s6Bin) s5Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8Bin : BinLower s8M s8W s8G 7 := by
  apply lowerDagBin _ _ _ _ s8A _ _ _ s8K _ (fun _ b hb => dagNodeBounds_mem b hb) s8R s8Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s8C, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s9M : Word := 0x5500550055005500
abbrev s9G : Word := sGoal &&& s9M
abbrev s9W : List Word := projectDAGStock s9M sBase [1, 2, 4, 5]
def s9F : Bound := (s9M, s9W, 5, s9G)
def s9E := unpackWitnesses s9W [13336, 276504, 537610, 809998]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s9Bin : BinLower s9M s9W s9G 5 := by
  apply essentialLiftBin (witnesses := s9E) (cut := s7M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesBinOfCheck (old := s7W) (by decide +kernel)
  · exact s7Bin
  · decide +kernel
def s10M : Word := 0x3300330033003300
abbrev s10G : Word := sGoal &&& s10M
abbrev s10W : List Word := projectDAGStock s10M sBase [0, 2, 4, 5]
def s10F : Bound := (s10M, s10W, 5, s10G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10Bin : BinLower s10M s10W s10G 5 := dagShiftLowerBin (width := 256) [ms0] s9Bin (by decide +kernel)
def s11M : Word := 0xaa00aa00aa00aa00
abbrev s11G : Word := sGoal &&& s11M
abbrev s11W : List Word := projectDAGStock s11M sBase [1, 2, 4, 5]
def s11F : Bound := (s11M, s11W, 5, s11G)
def s11E := unpackWitnesses s11W [7693, 269835, 537097, 808459]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s11Bin : BinLower s11M s11W s11G 5 := by
  apply essentialLiftBin (witnesses := s11E) (cut := s0M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesBinOfCheck (old := s0W) (by decide +kernel)
  · exact s0Bin
  · decide +kernel
def s12M : Word := 0xcc00cc00cc00cc00
abbrev s12G : Word := sGoal &&& s12M
abbrev s12W : List Word := projectDAGStock s12M sBase [0, 2, 4, 5]
def s12F : Bound := (s12M, s12W, 5, s12G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Bin : BinLower s12M s12W s12G 5 := dagShiftLowerBin (width := 256) [ms0] s11Bin (by decide +kernel)
def s13M : Word := 0xf000f000f000f00
abbrev s13G : Word := sGoal &&& s13M
abbrev s13W : List Word := projectDAGStock s13M sBase [0, 1, 4, 5]
def s13F : Bound := (s13M, s13W, 5, s13G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Bin : BinLower s13M s13W s13G 5 := dagShiftLowerBin (width := 256) [ms0, ms1] s9Bin (by decide +kernel)
def s14M : Word := 0xf000f000f000f000
abbrev s14G : Word := sGoal &&& s14M
abbrev s14W : List Word := projectDAGStock s14M sBase [0, 1, 4, 5]
def s14F : Bound := (s14M, s14W, 5, s14G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s14Bin : BinLower s14M s14W s14G 5 := dagShiftLowerBin (width := 256) [ms0, ms1] s11Bin (by decide +kernel)
def s15M : Word := 0xff00ff00
abbrev s15G : Word := sGoal &&& s15M
abbrev s15W : List Word := projectDAGStock s15M sBase [0, 1, 2, 4]
def s15F : Bound := (s15M, s15W, 6, s15G)
def s15E := unpackWitnesses s15W [7694, 269837, 531979, 799241]
abbrev s15N : List Word := normStock s15M s15W
def s15C : List Bound := []
def s15S : DagSample := (0x5078141904868141c0406c1c1e06078181d05868141b07068100f06864101c0c07010190503c101a0483c181c0603c160f0c068141a0703c1a0f048643019, 28)
def s15L : DagLinkList := dagExtractLinks 0x941282504a09412825046288308610420748c901c001 0xe44c1a88831080641a3b848750802e0e054183904c70088240f0401a5783f8f0771a0de2c19a743f6e876d90ddaa199742f0e8561909c2a11a403f46076880dd08199402f260564809c88118401f060360805c08098000f 11 5 12 4 3
def s15D : Forest := fun i => decodeNode 4 16 0x44c8444883468383830303c2034242b14271423101f101b10171013100f0 i
def s15T := dagTraceTagsBin s15M 28 (dagTagBases s15N 0xb6a6530510f10368e94330010acc 0xdf77db92b1f7a7f8d7e73fffdfde 28) 5 s15D
def s15St := dagTraceBin s15M s15N 5 s15D
def s15Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 3, 4, 5, 6, 7] 0 i.val)
def s15Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 3, 4, 5, 6, 7] 0 i.val)
def s15Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 2, 0, 3, 4, 5, 6, 7] 0 i.val)
def s15Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 0, 1, 3, 4, 5, 6, 7] 0 i.val)
def s15Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 3, 4, 5, 6, 7] 0 i.val)
def s15Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 3, 4, 5, 6, 7] 0 i.val)
def s15Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 0, 1, 3, 4, 5, 6, 7] 0 i.val)
def s15Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 2, 0, 3, 4, 5, 6, 7] 0 i.val)
def s15Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 0, 3, 4, 5, 6, 7] 0 i.val)
def s15Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 0, 3, 4, 5, 6, 7] 0 i.val)
def s15Mv := dagMoves ([([ms7], s15Mp0, s15Mi0), ([ms1, ms0], s15Mp1, s15Mi1), ([ms0], s15Mp2, s15Mi2), ([ms0, ms1], s15Mp3, s15Mi3), ([ms1], s15Mp4, s15Mi4)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15A : DagMovesOK s15M s15G 256 s15Mv := dagMovesOfCheck (by decide +kernel)
def s15NB : Nat → List Bound := dagNodeBounds s15C.toArray 0 0 2 1 1
def s15Ck := dagCheckNodeBin s15M s15G s15NB 15 s15St s15Mv s15L s15S s15T
def s15RA (token : Nat) : Bool :=
  let s := rootState s15N 5 token
  !dagAllowedRootBin s15M s15E s.2.1 || dagLocalBin s15M s15G (dagKnownClosesBin s15G s15C) s ||
  dagRefBin s15M 15 s15St s15Mv (fun p tok => dagFindLink (s15L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15RB0 : treeBlock 0 16 s15RA = true := by decide +kernel
theorem s15RV : treeBlock 0 16 s15RA = true := s15RB0
theorem s15R : dagCheckRootsBin s15M s15G (dagKnownClosesBin s15G s15C) s15E (dagRefBin s15M 15 s15St s15Mv (fun p tok => dagFindLink (s15L p) tok) 0) s15N 5 = true := s15RV
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15Bl0 : treeBlock 0 15 s15Ck = true := by decide +kernel
theorem s15Bk : treeBlock 0 15 s15Ck = true := s15Bl0
theorem s15K : KnownBin s15C := (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15Bin : BinLower s15M s15W s15G 6 := by
  apply lowerDagBin _ _ _ _ s15A _ _ _ s15K _ (fun _ b hb => dagNodeBounds_mem b hb) s15R s15Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s15C, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s16M : Word := 0xff00ff00ff00ff00
abbrev s16G : Word := sGoal &&& s16M
abbrev s16W : List Word := projectDAGStock s16M sBase [0, 1, 2, 4, 5]
def s16E := unpackWitnesses s16W [7694, 269837, 531979, 799241, 1070603]
abbrev s16N : List Word := normStock s16M s16W
def s16C : List Bound := [s4F, s8F, s10F, s12F, s13F, s11F, s14F, s9F, s15F]
def s16S : DagSample := (0x50e8161a07068541a0506c141e150e8182e0586c142e1486412390483c122d04070140f048ac1c1e0603c101a150b81019148e4582e050ac181c148b4542b148ac1c2e0c070301a068b41a0f0583c141a0c0641c0f058ac1219, 40)
def s16L : DagLinkList := dagExtractLinks 0xf0f0e1d11c01 0x483013112bc4f8f12e2c478710db84f4e12d28474610cb83f0e0ec2837060cc001f 8 4 12 3 3
def s16D : Forest := fun i => decodeNode 2 14 0x311283b60dd833407c i
def s16T := dagTraceTagsBin s16M 40 (dagTagBases s16N 0xf7425947100036066289fab096991b014da9bce67cab74437d 0xbf437dd71c013eb76bc9deff9ebb3bfffffffcf7eddff4c7ff 40) 8 s16D
def s16St := dagTraceBin s16M s16N 8 s16D
def s16Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 3, 4, 5, 6, 7] 0 i.val)
def s16Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 3, 4, 5, 6, 7] 0 i.val)
def s16Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 3, 4, 5, 6, 7] 0 i.val)
def s16Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 3, 4, 5, 6, 7] 0 i.val)
def s16Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 2, 0, 3, 4, 5, 6, 7] 0 i.val)
def s16Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 0, 1, 3, 4, 5, 6, 7] 0 i.val)
def s16Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 0, 1, 3, 4, 5, 6, 7] 0 i.val)
def s16Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 2, 0, 3, 4, 5, 6, 7] 0 i.val)
def s16Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 0, 3, 4, 5, 6, 7] 0 i.val)
def s16Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 0, 3, 4, 5, 6, 7] 0 i.val)
def s16Mv := dagMoves ([([ms7], s16Mp0, s16Mi0), ([ms0], s16Mp1, s16Mi1), ([ms1, ms0], s16Mp2, s16Mi2), ([ms0, ms1], s16Mp3, s16Mi3), ([ms1], s16Mp4, s16Mi4)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s16A : DagMovesOK s16M s16G 256 s16Mv := dagMovesOfCheck (by decide +kernel)
def s16NB : Nat → List Bound := dagNodeBounds s16C.toArray 0x1a4942dc5202 0x321076543210754321087654321010 9 4 4
def s16Ck := dagCheckNodeBin s16M s16G s16NB 5 s16St s16Mv s16L s16S s16T
def s16RA (token : Nat) : Bool :=
  let s := rootState s16N 8 token
  !dagAllowedRootBin s16M s16E s.2.1 || dagLocalBin s16M s16G (dagKnownClosesBin s16G s16C) s ||
  dagRefBin s16M 5 s16St s16Mv (fun p tok => dagFindLink (s16L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s16RB0 : treeBlock 0 32 s16RA = true := by decide +kernel
theorem s16RV : treeBlock 0 32 s16RA = true := s16RB0
theorem s16R : dagCheckRootsBin s16M s16G (dagKnownClosesBin s16G s16C) s16E (dagRefBin s16M 5 s16St s16Mv (fun p tok => dagFindLink (s16L p) tok) 0) s16N 8 = true := s16RV
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s16Bl0 : treeBlock 0 5 s16Ck = true := by decide +kernel
theorem s16Bk : treeBlock 0 5 s16Ck = true := s16Bl0
theorem s16K : KnownBin s16C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) s15Bin) s9Bin) s14Bin) s11Bin) s13Bin) s12Bin) s10Bin) s8Bin) s4Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s16Bin : BinLower s16M s16W s16G 9 := by
  apply lowerDagBin _ _ _ _ s16A _ _ _ s16K _ (fun _ b hb => dagNodeBounds_mem b hb) s16R s16Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s16C, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s17M : Word := 0xffffffffffffffff
abbrev s17G : Word := sGoal &&& s17M
abbrev s17W : List Word := projectDAGStock s17M sBase [0, 1, 2, 3, 4, 5]
def s17E := unpackWitnesses s17W [7694, 269837, 531979, 794119, 1061385, 1332747]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s17Bin : BinLower s17M s17W s17G 10 := by
  apply essentialLiftBin (witnesses := s17E) (cut := s16M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesBinOfCheck (old := s16W) (by decide +kernel)
  · exact s16Bin
  · decide +kernel

theorem hcsNotLowerBin6 (raw : List (BitVec 64)) (goal : BitVec 64) (min : Nat)
    (f : (Fin 6 → Bool) → Bool)
    (hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin 6 => r.testBit j.val) 6 0 = true)
    (hGoal : hcsCheckPow (fun r => goal.getLsbD r == f fun j : Fin 6 => r.testBit j.val) 6 0 = true)
    (binClaim : BinLower (fullMask 64) (raw.map BitVec.toNat) goal.toNat min)
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hnot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not)
    (hev : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = f x) :
    min + 1 ≤ C.gates.length := by
  let eb := C.gates.foldl hcsStep raw
  have same : eb.getD C.output 0 = goal := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let y : Fin 6 → Bool := fun k => j.testBit k.val
    have hbank : raw.map (fun v => v.getLsbD j) = List.ofFn y :=
      beq_iff_eq.mp (hcsCheckPow_spec hRaw (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
    have hfg : goal.getLsbD j = f y :=
      beq_iff_eq.mp (hcsCheckPow_spec hGoal (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
    have hbits := hcsFoldBits raw ⟨j, hj⟩ C.gates hfan
    have hevj : (C.wires (List.ofFn y)).getD C.output false = f y := hev y
    change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
      (List.ofFn y)).getD C.output false = f y at hevj
    rw [← hbank, ← hbits] at hevj
    rw [hfg, ← hevj, ← hcsGetDBit]
  obtain ⟨vs, len, built, reach⟩ := hcsBuildsBin raw (raw.map BitVec.toNat) C.gates
    (fun v hv => Or.inr (Or.inr (Or.inl (List.mem_map_of_mem hv)))) hfan
  have av : AvBin (fullMask 64) (vs ++ raw.map BitVec.toNat) goal.toNat := by
    rw [← same, List.getD_eq_getElem?_getD]
    cases hget : eb[C.output]? with
    | none => exact Or.inl rfl
    | some v => exact reach v (List.mem_of_getElem? hget)
  have lb := binClaim vs built av
  have hcnt := countNonNot_le_sub hnot
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma targetNotLower
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hnot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not)
    (hev : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) =
      Nat.testBit (4269860992 * 2 ^ 32 + 4261445632)
        (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) :
    11 ≤ C.gates.length := by
  let raw : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc,
    0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
  let goal : BitVec 64 := 0xfe80e880fe008000
  have hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) ==
      List.ofFn fun j : Fin 6 => r.testBit j.val) 6 0 = true := by decide +kernel
  have hGoal : hcsCheckPow (fun r => goal.getLsbD r ==
      Nat.testBit (4269860992 * 2 ^ 32 + 4261445632)
        (∑ i : Fin 6, if r.testBit i.val then 2 ^ (i : ℕ) else 0)) 6 0 = true := by
    decide +kernel
  have binRoot : BinLower (fullMask 64) (raw.map BitVec.toNat) goal.toNat 10 :=
    hcsBinLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) s17Bin
  exact hcsNotLowerBin6 raw goal 10 _ hRaw hGoal binRoot C hfan hnot hev

end PEqualNP.Outside.L_meta_12087_aux
