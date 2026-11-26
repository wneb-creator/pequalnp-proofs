import PEqualNP.Defs
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.NormNum
namespace PEqualNP.Outside.L_meta_18006

namespace WordEngine
def unpack (packed width index : Nat) : Nat :=
  (packed >>> (width * index)) &&& ((1 <<< width) - 1)
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
theorem treeBlock_merge {start left right : Nat} {check : Nat → Bool}
    (a : treeBlock start left check = true)
    (b : treeBlock (start + left) right check = true) :
    treeBlock start (left + right) check = true := by
  induction left generalizing start with
  | zero => simpa using b
  | succ left ih =>
    rw [Nat.succ_add]
    change (check start && treeBlock (start + 1) (left + right) check) = true
    change (check start && treeBlock (start + 1) left check) = true at a
    rcases Bool.and_eq_true_iff.mp a with ⟨here, rest⟩
    exact Bool.and_eq_true_iff.mpr ⟨here, ih rest (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using b)⟩
abbrev Word := Nat
abbrev RowState := Nat × List Word × List (Word × Word × Word)
def insertWord (w : Word) (ws : List Word) : List Word :=
  List.rec [w] (fun a tail next => if w ≤ a then w :: a :: tail else a :: next) ws
def childState (mask token : Nat) (state : RowState) : Option RowState :=
  let (fuel, ws, history) := state
  let keep := token % 4
  let op := (token / 4) % 3
  let a := token / (4 * 3 * 64)
  let b := (token / (4 * 3)) % 64
  if fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b) then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let w := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
    if w == 0 || w == mask || ws.contains w then none
    else
      let rest := if keep.testBit 0 then ws else ws.erase x
      let rest := if op == 2 || keep.testBit 1 then rest else rest.erase y
      some (fuel - 1, insertWord w rest, (w, x, y) :: history)
def gateToken (a b op keep : Nat) : Nat := ((a * 64 + b) * 3 + op) * 4 + keep
def maskFlat (mask word : Nat) : Bool :=
  let v := word &&& mask
  v == 0 || v == mask
def flatCount (mask : Nat) (words : List Word) : Nat :=
  List.rec 0 (fun word _ count => if maskFlat mask word then count + 1 else count) words
def availableB (mask : Nat) (bank : List Word) (w : Word) : Bool :=
  w == 0 || w == mask || bank.contains w
def AvailableWord (mask : Nat) (bank : List Word) (word : Word) : Prop :=
  word = 0 ∨ word = mask ∨ word ∈ bank
def GateWord (mask : Nat) (bank : List Word) (out : Word) : Prop :=
  (∃ a, AvailableWord mask bank a ∧ out = mask ^^^ a) ∨
  (∃ a b, AvailableWord mask bank a ∧ AvailableWord mask bank b ∧
    (out = a &&& b ∨ out = a ||| b))
theorem restrictWord (mask : Nat) (word : Word) : word &&& mask &&& mask = word &&& mask := by
  simp
theorem projectGate {mask cut : Nat} (submask : mask &&& cut = cut)
    {roots : List Word} {out : Word} (gate : GateWord mask roots out) :
    GateWord cut (roots.map (· &&& cut)) (out &&& cut) := by
  have av {word : Word} (ha : AvailableWord mask roots word) :
      AvailableWord cut (roots.map (· &&& cut)) (word &&& cut) := by
    rcases ha with rfl | rfl | hm
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl submask)
    · exact Or.inr (Or.inr (List.mem_map_of_mem hm))
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, eq | eq⟩
  · refine Or.inl ⟨a &&& cut, av ha, ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    have cutAt := congrArg (fun n : Nat => n.testBit i) submask
    simp only [Nat.testBit_and, Nat.testBit_xor] at cutAt ⊢
    cases h : cut.testBit i
    · simp
    · simp [h] at cutAt
      simp [cutAt]
  · subst out
    refine Or.inr ⟨a &&& cut, b &&& cut, av ha, av hb, Or.inl ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and]
    cases cut.testBit i <;> simp
  · subst out
    refine Or.inr ⟨a &&& cut, b &&& cut, av ha, av hb, Or.inr ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases cut.testBit i <;> simp
theorem availableWeaken {mask : Nat} {small big : List Word} {w : Word}
    (sub : ∀ x ∈ small, AvailableWord mask big x)
    (av : AvailableWord mask small w) : AvailableWord mask big w := by
  rcases av with rfl | rfl | h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact sub w h
def properWord (mask word : Word) : Prop := word ≠ 0 ∧ word ≠ mask
def binWord (isOr : Bool) (a b : Word) : Word :=
  if isOr then a ||| b else a &&& b
theorem binWord_comm (d : Bool) (a b : Word) : binWord d a b = binWord d b a := by
  cases d <;> simp [binWord, Nat.land_comm, Nat.lor_comm]
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
theorem liveWordProper {k t S} (h : LiveWord mask target k t S) : ∀ a ∈ S, properWord mask a := by
  induction h using LiveWord.ind with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
theorem liveWordSize {k t S} (h : LiveWord mask target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using LiveWord.ind with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : (mask ^^^ a) ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : binWord d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩
def wordRep (mask : Nat) (ws : List Word) (w : Word) : Prop :=
  w ∈ ws ∨ ¬properWord mask w
def Masked (mask word : Nat) : Prop := word &&& mask = word
theorem maskedAvailable {bank : List Word} {word : Word}
    (all : ∀ w ∈ bank, Masked mask w) (aw : AvailableWord mask bank word) :
    Masked mask word := by
  rcases aw with rfl | rfl | hw
  · simp [Masked]
  · simp [Masked]
  · exact all _ hw
theorem maskedGate {bank : List Word} {out : Word}
    (all : ∀ w ∈ bank, Masked mask w) (g : GateWord mask bank out) :
    Masked mask out := by
  rcases g with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, ea | ea⟩
  · have h := projectGate (mask := mask) (cut := mask) (by simp)
      (roots := bank) (out := mask ^^^ a) (Or.inl ⟨a, ha, rfl⟩)
    have ma := maskedAvailable all ha
    unfold Masked at ma ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have bit := congrArg (fun n : Nat => n.testBit i) ma
    simp only [Nat.testBit_and, Nat.testBit_xor] at bit ⊢
    cases hm : mask.testBit i <;> simp_all
  · subst out
    have ma := maskedAvailable all ha
    have mb := maskedAvailable all hb
    simp only [Masked] at ma mb ⊢
    rw [Nat.land_assoc, mb]
  · subst out
    have ma := maskedAvailable all ha
    have mb := maskedAvailable all hb
    unfold Masked at ma mb ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have bitA := congrArg (fun n : Nat => n.testBit i) ma
    have bitB := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and, Nat.testBit_or] at bitA bitB ⊢
    cases hm : mask.testBit i <;> simp_all
def binaryWitness (mask : Nat) (bank : List Word) (out : Word) : Prop :=
  ∃ d a b, a ∈ bank ∧ b ∈ bank ∧ properWord mask a ∧ properWord mask b ∧
    a ≠ b ∧ out = binWord d a b
theorem classifyBinary {bank : List Word}
    (all : ∀ w ∈ bank, Masked mask w) (d : Bool) {a b : Word}
    (ha : AvailableWord mask bank a) (hb : AvailableWord mask bank b) :
    wordRep mask bank (binWord d a b) ∨ binaryWitness mask bank (binWord d a b) := by
  have c0 : wordRep mask bank 0 := Or.inr fun h => h.1 rfl
  have cm : wordRep mask bank mask := Or.inr fun h => h.2 rfl
  have classify {w : Word} (hw : AvailableWord mask bank w) :
      w = 0 ∨ w = mask ∨ w ∈ bank ∧ properWord mask w := by
    by_cases zh : w = 0
    · exact Or.inl zh
    by_cases mh : w = mask
    · exact Or.inr (Or.inl mh)
    exact Or.inr (Or.inr ⟨(hw.resolve_left zh).resolve_left mh, zh, mh⟩)
  have ma : a &&& mask = a := maskedAvailable all ha
  have mb : b &&& mask = b := maskedAvailable all hb
  have absorbA : a ||| mask = mask := by
    apply Nat.eq_of_testBit_eq
    intro i
    have h := congrArg (fun n : Nat => n.testBit i) ma
    simp only [Nat.testBit_and, Nat.testBit_or] at h ⊢
    cases hm : mask.testBit i <;> simp_all
  have absorbB : b ||| mask = mask := by
    apply Nat.eq_of_testBit_eq
    intro i
    have h := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and, Nat.testBit_or] at h ⊢
    cases hm : mask.testBit i <;> simp_all
  rcases classify ha with rfl | hma | ⟨ha', pa⟩
  · rw [binWord_comm]
    cases d
    · exact Or.inl (by simpa [binWord] using c0)
    · rcases hb with hz | hm | hv
      · exact Or.inl (by simpa [binWord, hz] using c0)
      · exact Or.inl (by simpa [binWord, hm] using cm)
      · exact Or.inl (by simpa [binWord, wordRep] using
          (Or.inl hv : wordRep mask bank b))
  · rw [hma, binWord_comm]
    cases d
    · rcases hb with hz | hm | hv
      · exact Or.inl (by simpa [binWord, hz] using c0)
      · exact Or.inl (by simpa [binWord, hm] using cm)
      · exact Or.inl (by simpa [binWord, mb, wordRep] using
          (Or.inl hv : wordRep mask bank b))
    · exact Or.inl (by simpa [binWord, absorbB] using cm)
  rcases classify hb with rfl | hmb | ⟨hb', pb⟩
  · cases d
    · exact Or.inl (by simpa [binWord] using c0)
    · exact Or.inl (by simpa [binWord, wordRep] using
        (Or.inl ha' : wordRep mask bank a))
  · rw [hmb]
    cases d
    · exact Or.inl (by simpa [binWord, ma, wordRep] using
        (Or.inl ha' : wordRep mask bank a))
    · exact Or.inl (by simpa [binWord, absorbA] using cm)
  by_cases eq : a = b
  · subst b
    cases d <;> exact Or.inl (by simpa [binWord, wordRep] using
      (Or.inl ha' : wordRep mask bank a))
  exact Or.inr ⟨d, a, b, ha', hb', pa, pb, eq, rfl⟩
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
theorem gateTokenFields {a b op keep : Nat} (hb : b < 64) (ho : op < 3) (hk : keep < 4) :
    gateToken a b op keep % 4 = keep ∧
    gateToken a b op keep / 4 % 3 = op ∧
    gateToken a b op keep / (4 * 3 * 64) = a ∧
    gateToken a b op keep / (4 * 3) % 64 = b := by
  unfold gateToken
  omega
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
theorem binaryChild {mask fuel a b : Nat} {ws : List Word}
    {history : List (Word × Word × Word)} {x y : Word} {keep : Nat}
    (d : Bool) (hab : a < b) (hb : b < ws.length) (hb64 : b < 64)
    (hf : fuel ≠ 0) (hk : keep < 4)
    (hx : ws.getD a 0 = x) (hy : ws.getD b 0 = y)
    (p : properWord mask (binWord d x y)) (fresh : binWord d x y ∉ ws) :
    childState mask (gateToken a b (if d then 1 else 0) keep) (fuel, ws, history) =
      some (fuel - 1, insertWord (binWord d x y)
        (keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)),
        (binWord d x y, x, y) :: history) := by
  have oh : (if d then 1 else 0) < 3 := by cases d <;> decide
  obtain ⟨ke, op, aa, bb⟩ := gateTokenFields (a := a) hb64 oh hk
  simp only [childState, ke, op, aa, bb, hx, hy]
  cases d <;>
    simp_all [Nat.not_le_of_lt hab, Nat.not_le_of_lt hb, keepWord, binWord, properWord]
variable {rows : Nat}
def fullMask (rows : Nat) : Nat := 2 ^ rows - 1
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
theorem cofBinary (m a b : Word) (d : Bool) :
    binWord d a b &&& m = binWord d (a &&& m) (b &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases d <;> simp only [binWord, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and, Nat.testBit_or] <;>
    cases m.testBit i <;> simp
theorem flBoth {m a b : Word} {d : Bool} (ha : maskedFlat m a) (hb : maskedFlat m b) :
    maskedFlat m (binWord d a b) := by
  unfold maskedFlat at *
  rw [cofBinary]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> cases d <;>
    simp [binWord, ha, hb]
theorem simpleBin {m a b : Word} {d : Bool} (h : maskedFlat m a ∨ maskedFlat m b) :
    binWord d a b &&& m = 0 ∨ binWord d a b &&& m = m ∨
      binWord d a b &&& m = a &&& m ∨ binWord d a b &&& m = b &&& m := by
  rw [cofBinary]
  have top1 (x : Word) : m &&& (x &&& m) = x &&& m := by
    rw [Nat.land_comm x m, ← Nat.land_assoc]
    simp
  have top2 (x : Word) : m ||| (x &&& m) = m := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_or, Nat.testBit_and]
    cases x.testBit i <;> cases m.testBit i <;> rfl
  have right1 (x : Word) : (x &&& m) &&& m = x &&& m := restrictWord m x
  have right2 (x : Word) : (x &&& m) ||| m = m := by rw [Nat.lor_comm, top2]
  rcases h with (ha|ha)|(hb|hb) <;> cases d <;>
    simp [binWord, *, top1, top2, right1, right2]
def projectedStock (m : Word) (s : Finset (Word)) := insert 0 (insert m (visibleWords m s))
theorem availableB_spec {mask : Nat} {bank : List Word} {v : Word} :
    availableB mask bank v = true ↔ AvailableWord mask bank v := by
  simp [availableB, AvailableWord, or_assoc]
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
theorem kw_step (goal : Word) (D D' : Finset Word) (u v w : ℕ) (c : ℕ → ℕ → Bool) (f : ℕ → ℕ → ℕ)
    (hu : u ∈ D) (hv : v ∈ D) (huv : u ≠ v) (huD : u ∉ D') (hvD : v ∉ D')
    (hsub : ∀ x ∈ D', x ≠ w → x ∈ D)
    (hf : ∀ e i, goal.testBit e = true → goal.testBit i = false →
      f e i ∈ D' ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false)
    (hr : ∀ e i e' i', goal.testBit e = true → goal.testBit e' = true → goal.testBit i = false → goal.testBit i' = false → f e i = f e' i' → f e i' = f e i)
    (hcu : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = true →
      u.testBit e = true ∧ u.testBit i = false)
    (hcv : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = false →
      v.testBit e = true ∧ v.testBit i = false)
    (hc : ∀ e i e' i', c e i = c e' i' → c e i' = c e i) :
    ∃ g : ℕ → ℕ → ℕ,
      (∀ e i, goal.testBit e = true → goal.testBit i = false →
        g e i ∈ D ∧ (g e i).testBit e = true ∧ (g e i).testBit i = false) ∧
      (∀ e i e' i', goal.testBit e = true → goal.testBit e' = true → goal.testBit i = false → goal.testBit i' = false → g e i = g e' i' → g e i' = g e i) := by
  have hg : ∀ e i, goal.testBit e = true → goal.testBit i = false → f e i = w →
      ((if f e i = w then (cond (c e i) u v) else f e i) = u ∧ c e i = true) ∨
      ((if f e i = w then (cond (c e i) u v) else f e i) = v ∧ c e i = false) := by
    intro e i _ _ h
    rw [ite_eq_left (h)]
    cases c e i
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  refine ⟨fun e i => if f e i = w then (cond (c e i) u v) else f e i, ?_, ?_⟩
  · intro e i he hi
    obtain ⟨h1, h2, h3⟩ := hf e i he hi
    show (if f e i = w then (cond (c e i) u v) else f e i) ∈ D ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit e = true ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit i = false
    by_cases hw : f e i = w
    · rw [hw] at h2 h3
      rcases hg e i he hi hw with ⟨hx, hcc⟩ | ⟨hx, hcc⟩
      · rw [hx]; exact ⟨hu, hcu e i h2 h3 hcc⟩
      · rw [hx]; exact ⟨hv, hcv e i h2 h3 hcc⟩
    · rw [ite_eq_right (hw)]; exact ⟨hsub _ h1 hw, h2, h3⟩
  · intro e i e' i' he he' hi hi' heq
    show (if f e i' = w then (cond (c e i') u v) else f e i') =
      (if f e i = w then (cond (c e i) u v) else f e i)
    have heq' : (if f e i = w then (cond (c e i) u v) else f e i) =
      (if f e' i' = w then (cond (c e' i') u v) else f e' i') := heq
    by_cases h1 : f e i = w
    · by_cases h2 : f e' i' = w
      · have h3 : f e i' = w := (hr e i e' i' he he' hi hi' (h1.trans h2.symm)).trans h1
        have hcc : c e i = c e' i' := by
          rcases hg e i he hi h1 with ⟨hx, hx'⟩ | ⟨hx, hx'⟩ <;>
            rcases hg e' i' he' hi' h2 with ⟨hy, hy'⟩ | ⟨hy, hy'⟩
          · rw [hx', hy']
          · exact absurd (hx.symm.trans (heq'.trans hy)) huv
          · exact absurd (hy.symm.trans (heq'.symm.trans hx)) huv
          · rw [hx', hy']
        rw [ite_eq_left (h3), ite_eq_left (h1), hc e i e' i' hcc]
      · exfalso
        rw [ite_eq_right (h2)] at heq'
        have hm := (hf e' i' he' hi').1
        rcases hg e i he hi h1 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, heq']; exact hm)
        · exact hvD (by rw [← hx, heq']; exact hm)
    · by_cases h2 : f e' i' = w
      · exfalso
        rw [ite_eq_right (h1)] at heq'
        have hm := (hf e i he hi).1
        rcases hg e' i' he' hi' h2 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, ← heq']; exact hm)
        · exact hvD (by rw [← hx, ← heq']; exact hm)
      · have h1n : (if f e i = w then (cond (c e i) u v) else f e i) = f e i := ite_eq_right h1
        have h2n : (if f e' i' = w then (cond (c e' i') u v) else f e' i') = f e' i' := ite_eq_right h2
        rw [h1n, h2n] at heq'
        have h3 := hr e i e' i' he he' hi hi' heq'
        have h3n : ¬ f e i' = w := by rw [h3]; exact h1
        rw [h1n, ite_eq_right (h3n)]
        exact h3
theorem and_cu (u v e i : ℕ) (h1 : (u &&& v).testBit e = true) (_h2 : (u &&& v).testBit i = false)
    (h3 : (!(u.testBit i)) = true) : u.testBit e = true ∧ u.testBit i = false := by
  rw [Nat.testBit_and] at h1
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem and_cv (u v e i : ℕ) (h1 : (u &&& v).testBit e = true) (h2 : (u &&& v).testBit i = false)
    (h3 : (!(u.testBit i)) = false) : v.testBit e = true ∧ v.testBit i = false := by
  rw [Nat.testBit_and] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem or_cu (u v e i : ℕ) (_h1 : (u ||| v).testBit e = true) (h2 : (u ||| v).testBit i = false)
    (h3 : u.testBit e = true) : u.testBit e = true ∧ u.testBit i = false := by
  rw [Nat.testBit_or] at h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem or_cv (u v e i : ℕ) (h1 : (u ||| v).testBit e = true) (h2 : (u ||| v).testBit i = false)
    (h3 : u.testBit e = false) : v.testBit e = true ∧ v.testBit i = false := by
  rw [Nat.testBit_or] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
def KWPartition (goal : Word) (ws : Finset Word) : Prop :=
  ∃ f : Nat → Nat → Word,
    (∀ e i, goal.testBit e = true → goal.testBit i = false →
      f e i ∈ ws ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false) ∧
    (∀ e i e' i', goal.testBit e = true → goal.testBit e' = true →
      goal.testBit i = false → goal.testBit i' = false → f e i = f e' i' → f e i' = f e i)
theorem kwFromLive {mask goal : Word} {k : Nat} {S : Finset Word}
    (live : LiveWord mask goal k 0 S) (tight : S.card = k + 1) : KWPartition goal S := by
  induction k generalizing S with
  | zero =>
    obtain ⟨_, eq, _⟩ := live
    subst S
    exact ⟨fun _ _ => goal, fun _ _ hp hn => ⟨by simp, hp, hn⟩, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  | succ k ih =>
    rcases live with ⟨u, U, a, eq, _⟩ | ⟨U, a, b, op, rfl, pa, pb, ab, fresh, tail⟩
    · omega
    let w := binWord op a b
    have wU : w ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have wA : w ≠ a := fun eq => fresh (Finset.mem_insert.mpr (Or.inl eq))
    have wB : w ≠ b := fun eq => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl eq)))
    have tailSize := (liveWordSize tail).2
    change (insert w U).card + 0 ≤ k + 1 at tailSize
    rw [Finset.card_insert_of_notMem wU] at tailSize
    have paCard := Finset.card_insert_le a (insert b U)
    have pbCard := Finset.card_insert_le b U
    have aU : a ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h)] at tight
      omega
    have bU : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      have := Finset.card_insert_le a U
      omega
    obtain ⟨f, hf, hr⟩ := ih tail (by
      change (insert w U).card = k + 1
      rw [Finset.card_insert_of_notMem wU]
      omega)
    have keepA : a ∉ insert w U := by simp [wA.symm, aU]
    have keepB : b ∉ insert w U := by simp [wB.symm, bU]
    have other : ∀ x ∈ insert w U, x ≠ w → x ∈ insert a (insert b U) := by
      intro x hx hn
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((Finset.mem_insert.mp hx).resolve_left hn))
    have ha : a ∈ insert a (insert b U) := Finset.mem_insert_self ..
    have hb : b ∈ insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    cases op
    · exact kw_step goal _ _ a b w (fun _ i => !(a.testBit i)) f ha hb ab keepA keepB other hf hr
        (fun e i h1 h2 h3 => and_cu a b e i h1 h2 h3) (fun e i h1 h2 h3 => and_cv a b e i h1 h2 h3)
        (fun _ _ _ _ h => h.symm)
    · exact kw_step goal _ _ a b w (fun e _ => a.testBit e) f ha hb ab keepA keepB other hf hr
        (fun e i h1 h2 h3 => or_cu a b e i h1 h2 h3) (fun e i h1 h2 h3 => or_cv a b e i h1 h2 h3)
        (fun _ _ _ _ _ => rfl)
theorem liveDirected {mask goal : Word} {k : Nat} {S : Finset Word}
    (live : LiveWord mask goal k 0 S) {p n : Nat}
    (hp : goal.testBit p = true) (hn : goal.testBit n = false) :
    ∃ w ∈ S, w.testBit p = true ∧ w.testBit n = false := by
  induction k generalizing S with
  | zero =>
    obtain ⟨_,rfl,_⟩ := live
    exact ⟨goal, by simp, hp, hn⟩
  | succ k ih =>
    rcases live with ⟨u, U, a, ueq, _⟩ | ⟨U,a,b,op,rfl,pa,pb,ab,fresh,tail⟩
    · omega
    obtain ⟨w, hw, wp, wn⟩ := ih tail
    rcases Finset.mem_insert.mp hw with eq | hU
    · subst w
      cases op
      · by_cases ha : a.testBit n = false
        · exact ⟨a, Finset.mem_insert_self .., and_cu a b p n wp wn (by simp [ha])⟩
        · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
            and_cv a b p n wp wn (by cases h : a.testBit n <;> simp_all)⟩
      · by_cases ha : a.testBit p = true
        · exact ⟨a, Finset.mem_insert_self .., or_cu a b p n wp wn ha⟩
        · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
            or_cv a b p n wp wn (by cases h : a.testBit p <;> simp_all)⟩
    · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),wp,wn⟩
namespace PackedRect
end PackedRect
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
theorem liveMaskedImage {mask goal : Word} {select : Fin rows → Fin rows}
    (auto : DagAuto mask goal select) (maskBounds : Masked (fullMask rows) mask)
    {k t : Nat} {S : Finset Word} (live : LiveWord mask goal k t S)
    (masked : ∀ w ∈ S, Masked mask w) :
    LiveWord mask goal k t (S.image (relabel select)) := by
  let f := relabel select
  have hmask : f mask = mask := auto.2.1
  have inj {a b : Word} (ma : Masked mask a) (mb : Masked mask b) :
      f a = f b → a = b :=
    relabelInj select auto.1 (maskedBelow maskBounds ma) (maskedBelow maskBounds mb)
  have proper {a : Word} (ma : Masked mask a) (ha : properWord mask a) :
      properWord mask (f a) := by
    exact ⟨fun eq => ha.1 (inj ma (by simp [Masked]) (eq.trans (relabelZero select).symm)),
      fun eq => ha.2 (inj ma (by simp [Masked]) (eq.trans hmask.symm))⟩
  have freshImage {S : Finset Word} {v : Word} (hv : v ∉ S) (mv : Masked mask v)
      (ms : ∀ w ∈ S, Masked mask w) : f v ∉ S.image f := by
    intro hw
    obtain ⟨w,hs,eq⟩ := Finset.mem_image.mp hw
    exact hv (inj (ms w hs) mv eq ▸ hs)
  induction live using LiveWord.ind with
  | stop hp =>
    rw [Finset.image_singleton, auto.2.2]
    exact LiveWord.stop hp
  | @unary k t U a ha fresh tail ih =>
    let v := mask ^^^ a
    have ma := masked a (Finset.mem_insert_self ..)
    have mv : Masked mask v := by
      apply maskedGate (bank := [a]) (by simpa using ma)
      exact Or.inl ⟨a, Or.inr (Or.inr (by simp)), rfl⟩
    have hnew : ∀ w ∈ insert v U, Masked mask w := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem hU)
    have fve : f v = mask ^^^ f a := by
      change relabel select (mask ^^^ a) = _
      rw [relabelXor, auto.2.1]
    have ht := ih hnew
    have hf := freshImage fresh mv masked
    change LiveWord mask goal (k+1) (t+1) ((insert a U).image f)
    rw [Finset.image_insert] at ht hf
    change LiveWord mask goal k t (insert (f v) (U.image f)) at ht
    rw [fve] at ht hf
    rw [Finset.image_insert]
    exact LiveWord.unary (proper ma ha) hf ht
  | @binary k t U a b op pa pb ab fresh tail ih =>
    let v := binWord op a b
    have ma := masked a (Finset.mem_insert_self ..)
    have mb := masked b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have mv : Masked mask v := by
      apply maskedGate (bank := [a,b]) (by simpa using And.intro ma mb)
      exact Or.inr ⟨a,b,Or.inr (Or.inr (by simp)),Or.inr (Or.inr (by simp)),by
        cases op <;> simp [v, binWord]⟩
    have hnew : ∀ w ∈ insert v U, Masked mask w := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU))
    have fve : f v = binWord op (f a) (f b) := by
      cases op
      · exact relabelAnd ..
      · exact relabelOr ..
    have ht := ih hnew
    have hf := freshImage fresh mv masked
    change LiveWord mask goal (k+1) t ((insert a (insert b U)).image f)
    rw [Finset.image_insert] at ht
    change LiveWord mask goal k t (insert (f v) (U.image f)) at ht
    rw [fve] at ht
    rw [Finset.image_insert, Finset.image_insert, fve] at hf
    rw [Finset.image_insert, Finset.image_insert]
    exact LiveWord.binary (proper ma pa) (proper mb pb) (fun h => ab (inj ma mb h)) hf ht
def dagMoveWords (m : WordMove) (ws : List Word) : List Word :=
  List.rec [] (fun w _ next => insertWord (mixMove m w) next) ws
theorem dagMoveSet {m : WordMove} {ws : List Word} {select : Fin rows → Fin rows}
    (agree : ∀ w ∈ ws, mixMove m w = relabel select w) :
    (dagMoveWords m ws).toFinset = ws.toFinset.image (relabel select) := by
  induction ws with
  | nil => simp [dagMoveWords]
  | cons w ws ih =>
    change (insertWord (mixMove m w) (dagMoveWords m ws)).toFinset = _
    rw [insertWordSet, ih (fun w hw => agree _ (List.mem_cons_of_mem _ hw)),
      agree _ List.mem_cons_self, List.toFinset_cons, Finset.image_insert]
abbrev DagLink := Nat × Nat
abbrev DagLinks := Nat → Nat → Option DagLink
def dagRef (count : Nat) (states : Nat → Option RowState)
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
          else match moves[auto-1]? with
               | none => false
               | some m => saved.2.1 == dagMoveWords m state.2.1
def dagStateOK (mask : Word) (ws : List Word) : Bool :=
  (ws.dedup.length == ws.length) && ws.all (fun w => w &&& mask == w)
theorem dagStateOKSpec {mask : Word} {ws : List Word} (ok : dagStateOK mask ws = true) :
    ws.Nodup ∧ ∀ w ∈ ws, Masked mask w := by
  simp only [dagStateOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  exact ⟨List.nodup_iff_length_dedup_eq.mpr ok.1, ok.2⟩
theorem childStateData {mask token : Nat} {state child : RowState}
    (eval : childState mask token state = some child)
    (masked : ∀ w ∈ state.2.1, Masked mask w) :
    child.1 < state.1 ∧ ∀ w ∈ child.2.1, Masked mask w := by
  obtain ⟨fuel,ws,history⟩ := state
  let keep := token % 4
  let op := token / 4 % 3
  let a := token / (4 * 3 * 64)
  let b := token / (4 * 3) % 64
  let x := ws.getD a 0
  let y := ws.getD b 0
  let z := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
  let rest := keepWord (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
  let bad : Bool := fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b)
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z,x,y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb,hs] at eval
  have eq : (fuel-1, insertWord z rest, (z,x,y) :: history) = child := by simpa [hb,hs] using eval
  subst child
  have pos : 0 < fuel := by
    by_contra! h
    have he : fuel = 0 := by omega
    simp [bad, he] at hb
  refine ⟨by dsimp; omega,?_⟩
  have read (i : Nat) : AvailableWord mask ws (ws.getD i 0) := by
    simp only [List.getD_eq_getElem?_getD]
    cases h : ws[i]? with
    | none => exact Or.inl rfl
    | some a => exact Or.inr (Or.inr (List.mem_of_getElem? h))
  have hm : Masked mask z := by
    apply maskedGate masked
    unfold z
    split
    · exact Or.inr ⟨x,y,read _,read _,Or.inl rfl⟩
    split
    · exact Or.inr ⟨x,y,read _,read _,Or.inr rfl⟩
    · exact Or.inl ⟨x,read _,rfl⟩
  intro w hw
  rcases insertWordMem.mp hw with rfl | other
  · exact hm
  · apply masked w
    apply keepSubset (keep.testBit 0) x ws w
    exact keepSubset (op == 2 || keep.testBit 1) y _ w other
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
theorem dagLinked {mask goal : Word} {width count : Nat} {states : Nat → Option RowState}
    {moves : Array WordMove} {links : DagLinks} {parent token : Nat} {state : RowState}
    (bounds : Masked (fullMask width) mask)
    (valid : DagMovesOK mask goal width moves)
    (masked : ∀ w ∈ state.2.1, Masked mask w)
    (ok : dagRef count states moves links parent token state = true)
    {k t : Nat} (live : LiveWord mask goal k t state.2.1.toFinset) :
    ∃ i saved, i < count ∧ states i = some saved ∧ saved.1 = state.1 ∧
      LiveWord mask goal k t saved.2.1.toFinset := by
  unfold dagRef at ok
  split at ok
  · contradiction
  next destination auto h =>
    have hd := Nat.blt_eq.mp (Bool.and_eq_true_iff.mp ok).1
    have finish := (Bool.and_eq_true_iff.mp ok).2
    cases eq : states destination with
    | none => simp [eq] at finish
    | some saved =>
      simp only [eq, Bool.and_eq_true, beq_iff_eq] at finish
      refine ⟨destination,saved,hd,eq,finish.1,?_⟩
      have last := finish.2
      split at last
      · have same : saved.2.1 = state.2.1 := beq_iff_eq.mp last
        rwa [same]
      · split at last
        · contradiction
        next m hm =>
          obtain ⟨select,auto,agree⟩ := valid _ _ hm
          have same : saved.2.1 = dagMoveWords m state.2.1 := beq_iff_eq.mp last
          rw [same, dagMoveSet (fun w hw => agree w (masked w hw))]
          exact liveMaskedImage auto bounds live (fun w hw => masked _ (List.mem_toFinset.mp hw))
def dagLookupLinks (index data indexWidth sizeBits tokenBits destinationBits autoBits trials : Nat) :
    DagLinks := fun parent token =>
  let entry := unpack index indexWidth parent
  let size := entry &&& ((1 <<< sizeBits) - 1)
  let offset := entry >>> sizeBits
  let width := tokenBits + destinationBits + autoBits
  (Nat.rec (motive := fun _ => Nat → Nat → Option DagLink) (fun _ _ => none)
    (fun _ next lo hi =>
      if Nat.blt lo hi then
        let mid := (lo+hi)/2
        let code := unpack data width mid
        let key := code &&& ((1 <<< tokenBits) - 1)
        if Nat.beq token key then
          some ((code >>> tokenBits) &&& ((1 <<< destinationBits) - 1),
            code >>> (tokenBits + destinationBits))
        else if Nat.blt token key then next lo mid else next (mid+1) hi
      else none) trials) offset (offset+size)
theorem stockMaskedOfCheck {mask : Word} {stock : List Word}
    (h : stock.all (fun w => w &&& mask == w) = true) :
    ∀ w ∈ stock, Masked mask w := by
  intro w hw
  exact beq_iff_eq.mp (List.all_eq_true.mp h w hw)
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
theorem suppliesOfCheck {oldMask : Word} {old new : List Word} {rename : Word → Word}
    (h : new.all (fun w => availableB oldMask old (rename w)) = true) :
    ∀ w ∈ new, AvailableWord oldMask old (rename w) := by
  intro w hw
  exact availableB_spec.mp (List.all_eq_true.mp h w hw)
end WordEngine

open WordEngine PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Rep9102
abbrev AO (m : Nat) (stock : List Word) (out : Word) :=
  ∃ a b, AvailableWord m stock a ∧ AvailableWord m stock b ∧ (out = a &&& b ∨ out = a ||| b)
def AOBuild (m : Nat) (stock : List Word) : List Word → Prop
  | [] => True
  | w::ws => AO m stock w ∧ AOBuild m (w::stock) ws
def AOLower (m : Nat) (stock : List Word) (target : Word) (bound : Nat) : Prop :=
  ∀ vs, AOBuild m stock vs → AvailableWord m (vs++stock) target → bound ≤ vs.length
theorem aoOfAvailable {m stock w} (av : AvailableWord m stock w) : AO m stock w :=
  ⟨w,0,av,Or.inl rfl,Or.inr (by simp)⟩
theorem aoWeaken {m small big vs} (sub : ∀ w ∈ small, AvailableWord m big w)
    (h : AOBuild m small vs) : AOBuild m big vs := by
  induction vs generalizing small big with
  | nil => trivial
  | cons w ws ih =>
    obtain ⟨⟨a,b,ha,hb,ev⟩,tail⟩ := h
    refine ⟨⟨a,b,availableWeaken sub ha,availableWeaken sub hb,ev⟩,ih ?_ tail⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Or.inr (Or.inr List.mem_cons_self)
    · exact availableWeaken (fun v hv => Or.inr (Or.inr (List.mem_cons_of_mem _ hv))) (sub _ ha)
variable {mask target : Word}
theorem pullAO {w : List (Word)} {z : Word} {k S} (h : LiveWord mask target k 0 S)
    (hz : wordRep mask w z ∨ binaryWitness mask w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+1 ∧ LiveWord mask target k' 0 S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := liveWordProper h z hm
      rcases hz with hr | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (binWord d a b)
        have ht : LiveWord mask target k 0 (insert (binWord d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : binWord d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,LiveWord.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
theorem extractAO {roots values : List Word}
    (all : ∀ w ∈ roots, Masked mask w) (builds : AOBuild mask roots values)
    (hit : AvailableWord mask (values ++ roots) target) (p : properWord mask target) :
    ∃ k S, k ≤ values.length ∧ LiveWord mask target k 0 S ∧ ∀ w ∈ S, w ∈ roots := by
  have hm := (hit.resolve_left p.1).resolve_left p.2
  induction values generalizing roots with
  | nil =>
    exact ⟨0, {target}, Nat.zero_le _, LiveWord.stop p, by simpa using hm⟩
  | cons w ws ih =>
    have next : ∀ v ∈ w :: roots, Masked mask v := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact maskedGate all (Or.inr builds.1)
      · exact all _ hv
    have ht : AvailableWord mask (ws ++ w :: roots) target := by
      exact Or.inr (Or.inr (by simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hm))
    obtain ⟨k, S, hk, live, sub⟩ :=
      ih next builds.2 ht ((ht.resolve_left p.1).resolve_left p.2)
    have available : ∀ v ∈ S, v ∈ roots ++ [w] := by
      intro v h
      simpa [or_comm] using sub v h
    have gate : wordRep mask roots w ∨ binaryWitness mask roots w := by
      obtain ⟨a,b,ha,hb,eq|eq⟩ := builds.1
      · subst w; exact classifyBinary all false ha hb
      · subst w; exact classifyBinary all true ha hb
    obtain ⟨k', S', hk', hl, hsub⟩ := pullAO live gate available
    exact ⟨k', S', by simp only [List.length_cons]; omega, hl, hsub⟩
theorem aoGateWord {rows : Nat} (bank : List (BitVec rows))
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp))
    (hlen : g.inputs.length ≤ 2) :
    AO (fullMask rows) (bank.map BitVec.toNat) (hcsGateVal bank g).toNat := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have zeroAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) 0 := Or.inl rfl
  have maskAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) (fullMask rows) :=
    Or.inr (Or.inl rfl)
  rcases hop with rfl | rfl
  · cases ins with
    | nil => exact aoOfAvailable (by simpa [hcsGateVal, fullMask] using maskAv)
    | cons a t =>
      cases t with
      | nil => exact aoOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inl (by simp [hcsGateVal, BitVec.toNat_and])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact aoOfAvailable (by simpa [hcsGateVal] using zeroAv)
    | cons a t =>
      cases t with
      | nil => exact aoOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inr (by simp [hcsGateVal, BitVec.toNat_or])⟩
        | cons c t => simp at hlen
theorem aoBuilds {rows : Nat} (bank : List (BitVec rows))
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    ∃ vs, vs.length = gs.length ∧ AOBuild (fullMask rows) (bank.map BitVec.toNat) vs ∧
      ∀ v ∈ gs.foldl hcsStep bank, v.toNat ∈ vs ++ bank.map BitVec.toNat := by
  induction gs generalizing bank with
  | nil => exact ⟨[], rfl, trivial, fun _ h => List.mem_map_of_mem h⟩
  | cons g gs ih =>
    let v := hcsGateVal bank g
    have hg := hfan g List.mem_cons_self
    obtain ⟨xs, len, build, sub⟩ := ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
    have eq : (hcsStep bank g).map BitVec.toNat = bank.map BitVec.toNat ++ [v.toNat] := by
      simp [hcsStep, v]
    rw [eq] at build
    refine ⟨v.toNat :: xs, by simp [len], ⟨aoGateWord bank g hg.1 hg.2, aoWeaken ?_ build⟩, ?_⟩
    · intro u hu; exact Or.inr (Or.inr (by simpa [or_comm] using hu))
    · intro u hu; have m := sub u hu; rw [eq] at m
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using m
theorem monoFan {C : Circuit} (legal : Monotone2 C) : FanInTwo C := by
  intro g hg
  obtain ⟨op,sz⟩ := legal g hg
  refine ⟨?_,sz⟩
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
  tauto
end Rep9102

open WordEngine PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
namespace Rep9102
set_option maxHeartbeats 0 in
def posted (u v : Fin 5) : Bool := decide (u ≠ v)
set_option maxHeartbeats 0 in
def raw : List (BitVec 25) := [0x1f, 0x3e0, 0x7c00, 0xf8000, 0x1f00000, 0x210842, 0x421084, 0x842108, 0x1084210, 0x108421]
set_option maxHeartbeats 0 in
def stock : List Word := raw.map BitVec.toNat
set_option maxHeartbeats 0 in
def target25 : BitVec 25 := 0xfbefbe
set_option maxHeartbeats 0 in
abbrev T : Word := target25.toNat
set_option maxHeartbeats 0 in
def point (r : Fin 25) := oneEach (Fin.ofNat 5 (r.val / 5)) (Fin.ofNat 5 (r.val % 5))
set_option maxHeartbeats 0 in
theorem representation_live (C : Circuit) (legal : Monotone2 C) (right : Represents posted C) :
    ∃ k ≤ C.size, LiveWord (fullMask 25) T k 0 stock.toFinset := by
  let raw : List (BitVec 25) := [0x1f, 0x3e0, 0x7c00, 0xf8000, 0x1f00000, 0x108421, 0x210842, 0x421084, 0x842108, 0x1084210]
  let stock := raw.map BitVec.toNat
  rw [show Rep9102.stock.toFinset = stock.toFinset by decide +kernel]
  have rawBits : ∀ r : Fin 25, (raw.map fun w => w.getLsbD r.val) = point r := by decide +kernel
  have goalBits : ∀ r : Fin 25, target25.getLsbD r.val =
      posted (Fin.ofNat 5 (r.val / 5)) (Fin.ofNat 5 (r.val % 5)) := by decide +kernel
  let eb := C.gates.foldl hcsStep raw
  have eq : eb.getD C.output 0 = target25 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Fin 25 := ⟨j,hj⟩
    have bits := hcsFoldBits raw r C.gates (monoFan legal)
    have ack := right (Fin.ofNat 5 (r.val / 5)) (Fin.ofNat 5 (r.val % 5))
    change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (point r)).getD C.output false = _ at ack
    rw [← rawBits r,← bits] at ack
    exact (hcsGetDBit eb j C.output).trans (ack.trans (goalBits r).symm)
  obtain ⟨ws,len,built,sub⟩ := aoBuilds raw C.gates legal
  have hit : AvailableWord (fullMask 25) (ws++stock) T := by
    change AvailableWord _ _ target25.toNat
    rw [←eq,List.getD_eq_getElem?_getD]
    cases h : eb[C.output]? with
    | none => exact Or.inl rfl
    | some w => exact Or.inr (Or.inr (sub w (List.mem_of_getElem? h)))
  obtain ⟨k,S,budget,run,subset⟩ := extractAO (stockMaskedOfCheck (by decide +kernel : stock.all (fun w => w &&& fullMask 25 == w) = true)) built hit
      (by unfold properWord; decide +kernel)
  have witnesses : ∀ w ∈ stock, ∃ p n : Fin 25, T.testBit p.val = true ∧ T.testBit n.val = false ∧
      ∀ u ∈ stock, u.testBit p.val = true → u.testBit n.val = false → u = w := by decide +kernel
  have same : S = stock.toFinset := by
    ext w; constructor
    · exact fun h => List.mem_toFinset.mpr (subset w h)
    · intro h
      obtain ⟨p,n,yes,no,unique⟩ := witnesses w (List.mem_toFinset.mp h)
      obtain ⟨u,mem,a,b⟩ := liveDirected run yes no
      exact (unique u (subset u mem) a b) ▸ mem
  exact ⟨k,budget.trans (Nat.le_of_eq len),same ▸ run⟩
end Rep9102

open WordEngine PEqualNP.Represents
namespace Rep9102.Orbit
set_option maxHeartbeats 0 in
def MonoViable (mask goal : Word) (s : RowState) : Prop :=
  s.2.1.Nodup ∧ ∃ k ≤ s.1, LiveWord mask goal k 0 s.2.1.toFinset
set_option maxHeartbeats 0 in
def AOChild (mask : Word) (s c : RowState) : Prop :=
  ∃ a b op keep, a < s.2.1.length ∧ a < b ∧ b < s.2.1.length ∧ op < 2 ∧ keep < 4 ∧
    childState mask (gateToken a b op keep) s = some c
set_option maxHeartbeats 0 in
theorem binaryMonoProgress {mask fuel k : Nat} {x y target : Word} {d : Bool} {U : Finset Word}
    {ws : List Word} {history : List (Word × Word × Word)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel)
    (he : ws.toFinset = insert x (insert y U)) (xy : x ≠ y)
    (ordered : ws.idxOf x < ws.idxOf y) (fresh : binWord d x y ∉ insert x (insert y U))
    (tail : LiveWord mask target k 0 (insert (binWord d x y) U)) :
    ∃ child, AOChild mask (fuel, ws, history) child ∧ MonoViable mask target child := by
  let a := ws.idxOf x
  let b := ws.idxOf y
  have xm : x ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ym : y ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ha : a < ws.length := List.idxOf_lt_length_iff.mpr xm
  have hb : b < ws.length := List.idxOf_lt_length_iff.mpr ym
  have hab : a < b := ordered
  have hx : ws.getD a 0 = x := getWord xm
  have hy : ws.getD b 0 = y := getWord ym
  let v := binWord d x y
  have p := liveWordProper tail v (Finset.mem_insert_self _ _)
  let saveX := decide (x ∈ U)
  let saveY := decide (y ∈ U)
  let keep := (if saveX then 1 else 0) + (if saveY then 2 else 0)
  have fields : keep < 4 ∧ keep.testBit 0 = saveX ∧ keep.testBit 1 = saveY := by
    unfold keep
    cases saveX <;> cases saveY <;> decide
  obtain ⟨keepLt, bx, by'⟩ := fields
  have fn : v ∉ ws := by simpa [← List.mem_toFinset, he] using fresh
  let rest := keepWord saveY y (keepWord saveX x ws)
  let child : RowState := (fuel - 1, insertWord v rest, (v, x, y) :: history)
  refine ⟨child, ⟨a, b, if d then 1 else 0, keep, ha, hab, hb, ?_, keepLt, ?_⟩, ?_⟩
  · cases d <;> decide
  · have eq := binaryChild (fuel := fuel) (history := history) d hab hb (by omega) (by omega) keepLt hx hy p fn
    rw [bx, by'] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup (keepNodup nd saveX x) saveY y)
      (fun h => fn (keepSubset saveX x ws _ (keepSubset saveY y _ _ h))), k, by change k ≤ fuel - 1; omega, ?_⟩
    change LiveWord mask target k 0 (insertWord v rest).toFinset
    rw [insertWordSet, keepPairSet nd xy he]
    exact tail
set_option maxHeartbeats 0 in
theorem monoProgress {mask : Nat} {target : Word} {state : RowState}
    (width : state.2.1.length ≤ 64) (h : MonoViable mask target state) :
    target ∈ state.2.1 ∨ ∃ child, AOChild mask state child ∧ MonoViable mask target child := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨nd, k, cap, live⟩ := h
  cases k with
  | zero =>
    obtain ⟨_, eq, _⟩ := live
    left
    change ws.toFinset = {target} at eq
    rw [← List.mem_toFinset, eq]
    simp
  | succ k =>
    right
    rcases live with ⟨u,U,x,impossible,eq,px,fresh,tail⟩ | ⟨U,x,y,d,eq,px,py,xy,fresh,tail⟩
    · omega
    have xm : x ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have ym : y ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have diff : ws.idxOf x ≠ ws.idxOf y := by
      intro same
      apply xy
      rw [← getWord xm, same, getWord ym]
    by_cases h : ws.idxOf x < ws.idxOf y
    · exact binaryMonoProgress nd width cap eq xy h fresh tail
    · have eq' : ws.toFinset = insert y (insert x U) := by rw [eq, Finset.insert_comm]
      have fresh' : binWord d y x ∉ insert y (insert x U) := by
        rw [binWord_comm d y x, Finset.insert_comm]; exact fresh
      have tail' : LiveWord mask target k 0 (insert (binWord d y x) U) := by
        rw [binWord_comm d y x]; exact tail
      exact binaryMonoProgress nd width cap eq' xy.symm (by omega) fresh' tail'
set_option maxHeartbeats 0 in
def coverAt (n : Nat) (ws : List Word) : Word :=
  List.rec 0 (fun w _ acc => if w.testBit n then acc else w ||| acc) ws
set_option maxHeartbeats 0 in
theorem coverAt_bit {w : Word} {ws : List Word} {p n : Nat}
    (member : w ∈ ws) (pos : w.testBit p = true) (neg : w.testBit n = false) :
    (coverAt n ws).testBit p = true := by
  induction ws with
  | nil => simp at member
  | cons x xs ih =>
    change (if x.testBit n then coverAt n xs else x ||| coverAt n xs).testBit p = true
    rcases List.mem_cons.mp member with rfl | tail
    · simp [neg, Nat.testBit_or, pos]
    · cases x.testBit n <;> simp [Nat.testBit_or, ih tail]
set_option maxHeartbeats 0 in
theorem coverAt_live {mask goal : Word} {ws : List Word} {k n : Nat}
    (live : LiveWord mask goal k 0 ws.toFinset) (neg : goal.testBit n = false) :
    goal &&& coverAt n ws = goal := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_and]
  cases h : goal.testBit p with
  | false => rfl
  | true =>
    obtain ⟨w,mem,one,zero⟩ := liveDirected live h neg
    simp [coverAt_bit (List.mem_toFinset.mp mem) one zero]
set_option maxHeartbeats 0 in
def basicCut (goal : Word) (neg : List Nat) (s : RowState) : Bool :=
  decide (s.1+1 < s.2.1.length) ||
    neg.any (fun n => (goal &&& coverAt n s.2.1) != goal)
set_option maxHeartbeats 0 in
theorem basicOpen {mask goal : Word} {neg : List Nat} {s : RowState}
    (negative : ∀ n ∈ neg, goal.testBit n = false) (v : MonoViable mask goal s) :
    basicCut goal neg s = false := by
  obtain ⟨nd,k,cap,live⟩ := v
  have size := (liveWordSize live).2
  rw [List.toFinset_card_of_nodup nd] at size
  simp only [basicCut, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    List.any_eq_false, bne_iff_ne, ne_eq]
  constructor
  · omega
  · intro n mem
    simp [coverAt_live live (negative n mem)]
set_option maxHeartbeats 0 in
abbrev Table := Nat → Option RowState
set_option maxHeartbeats 0 in
abbrev EdgeCut := Nat → Nat → RowState → Bool
set_option maxHeartbeats 0 in
def pass (m g : Word) (neg : List Nat) (states : Table) (count : Nat)
    (moves : Array WordMove) (links : DagLinks) (cut : EdgeCut) (i : Nat)
    (s : RowState) (a b op keep : Nat) : Bool :=
  let tok := gateToken a b op keep
  match childState m tok s with
  | none => true
  | some c => basicCut g neg c || cut i tok c || dagRef count states moves links i tok c
set_option maxHeartbeats 0 in
def scan (m g : Word) (neg : List Nat) (states : Table) (count : Nat)
    (moves : Array WordMove) (links : DagLinks) (cut : EdgeCut) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some s =>
    let n := s.2.1.length
    dagStateOK m s.2.1 && decide (n ≤ 64) && !(s.2.1.contains g) &&
    treeBlock 0 n (fun a => treeBlock (a+1) (n-(a+1)) (fun b =>
      treeBlock 0 2 (fun op => treeBlock 0 4 (pass m g neg states count moves links cut i s a b op))))
set_option maxHeartbeats 0 in
theorem tableSound {m g : Word} {width count : Nat} {neg : List Nat} {states : Table}
    {moves : Array WordMove} {links : DagLinks} {cut : EdgeCut}
    (mb : Masked (fullMask width) m) (autos : DagMovesOK m g width moves)
    (negative : ∀ n ∈ neg, g.testBit n = false)
    (cutOpen : ∀ i tok s, MonoViable m g s → cut i tok s = false)
    (checked : ∀ i < count, scan m g neg states count moves links cut i = true) :
    ∀ fuel i s, i < count → states i = some s → s.1 = fuel →
      ∀ k ≤ fuel, ¬ LiveWord m g k 0 s.2.1.toFinset := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | ind fuel ih =>
    intro i s hi row cap k fit live
    have h := checked i hi
    simp only [scan, row, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    obtain ⟨nd,masked⟩ := dagStateOKSpec h.1.1.1
    rcases monoProgress h.1.1.2 ⟨nd,k,cap ▸ fit,live⟩ with hit | ⟨c,edge,v⟩
    · simpa [hit] using h.1.2
    obtain ⟨a,b,op,keep,ha,hab,hb,hop,hkeep,ev⟩ := edge
    have aa := treeBlock_at h.2 (i := a) (Nat.zero_le _) (by simpa using ha)
    have bb := treeBlock_at aa (i := b) (by omega) (by omega)
    have oo := treeBlock_at bb (i := op) (Nat.zero_le _) (by simpa using hop)
    have kk := treeBlock_at oo (i := keep) (Nat.zero_le _) (by simpa using hkeep)
    simp only [pass, ev, basicOpen negative v, cutOpen _ _ _ v, Bool.false_or] at kk
    obtain ⟨less,cm⟩ := childStateData ev masked
    obtain ⟨_,j,fit',plan⟩ := v
    obtain ⟨dest,saved,inRange,lookup,eq,tail⟩ := dagLinked mb autos cm kk plan
    exact ih c.1 (cap ▸ less) dest saved inRange lookup eq j fit' tail
set_option maxHeartbeats 0 in
def diagonal : List Nat := [0,6,12,18,24]
set_option maxHeartbeats 0 in
theorem lowerFromTable {fuel count root : Nat} {states : Table} {s : RowState}
    {moves : Array WordMove} {links : DagLinks} {cut : EdgeCut}
    (autos : DagMovesOK (fullMask 25) T 25 moves)
    (cuts : ∀ i tok c, MonoViable (fullMask 25) T c → cut i tok c = false)
    (checked : ∀ i < count, scan (fullMask 25) T diagonal states count moves links cut i = true)
    (bound : root < count) (lookup : states root = some s) (budget : s.1 = fuel)
    (bank : s.2.1.toFinset = stock.toFinset) : ¬ RepSizeAtMost posted fuel := by
  rintro ⟨C,legal,size,right⟩
  obtain ⟨k,fit,run⟩ := representation_live C legal right
  rw [←bank] at run
  exact tableSound (m := fullMask 25) (by unfold Masked; decide +kernel) autos
    (by decide +kernel : ∀ n ∈ diagonal, T.testBit n = false) cuts checked fuel root s bound
    lookup budget k (fit.trans size) run
end Rep9102.Orbit

open WordEngine
namespace Rep9102.Geometry
open Rep9102.Orbit
set_option maxHeartbeats 0 in
def forcesAt (goal : Word) (ws : List Word) (w : Word) (p n : Nat) : Bool :=
  goal.testBit p && !goal.testBit n &&
    ws.all (fun v => v == w || !v.testBit p || v.testBit n)
set_option maxHeartbeats 0 in
theorem forcedAnswer {g : Word} {ws : List Word} {w : Word} {p n : Nat}
    {f : Nat → Nat → Word}
    (legal : ∀ p n, g.testBit p = true → g.testBit n = false →
      f p n ∈ ws.toFinset ∧ (f p n).testBit p = true ∧ (f p n).testBit n = false)
    (h : forcesAt g ws w p n = true) :
    g.testBit p = true ∧ g.testBit n = false ∧ f p n = w := by
  simp only [forcesAt, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨mem,on,off⟩ := legal _ _ h.1.1 h.1.2
  have v := List.all_eq_true.mp h.2 _ (List.mem_toFinset.mp mem)
  exact ⟨h.1.1,h.1.2,by simpa [on,off] using v⟩
set_option maxHeartbeats 0 in
def overlap (g : Word) (ws : List Word) (x y : Word) (p n px nx py ny : Nat) : Bool :=
  x != y && forcesAt g ws x p nx && forcesAt g ws x px n &&
  forcesAt g ws y p ny && forcesAt g ws y py n
set_option maxHeartbeats 0 in
theorem overlapImpossible {g : Word} {ws : List Word} {x y p n px nx py ny : Nat}
    (kw : KWPartition g ws.toFinset) : overlap g ws x y p n px nx py ny = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨f,legal,box⟩ := kw
  simp only [overlap, Bool.and_eq_true, bne_iff_ne] at h
  obtain ⟨⟨⟨⟨ne,a⟩,b⟩,c⟩,d⟩ := h
  obtain ⟨pos,nnx,xa⟩ := forcedAnswer legal a
  obtain ⟨ppx,neg,xb⟩ := forcedAnswer legal b
  obtain ⟨_,nny,ya⟩ := forcedAnswer legal c
  obtain ⟨ppy,_,yb⟩ := forcedAnswer legal d
  have X := box p nx px n pos ppx nnx neg (xa.trans xb.symm)
  have Y := box p ny py n pos ppy nny neg (ya.trans yb.symm)
  exact ne ((X.trans xa).symm.trans (Y.trans ya))
set_option maxHeartbeats 0 in
theorem tightPartition {m g : Word} {s : RowState} (live : MonoViable m g s)
    (tight : s.2.1.length = s.1+1) : KWPartition g s.2.1.toFinset := by
  obtain ⟨nd,k,fit,run⟩ := live
  have sz := (liveWordSize run).2
  have card := List.toFinset_card_of_nodup nd
  apply kwFromLive run
  omega
set_option maxHeartbeats 0 in
def rectangleReject (g : Word) (s : RowState) (code : Nat) : Bool :=
  let field := unpack code 5
  (s.2.1.length == s.1+1) &&
  overlap g s.2.1 (s.2.1.getD (field 0) 0) (s.2.1.getD (field 1) 0)
    (field 2) (field 3) (field 4) (field 5) (field 6) (field 7)
set_option maxHeartbeats 0 in
theorem rectangleOpen {m g : Word} {s : RowState} (code : Nat)
    (live : MonoViable m g s) : rectangleReject g s code = false := by
  unfold rectangleReject
  by_cases t : s.2.1.length = s.1+1
  · simp [t,overlapImpossible (tightPartition live t)]
  · simp [t]
end Rep9102.Geometry

open WordEngine
namespace Rep9102.Project
def Pool (g : Word) : Nat → Finset Word → Prop
  | 0, s => g ∈ s
  | n+1, s => Pool g n s ∨ ∃ a ∈ s, ∃ b ∈ s, ∃ d, Pool g n (insert (binWord d a b) s)
theorem weakenPool {g : Word} {n s q} (sub : s ⊆ q) (h : Pool g n s) : Pool g n q := by
  induction n generalizing s q with
  | zero => exact sub h
  | succ n ih =>
    rcases h with h | ⟨a,ha,b,hb,d,run⟩
    · exact Or.inl (ih sub h)
    · exact Or.inr ⟨a,sub ha,b,sub hb,d,ih (Finset.insert_subset_insert _ sub) run⟩
theorem maskedAO {mask goal : Word} {k s} (run : LiveWord mask goal k 0 s) (m : Word) (properGoal : ¬ maskedFlat m goal) :
    ∃ n, n+(flatSet m s).card ≤ k ∧ Pool (goal &&& m) n (projectedStock m s) := by
  induction k generalizing s with
  | zero =>
    have es := run.2.1
    subst s
    refine ⟨0,?_,?_⟩
    · simp only [flatSet, Finset.filter_singleton, properGoal, ite_false, Finset.card_empty,
        Nat.add_zero, Nat.le_refl]
    · change goal &&& m ∈ projectedStock m {goal}
      simp [projectedStock,visibleWords]
  | succ k ih =>
    rcases run with ⟨v,u,a,impossible,_⟩ | ⟨u,a,b,d,eq,pa,pb,ab,fresh,tail⟩
    · omega
    subst s
    let v := binWord d a b
    obtain ⟨n,cap,built⟩ := ih tail
    have nn : v ∉ u := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    change n+(flatSet m (insert v u)).card ≤ k at cap
    rw [flIns nn] at cap
    have ca := flLe m a (insert b u)
    have cb := flLe m b u
    by_cases simple : maskedFlat m a ∨ maskedFlat m b
    · have budget : n + (flatSet m (insert a (insert b u))).card ≤ k+1 := by
        by_cases fa : maskedFlat m a <;> by_cases fb : maskedFlat m b <;>
          simp only [fa,fb,ite_true,ite_false] at ca cb simple
        all_goals first | have vf : maskedFlat m v := flBoth fa fb; simp only [vf,ite_true] at cap; omega | omega | tauto
      refine ⟨n,budget,weakenPool ?_ built⟩
      intro w hw
      simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
      rcases hw with e|e|e|e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · subst w
        have cases := simpleBin (d := d) simple
        tauto
      · tauto
    · have fa : ¬maskedFlat m a := fun h => simple (Or.inl h)
      have fb : ¬maskedFlat m b := fun h => simple (Or.inr h)
      simp only [fa,fb,ite_false] at ca cb
      refine ⟨n+1,by omega,Or.inr ⟨a &&& m,?_,b &&& m,?_,d,weakenPool ?_ built⟩⟩
      · simp [projectedStock,prIns]
      · simp [projectedStock,prIns]
      · intro w hw
        simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
        rw [cofBinary] at hw
        tauto
theorem toBuild {m g : Word} {n s} {stock : List Word}
    (sources : ∀ x ∈ s, AvailableWord m stock x) (h : Pool g n s) :
    ∃ vs, vs.length ≤ n ∧ AOBuild m stock vs ∧ AvailableWord m (vs ++ stock) g := by
  induction n generalizing s stock with
  | zero => exact ⟨[],by simp,True.intro,sources g h⟩
  | succ n ih =>
    rcases h with h | ⟨a,ha,b,hb,d,h⟩
    · obtain ⟨vs,len,built,hit⟩ := ih sources h; exact ⟨vs,by omega,built,hit⟩
    · let z := binWord d a b
      have sub : ∀ x ∈ insert z s, AvailableWord m (z::stock) x := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Or.inr (Or.inr List.mem_cons_self)
        · exact availableWeaken (fun v hv => Or.inr (Or.inr (List.mem_cons_of_mem _ hv))) (sources _ hx)
      obtain ⟨vs,len,built,hit⟩ := ih sub h
      refine ⟨z::vs,by simp; omega,⟨⟨a,b,sources _ ha,sources _ hb,?_⟩,built⟩,?_⟩
      · cases d <;> simp [z,binWord]
      · rcases hit with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (by simpa [List.mem_append,List.mem_cons,or_left_comm,or_assoc] using h))
theorem appendAO {mask : Word} {stock xs ys : List Word} (left : AOBuild mask stock xs)
    (right : AOBuild mask (xs ++ stock) ys) : AOBuild mask stock (xs ++ ys) := by
  induction xs generalizing stock with
  | nil => exact right
  | cons x xs ih =>
    refine ⟨left.1, ih left.2 (aoWeaken ?_ right)⟩
    intro w hw
    exact Or.inr (Or.inr (by simpa [List.mem_append,List.mem_cons,or_assoc,or_left_comm] using hw))
theorem cut {mask goal m k S stock prep floor} (run : LiveWord mask goal k 0 S)
    (proper : ¬ maskedFlat m goal) (built : AOBuild m stock prep)
    (supply : ∀ x ∈ projectedStock m S, AvailableWord m (prep ++ stock) x)
    (lower : AOLower m stock (goal &&& m) floor) :
    floor + (flatSet m S).card ≤ prep.length + k := by
  obtain ⟨n,len,red⟩ := maskedAO run m proper
  obtain ⟨vs,cap,prog,hit⟩ := toBuild supply red
  have total := appendAO built prog
  have hit' : AvailableWord m ((prep++vs)++stock) (goal &&& m) := by
    rcases hit with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by simpa [List.mem_append,or_left_comm,or_comm,or_assoc] using h))
  have bound := lower _ total hit'
  simp only [List.length_append] at bound
  omega
end Rep9102.Project

open WordEngine
namespace Rep9102.Project
def oneAO (stock : List Word) (w : Word) : Bool :=
  stock.any fun a => stock.any fun b => (a &&& b == w) || (a ||| b == w)
theorem oneAO_spec {m : Word} {stock w} (h : oneAO stock w) : AO m stock w := by
  obtain ⟨a,ha,ok⟩ := List.any_eq_true.mp h
  obtain ⟨b,hb,ok⟩ := List.any_eq_true.mp ok
  have eq := Bool.or_eq_true_iff.mp ok
  exact ⟨a,b,Or.inr (Or.inr ha),Or.inr (Or.inr hb),eq.elim (fun e => Or.inl (eq_of_beq e).symm)
    (fun e => Or.inr (eq_of_beq e).symm)⟩
def cheapPrep (m : Word) (stock : List Word) : List Word → Option (List Word)
  | [] => some []
  | w::ws =>
    if availableB m stock w then cheapPrep m stock ws
    else if oneAO stock w then (cheapPrep m (w::stock) ws).map (w::·)
    else none
theorem inLarger {m w : Word} {xs raw : List Word} (h : AvailableWord m raw w) :
    AvailableWord m (xs ++ raw) w :=
  availableWeaken (fun _ hw => Or.inr (Or.inr (List.mem_append_right _ hw))) h
theorem cheapPrep_spec {m : Word} {stock needed vs}
    (h : cheapPrep m stock needed = some vs) :
    AOBuild m stock vs ∧ ∀ w ∈ needed, AvailableWord m (vs++stock) w := by
  induction needed generalizing stock vs with
  | nil =>
    obtain rfl := Option.some.inj h
    exact ⟨True.intro,by simp⟩
  | cons w ws ih =>
    simp only [cheapPrep] at h
    split at h
    · rename_i present
      obtain ⟨built,covered⟩ := ih h
      refine ⟨built,?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact inLarger (availableB_spec.mp present)
      · exact covered _ hv
    · split at h
      · rename_i step
        cases he : cheapPrep m (w::stock) ws with
        | none => simp [he] at h
        | some more =>
          simp [he] at h
          subst vs
          obtain ⟨built,covered⟩ := ih he
          refine ⟨⟨oneAO_spec step,built⟩,?_⟩
          intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact Or.inr (Or.inr (by simp))
          · apply availableWeaken (small := more++w::stock) (big := (w::more)++stock) _ (covered v hv)
            intro x hx
            exact Or.inr (Or.inr (by simpa [List.mem_append,List.mem_cons,or_assoc,or_left_comm] using hx))
      · contradiction
def cheapCut (m : Word) (low fuel : Nat) (stock ws : List Word) : Bool :=
  let needed := ws.map (· &&& m)
  match cheapPrep m stock needed with
  | none => false
  | some vs => decide (vs.length + fuel < low + flatCount m ws)
theorem cheapCut_sound {m mask goal low fuel stock ws k}
    (lower : AOLower m stock (goal &&& m) low) (proper : ¬ maskedFlat m goal)
    (nd : ws.Nodup) (hk : k ≤ fuel) (close : cheapCut m low fuel stock ws = true) :
    ¬ LiveWord mask goal k 0 ws.toFinset := by
  intro run
  unfold cheapCut at close
  cases he : cheapPrep m stock (ws.map (· &&& m)) with
  | none => simp [he] at close
  | some vs =>
    simp [he] at close
    obtain ⟨built,covered⟩ := cheapPrep_spec he
    have source : ∀ w ∈ projectedStock m ws.toFinset, AvailableWord m (vs++stock) w := by
      intro w hw
      simp only [projectedStock,visibleWords,Finset.mem_insert,Finset.mem_image,List.mem_toFinset] at hw
      rcases hw with rfl | rfl | ⟨v,hv,rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact covered _ (List.mem_map_of_mem hv)
    have bound := cut run proper built source lower
    rw [flatCountCard m nd] at close
    omega
end Rep9102.Project

open WordEngine
namespace Rep9102.Project
theorem lowerFromPrep {m goal low : Word} {raw derived prep : List Word}
    (h : cheapPrep m raw derived = some prep) (floor : AOLower m raw goal low) :
    AOLower m derived goal (low-prep.length) := by
  obtain ⟨built,supply⟩ := cheapPrep_spec h
  intro vs prog hit
  have combined := appendAO built (aoWeaken supply prog)
  have hv : AvailableWord m ((prep++vs)++raw) goal := by
    rcases hit with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rcases List.mem_append.mp h with hy | hy
      · exact Or.inr (Or.inr (by simp [List.mem_append,hy]))
      · exact availableWeaken (small := prep++raw) (big := (prep++vs)++raw)
          (fun a ha => Or.inr (Or.inr (by simpa only [List.mem_append] using
            (show (a ∈ prep ∨ a ∈ vs) ∨ a ∈ raw from (List.mem_append.mp ha).elim
              (fun h => Or.inl (Or.inl h)) Or.inr)))) (supply goal hy)
  have bound := floor _ combined hv
  simp only [List.length_append] at bound
  omega
abbrev Minor := Word × Nat × List Word
def Minor.mask (x : Minor) : Word := x.1
def Minor.low (x : Minor) : Nat := x.2.1
def Minor.raw (x : Minor) : List Word := x.2.2
def Minor.Valid (goal : Word) (q : Minor) : Prop :=
  ¬ maskedFlat q.mask goal ∧ AOLower q.mask q.raw (goal &&& q.mask) q.low
def bankCut (minors : Array Minor) (hint : Nat → Nat → Nat) : Orbit.EdgeCut :=
  fun i tok s =>
    match minors[hint i tok]? with
    | none => false
    | some q => cheapCut q.mask q.low s.1 q.raw s.2.1
theorem bankCut_open {goal mask : Word} {minors : Array Minor} {hint : Nat → Nat → Nat}
    (valid : ∀ q ∈ minors, Minor.Valid goal q) (i tok s) (v : Orbit.MonoViable mask goal s) :
    bankCut minors hint i tok s = false := by
  obtain ⟨nd,k,fit,run⟩ := v
  unfold bankCut
  cases h : minors[hint i tok]? with
  | none => rfl
  | some q =>
    have proof := valid q (Array.mem_of_getElem? h)
    exact Bool.eq_false_iff.mpr (fun pos => cheapCut_sound proof.2 proof.1 nd fit pos run)
end Rep9102.Project

open WordEngine
namespace Rep9102.Project
def geometryOrMinor (minors : Array Minor) (hint : Nat → Nat → Nat) : Orbit.EdgeCut :=
  fun i tok s =>
    let code := hint i tok
    if code < 16 then bankCut minors hint i tok s else Geometry.rectangleReject T s (code - 16)
theorem geometryOrMinor_open {mask} {minors : Array Minor} {hint : Nat → Nat → Nat}
    (valid : ∀ q ∈ minors, Minor.Valid T q) (i tok s) (v : Orbit.MonoViable mask T s) :
    geometryOrMinor minors hint i tok s = false := by
  simp only [geometryOrMinor]
  split
  · exact bankCut_open valid i tok s v
  · exact Geometry.rectangleOpen _ v
end Rep9102.Project

open WordEngine
namespace Rep9102.Orbit
abbrev requiredTests (width : Nat) (goal : Word) (ws : List Word) : Prop :=
  ∀ w ∈ ws, ∃ p n : Fin width, goal.testBit p.val = true ∧ goal.testBit n.val = false ∧
    ∀ v ∈ ws, v.testBit p.val = true → v.testBit n.val = false → v = w

theorem lowerStock {m goal width fuel root count raw} {states : Table} {row : RowState}
    {neg : List Nat} {moves : Array WordMove} {links : DagLinks} {cut : EdgeCut}
    (all : ∀ w ∈ raw, Masked m w) (proper : properWord m goal) (needs : requiredTests width goal raw)
    (mb : Masked (fullMask width) m) (autos : DagMovesOK m goal width moves)
    (negative : ∀ n ∈ neg, goal.testBit n = false)
    (cutOpen : ∀ i tok s, MonoViable m goal s → cut i tok s = false)
    (checked : ∀ i < count, scan m goal neg states count moves links cut i = true)
    (index : root < count) (look : states root = some row) (rFuel : row.1 = fuel)
    (exactStock : row.2.1.toFinset = raw.toFinset) : AOLower m raw goal (fuel+1) := by
  intro vs builds hit
  by_contra! h
  obtain ⟨k,S,budget,live,sub⟩ := extractAO all builds hit proper
  have eq : S = raw.toFinset := by
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub _ hw)
    · intro hw
      obtain ⟨p,n,yes,no,only⟩ := needs _ (List.mem_toFinset.mp hw)
      obtain ⟨v,hv,a,b⟩ := liveDirected live yes no
      exact (only v (sub v hv) a b) ▸ hv
  rw [eq,←exactStock] at live
  exact tableSound mb autos negative cutOpen checked fuel root row index look rFuel k (by omega) live
def joined : List Word := [1082431,2165730,4357252,9412872,33047056]
theorem joinedTests : requiredTests 25 T joined := by decide +kernel
end Rep9102.Orbit

open WordEngine
namespace Rep9102.CompactMoves
abbrev RawMove := WordMove × Nat × Nat
def rawMove (code : Nat) : RawMove := Id.run do
  let mut left := Array.replicate 25 0
  let mut right := Array.replicate 25 0
  let mut select := 0
  let mut inverse := 0
  for s in [:25] do
    let r := unpack code 3 (s/5)
    let c := unpack code 3 (s % 5)
    let d := if code.testBit 15 then 5*c+r else 5*r+c
    if s ≤ d then left := left.modify (d-s) (· ||| (1 <<< s))
    else right := right.modify (s-d) (· ||| (1 <<< s))
    select := select ||| (s <<< (5*d))
    inverse := inverse ||| (d <<< (5*s))
  let parts := fun (a : Array Nat) => (List.range 25).filterMap (fun n =>
    if a[n]! == 0 then none else some (a[n]!,n))
  return ([(parts left,parts right)],select,inverse)
def rawList (count packed : Nat) : List RawMove :=
  (List.range count).map (fun i => rawMove (unpack packed 16 i))
def record (r : RawMove) : DagMoveRecord 25 :=
  (r.1,fun i => Fin.ofNat 25 (unpack r.2.1 5 i.val),fun i => Fin.ofNat 25 (unpack r.2.2 5 i.val))
end Rep9102.CompactMoves

open WordEngine

namespace Rep9102.SmallCrown

open Orbit

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def records : List (DagMoveRecord 25) := [
([([(0x1041041,0),(0x82082,4),(0x4104,8),(0x208,12),(0x10,16)], [(0x820820,4),(0x410400,8),(0x208000,12),(0x100000,16)])], (fun i => Fin.ofNat 25 (unpack 0x189b924bc9a81da2c38ab0598347a8a0 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x189b924bc9a81da2c38ab0598347a8a0 5 i.val))),
([([(0x1300273,0),(0x400084,1),(0x2000,4),(0x4c00,5),(0x1000,6)], [(0x800108,1),(0x20000,4),(0x98000,5),(0x40000,6)])], (fun i => Fin.ofNat 25 (unpack 0x18b5eb4731ab54e3283d27418a410c20 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x18b5eb4731ab54e3283d27418a410c20 5 i.val))),
([([(0x1022041,0),(0x80100,3),(0x2,4),(0x1000,6),(0x8,7),(0x4080,9),(0x200,12),(0x4,13),(0x10,16)], [(0x400800,3),(0x20,4),(0x40000,6),(0x400,7),(0x810000,9),(0x200000,12),(0x8000,13),(0x100000,16)])], (fun i => Fin.ofNat 25 (unpack 0x1874d24b322715db240eab8183453ca0 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x1874d24b322715db240eab8183453ca0 5 i.val))),
([([(0x19c8019,0),(0x210002,1),(0x80,4),(0x320,5),(0x40,6)], [(0x420004,1),(0x800,4),(0x6400,5),(0x1000,6)])], (fun i => Fin.ofNat 25 (unpack 0x18bd6d49ca117a506395cd5b14418440 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x18bd6d49ca117a506395cd5b14418440 5 i.val))),
([([(0x1040881,0),(0x2004,3),(0x80000,4),(0x40,6),(0x4000,7),(0x102,9),(0x8,12),(0x200,13),(0x10,16)], [(0x10020,3),(0x800000,4),(0x1000,6),(0x200000,7),(0x20400,9),(0x8000,12),(0x400000,13),(0x100000,16)])], (fun i => Fin.ofNat 25 (unpack 0x189a5c4bc90d1d606586d13b05479540 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x189a5c4bc90d1d606586d13b05479540 5 i.val))),
([([(0x1100011,0),(0x600006,1),(0x2100,3),(0x4620,5),(0x18c0,6)], [(0x800008,2),(0x30000,9),(0x88000,10),(0x40000,12)])], (fun i => Fin.ofNat 25 (unpack 0x18b56f47316d524e641671849e410460 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x18aded4499072ce128bdcb6b14408c40 5 i.val))),
([([(0x1000001,0),(0x80808,2),(0x1040,6),(0x4002,9),(0x80,10),(0x204,13),(0x10,16)], [(0x20100,1),(0x400020,3),(0x12000,5),(0x200400,7),(0x40000,12),(0x808000,14),(0x100000,16)])], (fun i => Fin.ofNat 25 (unpack 0x1872664b30f115566806ed44874515e0 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x184cdc4a9a0b0dd1268ec78b0542bd40 5 i.val))),
([([(0x1100011,0),(0x200002,2),(0x180,9),(0x220,10),(0x40,12)], [(0xc0000c,1),(0x10800,3),(0x8c400,5),(0x63000,6)])], (fun i => Fin.ofNat 25 (unpack 0x18aded4499072ce128bdcb6b14408c40 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x18b56f47316d524e641671849e410460 5 i.val))),
([([(0x1000001,0),(0x10080,1),(0x80004,3),(0x900,5),(0x4008,7),(0x40,12),(0x202,14),(0x10,16)], [(0x202020,2),(0x41000,6),(0x800400,9),(0x20000,10),(0x408000,13),(0x100000,16)])], (fun i => Fin.ofNat 25 (unpack 0x184cdc4a9a0b0dd1268ec78b0542bd40 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x1872664b30f115566806ed44874515e0 5 i.val))),
([([(0x1011101,0),(0x80008,2),(0x880,6),(0x4004,8),(0x40,12),(0x202,14),(0x10,16)], [(0x200020,2),(0x22000,6),(0x400400,8),(0x40000,12),(0x808000,14),(0x100000,16)])], (fun i => Fin.ofNat 25 (unpack 0x184ba64a99700d8ec88ae86c8742a9e0 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x184ba64a99700d8ec88ae86c8742a9e0 5 i.val))),
([([(0x1ce7000,0),(0x108400,1),(0x2,4),(0x1c,5),(0x1,6)], [(0x210800,1),(0x20,4),(0x380,5),(0x40,6)])], (fun i => Fin.ofNat 25 (unpack 0x18bda959ca2f839ac52c831002941ca6 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x18bda959ca2f839ac52c831002941ca6 5 i.val))),
([([(0x1041022,0),(0x80,3),(0x82000,4),(0x1,6),(0x100,7),(0x4000,8),(0x4,9),(0x200,11),(0x8,13),(0x10,17)], [(0x400,3),(0x820000,4),(0x40,6),(0x8000,7),(0x400000,8),(0x800,9),(0x100000,11),(0x10000,13),(0x200000,17)])], (fun i => Fin.ofNat 25 (unpack 0x189b889bc9a345a2c11e8f500b582c26 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x189b889bc9a345a2c11e8f500b582c26 5 i.val))),
([([(0x1000000,0),(0x500000,1),(0x280a,4),(0x4010,5),(0x1405,6)], [(0xa00000,1),(0x280a0,4),(0x80200,5),(0x50140,6)])], (fun i => Fin.ofNat 25 (unpack 0x18b5e95731aa5ce327c082180293a0a6 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x18b5e95731aa5ce327c082180293a0a6 5 i.val))),
([([(0x1022022,0),(0x100,2),(0x80000,3),(0x1001,6),(0x88,8),(0x4000,9),(0x200,11),(0x4,14),(0x10,17)], [(0x400,2),(0x400000,3),(0x40040,6),(0x8800,8),(0x800000,9),(0x100000,11),(0x10000,14),(0x200000,17)])], (fun i => Fin.ofNat 25 (unpack 0x1874c89b32223ddb21a28a780b55c026 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x1874c89b32223ddb21a28a780b55c026 5 i.val))),
([([(0x18c0000,0),(0x318000,1),(0x84,3),(0x318,5),(0x63,6)], [(0x420000,2),(0xc00,9),(0x6000,10),(0x1000,12)])], (fun i => Fin.ofNat 25 (unpack 0x18bd6969ca0f8a50629c830804e6ad4c 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x18bd2d59c9f181060105cd53169414e6 5 i.val))),
([([(0x1040000,0),(0x2020,2),(0x80000,4),(0x4041,6),(0x100,9),(0x2,10),(0x208,13),(0x10,17)], [(0x804,1),(0x10000,3),(0x800000,4),(0x480,5),(0x208000,7),(0x100000,11),(0x1000,12),(0x20000,14),(0x400000,18)])], (fun i => Fin.ofNat 25 (unpack 0x189a48ebc9036d6060ae8f2815689c4c 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x18991c9bc86d451e0516d1130f580566 5 i.val))),
([([(0x1000000,0),(0x700000,1),(0x2108,2),(0x4210,5),(0x1ce7,6)], [(0x800000,3),(0x38000,14),(0x80000,15),(0x40000,18)])], (fun i => Fin.ofNat 25 (unpack 0x18b56977316a6a4e62a082080738c1f2 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x18a5ed5200620cdf28c1ca6b1692a0e6 5 i.val))),
([([(0x1000000,0),(0x80000,1),(0x820,2),(0x1041,6),(0x4000,9),(0x82,10),(0x200,13),(0x4,14),(0x10,17)], [(0x20408,2),(0x400000,3),(0x10100,6),(0x200000,7),(0xa000,10),(0x100000,11),(0x40000,18),(0x800000,19)])], (fun i => Fin.ofNat 25 (unpack 0x1872493b30e28d5660c28a281f76a072 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x1824dc9a01ea2dc726a2c28b0f50c166 5 i.val))),
([([(0x18c0000,0),(0x108000,2),(0x6,9),(0x18,10),(0x1,12)], [(0x630000,1),(0x420,3),(0x6300,5),(0x18c0,6)])], (fun i => Fin.ofNat 25 (unpack 0x18bd2d59c9f181060105cd53169414e6 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x18bd6969ca0f8a50629c830804e6ad4c 5 i.val))),
([([(0x1040000,0),(0x402,1),(0x2000,3),(0x80000,4),(0x24,5),(0x4100,7),(0x200,11),(0x1,12),(0x8,14),(0x10,18)], [(0x8080,2),(0x800000,4),(0x101040,6),(0x20000,9),(0x800,10),(0x410000,13),(0x200000,17)])], (fun i => Fin.ofNat 25 (unpack 0x18991c9bc86d451e0516d1130f580566 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x189a48ebc9036d6060ae8f2815689c4c 5 i.val))),
([([(0x1000000,0),(0x400000,1),(0x100000,2),(0x2000,3),(0x800,4),(0x4000,5),(0x1000,6),(0x400,7),(0x8,8),(0x2,9),(0x10,10),(0x4,11),(0x1,12)], [(0x200000,1),(0x800000,2),(0x20,3),(0x80,4),(0x200,5),(0x40,6),(0x100,7),(0x8000,8),(0x20000,9),(0x80000,10),(0x10000,11),(0x40000,12)])], (fun i => Fin.ofNat 25 (unpack 0x18b52f57314d59040186717ca0939506 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x18ade96499053ce127c4811804e5b54c 5 i.val))),
([([(0x1000000,0),(0x2,1),(0x80000,2),(0x400,3),(0x8,4),(0x20,5),(0x1000,6),(0x80,8),(0x4000,9),(0x200,11),(0x1,12),(0x4,15),(0x10,18)], [(0x20000,1),(0x400100,3),(0x8000,4),(0x2000,5),(0x100040,6),(0x800,8),(0x40000,12),(0x800000,14),(0x10000,15),(0x200000,17)])], (fun i => Fin.ofNat 25 (unpack 0x1871269b30513d140796ed1c91558606 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x184cc8ea9a015dd121b685781563c44c 5 i.val))),
([([(0x1ad0340,0),(0x108020,2),(0x4,8),(0x1a,10),(0x1,12)], [(0x420080,2),(0x400,8),(0x6800,10),(0x1000,12)])], (fun i => Fin.ofNat 25 (unpack 0x18bd2b69c9f08906008928298ee6a96c 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x18bd2b69c9f08906008928298ee6a96c 5 i.val))),
([([(0x1000040,0),(0x80000,1),(0x400,3),(0x1022,6),(0x4080,9),(0x201,12),(0x4,15),(0x10,18)], [(0x8,1),(0x20000,2),(0x400800,3),(0x8000,5),(0x100000,6),(0x100,7),(0x2000,10),(0x10000,11),(0x200000,12),(0x40000,18),(0x800000,19)])], (fun i => Fin.ofNat 25 (unpack 0x1871133b30478d1402beab09a1768d12 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x1824d2ea01e555c72436a181976144ec 5 i.val))),
([([(0x1000000,0),(0x300000,2),(0x18c,8),(0x210,10),(0x63,12)], [(0xc00000,2),(0x18c00,8),(0x84000,10),(0x63000,12)])], (fun i => Fin.ofNat 25 (unpack 0x18ad2f6498a83902018a707ca2e5a9ac 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x18ad2f6498a83902018a707ca2e5a9ac 5 i.val))),
([([(0x1010504,0),(0x80000,2),(0x808,4),(0x4000,6),(0x20,8),(0x41,12),(0x200,14),(0x2,16),(0x10,18)], [(0x200000,2),(0x8080,4),(0x100000,6),(0x2000,8),(0x41000,12),(0x800000,14),(0x20000,16),(0x400000,18)])], (fun i => Fin.ofNat 25 (unpack 0x184926ea98305d0a07aae81c9b638a2c 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x184926ea98305d0a07aae81c9b638a2c 5 i.val))),
([([(0x1000000,0),(0x300000,2),(0x108,7),(0x84,9),(0x210,10),(0x63,12)], [(0x400000,1),(0x800c00,3),(0x4000,5),(0x1000,6),(0x2000,8),(0x18000,13),(0x80000,15),(0x20000,16),(0x40000,18)])], (fun i => Fin.ofNat 25 (unpack 0x18ad2d7498a74102010dcb531b383e32 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x18a56f620023124a641e6f84a2e52dac 5 i.val))),
([([(0x1000000,0),(0x8102,2),(0x80000,3),(0x404,6),(0x4000,7),(0x28,10),(0x200,11),(0x1,18),(0x10,19)], [(0x100000,1),(0x2080,2),(0x41040,6),(0x800000,9),(0x20800,10),(0x400000,13),(0x10000,14),(0x200000,17)])], (fun i => Fin.ofNat 25 (unpack 0x1824dc9a01ea2dc726a2c28b0f50c166 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x1872493b30e28d5660c28a281f76a072 5 i.val))),
([([(0x1200240,0),(0x100020,3),(0x4,13),(0x8,14),(0x12,15),(0x1,18)], [(0x800100,1),(0x408080,2),(0x90000,5),(0x40000,6),(0x20400,7),(0x4800,10),(0x2000,11),(0x1000,12)])], (fun i => Fin.ofNat 25 (unpack 0x18a5eb62006114df284525418ee5356c 5 i.val)), (fun i => Fin.ofNat 25 (unpack 0x18b52b77314b6904008d27299138be12 5 i.val)))]

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def mask : Word := 0x7bdef

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def goal : Word := 0x3adae

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def raw : List Word := [15,480,15360,33825,67650,135300,270600,491520]

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def neg : List Nat := [0,6,12,18]

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem autos : DagMovesOK mask goal 25 (dagMoves records) := dagMovesOfCheck (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def hullCode (i : Nat) := unpack 0x640cd92c8263e42044c463e42044c363e42044a363e42044a263c0d9286263c0d92841620cd92c61620cd92c406140b328836140b328626140b328416140b32820614013284160e4a034e160e4a034c160e4a034c060e4a034a460e4a034a060e4a0348060e42034a460e42034a360e420348360e420346260ccd9286160ccd9284160ccd9284060ccd9282060ccd9042060c0d9286260c0d9284160c0d9282060c089146260c0891441604cd92820604ca02ca2604ca02c81604ca02c61604ca02c60604ca02c40604c502c606040b328626040b328616040b328416040b328406040b3282060407328413458891cc23458891cc13458891ca13458891ca03458891c8034583908c234583908a13458390862345839084133e41040e433e41040c333e41040c233e41040a133c089148233c089148133647620c133647620c033647620a03364160c603358891ca23358891c823358891c813358891c803358891c623358891c613358891c603358891c41335839286133583908a23358390862335839086133583908413358390440335839042033581908203298501c203298102ca33298102c82328076148232807614813280761461328076146032807614413280761440328076142030e45020e130e45020e030e45020c030e41040a230e410408130e41020a230d889044130d889042030c089146130c089144130c089144030c08914203098501cc13098501cc03098501ca13098501ca03098501c813098501c803098102ca43098102c833098102c623098102c413098101c833098101c623098101c413080761461308076146030807614413080761440308076142004583908c104583908c004583908a0045839088204583908610424533d040424533ce30424533ce20424133ca0040c3904a1040c3904a0040c390480040c390462040c3904600364260ce10364260ce00364260cc00364260c800358f92861035839288103583928600358390861035839084002d85328c302d85328a202d81328a102cca6048302cca6046202cca6044102cca6042002cc2604a102cc2604a002cc26048302cc26048102cc26048002cc26046202cc26046002cc26044102cc2604200224533cc20224130cc00224130ca10224130ca00218390420020c390462020c390441020c39042001d85328a301d85328a201d853288201d85308a301d813288101d813286101d813286001d813284001d81308c101d81308c001d81308a201d81308a001d813088101d813088001d813086101d813086001d813084001cca6148201cca6146201cca6146101cca6046201cca6046101cca6044101cca6044001cc26148201cc26048101cc26048001cc26046201cc26046101cc26046001cc26044101cc26044001cc260420 40 i

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state0 (i : Nat) : Option RowState :=
  let h := unpack 0x3b9932992999209917990f890879008a 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack 0x780004210821084108420842103c00001e00000f00001780004210821084108420842103c00001e00000f00002780004210821084108420842103c00001ef001e00000f780004210821084108420842f0842103c00001e00000f7800042108210841084f108420842103c00001e00000f780004210821084108420842f03c00001e00000f780004210821084108420842f03c00001e0780004210821084108420842103c00001e00000f 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge0 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x9a1288a378a063aa522332bf1c2d0038 0x3101566310156506335642e0094e310094d043294c1800642310064100326406100336740033500303342d000662d0005a2d0004e1700042300002a300001e4f015664f0156511215644f00c41410094e4f0094d0f2094c4f006424f006410b2264072003427400341002e340610033674003350122334950031e4d000664f0006502280644d0005a4f000590e28058400004e4f0004d0c2804c4e000364f000350c260344e0002a4f000290028028170001e4f0001d002601cc001566c001565022d564380094e4a0094d002c94c4400666440065a30006562d0064e450064abf00642170063ea6006363000632300062abf00366bf0035abf0034ebf00342c0003410b1e3409a003324a0032abf00066bf0005abf0004e950003ea600036c000035001e0344a0002a6101566610156511195645f00c663000c625f00c5a3100c566d00c4e4600c4a6100c424f00c3e5f0096673009625f0095a6d0094e61009426d0064e610064d0f1864c6100635300063161006298c00625bb00342a6003410b18340a6003353000331a6003299a003255e000665e0005a61000566c0004e990004a6000042610003e610002674000250030024600001ea6000127201566720156511175644400f663000f624400f5a3100f562d00f4e4600f4a7200c667200c5a7200c4e6100941310093d700064e720064d0f1664c2d00641450063d7200635bf00341300033dbe00336bf003350c1a3346f000666f0005a6f0004e72000327400031002e030600002a7200029001a028710001e720125b062b25a0625259111525872012577200f5b7200f577200f4f7200c5b7200c577200c4f7200c435f0095b73009575f0094f740094b6d00943740093f61009377400933720065b720064f730064b72006430424642042a6410f14640730063f72006377300633610062b8c00627bf0035bbf0034f740034bbf003438d0033fbf003370024336002a3350b143347400333a60032b9a003274a0031f720005b061e05a720004f061a04e740004b072204a7200043041a042740003f052203e7200037001a03674000330122032730001f041e01ec000013001e0120618f4f0614f4e0714f4d0612f4c1132f4b0916c4f0920c4b1a2cc43031694f032094b162c943142c937061c64f062264b071c643072263f051c6370522633011c62b0122627192c34f0816343082033f04183370514336041433504123340f32333011632b0120327041c31f042231b152c04f0216043022003f00160370020033001802b011402a001402900120280b32027001c01f002201b132c013110b25b110725a1207259110525811112571a08f5b1a0ef571a0cf4f1608c5b160ec57160cc4f140cc43070895b070e957070c94f050c943010c937190c65b190864f190e64b0f0a64310066420f066410f046400f1063f1408637140e633050862b050e627150c35b150834f150e34b1308343130e33f0b0a3370c063360b063350b043340b10333010832b010e327130c31f060c05b060804f060e04b0408043040e03f0008037000e033000a02b010602a000602900040280010027040c01f000c013 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state1 (i : Nat) : Option RowState :=
  let h := unpack 0x35882d8825881d8815880d8806780068 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack 0x780004210821084108420842f03c00001e000080780004210821084108420842f03c00001ef001e078000421082108410842085ef0842f03c00001e07800042108210841084f108420842f03c00001e0780004210821084109e2108420842f03c00001e07800042108211e421084108420842f03c00001e0780004210821084109e20842f03c00001e0780004210821084109e20842f03c00 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge1 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x709d6498569c499a38232a1c11320022 0x650125a650125906452586500c416400642650064117646409e00342a000341005e3409e00336a0003351464334a90031e630005a6500059055a058630004e650004d005a04c63000366500035054c0346b0002a65000290052028530001e650001d004c01ca00125aa001259025d25834006423500641005c640630035a630034e540034a5100342650033e9e003365400332a50032a5f00326530031e9e0005a9e0004e9e000429e00036a00003500460349800026350001ea50125aa501259024b258630095a5300956630094e540094a5100942650093eba009365400932a40065aa40064ea40064276003429100341004a34051003295300325910031da30005aa30004ea300042b900036a5000350042034a50001a91000126f0125a6f01259113d2586f00c5a5100c566f00c4e5400c4a5100c427200c3e6f0095a6f0094e6f009425e00635720063172006256e003426f003410f3c340510033553003316f003299e0003554000319c0002a9e0002900400289e0125a9e01259063b2589e00c5a5100c569e00c4e5400c4a9e00c426500c3e9e0095a9e009569e0094e9e00942ba006359800631ba00629bf0062536003421600341043a340160033553003311600329ac003259c0005a9c0004e9e0004a9c000429e0003e9e00026a0000250b6a024b90001e9e0001a16000129e0125a9e0125906392589600f5a5100f569600f4e5400f4a9e00c5a9e00c4e9e00941540093d5100641980063da4006352c00341530033d2a003362c00335053c3349c0005a9c0004e9e00032a000031005e0309c0002a9e00029003c028a30001e9e00f4f0254f4e0248f4d0636f4c9e00f4b9e00c4f9e00c4b9e00c439e0094f9e0094b9e00943a00093f9e00937a000933a40064f9f0064ba400643a00063fa400637a000633ba0062bac006272c0034f2c00343a00033f2c00337004833600543350436334a000333160032bac00327910031fc90031b9e0004f155c04e9e00043023c042a00003f166403e9e00037003c036a0000331464032a50001f004201ea00001b006201a2f00013135c012023ac430236c420336c410234c40116cc3f0138943014493f1a68937154a643156463f164a6371664633144a62b1464627064a343066433f074a3370764333054a32b0564327003e31f006031b196804300380370044033003a02b013602a003602900340280f6c027134a01f136401b044a013046400f 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state2 (i : Nat) : Option RowState :=
  let h := unpack 0x38883088288820881888108808880088 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack 0x780004210821084108420842f03c00001e0000017800042108210841084f0842103c00001e000002780004210823c841084208421001ef001e00000f780004210821084109e20842f03c00001e00000f780004210821084108420842103c02001e00000f780004210821084108420842103c00001e20000f780004210821084109e2108420842f03c000000f780004210821084108420842f03c00001e000020 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge2 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x4e8f4396369a2a1921911a8e0c9c0019 0x540125a5401259066b25852006425400641046a6409e00336a000335006a334510005a510004e51000425100036530001ea000012720125a7201259115f2585f00935700064272006410f5e640bf003356f0005a720005902500586f0004e720004d0e5004c6f0004272000410c500407200029710001e720001d005001c7200011200125a20012590069258420065a420064e2d0064a2b00642440063e1f0063615006325b0062a2d006261e0035a1e0034e48003421f0033620003350b5c33487003261e0005a1e0004e48000427e000325b0002a2000029005c028bf0125abf012591155258370064249006410f54640be0035abe0034ebf0034abe00342bf0033ea50032ac400326490031ebe0005abe0004ea00004abe00042a00003e9e00036bf000321d0001ea000012bf0001100460104d0125a4d01259185b2584d009353f006424d006410f526404d003364d003350b4e3346f00036720003500500345e0002a720002901580289400012150125a1501259114d2580000935270064215006410f4c64015003361500335006633472000355e0002a72000290156028be0125abe012591149258be0095abe00956be0094ebe00942ba00629bf006250d003420f003410f483400e00329c400325bd0005abd0004e9e0004abd000429e0003e9c00036be000329c0002abe000290040028be00026bf0002501620240800012980125a980125902652588b00642980064100646409e00336a0003350062334a50032a960005a9800059024e058960004e980004d025804c8a0004298000410058040970003698000350056034970001e980001d004e01c 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state3 (i : Nat) : Option RowState :=
  let h := unpack 0x2f77287721771a7713770d6708570088 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack 0x780004210821084109e21084f0842f03c0078000421082108418def109e20842f03c007800042108211e421084109e20842f03c00780004210823c8421084109e20842f03c007800043d084210821084109e20842f03c00780004210823c84109e20842f03c00780004210823c84109e20842f780004210821084109e20842103c000000f00001 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge3 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x541247993d942f9c251512a50717000e 0x9c00f4e9c00f4d1176f4c9c0064e9c0064a9c006429e0063e9c006369e006329c0062a9c00626b70031dbe0031909000360b000350f760349c0001dab00019b900f4ec800f4d0278f4cb60094e9c0094a22009429e0093e9c009369e00932b60064ec700642b700636b60034ec700342b700336b10031ac20031900a0318b800036c80003500780349c000290500025c80001dc8000119c00f4e9c00f4d0674f4c9c00c4e9c00c4a9c00c429e00c3e9c0094e9c009429c006359e006319e006259c003359e00331a20032902000359e00031000002a020002900760280200f4e0200f4d0272f4c0200c4e9c00c4a0200c429e00c3e020094e020094a02009422600635ab0063126006292c006256800335c20033168003290c00325000004e0000042020003e020002605000250fa6024250001e020001a6800012020000e0200f4e9c00f4a0200c4e0200c4d0374c4c02009419e0093dc100641ab0063d1200635aa00341c20033d560033502000320500031008e030000002a02000290074028110001e56000120200c430084c420086c410370c400200c3f0200943020093f020093705009331200643040063f12006370500633260062b23006275600343050033f56003370500333680032b2300327c80031f4c0031b0200043199c0420200037007403605000331aa4032140001f137a01e050001b13a201a5700013047a012050000f04a200e007293701709360070935006e93411a8933199663719a46331a9662b1aa4627159633715a4333169632b16a4327137831f139e31b069603706a4033079602b07a4027047801f049e01b0078013009e00f070125a0701259026d25804006420700641006c640a50032abf00329006a328030005a030004e03000421500036060001e 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state4 (i : Nat) : Option RowState :=
  let h := unpack 0x31772a7723771c7715770e7707770077 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack 0x7800042108210841084f0842103c02001e0780004210821084108420842f03c20001e0780004210821084108420842f03c80001e0780004210823c8410842085ef0842f001e0780004210823c8421084109e20842f001e0780004210821084109e20842f03c00001ef780004210821084109e20842f03c0002000780004210821084109e2085ef0842f03c00 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge4 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x3e88398a340b29951e1716100a970015 0x6f00f4e6f00f4d188cf4c5c006296e003366f003350f82334bc000299600f4e9600f4d0098f4c8900336960033500943349c0002a9e00029007e028a10001e5100f4e5100f4d0a88f4c770093550003365100335048a3349b000359c0002a9e0002914920285a00f4e5a00f4d0096f4c620064e510064a6200642520063e50006366300632b50062a5200626590034e59003428f00336590004e59000428f00036b50002a5a00029007a028860000e2a00f4e2a00f4d0686f4c2a0094e2a0094a2a009421b006292c0062559003293400325290004e2900042020003e00000362a00032000002a2a0002900760282a000262c0002514a20247500012020000e9e00f4e9e00f4d0290f4c3300336340033500903349c0004e9c000429e0003e9c000369e000329c0002a9e00026a30001ec30001a9d000129e00f4e9e00f4d1ba4f4c9e00c41020034e02003420500341008e340020033605003351aa43349c0004e9e0004d038804c9c000369e0003500880349c0002a9e000290b80028a30001e9e0001d008001ca300f4ea300f4d027af4ca20064e9d0064aa2006429e0063e9c006369e00632b70062a9e00626a20034ea200342a200336b00032675000369000035007a0349c0001dc2000199000011 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state5 (i : Nat) : Option RowState :=
  let h := unpack 0x31772a7723771c7715770e7707770077 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack 0x780004210821084109e20842f03c00000227800042108211e4108420842f03c0000080780004210823c84108420842f001ef001e0780004218821084108420842f03c00001e07800042108210a4108420842f03c00001e0780004210821084108620842f03c00001e0780004210823c84109e20842f03c00001e078000421082108410842084af03c00001e0 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge5 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x33952b9022131b0e160a110a0714000e 0xab00f4eab00f4d029ef4cb10062ac20062900a06283c003364c00335009e334aa0004eab0004d027c04caa00042ab00041037c040aa00036ab00035017c0344c00012ab00011007c0109e00f4e9e00f4d068ef4c9e009352c003359c0004e9e0004d058c04c9c000429e00041008c0409e00029a30001e9e0001d008201c9e000113400f4e3400f4d009cf4c620034e6200342520033e500033664003321c0032a52003265a0031e5d0031a330004e330004233000361c0002a34000290090028850001a6300f4e6300f4d1180f4c6300935620033663003351d9a3349c000369e00035008c0349c0002a9e000291c98028a8000129600f4e9600f4d009af4c8900336960033500943349c0002a9e000290c7e028a30001e9600f4e9600f4d0292f4c8900336960033500923349c0002a9e00029008a028a30001e2c00f4e2c00f4d0684f4c2a0034e2a003422c0033e140032a4300326900031e2c0031a2a0004e2a00042050003e02000362c00032900001e050001a05000122c0001113900106300f4e6300f4d0680f4c63009356200336630033517943349c000369e0003500820349c0002a9e000291494028a800012 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state6 (i : Nat) : Option RowState :=
  let h := unpack 0x2e562a4623771c7715770e7707770077 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack 0x7a1084210823c84109e20842f7a10823c84109e20842f780004210823c84109e2084210000f00001780004210821084109e20842f03c00000017a10823c841084208421001ef001e00000f780004210821084109e20842103c000000f780004210823c84108420842f001e000020780004210821084109e20842f03c0000020 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge6 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x31982b8c268a210b1714128909130012 0x6370000633000062b1aba62902006271aca62510003370100333100032b16ba329020032716ca325470031f220031b55000370200033550002b07ba029020002707ca0258e0001f220001bc6000133a0000f19b862b19c862715b832b15c832713b831f13c831b06b802b06c802704b801f04c801b00b801300c800f0400f4e0400f4d00a8f4c050031e0e0031d00a631c010004e01000420100036130002a9e00f4e9e00f4d02a6f4c0200336050033500a63349c0004e9c000429c000369c0002a0500012420064e2d0064a2b00642440063e1f0063615006325b0062a2d006261e0034e28003421f0033620003350b9c33487003261e0004e28000427e000325b0002a2000029009c0280300f4e0300f4d158af4c01003360300335138a334a30001ebe0001d008a01c8500f4e8500f4d00a4f4c140032a2c0032900a2328860031e810004e850004d029804c81000428500041029a040890003685000350094034840002a850002900920289e00f4e9e00f4d02a2f4c0200336050033500a23349c0004e9e0004d027e04c9c000429e000410e7e0409c000369e000350c7e03405000129e00011007e010 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state7 (i : Nat) : Option RowState :=
  let h := unpack 0x2a6624661e66186612660c6606660066 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack 0x780004210821084109e20a42f03c00780004210821084109e20842f03c20780004210821084109e20842f03c22780004210823c84109e2085ef0842f780004210823c8418def109e20842f780004210823c84211e4109e20842f7800043d084210823c84109e20842f7a108780004210823c84109e20842f 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge7 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x300b2d062889210f1812118d0a8e0015 0x9c00c429c00c411bc4c409c0093500000420000036020003500ac034000002a02000291ac40289c00c429c00c4100bec40000002a020002900b0028aa00c42aa00c4103b4c40af0031ec10031d00bc31c3b0002a4b0002900ae0285900c425900c4100bac402100342020033e21003360200332000032a2200326b30031e120031a580004258000368e0002a7c0001ab400c42c600c4100b8c402100642000063e21006360200632000062a2200626b200342c5003360baa32ab200042c50003600aa02a7d0000e830000d00c600c0000c420000c4106b2c400000642000063e00006360200632000062a0000626190031d2a00319000001d0a000190000c420000c3e0000942000094100b29400000635020063102006251000335020033110003293900035020003155000290000932000093111cc9300000641000063d00006350000631000062902006251000341010033d10003350100331100032902003255500041020003d5500035020003155000290200025 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state8 (i : Nat) : Option RowState :=
  let h := unpack 0x2a6624661e66186612660c6606660066 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack 0x780004210823c84109e20842f001ef7800043d0821084109e20842f020007800042188211e4108420842f03c00780004210821084109e20842f03c00780004210823084109e20842f03c007a1084210823c84109e20842f03c007a1087800023c84109e20842f03c007800042108211e410842084af03c00 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge8 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x218c1c8a1a05170613080a12028f0005 0x3300c423300c4100c0c40320004232000360200032000002a33000261a0001e120001a59000123d0000e0200c42020093502000410200029110001e020001d0bac01c5600012020001100ac0109c00c429c00c4111acc409c006292a000299c00c429c00c4102b6c40000002a020002900b60289c00c429c00c411bc2c4000000420000036000002a020002900b60280200935050093112006350500631560033505003310000042020003e0000036020003500b2034020003205000311aca030110001e020001a5600012020000e0200935020093112006350400631560033505003310000042020003e0000036020003519c0034110001e020001a5600012020000e9c00c429c00c4106acc409c006292a00029 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state9 (i : Nat) : Option RowState :=
  let h := unpack 0x2a6624661e66186612660c6606660066 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack 0x78000421082108418def03c0000022780004210823c84109e20842f000227a10823c84108420842f001ef001e07a108210a4108420842f03c00001e07a10821084108420842f03c20001e07a10823c8410842085ef0842f001e0780004210823ca4108420842f001e0780004210823c84108620842f001e0 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge9 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x23921c0f150e11870e07070e03870007 0xb000c42b000c4102c6c407f0032a930032900c6328a700042b00004102bc040a700036b00003503bc034ae0002ab00002901bc0289300012b00001100bc0103a00c423a00c4100c8c407d0031e830031d00c631c39000423a0004101b404039000363a0003500b40343e0002a3a0002900ae0286200342520033e500033664003321c0032a52003265a0031e5d0031a330004233000361c0002a340002900c0028850001a8900336960033500c43349c0002a9e000290cbe028a30001e8900336960033500c43349c0002a9e0002900be028a10001e6200642510063e50006366300632b50062a520062659003426a0033659000426a00036b50002a5a0002900ba028860000e8100c428100c4100c4c40110001e2a0001d00b001c82000128100c428100c4100c2c40110001e2a0001d00b601c8200012 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state10 (i : Nat) : Option RowState :=
  let h := unpack 0x285523551e55186512660c6606660066 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack 0x780004210823ca4109e20842f780004210823ca6109e20842f7800043d0821084109e20a42f78000421082bcaf23c8418def109e27a10823c84109e2084210000f00001780004210823c84109e20842f000017a10823c84108420842f001e000020780004210823c84109e20842f00020 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge10 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x198316861582130510060c87060d000c 0x936000093500d89343900936390093500d69347b00012800001100d00100000936000062900d4c40210032467003187b0002400ce01c050031e0e0031d00cc31c01000420100036130002a0200c420200c4100ccc4000000420000036000002a110001e140032a2c0032900ca328860031e8100042850004102c40408900036850003500c4034840002a850002900c20280200c420200c4100cac400000042020004102be040000003602000350ebe034000002a020002900b0028 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state11 (i : Nat) : Option RowState :=
  let h := unpack 0x23551e55195514550f550a5505550055 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack 0x7a10823c84109e20842f001ef7a10821084109e20842f03c2078000421082108418def03c227a10823c84109e2085ef0842f7a10823c8418def109e20842f780004210823c84109e20842f780004212a23c84109e20842f7a10843d0823c84109e20842f 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge11 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x1708158312860e09088b070304060008 0x32000360200032000002a33000261a0001e120001a59000123d0000e000002a020002900d8028ad00936ad0093503d29347a0001e920001d00d001c21003360200332000032a2200326b30031e120031a5800036690002a7c0001a21006360000632000062a22006260dd43360bd432a02d403600d402a7d0000e830000d00dc00c0000936000093500da9343900936390093502d69347b00012800001100d201000009360000932000062902006251000329020032539000290200025 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state12 (i : Nat) : Option RowState :=
  let h := unpack 0x23441e54195514550f550a5505550055 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack 0x780004210823ca618def780004210833de62bcaf18def7a10823c84109e20842f000017a10823c84109e20842f000207a10823c84109e20842f00022780004210823c8418def000227a10823ca4108420842f001e07a10823c84108620842f001e0 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge12 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x1503130411830e860a09040c02040004 0x790062a790062900e062800de93479003186600018240000c0000036000002a110001e0000036020003502d8034000002a020002900d80287d0031e830031d00dc31c39000363a0003502d60343e0002a3a0002900d60287b009367b0093500dc93478000367b0003501d2034780002a7b0002900d2028880001e7b0001d00d001c110001e2a0001d00d801c8200012110001e2a0001d00da01c8200012 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state13 (i : Nat) : Option RowState :=
  let h := unpack 0x1d331943154411440d44094404540044 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack 0x7a10823ca618def7a10833de62bcaf18def7a10823c8418def000227a10823c84109e20842f7a10823ca4109e20842f7a10823ca6109e20842f7a1082bcaf23c8418def109e2780004212a23c8418def 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge13 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x9800803050605000500038301840003 0x79003186600018240000c780002a7b0002902e0028880001e7b0001d00e001c7b00012800001100e0010210032467003187b0002400de01c780062a780062902e0628 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def states (i : Nat) : Option RowState := (if i < 56 then (if i < 24 then (if i < 8 then state0 i else (if i < 16 then state1 i else state2 i)) else (if i < 40 then (if i < 32 then state3 i else state4 i) else (if i < 48 then state5 i else state6 i))) else (if i < 80 then (if i < 64 then state7 i else (if i < 72 then state8 i else state9 i)) else (if i < 96 then (if i < 88 then state10 i else state11 i) else (if i < 104 then state12 i else state13 i))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge (i tok : Nat) : Option DagLink := (if i < 56 then (if i < 24 then (if i < 8 then edge0 i tok else (if i < 16 then edge1 i tok else edge2 i tok)) else (if i < 40 then (if i < 32 then edge3 i tok else edge4 i tok) else (if i < 48 then edge5 i tok else edge6 i tok))) else (if i < 80 then (if i < 64 then edge7 i tok else (if i < 72 then edge8 i tok else edge9 i tok)) else (if i < 96 then (if i < 88 then edge10 i tok else edge11 i tok) else (if i < 104 then edge12 i tok else edge13 i tok))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def links (i tok : Nat) : Option DagLink := do
  let (d,a) ← edge i tok
  if d == 0 then none else some (d-1,a)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def cut (i tok : Nat) (s : RowState) : Bool :=
  match edge i tok with
  | some (0,code) => Geometry.rectangleReject goal s (hullCode code)
  | _ => false
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem cutOpen (i tok s) (h : MonoViable mask goal s) : cut i tok s = false := by
  unfold cut
  split
  · exact Geometry.rectangleOpen _ h
  · rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def check := scan mask goal neg states 112 (dagMoves records) links cut

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b0to28 : treeBlock 0 28 check = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b28to56 : treeBlock 28 28 check = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b0to56 : treeBlock 0 56 check = true := treeBlock_merge (left := 28) (right := 28) b0to28 b28to56

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b56to84 : treeBlock 56 28 check = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b84to112 : treeBlock 84 28 check = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b56to112 : treeBlock 56 56 check = true := treeBlock_merge (left := 28) (right := 28) b56to84 b84to112

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b0to112 : treeBlock 0 112 check = true := treeBlock_merge (left := 56) (right := 56) b0to56 b56to112

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem lower : AOLower mask raw goal 11 := by
  apply lowerStock (width := 25) (root := 0) (fuel := 10) (row := (10,raw,[]))
    (stockMaskedOfCheck (by decide +kernel)) (by unfold properWord; decide +kernel)
    (by decide +kernel) (by unfold Masked; decide +kernel) autos
    (by decide +kernel : ∀ n ∈ neg, goal.testBit n = false) cutOpen
    (fun i hi => treeBlock_at b0to112 (Nat.zero_le i) (by simpa using hi))
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
end Rep9102.SmallCrown

open WordEngine
namespace Rep9102.Subfloor
open SmallCrown

def rawOn (m : Word) := Rep9102.stock.map (· &&& m)
def dropMask (v : Fin 5) : Word :=
  (![0x1ef7bc0,0x1def41d,0x1bd837b,0x1705ef7,0x7bdef] : Fin 5 → Nat) v
def omitRowMask (v : Fin 5) : Word :=
  (![0x1ffffe0,0x1fffc1f,0x1ff83ff,0x1f07fff,0xfffff] : Fin 5 → Nat) v
def omitColMask (v : Fin 5) : Word :=
  (![0x1ef7bde,0x1def7bd,0x1bdef7b,0x17bdef7,0xf7bdef] : Fin 5 → Nat) v

private theorem mapLower {m n target low roots bank} (f : Word → Word)
    (zero : f 0 = 0) (ones : f m = n)
    (andG : ∀ a b, f (a &&& b) = f a &&& f b) (orG : ∀ a b, f (a ||| b) = f a ||| f b)
    (supply : ∀ a ∈ roots, AvailableWord n bank (f a)) (lower : AOLower n bank (f target) low) :
    AOLower m roots target low := by
  have av {roots bank} (src : ∀ a ∈ roots, AvailableWord n bank (f a)) {a}
      (h : AvailableWord m roots a) : AvailableWord n bank (f a) := by
    rcases h with rfl | rfl | h
    · exact Or.inl zero
    · exact Or.inr (Or.inl ones)
    · exact src _ h
  intro vs built hit
  have mapBuilt {ws roots bank} (src : ∀ a ∈ roots, AvailableWord n bank (f a))
      (b : AOBuild m roots ws) : AOBuild n bank (ws.map f) := by
    induction ws generalizing roots bank with
    | nil => trivial
    | cons w ws ih =>
      obtain ⟨⟨a,b,ha,hb,op⟩,tail⟩ := b
      refine ⟨⟨f a,f b,av src ha,av src hb,?_⟩,ih ?_ tail⟩
      · rcases op with rfl | rfl
        · exact Or.inl (andG _ _)
        · exact Or.inr (orG _ _)
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inr (Or.inr List.mem_cons_self)
        · exact availableWeaken (fun _ h => Or.inr (Or.inr (List.mem_cons_of_mem _ h))) (src _ hx)
  rw [← List.length_map (f := f) (as := vs)]
  apply lower (vs.map f) (mapBuilt supply built)
  apply av _ hit
  intro w hw
  rcases List.mem_append.mp hw with hv | hr
  · exact Or.inr (Or.inr (List.mem_append_left _ (List.mem_map_of_mem hv)))
  · exact availableWeaken (fun x hx => Or.inr (Or.inr (List.mem_append_right _ hx))) (supply _ hr)

private def gather : List Nat → Word → Word
  | [], _ => 0
  | j::js, w => Nat.bit (w.testBit j) (gather js w)

private theorem gatherGates (js : List Nat) (x y : Word) :
    gather js (x &&& y) = gather js x &&& gather js y ∧
    gather js (x ||| y) = gather js x ||| gather js y := by
  induction js with
  | nil => simp [gather]
  | cons j js ih => exact ⟨by simp [gather,Nat.land_bit,ih.1], by simp [gather,Nat.lor_bit,ih.2]⟩

private def slots (v : Fin 5) : List Nat :=
  (List.range 19).map fun j =>
    let skip := fun a => if a < v.val then a else a+1
    if j % 5 = 4 then 25 else 5*skip (j/5) + skip (j % 5)

theorem allFour (v : Fin 5) : AOLower (dropMask v) (rawOn (dropMask v)) (T &&& dropMask v) 11 := by
  have ok := (by decide +kernel : ∀ i : Fin 5,
    let f := gather (slots i)
    f 0 = 0 ∧ f (dropMask i) = SmallCrown.mask ∧ f (T &&& dropMask i) = SmallCrown.goal ∧
    (rawOn (dropMask i)).all (fun w => availableB SmallCrown.mask SmallCrown.raw (f w)) = true) v
  obtain ⟨zero,ones,goalEq,cover⟩ := ok
  exact mapLower _ zero ones (fun a b => (gatherGates _ a b).1) (fun a b => (gatherGates _ a b).2)
    (suppliesOfCheck cover) (goalEq ▸ SmallCrown.lower)

private abbrev removesPort (m s : Word) : Prop :=
  ∃ p n : Fin 25, (T &&& m).testBit p.val = true ∧ (T &&& m).testBit n.val = false ∧
    ∀ w ∈ rawOn m, w.testBit p.val = true → w.testBit n.val = false → maskedFlat s w

private def lineMask (row : Bool) (i : Fin 5) := if row then omitRowMask i else omitColMask i

theorem line12 (row : Bool) (i : Fin 5) :
    AOLower (lineMask row i) (rawOn (lineMask row i)) (T &&& lineMask row i) 12 := by
  let m := lineMask row i
  let s := dropMask i
  have properties := (by decide +kernel : ∀ r : Bool, ∀ v : Fin 5,
    let m := lineMask r v
    let s := dropMask v
    (rawOn m).all (fun w => w &&& m == w) = true ∧
    (T &&& m ≠ 0 ∧ T &&& m ≠ m) ∧
    ¬ maskedFlat s (T &&& m) ∧ (T &&& m) &&& s = T &&& s ∧
    (rawOn m).all (fun w => availableB s (rawOn s) (w &&& s)) = true ∧ removesPort m s) row i
  obtain ⟨masked,proper,nonflat,restrict,sources,p,n,pos,neg,sep⟩ := properties
  intro vs built hit
  obtain ⟨k,S,budget,live,sub⟩ := extractAO (stockMaskedOfCheck masked) built hit proper
  obtain ⟨w,hw,yes,no⟩ := liveDirected live pos neg
  have flat : w ∈ flatSet s S := Finset.mem_filter.mpr ⟨hw,sep w (sub w hw) yes no⟩
  have posCard := Finset.card_pos.mpr ⟨w,flat⟩
  have supply : ∀ x ∈ projectedStock s S, AvailableWord s ([] ++ rawOn s) x := by
    intro x hx
    simp only [projectedStock,visibleWords,Finset.mem_insert,Finset.mem_image] at hx
    rcases hx with rfl | rfl | ⟨a,ha,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact suppliesOfCheck sources a (sub a ha)
  have cut := Project.cut live nonflat (show AOBuild s (rawOn s) [] from trivial) supply (restrict ▸ allFour i)
  simp only [List.length_nil,Nat.zero_add] at cut
  change 11 + (flatSet s S).card ≤ k at cut
  omega

theorem row12 (v : Fin 5) : AOLower (omitRowMask v) (rawOn (omitRowMask v)) (T &&& omitRowMask v) 12 :=
  line12 true v
theorem col12 (v : Fin 5) : AOLower (omitColMask v) (rawOn (omitColMask v)) (T &&& omitColMask v) 12 :=
  line12 false v
def minorFacts : List (Word × Nat) :=
  (List.finRange 5).map (fun v => (dropMask v, 11)) ++
  (List.finRange 5).map (fun v => (omitRowMask v, 12)) ++
  (List.finRange 5).map (fun v => (omitColMask v, 12))

theorem minorMasks_distinct : minorFacts.length = 15 ∧ (minorFacts.map Prod.fst).Nodup := by
  decide +kernel

theorem minorLower {m n} (h : (m,n) ∈ minorFacts) : AOLower m (rawOn m) (T &&& m) n := by
  simp only [minorFacts, List.mem_append, List.mem_map, or_assoc] at h
  rcases h with ⟨v, _, e⟩ | ⟨v, _, e⟩ | ⟨v, _, e⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact allFour v
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact row12 v
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact col12 v

theorem cutMinor {mask k S prep m n} (h : (m,n) ∈ minorFacts)
    (run : LiveWord mask T k 0 S) (built : AOBuild m (rawOn m) prep)
    (sources : ∀ x ∈ projectedStock m S, AvailableWord m (prep ++ rawOn m) x) :
    n + (flatSet m S).card ≤ prep.length + k := by
  have valid : minorFacts.all (fun p => decide (¬maskedFlat p.1 T)) = true := by
    unfold maskedFlat
    decide +kernel
  exact Project.cut run (of_decide_eq_true (List.all_eq_true.mp valid _ h)) built sources (minorLower h)

end Rep9102.Subfloor
open WordEngine
namespace Rep9102.Project

theorem validCuts (pairs : Array (Word × Nat))
    (known : ∀ q ∈ pairs, q ∈ Subfloor.minorFacts)
    (proper : ∀ q ∈ pairs, ¬ maskedFlat q.1 T) :
    ∀ q ∈ pairs.map (fun x => (⟨x.1,x.2,stock.map (· &&& x.1)⟩ : Minor)), Minor.Valid T q := by
  intro q h
  obtain ⟨x,mem,rfl⟩ := Array.mem_map.mp h
  exact ⟨proper _ mem,Subfloor.minorLower (known _ mem)⟩
end Rep9102.Project

open WordEngine PEqualNP.Represents

namespace Rep9102.Final9102

open Orbit Project

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def moveParts (p : Nat) : List (Word × Nat) :=
  (Nat.rec (motive := fun _ => Nat → List (Word × Nat)) (fun _ => [])
    (fun _ next v => (unpack 0xf7bde0739c0035a06819c8019c600005816b02a0a82b405000980139c820902400481100011820820c10408a0820010408818202224101002080001022041811020408808a044001018000808880c044402020a09010000804824402222201000100100080020040001020000030000007800003800001a00000c0000c6000002c00001405000a0000048120024004812000008810414408002202205100800880000418000208208104000081020040800020200010080008021004010102008021004000800c004004002001001000210800100400010200004100001080000039c0001c00000c600006000063000001400280a0000048000022202091100008401004200042100001050404828200410400208104104000081010040800020202010100008040004008002002001000800800200400084200040100008080000440000018c6000c600006080003010001800000a0000048240224120012030208888044400002108001080010840000418200209208104082082000040810020400010101008080004024002010001004040802008401000200400100100080040040004020001010000408000084000001800000a0448044000021084010840008418004201002100401080000824100410800208104104000081010040800020318010104008080004024002011001008000802100401000200400100180080080040020020008010002008000804000202000000b00000540000280a001400400a0014050000026000012002409000004620002200001084200842000420c002100401080000824100410800208208104000080810040404020200810100008048004010802008001002000800a00400400200080100020080008040002020000810000007bdef039ce001ad0340c602006300002c0b58140500090412048009020820810410008204404101002080081040000811000404440202000100840080080040010020000810000007000003042001800800c00000501400280000120100090000044080022010011000008300004104002080001020400810000404080202000100800080210040100020010010002008000003180001821000c000004804002400001110000841000420080210000106080082000040800020200010080008010004004002001001000400800100400000140000090480044000021080010820008400004104002080001020400810000404000201200100800080200040080020020010008008000003400001900000c63000630000300000130000090240048000023100010840008402004200002082001040000810000404100202000100880080400040100020040010010008004004000001600000a028005000002400001100000842000420c00210000104200082080041000020200010040008010004004002000000e73800630000280a00104100082000040880020200010080008008004000001800000a0000048000022040011000008200004080002020001008000802000400000120000088800042000020c000104000081000040400020100010000007380003800001900000c600006000002a0000140000088000042000020800010200008080004020002000000d000006300003000001200000880000420000208000102000080800040000014000009000004400002100001040000800000318000104000080000030000014000009000004400002000000f000007000003400001800000b000005000002400001000000700000300000140000080000030000010000004000001 25 ((v >>> 5) &&& 511), v &&& 31) :: next (v >>> 14))
    (p &&& 15)) (p >>> 4)
def quickRecord (code l r : Nat) : DagMoveRecord 25 :=
  ([(moveParts l,moveParts r)], (CompactMoves.record (CompactMoves.rawMove code)).2)
def actions0 : List (DagMoveRecord 25) := [quickRecord 50824 0x1101630de871132605 0x7ac24cca422d444,quickRecord 14472 0x17465c95a242f04a605 0xbe1aac5ac10e414,quickRecord 47240 0x2443cd042ca8901205075d18324320ee00a 0x1eb18ab4f8b9c246c8471ef8622114439,quickRecord 17608 0x9463b14a849e072e05 0x5d19dc55112ba14,quickRecord 50376 0x110013450c36a408725180246c8f1809 0x7ac0f8d8ab2ce91b1d74608128038,quickRecord 10440 0x19865095ca313042e05 0xbe3266abba45a24]
set_option maxHeartbeats 0 in
theorem verifiedActions0 : actions0.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions6 : List (DagMoveRecord 25) := [quickRecord 43208 0x24442d2a28309621802454082c08 0x1eb28abaf8c3e2d2e7a8142041f8eca19,quickRecord 13576 0x94c24a8ee90d082e05 0xcd9a6c5a58c6414,quickRecord 46344 0x14830e253010b161d64500903c3a0842c0a 0x1eb19336b0a47271c60811ba27,quickRecord 9992 0x94c31a8c8853099605 0xbe32eca9c21b624,quickRecord 42760 0x14830e26303c85818024140a9e08 0x1eb28abb02c4722da608107e27,quickRecord 18000 0x2a6199430495873805 0x2518f451f929814]
set_option maxHeartbeats 0 in
theorem verifiedActions6 : actions6.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions12 : List (DagMoveRecord 25) := [quickRecord 50768 0x110143408c1024c870a99a242b0f2009 0x7ac270d3e315498a9c946ac112638,quickRecord 14416 0x19464015e4402840005 0xcc19fc5ba901414,quickRecord 47184 0x910f3810b00a4be85e98043320adc09 0x7ac670e3e2c6c996a3006080d1c28,quickRecord 17104 0xa463994b83aa072805 0x5d31d4a5b26b224,quickRecord 49872 0x11015b430a32a49e66f8afa07 0x1eb0b33974c8e1d3a59d0d4e17,quickRecord 6352 0x19e64515d0203840005 0xbe49eafbd381034]
set_option maxHeartbeats 0 in
theorem verifiedActions12 : actions12.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions18 : List (DagMoveRecord 25) := [quickRecord 39120 0x910f3804d2ca8029631958204040009 0x7acef923e2e64a1b1e846080ed028,quickRecord 13072 0x94c1fac6ca3224a880c1c2a608145040f0c0420084000d 0x5d31a2b3e291c95122b07be19ea58a927030208101c,quickRecord 45840 0x520c3c94c042c02914202a632154441f8c0829c04000d 0x7ac6b0f3e3974c8aa2fe64714a846b0c3c1a,quickRecord 5904 0x94c1facc0a369c2a6121552247859009 0x2f92b8be2ae9c35aa35,quickRecord 38672 0x14830f263040958987e304057608 0x1eb3be48f8c68ae2aaac1c6c63215263140a701b,quickRecord 17496 0x2ac17284a98b0b2805 0x6619d654c8ef014]
set_option maxHeartbeats 0 in
theorem verifiedActions18 : actions18.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions24 : List (DagMoveRecord 25) := [quickRecord 50264 0x44054e0ab0ce72395a634a06fa08 0x7ac288d512abc9611a4626,quickRecord 10328 0x2ac0f2c20a0c24508471d7463e15444688c0220204000d 0xbe3270b7aaab098aa0c8725186c52a107e30408041c,quickRecord 43096 0x910f3c02e0ab0a885e187e514112030c04000b 0x7aca70fbe30f8b1b254482519a258a90c83080ab01c,quickRecord 17048 0x2ac18283c88f0b3205 0x5d31e6a4722c424,quickRecord 49816 0x11015382ac33208a66a0b0e07 0x7ac2cce5d327e8579a3226,quickRecord 6296 0x2ac0f2c3aa4b1d7465a15bc22b84a209 0x2f92a8beb0e8ab4d035]
set_option maxHeartbeats 0 in
theorem verifiedActions24 : actions24.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions30 : List (DagMoveRecord 25) := [quickRecord 39064 0x2443cf00b82ac2a2404860991c30404960a 0x7acef92a22da2a1b20c878a95443ad88501a,quickRecord 8984 0xa4c1e28f0801880005 0xcdb218aaaa01824,quickRecord 41752 0x520c4002e27b07e80419504020a9409 0x7acab103e3b1ac68a06c691102028,quickRecord 5400 0x293078a2e24e0701880006 0x2f92ac41eafa9b5a285d18f855b8c0819,quickRecord 38168 0x520c4002e27b07e8021d4e54f040009 0x7acef923e36d8c5f9a485080a7c18,quickRecord 13408 0x2b2083c68e008c0005 0xcf1a20596081c14]
set_option maxHeartbeats 0 in
theorem verifiedActions30 : actions30.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions36 : List (DagMoveRecord 25) := [quickRecord 46176 0x330ac810b24280874a9804392880009 0x7ac670e3e36d2a1b2722670882018,quickRecord 9824 0xac848f0c3850d478d9006 0xbe3270bb8aa4872518c0570094618,quickRecord 45728 0x330ac886b14280480c1d1c5320e2e20f04960b 0x1eb1ac3cf8e5d327091b23126688c2019,quickRecord 38560 0x330ac808c23ac0484a1ca8404066209 0x7acef923e32a0b1b22ca751102018,quickRecord 41696 0x330ac804d22b09a64b140828d040009 0x7acab103e3b1ac68a06c7a0956618,quickRecord 5344 0x2b20c4020f0f3850c1fa09461b14a84008cc820104000d 0xbe4ab107abe70e8ab1a285d18f8551101034708081c]
set_option maxHeartbeats 0 in
theorem verifiedActions36 : actions36.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions42 : List (DagMoveRecord 25) := [quickRecord 38112 0xcc2b201348ac021d38604065c08 0x1eb3be48f8db6306c7a7182017,quickRecord 18049 0x6071402488073c05 0xa9868508125814,quickRecord 50817 0x44408d142c04932203c70019c240c0f240a 0x22b14735eab1fa67083e1c2a6b4906c39,quickRecord 14465 0x19065195da430049405 0xca9a765b910e814,quickRecord 17601 0xa263414c44a886f805 0x6519b455a92e814,quickRecord 50369 0x111013850b32243682599a230f0b1409 0x8ac51ce7aaeb0945a17a69c0c6c28]
set_option maxHeartbeats 0 in
theorem verifiedActions42 : actions42.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions48 : List (DagMoveRecord 25) := [quickRecord 10433 0x19c64d11cc33 0xbe322abbca45070a984e46,quickRecord 43201 0x24804e0f30a8a0c2010761994421404220a 0x8acdeadc2307e8409aa051b0aca18,quickRecord 13569 0x25306cb3da404700181a46 0x33a686929a33,quickRecord 9985 0x94c1b2ca8a1fa4c88011c0060214024040d4423e05740d 0xbe322abac29ea99c205070a983c5081030368891c1c,quickRecord 17937 0x2e619143439b073605 0x2530eea24a69624,quickRecord 50705 0x44458d00a83c93619a242c0b1a08 0x2712513894c7aae4c71f16b04470c8219]
set_option maxHeartbeats 0 in
theorem verifiedActions48 : actions48.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions54 : List (DagMoveRecord 25) := [quickRecord 14353 0x19666d914c33 0x2530c8b31a6707be1aec46,quickRecord 16593 0xa663914bc2ab06f805 0x5d49a2f5cbab034,quickRecord 49361 0x111013850d0ca8c8928188826886f809 0xac4d7527aad1aa8a9d2a69c0d5628,quickRecord 2257 0x6819d212 0xbe62f732,quickRecord 35025 0x9210b8b4a63995a25 0x2f988a3e48b9f1cf86ad0d2e27,quickRecord 12561 0x94c24acc892d9c2e616904427 0x5d49a304fb944dac22f8699927038]
set_option maxHeartbeats 0 in
theorem verifiedActions54 : actions54.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions60 : List (DagMoveRecord 25) := [quickRecord 17433 0x2ac082c50a0f24308009c0060414084010e2a27a86f80d 0x2530a8b32286c91fa14475d19a253e111c39c0ab01c,quickRecord 10265 0xab048b17a11e76419e036 0x330cb9a63a83,quickRecord 16537 0x2ac082c5ea101c00605163e27f073009 0x175277bcf8e4736c235,quickRecord 2201 0x2ac122c30a479d92651947e272049409 0x2f989c52e338ac8c845,quickRecord 8473 0xa4c1e2ce082e9c006040c0827 0x175268c4f8eb5b6f8c7aa6a687,quickRecord 1305 0xa4c1e2cb89019ce2602101017 0xbe62b157acea7268a57463e116c38]
set_option maxHeartbeats 0 in
theorem verifiedActions60 : actions60.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions66 : List (DagMoveRecord 25) := [quickRecord 17986 0xc0628069860b3605 0x2918f051e0eaa14,quickRecord 50754 0x44808e003050b371c2456890a831b871a0a 0x22b1a3347ea5126086ac110627,quickRecord 14402 0x3008b05a4f875d19e846 0x3346b211fe33,quickRecord 17090 0xc012c10a00a40881b1c94632147e42a0dea29c06f80d 0x5d311cb68a94493e203c70a985050c10203ac0a2a1c,quickRecord 49858 0x112013c00c142cc890c2094608140841b0da220086f80d 0x8ac51cfac3974c1fa1f262a14f849e8d441a,quickRecord 6338 0xc032c029449d9864c91ca27 0xbe4a2b0bbb9ead14202a612902038]
set_option maxHeartbeats 0 in
theorem verifiedActions66 : actions66.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions72 : List (DagMoveRecord 25) := [quickRecord 39106 0x24c04f0fb0a8a0c2184608147435108021a 0x8ad2f924731a2a7aa47e8a198504ac08f81a,quickRecord 13058 0xa2c3aa4ae83 0x5d31d8b5a22b87ca9aa436,quickRecord 45826 0x540e3496c1418d2555927217 0x22b2b3bd74c801efc64691b237,quickRecord 5890 0x28b0aea2024d075a097406 0x2f928ac2b0fa8b45080a983c56c0d1c19,quickRecord 38658 0x54023830d25b03c757982051b101030085740b 0x22b4be491cd68adea9af9c2a632145043e0a701b,quickRecord 17930 0xc06a8048868b3a05 0x2530f6a1b229a24]
set_option maxHeartbeats 0 in
theorem verifiedActions72 : actions72.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions78 : List (DagMoveRecord 25) := [quickRecord 50698 0x44808e14b03c83519a242a0b1e08 0x2712513a40c4722026ac10f827,quickRecord 14346 0xc022c02a04240483e1d7464715a24510c2020f042a0d 0x2530c8b1fa8a891b22707be1a2a5ac11ea30c08501c,quickRecord 16586 0xc012c12a1c9c9463a160e29d872a09 0x1752763d44e3e36b835,quickRecord 49354 0x44804f14b0da927186c36886fc08 0x2b135d4a2ac472ca8a0f1dea63e168035108081b,quickRecord 2250 0xc032c02a441d9a64c9420273842a09 0x2f988ad2ef37ac85045,quickRecord 35018 0x24c04f0f3400c2a2830962986c351082a0a 0xbe622b068bcc8b7aa8508a31ebe30408f81a]
set_option maxHeartbeats 0 in
theorem verifiedActions78 : actions78.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions84 : List (DagMoveRecord 25) := [quickRecord 16922 0x2ec16a84c8998af805 0x6631caa50a2ee24,quickRecord 49690 0x11200c050e0b302083218844688b0a09 0x9c49450ac3984c2a21ea641922a28,quickRecord 6170 0x2ec112c348501d746510da227 0x2f929c46b0e9ab494c2a249287,quickRecord 38938 0x24c0300f3c2cc0820a875d187e4490c700a 0x9c56f92513494c68aa1098a94304ac090c1a,quickRecord 16474 0xbb05aa0d24447998af806 0x17525141a2f4fb4a882518c85b00e7019,quickRecord 49242 0x11200c050e0b30208321c8256e06f809 0xac4d7529c355ec81990858a892218]
set_option maxHeartbeats 0 in
theorem verifiedActions84 : actions84.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions90 : List (DagMoveRecord 25) := [quickRecord 2138 0x2ec112c3494f9d7c65111a217 0xbe62715ac4e67232249462a109238,quickRecord 34906 0x9300c03cf0b30b085d18825470c7c19 0xbe6271168bcc8d7aa9448909ab030408f81a,quickRecord 4378 0x29b0f272 0xcdcaaed2,quickRecord 37146 0x15033028308881b114836 0xac5b1b268ba0c994968e16,quickRecord 45602 0x350ac810d003050a22251c502122a23704700b 0x27135142b0f6130a887a9ef863e11ae39,quickRecord 38434 0xd42b2023800c0f2c889471c1032a0a5e0a 0x2715be4944e2531a2b8426b070c0cf829]
set_option maxHeartbeats 0 in
theorem verifiedActions90 : actions90.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions96 : List (DagMoveRecord 25) := [quickRecord 45154 0xd42b2043400c242820901151c492886c1a 0x2b145d4a70e57b1ea7c018f856c900819,quickRecord 34402 0x350ac808e00303cb1fa8209471c0452a0c3021b05740d 0x2f989c45a303235eaa5126b0825185053f8a2a1b,quickRecord 37090 0x350ac804f233020925191c41d0e3609 0xac5b1b268b8a8a7aa68463e143c45108081a,quickRecord 33506 0xd42b2013c8cc082494647140841b0c3c1a 0xbe62d925d30c8b7aaa7072f94f84040a5a1a,quickRecord 17475 0x12043c0ee7a8ef805 0x6799d05450af414,quickRecord 50243 0x113004850b09a8c871c19a23428af809 0x8ac51ce9c3558aac258c62c89ea18]
set_option maxHeartbeats 0 in
theorem verifiedActions96 : actions96.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions102 : List (DagMoveRecord 25) := [quickRecord 10307 0x4809001b810d3e217465b11a238 0x2f8ca9aeb09851ca462e107827,quickRecord 17027 0x4814f00b808d7f0f3006 0x5d311cb77a90870a985e5b18a3a18,quickRecord 49795 0x113004856b0828c881b1c0850c0da423e07000b 0x22b1473eb0e5d307e99c216260f0dea19,quickRecord 6275 0x12024004f00b810c3e2174651151c41b0da222a04940d 0xbe4a2b09c3eb0e7ab05080a983050f10c8308087e1c,quickRecord 39043 0x2500120f3004b0828a891b1d7463f903030088940c 0x22b4be491cc9c2da2a1fa4c870a99fa4510eb02b,quickRecord 8963 0x12014402e1db494c1fa4ee87 0x336c952e968879c2a60c0c2027]
set_option maxHeartbeats 0 in
theorem verifiedActions102 : actions102.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions108 : List (DagMoveRecord 25) := [quickRecord 5379 0x1201440ae1b349ac30a4c877 0xbe4ae909c35eac6d21946528d0028,quickRecord 38147 0x1540120c3494c09a86c951141044288a81a 0x22b4be491ceb6307e75e98c857e927019,quickRecord 17419 0x4812f023804d7c0f2a06 0x2530a8b3a295475d19d85a28ab818,quickRecord 50187 0x44c012143020b022802732186c56c8cf820106fc0c 0x2712513e40cb3a58262a0dea17,quickRecord 10251 0x4809000bc14d3e217464715e230f042a0a 0x330c8eaac297f1c5e25,quickRecord 43019 0x2500120f3420b0424aa75d186c53e1050201042a0c 0x9c522ae513700c471c8a66894c847a8eb01a]
set_option maxHeartbeats 0 in
theorem verifiedActions108 : actions108.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions114 : List (DagMoveRecord 25) := [quickRecord 16523 0x1205bc08c7f8f3405 0x5d49e8f3e32c834,quickRecord 49291 0x113004850c092cc881b9c30468870609 0xac4d7528ab13ab9c214e71f91ea18,quickRecord 2187 0x4809001bc10b3e217465b147837184a40a 0x2f98a9d2b137ac4e045,quickRecord 8459 0x12014402f1d3498c1fa8c882a1c2030c082a0b 0x5d49a31473ed2dc0b22aa9c21ea70f0c502a,quickRecord 1291 0x12014402f02386cd253010b1fa8a8932182030c082a0d 0xbe62b158ad27127ac5a295d191c514114433e083c1c,quickRecord 16915 0x48030043c0cd08202a61415f838a86f80a 0x198c72a9329441eee25]
set_option maxHeartbeats 0 in
theorem verifiedActions114 : actions114.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions120 : List (DagMoveRecord 25) := [quickRecord 49683 0x113004850d08b0d661c95a223e86f809 0x9c49450ac3984c2a222a74a160418,quickRecord 6163 0x480b0013410c4021946528db428 0x2f929c46e8e323606c30a46c77,quickRecord 38931 0x9400483ce08b0a875e986c53f900419 0x9c56f92513494c9928c890c15ea4b4087e1a,quickRecord 16467 0x1200c010f013808c08202a614143047a8c3c28a86f80d 0x5d4945068bd1ce3e30a882518c851f92b031b0a701c,quickRecord 49235 0x44c012143422c321c7a668870408 0x2b135d4a70d57b22a74e19ea17,quickRecord 34899 0x2500120f3822c2a218063e108a08 0xbe6271168bcc8d8aad448141c9467a96b034708101c]
set_option maxHeartbeats 0 in
theorem verifiedActions120 : actions120.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions126 : List (DagMoveRecord 25) := [quickRecord 37139 0x55004830f27306c90a98104560cfc09 0xac5b1b268ba2aa2a252a63215ea4140a701a,quickRecord 33555 0x1540120c3c9cc1b242a602154441f8cf81a 0xbe62d925d322ab32285078914a849c08461a,quickRecord 8739 0xbc86ad2 0xcf326e72,quickRecord 41507 0xd82d208388694c164e16 0x9c52d30c8b1c283211f436,quickRecord 5155 0xbc844e0d345ac4 0xbe4a711ac40c8d9a30a8b68a15c75d193e2a,quickRecord 37923 0x360b4820e02287e94a986c50410f820106360b 0x9c56f92513edec32257467a90b238]
set_option maxHeartbeats 0 in
theorem verifiedActions126 : actions126.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions132 : List (DagMoveRecord 25) := [quickRecord 8291 0xbc834e16b444c4 0x5d49a315142b0dc43270b2a226a72518922a,quickRecord 4259 0x2f20d3c64c248c9405 0xcdca96f9b30ee34,quickRecord 37027 0x360b4820e20ac7c749125007 0xac5b1b268ba82b591df646,quickRecord 33443 0xd82d2083882b1f1d22542049408 0xbe62d92a7315e67e963016,quickRecord 13380 0x601f32 0xcf9a2212,quickRecord 9796 0x6009401cc1123e117406 0xbe32a6bac28e078298b8568897018]
set_option maxHeartbeats 0 in
theorem verifiedActions132 : actions132.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions138 : List (DagMoveRecord 25) := [quickRecord 12932 0x6005404cc0921b109406 0x5d31d8b512ab87cb1a7652a0a1618,quickRecord 45700 0x6028f1c310e6848c9406 0x8acacef5d32809c599b236,quickRecord 5764 0x600d400cc11144119806 0x2f928ac2eef7aac5080a984a5728d3619,quickRecord 38532 0x18024020f1c30f880f1c1052a103237a85840b 0x8ad2f924736a0b1fa6ca70a995048,quickRecord 8900 0x6005500cc1921b249461f90ee38 0x336c952e969189e1c60c102017,quickRecord 5316 0x6005502cc1111b249463090c828 0xbe4ae909c39eab6d2194652910018]
set_option maxHeartbeats 0 in
theorem verifiedActions138 : actions138.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions144 : List (DagMoveRecord 25) := [quickRecord 8396 0x18015403404480911b249461f94204320ca820c042a0d 0x5d49a31473d44eac36f8c3e2e2aa9c25ea60f0c502c,quickRecord 45588 0x60211043c02d1b285084119ea30108c81a 0x27135142b0f6132448be19285688c8e19,quickRecord 38420 0x60211024002d1b283c93e202a60414ac27a85740c 0x9c56f92513894c68ae2aa3226b070c151c314087e1c,quickRecord 45140 0x18084410f00b46cb14200470a98f857a8cc8202048a0d 0x2b145d4a70e57b22a8c319a247,quickRecord 34388 0x18084409000b46cb0f24f88011c2a62a0e260b 0xbe6271168c0c8d8aad449ac2050725191c3a,quickRecord 37076 0x602511bb430a2798fe51f89ec18 0xac5b1b268ba44aa4995026]
set_option maxHeartbeats 0 in
theorem verifiedActions144 : actions144.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions150 : List (DagMoveRecord 25) := [quickRecord 33492 0x1809446ed0c291861f89ee07 0x2f98b64974c922e7c74e954e17,quickRecord 37916 0x602320ab008b1b28f8711947e4010a241a 0x9c56f92513edec32257468a943042a0c501a,quickRecord 33884 0x602320ab072b3e9c8e54a05ee08 0xbe62a11b2b544a9818a826,quickRecord 4252 0x1800d8054064420e0ab030a189c6c41f88940b 0x3372a5be54d862cee35,quickRecord 37020 0x1808c87ac2298fe57b049407 0x2b16c6c9a2ea0ad6478d152c17,quickRecord 668 0x1800d8054024811008382ac0c283c814186c41f88940d 0xbe62b169c522b27ac1a2e5d3144a4720f863210a82c]
set_option maxHeartbeats 0 in
theorem verifiedActions150 : actions150.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
theorem allActions {a b : List (DagMoveRecord 25)} (ha : a.all (dagMoveRecordOK (fullMask 25) T) = true) (hb : b.all (dagMoveRecordOK (fullMask 25) T) = true) : (a++b).all (dagMoveRecordOK (fullMask 25) T) = true := by simp [ha,hb]
def records : List (DagMoveRecord 25) := ((((actions0++(actions6++actions12))++(actions18++(actions24++actions30)))++((actions36++(actions42++actions48))++((actions54++actions60)++(actions66++actions72))))++(((actions78++(actions84++actions90))++(actions96++(actions102++actions108)))++((actions114++(actions120++actions126))++((actions132++actions138)++(actions144++actions150)))))
theorem autos : DagMovesOK (fullMask 25) T 25 (dagMoves records) := dagMovesOfCheck (allActions (allActions (allActions (allActions verifiedActions0 (allActions verifiedActions6 verifiedActions12)) (allActions verifiedActions18 (allActions verifiedActions24 verifiedActions30))) (allActions (allActions verifiedActions36 (allActions verifiedActions42 verifiedActions48)) (allActions (allActions verifiedActions54 verifiedActions60) (allActions verifiedActions66 verifiedActions72)))) (allActions (allActions (allActions verifiedActions78 (allActions verifiedActions84 verifiedActions90)) (allActions verifiedActions96 (allActions verifiedActions102 verifiedActions108))) (allActions (allActions verifiedActions114 (allActions verifiedActions120 verifiedActions126)) (allActions (allActions verifiedActions132 verifiedActions138) (allActions verifiedActions144 verifiedActions150)))))
def masks : Array (Word × Nat) := #[(1048575,12),(32538623,12),(33522687,12),(33553439,12),(33554400,12),(16236015,12),(24895223,12),(29224827,12),(31389629,12),(32472030,12),(507375,11),(24141559,11),(29197179,11),(31388701,11),(32472000,11)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def minors : Array Minor := masks.map (fun x => ⟨x.1,x.2,stock.map (· &&& x.1)⟩)

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def words (j : Nat) : Nat := unpack 0xfff18c7ff0843ff4211ff8000fd755d7e9fa53f39f39f94bf2fc63ce7e318fff18739f843f0fc21ce7e108cbf0843ff84210fa3e847d08423e4f909f21084f8c1087c21633e01a11f00694f802c67c01213e00529f00210f800c67c00423e000018c7f18c6318c56bfffeb5fd7f4a7e94a529ffd294fd294a53f4a52949ce7ffca52fca3f8c7f18fe3f8c63ffc6318fe1ffc210fc21085755d4273e72118f3908c39c843f084213c62109d2908479c84234a4210e7210863108423284210837ff6fdadfffed6fdbf67fff633ff6b99ffb3ecffd8c67d9ffb3ecfb19f633ecfb18c633ec6318cffd8c67d8c6319f6318c62febffd731ffeafabea57d4a52a42f893ffa7e9fa7ff4fd29fa53f4fd294ffe94a53f47fe8fa3ff4211f5b188fa79c47d2c623e8ffd1f47d08fa39c47d09523e847d1f421088000042d18c211fffd08ffd0847d1f423e8421096310847fe8423e84210c62108420e7fffe637fe631be6318c637cbf297e52ffff297e5f94a5ffca5297e4ffc8427c9f213e421087fd28427fff213ff2109fe7084fd28427d8c213e53109f27c84f9084213ff2109f2108427c8421083f8fff18ffff8c63ffc5f1084218dce10be2f885f108421dac210cc61085ff8842f884216b4210ad610852908427384212942108c610842f88421083f087e10ffff087e1f8421ffc21087e10842107fe0f83ff0001f1a100f8c8407c2c603e12101f07fe0f83e007c18c03e06301f02100f808407c00000aa2a8031b180182100042c6002063000fffe007fe0003ec6001f21000f83e007c000006840003210000d2800058c00026300012100007fe0003e000018c0000a5000042000018c000084000021000004400001f 25 j

def hull0 (i : Nat) : Nat := unpack 0x20cf914a2020cf91481020cf91480020cf91461020cf91460020cf91440020c590420020c391461020c391440020c390841020c3904a1020c390482020c390481020c390480020c390462020c390461020c390460020c390441020c390440020c390420020c29042001f013110001f013108001d85328e501d85328e401d85328e301d85328c401d85328c301d85328a301d85328a201d853288201d853288101d853286001d853284001d85308a301d813348301d81308e001d81308c001d81308a001d813088201d813088101d813088001d813086101d813086001d813084101d813084001d813082001cca614c201cca614c101cca614a101cca6048201cca6046201cca6046101cca6044101cca6044001cca6042001cc56042001cc39144001cc26146101cc26144001cc26046201cc26046101cc26044101cc260420 40 (i % 64)

def hull1 (i : Nat) : Nat := unpack 0x2705350c0027053110302705310e3027013510302701350e202701350c10270131120027013110002701310c002701310a202701310a102701310a0027013108102644c048102644c046002584c046102584c0440024d4c14a0024d4c1481024d4c1460024c4c1461024c4c1440024c4c0862024c4c0841024c4c0481024c4c0462024c4c0461024c4c0460024c4c0441024c4c0440024c4c0420024c2c04400230533cc1023013110002301310800224533d050224533d040224533ce40224533ce30224533ce20224533cc30224533cc20224533cc10224533ca20224533ca10224533ca00224533c810224533c800224533c600224530cc30224133c6002241334820224130c810224130c800224130c610224130c600224130c410224130c2002185328c302185328c202185328a202185328a102185328800218390420 40 (i % 64)

def hull2 (i : Nat) : Nat := unpack 0x34cf91481034cf91460034cf91440034ca614c3034ca614c2034ca614a2034ca614a1034ca61482034ca61481034ca61480034ca6146002e4760c8002d853290402d85328e402d85328c402d85328c302d85328a302d85328a202d853288202d853288102d853288002d853286002d853284002d839082002d813286102d813284002d813084002cd1604c302cd16048202cd16046202cd16044102cca614c502cca614a402cca6148302cca6146202cca6144102cca6142002cca604c502cca604a402cca6048302cca6046202cca6044102cca6042002cc56046202cc56044102cc56042002cc2604e002cc2604c002cc2604a102cc2604a002cc26048002cc26046202cc26046002cc26044102cc26044002cc2604200270535145027053512402705351230270535103027053510202705350e202705350e102705350c1 40 (i % 64)

def hull3 (i : Nat) : Nat := unpack 0x364a63ca10364a614810364760ce20364760ce10364760cc10364760cc00364760ca003644c0c8103644c0c6103644c0c400364263c6003642620e003642620c003642620a003642620600364260d010364260ce20364260ce10364260cc10364260ca10364260ca00364260c810364260c800364260c610364260c600364260c4003642604200358f928810358f9286103588928a2035889284003588908a00358890880035889086003584c088103584c086103584c0840035839288203583928810358392861035839286003583928400358391c4003583908c103583908a103583908a0035839088203583908810358390880035839086203583908610358390860035839084103583908400358390820035839046103583904410358390440035839042003581908410358190820034cf914a3034cf914a2034cf91482 40 (i % 64)

def hull4 (i : Nat) : Nat := unpack 0x40cd90462040cd90461040cd90460040cd90441040cd90440040cd90420040c590441040c590420040c3904c1040c3904c0040c3904a1040c3904a0040c390481040c390480040c390462040c390461040c390460040c390441040c390440040c39042003b07610e103b07610e003b07610c103b07610c003b07610a003b02650c003b02610a003a54c3ca203a49c0c8103a49c0c6003a44c3c4003994c286103989c284003989c08a003989c088003984c288103984c286003984c284003984c1c4003984c08c103984c08a103984c088203984c088103984c088003984c086203984c086103984c086003984c084103984c084003984c082003984c044103984c042003981c0820038d4c1460038ca614e3038ca614c20370f951240370f951230370f951030370f951020370f950e20364a63ce40364a63cc30364a63cc2 40 (i % 64)

def hull5 (i : Nat) : Nat := unpack 0x4ccec04410470a651240470a651020464763ca004590908c504590908a4045909088304588908e004588908c504588908c304588908c004588908a204588908a0045889088304588908810458890880045889086204588908600458890840045839090104583908e104583908c104583908c004583908a104583908a0045839088204583908800458390861045839086004583908400424533d040424533ce40424533ce30424533ce20424533cc30424533cc20424533cc10424533cc00424533ca30424533ca20424533ca10424533c810424130c400418f928c30418f928a30418f9288204188908a00418890881041889088004188908610418890860041889084004185328c304185328c2040cf90462040cf90441040cf90420040cd904c2040cd904a4040cd904a2040cd90483040cd90482040cd90481040cd90480 40 (i % 64)

def hull6 (i : Nat) : Nat := unpack 0x570535166057053516505705351450570535144057053514305705351240570535123057053512205705351030570535102057053510105705350e205705350e105705350e00570135123057013510205701350e105594c288205589c088005589c086105589c086005589c0840054cec04a2054cec0483054cec0482054cec0481054cec0462054cec0461054cec0441054c4c04c1054c4c04c0054c4c04a1054c4c04a0054c4c0481054c4c0480054c4c0462054c4c0461054c4c0460054c4c0441054c4c042004f03910c104e49c3c8004e44c3ca104e44c3c8104e44c3c8004e44c3c6004e44c148004e44c0ca104e44c0c8104e44c0c8004e44c0c6104e44c0c6004e41c0c4004d94c28a204d8f928c204d89c08a004d89c088004d89c086104d89c084004d889086004cd4c14a104ccf914e204ccf914c104ccec0462 40 (i % 64)

def hull7 (i : Nat) : Nat := unpack 0x308089144030808914203080890482308089046130808904413080890440308089042030807614a130807614a0308076148130807614803080761461308076146030807614413080761440308076142030807604803080760461308076046005f089510105f08950e105f08950e005f08950c005f08910c005e44c0ce105e44c0cc105e44c0cc005e44c0ca205e44c0ca105e44c0c8205e44c0c8105e44c0c8005e44c046105d8f928e205d89c08c005b076510105b076510005b07650e105b07650e005b07650c005b07610c005b026510105b02650e005995c088305989c08c005989c08a205989c08a005989c088305989c088105989c088005984c08e105984c08c105984c08c005984c08a105984c08a005984c088305984c088205984c088005984c086105984c086005984c084005984c0462058ca61503058ca614e2 40 (i % 64)

def hull8 (i : Nat) : Nat := unpack 0x30a450206030a450204030a450202030a41040a330a410408330a410408230a410406230a41020403099092c413099090441309909042030989c146030989c144130989c144030989c04413098891481309889148030988914623098891461309889146030988914413098891440309889142030988904623098890441309889044030988904203098501ce03098501cc13098501cc03098501ca13098501ca03098501c813098501c803098501c613098501c603098501c4030981034833098102cc53098102cc33098102ca43098102ca23098102c833098102c823098102c623098102c613098102c413098102c203098101ca43098101c823098101c813098101c623098101c603098101c413098101c203081090441308109042030809c144030809c044030809c042030808914a0308089148030808914603080891441 40 (i % 64)

def hull9 (i : Nat) : Nat := unpack 0x30e41040a130e410408230e410408130e410406130e410406030e410404030e41020c430e410208130e410206130e410206030e410204030e410202030d9092c6230d9092c4130d909046230d909044130d909042030d88914a130d889148130d889148030d889146230d889146130d889146030d889144130d889144030d889142030d889046230d889046130d889044130d889044030d889042030d8102ca230c109048230c109046130c109046030c109044030c109042030c09c148030c08914c130c08914c030c08914a130c08914a030c089148030c089146130c089146030c089144130c089144030c089142030c089084030c089048230c089048130c089046130c089046030c089044130c089044030c089042030c079142030b05024e030b05024c030b05024a030b010248130a45020c030a45020a030a4502080 40 (i % 64)

def hull10 (i : Nat) : Nat := unpack 0x31301024a231255c046131249c14a031249c148031249c048231249c048131249c046031189c14a131189c14a031189c148131189c148031189c146231189c146131189c146031189c144131189c144031189c046231189c046131189c044131189c044031015c048031015c046131015c046031015c044031009c14c031009c14a131009c14a031009c148131009c148031009c146131009c146031009c144131009c144031009c142031009c048231009c048131009c046131009c046031009c044131009c044031009c042030f05024e030f05024c030f05024a030f0104c8330f01040e430f01040c330f01040c230f01040a230f01040a130f010248130e45020c130e45020a130e45020a030e450208130e450208030e450206030e41040e530e41040e430e41040c430e41040c330e41040c230e41040a330e41040a2 40 (i % 64)

def hull11 (i : Nat) : Nat := unpack 0x33410904613341090441334109044033410904203340b604c33340b604c23340b604a33340b604a23340b604823340b604813340b604623340b604613340b604413340b604403298501c203298102ce43298102cc43298102cc33298102ca43298102ca33298102c833298102c823298102c813298102c623298102c613298102c413298102c403298101c823298101c6132811614a33281161462328089144032807614a0328076148232807614813280761480328076146132807614603280761441328076144032807614203164b604823164b6046131590904413159090420315889042031305025213130502501313050250031305024e131305024e031305024c031305024a03130105546313010552531301055243130105504313010550331301054e331301054e231301054c231301054c1313010250431301024e4 40 (i % 64)

def hull12 (i : Nat) : Nat := unpack 0x336426208033642620403364260c4033641620603359092ca43359092c833359092c623359092c4133590904623359090441335909042033589c1c8133589c1c613358892c623358892c4133588928203358891cc03358891ca13358891ca03358891c813358891c803358891c613358891c603358891c413358891c4033588914a1335889144033588908a03358890881335889088033588908613358890860335889084133588908403358890820335889044133588904203358391ca33358391ca13358391c813358391c803358391c613358391c603358391c403358390841335839082033583904203358192c413358192c203358191c413358191c2033581908203358102c623358102c413341091462334109144133410904c433410904c333410904a433410904a333410904a2334109048333410904823341090462 40 (i % 64)

def hull13 (i : Nat) : Nat := unpack 0x33989c1c4033989c144033989c088033989c086133989c086033989c084033989c044133989c042033984c1c8133984c1c6033984c1c4033984c086233984c084133984c042033981c1c2033981c08203398102c623398102c4133815c146233815c144133815c04a433815c048333815c046233815c046133815c04413380b604c33380b604a23380b6048133710954c23370264c833370164c623364b640e53364b640c43364b640c33364b640a33364b640a23364b6408133649c208133649c2061336476210133647620e233647620e133647620e033647620c133647620c033647620a133647620a0336476208133647620803364762061336476206033647620403364760c803364760c40336426210033642620e333642620e233642620e033642620c333642620c233642620c033642620a233642620a13364262081 40 (i % 64)

def hull14 (i : Nat) : Nat := unpack 0x3440b604a23440b6048133e450202033e41040e533e41040e433e41040e333e41040e233e41040c433e41040c333e41040c233e41040c133e41040a333e41040a233e41040a133e410408233e410408133e410406233e410406133d9092ca333d9092c6133d909046133d909044033d8102ca333c10904a333c109048233c109046133c0d914a233c08914a033c089148133c089148033c089146133c089146033c089144133c089144033c089142033b07610a033b026250033b02624e133b02624e033b02624c133b02624c033b02624a133b02624a033a55c408233a44c086233a44c086133a44c084133a44c044133a44c042033a41c084133a41c084033a41c082033995c2c8333995c2c6233995c2c4133994c1c8133993c1c8033989c1ca133989c1ca033989c1c8233989c1c8133989c1c8033989c1c6133989c1c60 40 (i % 64)

def hull15 (i : Nat) : Nat := unpack 0x35301054e135301054c235301054c135195c2c6135015c046135009c14a235009c14a135009c148135009c148035009c146135009c146035009c144135009c144035009c142034f08924c134f08924a134f08924a034f03924c134f03924c034f03924a134e55c40c334e55c40a234e49c20c034e49c20a134e49c20a034e49c208234e49c208134e49c208034e49c206134e49c206034e49c204034e49c148034e44c206134e44c206034e41c204034d95c2c8234d9092ca234d8391c8034c15c048134c10904c234c10904c134c10904a13464b640e53464b640c43464b640a33464763c203459092c623458891d013458891ce13458891ce03458891cc13458891cc03458891ca03458891c813458891c803458891c6034588908a0345889088034588908613458391c6134410904c434410904a334410904833441090462 40 (i % 64)

def hull16 (i : Nat) : Nat := unpack 0x6040b328816040b328806040b328626040b328616040b328606040b328416040b328406040b32820604083286160408328406040732861604073284060407308816040730880604073086260407308616040730860604073084035f03954e135e49c20e035e49c20c135e49c20a235e49c20a135e49c20a035e49c208235e49c0c8135e49c046135e44c20e035e44c20c035e44c20a235e44c20a135d9092cc235b026550235b02654e135b02654c035989c1cc135989c1cc035989c1ca035989c1c8135989c1c8035989c1c6035989c08a035989c088035989c086135989c046235984c1cc035984c1ca035815c048335815c04623580b604c2353020550435302054e335302054c235301055463530105545353010552535301055243530105523353010550435301055033530105502353010550135301054e335301054e2 40 (i % 64)

def hull17 (i : Nat) : Nat := unpack 0x60e4a034c060e4a034a060e4a0348060e4a0346060e45034c460e45034a360e420450760e42044e660e42044c560e42044a460e42040a460e420408360e420350760e42034e660e42034c560e42034c160e42034c060e42034a460e42034a060e420348360e420346260e420344160e410342060c0d928a160c0d9288160c0d9286160c0d9286060c0d9284160c0d9284060c0d9282060a4a034c160a4a034c060a4a034a06064ec08416064ec08206064b334806064b328806064b3286060647334a4604ca02cc2604ca02cc1604ca02cc0604ca02ca2604ca02ca1604ca02ca0604ca02c82604ca02c81604ca02c80604ca02c61604ca02c60604ca02c41604ca02c40604ca02c20604c302c60604c202c81604c202c61604c202c60604c202c406040b328a46040b328a36040b328a26040b328a16040b328836040b32882 40 (i % 64)

def hull18 (i : Nat) : Nat := unpack 0x620cd92c816200d928816200d928616200d928606200d928406200d928206200d908606200d908406140b328c56140b328c46140b328c36140b328c26140b328a36140b328a26140b328836140b328826140b328816140b328806140b328626140b328616140b328606140b328416140b328406140b328206130a038e06130a038c061305038e461305038c461305038c261305038a2613020594761302058e461302058c361302058c261302039266130203906613020390561302038e561302038e461302038e361302038c461302038c361302038c261302038a361302038a2613020388161301038826124ec08626124ec08416124ec04416124ec04206100ec28a06100ec28816100ec28806100ec28616100ec28416100ec28406100ec282061009c148261009c146160f0204c8360f0104c6260e4a034e060e4a034c1 40 (i % 64)

def hull19 (i : Nat) : Nat := unpack 0x64f08938c064f03938c064e4ec34c564e4ec34a464e4ec348364e4ec348064e4ec346264e4ec208064e44c346264e44c344164e44c0c6264e44c0c4164e44c084164e44c044164e44c042064e41c344164e41c0c4164e41c082064241344a36424134482640cd92ca2640cd92c81640cd92c61640cd92c4063e42044e563e42044c463e42044a463e42044a363e42034a463e42034a363e420348363e420348263c0d9286063c0d9284063c0d9282063c089146263c089146163c089144162701338c362701338c162701338a362701338a26270133882627013388162644c046262644c04416240ec28616240ec28406240ec28206240ec08406230134c836230134c6262242c042062241334e362241334c562241334c262241334a46224133483622413346262241334416224130c826224130c626224130c416224130841 40 (i % 64)

def hull20 (i : Nat) : Nat := unpack 0x904cf04061904cf04060904cf04041904cf04040904cf04020904ca04060904c404040904c304061904c304040904c304020904c204082904c204061904c204041904c204040904c2040209041163c419041163c209041033ca49041033ca39041033c839041033c829041033c809041033c629041033c619041033c609041033c419041033c409041033c209040b33c209040933c419040933c209040833c419040833c209040830c819040733c4165e4ec350365e4ec34e265e4ec34e165e4ec34c165e4ec34c065e4ec34a065e44c34c0657013590465701358e365701358c265701358c165701338a16530205926653020592565302059056530205904653020590365302058e365302058e265302058c265302058c165302058a06500ec28606500ec28406500ec282065009c148265009c146164f0d938e164f0d938c0 40 (i % 64)

def hull21 (i : Nat) : Nat := unpack 0x9130104c8391193c448291193c446191189c148291013c3c6291013c3c4191013c3c2091009c146291009c1441909930448190993044609098f044e29098f044c29098f044c19098f044a29098f044a19098f044a09098f044819098f044809098f044609098f044409098f040a29098f0408190989c1461909830448190983044809098304460908d1640a3908d164082908d164041908cf04081908cf040609081163c629081163c619081163c419081163c409081163c209080761462908076144190590344a290590344a1905903448190590344809059034461905903446090590344409059033c819059033c619059033c609059033c4090590308609058830840904d164061904d164041904d164020904cf040c3904cf040c2904cf040a3904cf040a2904cf040a1904cf04082904cf04081904cf04080904cf04062 40 (i % 64)

def hull22 (i : Nat) : Nat := unpack 0x9281163c629281163c419281163c209271034ce19271034cc19270834cc59270834ca4924d3c4062924d3c404192413c3c4192413c3c2092413c0c2091d933448191d933446091cd16406191cd16404191cd16404091c1163c6291c1163c4191c1163c2091c1160c20914cf04061914cf04041914cf04040914cf040209141033cc59141033cc49141033ca49141033ca39141033c839141033c829141033c629141033c619141033c419141033c409141033c209130f04d029130f04d019130f04d009130f04ce69130f04ce19130f04ce09130f04cc59130f04cc19130f04cc09130f04ca19130f04ca09130305d289130305d079130305ce69130305cc59130305cc49130305ca49130305ca39130304d079130304ce69130304ce59130304cc59130304cc49130304ca49130304ca39130304c839130204ca49130104ca4 40 (i % 64)

def hull23 (i : Nat) : Nat := unpack 0x95993c44a195984c44a1954d3c4082954d3c40619530305d279530305d069530305d059530305ce59530305ce49530305cc49530305cc39530305ca39530304cc59530304cc49530304ca49530105cc39530104ca393b1164ce193b1164cc193b1164cc093b0d64cc593b0d64ca493b0264ca493b0164c8393993c44c393993c44a293993c44a193993c448293993c448193993c448093993c446193993c446092cd1640c392cd16408292cd16408192cd16406192cd16406092cd16404092ccf0408292ccf0406292ccf0404192cc2040419281163cc49281163ca39281163c82 40 (i % 64)

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def hull (i : Nat) : Nat := (if Nat.blt i 768 then (if Nat.blt i 384 then (if Nat.blt i 192 then (if Nat.blt i 64 then hull0 i else (if Nat.blt i 128 then hull1 i else hull2 i)) else (if Nat.blt i 256 then hull3 i else (if Nat.blt i 320 then hull4 i else hull5 i))) else (if Nat.blt i 576 then (if Nat.blt i 448 then hull6 i else (if Nat.blt i 512 then hull7 i else hull8 i)) else (if Nat.blt i 640 then hull9 i else (if Nat.blt i 704 then hull10 i else hull11 i)))) else (if Nat.blt i 1152 then (if Nat.blt i 960 then (if Nat.blt i 832 then hull12 i else (if Nat.blt i 896 then hull13 i else hull14 i)) else (if Nat.blt i 1024 then hull15 i else (if Nat.blt i 1088 then hull16 i else hull17 i))) else (if Nat.blt i 1344 then (if Nat.blt i 1216 then hull18 i else (if Nat.blt i 1280 then hull19 i else hull20 i)) else (if Nat.blt i 1408 then hull21 i else (if Nat.blt i 1472 then hull22 i else hull23 i)))))

end Rep9102.Final9102

open WordEngine PEqualNP.Represents

namespace Rep9102.Final9102

open Orbit Project

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def hashToken (v : Nat) : Nat :=
  let a := ((v ^^^ (v >>> 16))*2246822507) % 4294967296
  let b := ((a ^^^ (a >>> 13))*3266489909) % 4294967296
  b ^^^ (b >>> 16)
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def getLocal (data bits off span salt tok : Nat) : Nat :=
  let h := hashToken (tok+40503*salt)
  (unpack data bits (off+(h % 1024) % span)) ^^^
    (unpack data bits (off+span+(h/1024 % 1024) % span)) ^^^
    (unpack data bits (off+2*span+(h/1048576 % 1024) % span))

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def bankPage (headerData raw : Nat) (i : Nat) : Option RowState :=
  let z := unpack headerData 16 (i % 16)
  some (z % 16, (List.range ((z/16) % 16)).map fun j => words (unpack raw 8 (z/256+j)), [])
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def actionPage (header data bits tiny hulls deps i tok : Nat) : Nat :=
  let m := unpack header 64 (i % 16)
  let mCount := (m>>>26) % 16
  let hCount := (m>>>30) % 32
  let x := getLocal data bits (m % 4096) ((m>>>12) % 128) ((m>>>19) % 128) tok
  if x < mCount then 2*unpack tiny 4 ((m>>>35) % 256+x)
  else if x < mCount+hCount then 2*(16+unpack hulls 11 ((m>>>43) % 512+x-mCount))
  else 1+2*unpack deps 19 ((m>>>52) % 1024+x-mCount-hCount)

def as0 := bankPage 0x97ac8dac82bc77bc6dac62bc58ac4eac44ac3b9c338c28bd1dbd13ad0a9d00ae 0xa98b5a4136291b100800a98b5a41362e291b1000a98b5a412e281b11100908a98b5a42412e281b100908a98b5a412e291b100908a98b5a42412f2e281b1008a98b5a412e2a291b1008a98b5a412f2e291b1008a98b5a43412e291b1008a98b5a4136291b1008a98b5a4136291b10a98b5a412e281b10090800a98b5a412f2e281b100800a98b5a412e291b100800a98b5a412e291b1008a98b5a412e281b100800
def ac0 := actionPage 0x24103d78280328ca21f03d202c03482e20501cb13803c77a1ec00c38bc03e6c01c400bc83803162d1ab003687004056d17d002f8380354ce155002a02c034432131002482c03539310f00200240263210ed001b82401c2cd0be001403c0ba21f08f000e82c03e165063000982802d0de03700050240220780000000028028000 0xcf80006c02c003d10a0000026187078000fcd833608e820e0002b3e680002e3028000b8895224000426ec799583cc80160c600365c00d1800698027c02408d470c0001e806c0c91862700290e2c011005841e160172404480006800dba64683001e20b0b000001a0050e0f542c9806e00a9a0020518002523e1224000789c000008d7800600000165d1021ae058a0045e09123801d00900000a5020204300120009400121578016b4b801e740001a0158c12edc0e32a40250024000380048000000861855c80008868d50146001c9460e365000b5c1c000000039f120148c22101803a19b800000c8026645000001e81348870058380284c20d8020002801e70426323800036000065281480000958000016870090eab0028d86362402f6800b912e08f82620003000ddf060c00600000048d00347261a342020e0108c16897af1ec802d687401210000b916000255ca00003210dbc164db8400005803c1800d5a100004e1462d00017a906a55000001b0000a5c302c000051600601007400c16143a656597a4680001e5494a1a0021d891e044821c0000b6c0cb2608003003c000160055d8100296805a0c1805c9149400480027c9468456a400b2c000004814001421002a1604180003419a52001804a2910c069018d00106000024000260c125182450000016832200c8158000001e0c0001a247806e940364e0070f00791b60038b0e7400024004812b1801086143d500720c03800017ad181023f060c00000014803481403500132060140003a216b54a0108002001800628009180048f18002803618985080050a001c98420a80001e182800079a803c0013f1e600001e18aaa0001f8a008400e1cc40144eb468008000005400dbc26f17bb08f858066d00201c9438036f1528000000554a80000091f803eb80045200c87000028072844800cc800038e90a064ad20000612a2022420018e0229009468c0400d274a7d0a01a0003530506251ec020018c591414240020020a80000001c581c0050000009000078518000052874380540002a2a24888008840b4c446a7141c02200002802a00003185519b00500001228703004c00e2c18012006858b0034eaa001d89716c001100000040030397280c400642d2800c482890200d8040406002a59a0046481a03e702800c006aa2c64a80000438c007da8d083400c00002800c1c801209801e0230d0300606ad0a580053e2c5001e00022009400000ac00000159000e54403125c0000e000004400480029400000059b6380038000304377201c007e845803e09f3c66005bd5645d2a5c1c00000f81a4000c50300740800001d3800300000460c2d4200a8000fda361a0c08000005224e890000035a8974f898038e12b30010db0024c20d200d082540128c72547802e0023c003810c1c0810000c81037eb4005000000f5458d8f6a01a940000401002c1806a0048218c0000000000000383ab2cb8700320000408c82b80025e2f5085a2b7800400422c80500001004ce9d80608521500b122c20848031ec4018744c00052a013b0001ba2000000046018211cd1aa500005381c38025780552c0ed802b0acc3003c0000074011b340440396e10e8150bc68000d850e00005140000016061862500a41bb0074b386400000004953a6e281824e010000c2590e00d4c19000400020315ac00000856800739009d90000002110a1c1246624080003dd8010e4000000c0006e083000a0118e040000f0018a8d7cb00a21a24a8f0e4003b4268480000000000c479b0874a81009dfb904c002b4649b13443803f0658109021c000606cd19006cab100fc98000001bf26f800000f4026007d513182d08000005bf2c0178f1a1000028004971ca8800502000e7a4cf0678001981278f803c000372631e8a00005210000f182cbc3a1004db812c2cb0f00100277a140154afc0201aa052d00609242c5002c580003f4e2400d00009802c1c0052c113b92ec80000061a171e480074e708006a3838a00d409334bc4050000380464800010448000600eac1a58433000179c3e01e000651e8000015bd680021b001d08400380381c4c500029000000085364e1802500000244a0d580005c483000418700ada0550e470a4ab888072342121cf000e5800d023a444b2001980400a8023000051d4c3400060c149200900010014d800e01f0d388ca1e00b0000740169000a9c9c000402b48d468032e40017401b917814f327838000000018030ec91f5e0050030e820e0051b802674f802ae96280a492800a00084546c00000ac4b10e00c9646001010200000560003e00a110008000330afd51c4c14a2f00cc6005a5401a12dc4027ea47953ae00000081789000110f1000f0d7ac800246100b40004000000000002080003c016bd00a879b1a0c68600b08ac3c01a8e000063700b098f5601a0212a982700d878d12311003eec200620002d08b4b003c4c013060138700080302c00c0072d8024002168000cdebb24b800a3c00031026d6800018000000100000bdb276e0179f42ac03408f5f00047d635002c0005e00e834470005005c0277000d1c6e145ab00a5d000a1c6a000ddd045ef801a00c000002015006e8cc1d7225995148c0005a242125c0570066001ad3e2800068440231c013290a7930342acf8b2c05bb830cc0224aec0003898e94040db00004980c004503a26e972904018bf00000214a980ad320c0066c0000c42a0600006c01134014150001b803a25c134201c03780193f18000173098b0000049874c011803c00003000002976f4e8036006be00d80407a19b806a00e28780c0002c001c5622af8000401a307b0200023c000629c8007e092877201bfa0178d0040c400000fc038124c0927201e775800f917df983a4a007806851d000c0085753d880056d80008001c3300e007500cc5a2 7 0xedcba43210edcba843210edcba987653210edcba9876543210edcba876543210edcba8743210edcba876543210edcba843210edcba743210dcba43210dcba43210edcba9876543210edcba843210edcba43210dcba43210edcba43210 0x170ad2da437d2ca582da 0xba1fd5c3faa87f5e0e4b01c9583905067080ce0c19c103381067000ce0c198103300066060c2081840030a4051460a2861444828880510c0a2900f5181ea183d1207a200f4301e9d034380686a0d00013bf87d7b0faf21f5743eab87d550fa921851c30a2061120c220184303085060080c00c180103001060000c0921311c262204c120982013030262482f4705e880bc48178802f0c05e740b8e0171a82e0004400178082e8005d020b800170082d8005b0e0941812808250004a0e092181240824800490e05a180b408168002d0e058180b008160002c0c056000ac001301058000b00415c002b81056000ac04154002a81050000a00413c00278004e12092201240823800470208c00118c4161782c02054000a8001496028060b408168002d04059020b200164182a02054000a81414c202983053040a60414c002984052020a400148182882051000a20c13010260004c060960812c0025830480409000120181c0203800070620acbc159602b06050080a0001400027580d2ac1a52434a3869540d0a41a0e82f9c05f580acac159242b238561e08c381184823080460e08a181140822800453606c5a0d910149d02338046ba1e15c3c2a8785e0ecb01d9583b24062460c4861892026a304d4309a0c110102200044060860810c002185042080840c108102101042000840c1041020800410606e080dc001b8303304066000cc181902032000640c0c410188003106060080c00018030250404a0009400122f079580f2ac1e5743bab877550ee9218d1c31a20634909c8e1391027030400408000100181f8203f0007e140f8201f0303e0407c040f8001f0303d0407a000f4481c080380c0700c0d8101b000360605e080bc0017800223a04070080d410318755d0eaf6191e43235064680c8f613de427b504f6809e3e108742109042100841e0ec341d8103b00076000e8081c800390006e3e0d4741a890351006a1a0940012878230d0460408c001186820000402407c400fae873570e6aa1cd7838ac071560e29012d1825a184b12082201043020850350806a0c0d4101a810350006a0c0d0101a0003413062220c434188302e0405c000b80012030200404000080480f0801e0c03cbc1c174382c070570e0ac1c1543824830480608e0c118182203043060260c0481808830100601a0c03018000210903e1007c0c0f8101f0103e0007c1c0f0301e0503c08078040f0001e0603a08074000e8301c0403800070200d8101b000360c068100d0001a0a03210064180c820190203200064200c01018000300c05c100b800170602c08058000b030150402a00054180a02014000280c0441008800113101a5e034b0068300d0401a00034c4061780c2c0180c03010060000c2c0160002dfc0cbd81979032ba0655c0caa819320266004cb40983013040260004c2809040120602408048080900012490228e04510088901110022180455008290104f02074040e0081a810490188e03110060900c1001818030c8051800a2d0140c02810050000a2d01000020e8039c0073500eba05d5c0baa8174802e8c05d0c0baf0165802cac059240b238164402c4404080080f0101c020340406008090101002018040180802010000202403c40078600f0001e2403840070600e0001c2402c40058600b00016240204004060080001074018e0031a8062c00cbc055740aac0155702aac055540aa48154802a8e055180aa20154302a26024480488809100121a024300480809000124201c80038d8071a00e3201c6003838070600e0a01c1003808070000e260184803088061000c1a0183003008060000c240144002860050000abc01174022c00457008ac011540224804480088e0111802220044300826010480208804100081a01030020080400008bc00d7401ac00357006ac00d5401a4803480068e00d1801a2003430062600c480188803100061a00c3001808030000676008e8011c802380046c008d401168022c0040200800011d001380026a004b00080001
def as1 := bankPage 0xa49b9c8b957b89cc7dcc71cc65cc59cc4ebc43bc39ac2ebc22cc16cc0bbc00bc 0xa98b5f5a4136291b10a98b5a4536291b10a98b5a4536291ba98b5a412e281b1510090800a98b5a412e28261b10090800a98b5a44412e281b10090800a98b5f5a412e281b10090800a98b7b5a412e281b10090800a98b5a452e281b10090800a98b5a45412e281b090800a98b5a452e281b090800a98b5a412e281b15100800a98b5a413b2f2e281b100800a98b5f5a412f2e281b100800a98b5a44412e281b100800a98b5a43412e291b100800
def ac1 := actionPage 0x1271b5882c02c7ec10e1b5402401f78f0f51b4f82401674d0f017c91f401b6fc0de13c22380286840d9113d96401d62d0cb0d36a3802b5ac0bc0a2f9b802953109f08a80fc04146e08307208fc0433a505f071983803230f04806130b40b9264043040e92401e20a035018916c02d18301c008589c03b0d2000000006c046000 0x39b22223f03c0a1d590010c3000001358000fc004c000057f000215000e9e400a12151000360392dd9440240f882b102bc4700b68000801030a80d015540034ac07c07c041e6c0c1197f687abb62289d0197440007eb4000140d8280f7607032f0177891d37da00738c00070009701a0005c07d67db01e08754019e01c100000d957c400b6407934990146c009bd5b7820c00222430d3299680000000d020447004d1080592000782245580000380792c00708000018000b0f1cd278652ad14406c000150f00001260a03204b01f0196471c900c68475078048c2000070c23400106ca00701a4c00165c600b01120250201e00a00101a04050654635f41600054e01900730051a5d26c000d15900a1806000096cf0100001750d8480f4028d68064b2d003b20001409a01b280021f0001faea01da1500e02586100d6c06da70500d0336800014f60007800717003ca840dc001c7400168df10901e0247907dcfc06c62d7f001a430b02800004e00070e00a00700024800c0002803400002c934030008020f00028a28000001c1ce3c320c0c03402cb2c038e04218028000c2887cf00400d00610d38b1df3001c91071cf01d01e3800070173030a70c00160003190050400060199c03db65102299cf800bd00b0243053bf80e40001238002054095400041f36a7d103c00708149402c50b0df39d00001e000000f1d6f06088ff5d8fcc340105c9344074be545f12850001009c01b601000600402f14fa50ce41000000003a70002a8f055d63e105137a3400783910040006937401c6000017840000b564005b700071400a08079500a669553008034f3f0750139152161c0187c007b370401d0070c5a9b0147f901c3800444472c01cb73903f03dac30003bb94001500308a01568925f18103c044948dc008402bccd0072f564000000048000210c0c908000afc00000141c236910a0000094265806f000001f03d08457c0af3854c8a009e70030000006dc2434b80060104965af540d32024002b604ca7801408890000ca2658d60401000ab37a50a01210b100ac10991cd080d003c020400d587480d470c70e1037458b0700030078c4400000040005e154078000788002801d36c64e378004000c40980a94cc0795fc0cbe5990c27d0000cc02bc7c4015101c9bd8000474785efbc1e60ea3c10398401c1240007000880be300bc6cb595c06fc0eb00094419a0001403c702b0009146274875000077d2bc90000005a595144d13dd80700000b00e870006dcb1d880782bc448cf40c8539720002000012b000000b7a4b7c8c42c300d9500568ba23bae11759dde55030370402521250144405400073c03be2e63803c0e177963f0240000b008c066500001602696af7b5b540a7fc0040000085ad4770000d6202000df41d7d81349035c8a4000c066825f3ac88000002b840978d820140120800010260104fdb0e01db4002a800880db138866724b03828001ae4b0c20c30fd1c000101e00001801142828e8ae36780c64b000d0078136b0001845c0bc31280087d221409efd10804c003600010e9c819e76501501a000ac00c05183d63802a548064c01a00000974003500a4014b14d20d84003d800b00080b00444c00030b00800031100a05700400c30c14258040000800010000620028c01015b08629300910e6400000c50031075cf00324d0833ce00020074020008131d08d70038a24000f41b40419819d0020031007d47800003c10060082000051c42452402400090c535000c0002c53c22803860000020071c00021000131ce00e18000801a39829a00000b7081cb2c41802070100092c408500c00024100a1022c01dd0000023893da1540001ba7557cd0ae5c15db12b40000801a00c5402a200369600452410320005d5ce03a50000e021080000900240284780013000411f8900015328003d0141c01400197c0000000a6630088b1406fb5400110870001c00141a00950073093450143233c66a1e3bd00118016aa5f420000f9004582c000c05018401db21f1010f2b830450120ca00002500040007601502d41f30d02f4a20005e554000528a004000a0002b18e60b34000c02201c5e2e401ac4442400035490397c0b460216970e330014044628a47222b28a500026600a02100000dc06079804406c0c4083d4c364200071800b7a202400310a1001003d30283030610000040390002403417199be00003288320a1dd1d90ca1fb8402009803223c3a400f70001592c000e04d503004 6 0xedcba643210dcba43210dcba43210edc9876543210edcb9876543210edc743210edcb9876543210edcb9876543210edcba9876543210edcba9876543210edba9876543210edc9876543210edc843210edcb8643210edc7430edcba743210 0x2d24b796b2d259cb212369a8e4b77a06fcdf1a12d92ce594b1960242d25a2a392cde699f2d423a5b4b3960684cf88eb4b690df5a3b442c8488905bab716dada5bab6d6d19f11c240474b0 0x43975832eb0e5560caaa6900482002e4004880218f70c1ee002a8b050000a00513e0027c2c4e8309d69126ca24c74498c09305112002241443800870610cbc60574c02b9355526a903fd187f890ff101fe923b11c76098ec111d8002a4084e8009d0213800270084880091431161822c0843800870610a0821578bfae97f581d6ae3ad5875aa8eb491d6903ad1c75a30eb131d6243ac4475880eb43114182280045008860010c062140842808850010a0421000420108200104001f0b02d0005a0010200202142f4085e310bc0c179642caa8592c0b2001650c251f84a3d094181291816a182d1005a180b4083f0007e000f658150002a02079000ee0c1d40035820692f0ac08158b029800534309218124f423a182c0c0580020c183a0006a5a0aeac15cb02b800572f0aa58154102a800555a0a4ac148b0290005208102041fc003f8107d000fa001f0083b80077060e6081cc18378206f060d8081b0c42e9785d060ba081755c2caa859310b05e160182c020582c0a200144d4242182b0c0560c1f4103e8007b020f2001e4083900072060e2081c418370206e060ca0819400319885c2f0b80c170102e2c052560a462140bc2803050040a05813800271604c000980c208104104080060fc081f8003d01078000f0041d8003b01075000ea001d0083980073020e2001c4083800070060da081b4183202064000c46216cbc2d8305b040b66213cbc278304f0409e5813400269604b00096041bc00378106e000dc041b400368106b000d67c128f4251884a2f0940c12810251a8482c09000120f8239e8473108e5e11c182382047000805a0fcd41e1d03b38076181a9d023238463d08c181191022880457d07caa0f8c01f0003e3a0728e0a830150106c000d80c1ac10358106a000d4041a4003481065000ca04190003200063580aeac15cc424978490609208124c423178460608c08118b01c000386a0d8d01b0083400068120ce2019dec32bc865120c020180082f8005f6a0b0d01604829880537b0a0f2140481f0803e4307a000f0001c060363a06a700d53c1780028
def as2 := bankPage 0x93ab8a9b7fbb74bb6aab5fbb55ab4bab429b38ab2eab259b1bab129b099b009b 0xa98b5a45412f2e291b08a98b5a454136291b08a98b5a412e28201b111009a98b5c5a412e281b111009a98b5a4136281b111009a98b5c5a42412e281b1009a98b5a43422e281b1009a98b5a43412e291b1009a98b5a4136291b1009a98b5a412e281b141109a98b5a43412e2a291b10a98b5a41362a291b10a98b5c5a43412e291b10a98b5a41362f291b10a98b5a413e36291b10a98b5a434136291b10
def ac2 := actionPage 0x1560ed987003b77413d0ed482802c6f01370d500e40166ae1310bcb8e401666c11e09c413c0325d611806c01a001659410605b90b80334fb0f304b20b80334620d204ab8340283ea0bf022517402f35d0a5011e0b80b72b807e011783402c23406c00118b00b718f04b000c02c02b10e01e000583402e084000000002c02c000 0x7940010009d80f8001e0008c0000000752200b00b964d25bc02265820888078c01d5e4cdfc8a0004c0d05b8004062b640140016b005492c0dceedb7468520c04f2032a007c000b096017000e85000ac0c46dc00480004b318060b010bef805bcf0000b8b612711556ef2805af6db1002400004ac88d10c81247a02d286c9d00014030001824a7c490460e74000031b00001400e0106460051c015900000500015001b65684000301600034f40a70500018010280938a0155d2000340e1d8cc00021b0070df9c000824700d1060016d906558060901a01101da4045703c3c660994f0190805cc49854a34000c00030a1000c001200c1000077c000018504b0010003c00010460054480050086403c634400028d08c00e14b0c639a2da0000007d000058005a01500f3c075800700b7400c07850132dd01a0532806593480060006c105b08934901c00024003f0180005ba080a400000e68d741b37318e3965fe1ab00c9a1cc35543430cd53503a01f9f54008969d50001dce4539e0090220cc15d7d449d000000004182000031580fad3943805025bb640030d40a54008e004c00180000309c7514edaa40d0028400001b20ae0b0000100270d900034701000400c0032882c000010004d00800b5c72923405003c00090003ce30d1000120c64161810001401c90005843451c10167b50e800000003f9c0c40007000200142014ecc7fc000100a4d12f00a0c0015bab304107082507e00dc00000000cc05a0007c524c240900f870403801fa39e00400000d6836ce00a1730cb340244f4038429068a28a5403150cd00100ed5601000cc4c00c04502c24a035b0091e9c00f9100d1d0c03350002c000b24f0002c000800108060760c00000d00e72a1006812c00c0440100097e4d0d101e1c00000163013400091492415170004977c000003a0b40000803f800038001239f00cd0d2d30051c871329260154c73534e44438046e740018100156dc07401401004c835601d2770000137e4020b809c003c02a4c799c0872c0b510000000330eb86a3c095726c231003bc0ac5000a405a708002548c000c43038bec80f01c3400d683902dbf57c703f07d00112eac001c494031100893e00bc0bc3521c08300ce403700000000068001d018185f40300000024bc07872c001b251c0028834d307022000fcd28d0000000195053a3007263c987d70d80cca802821a1503c9e7420010143a72ce01c340c9241b03b0805401573052c01b80006d00000c0082000e80f582c42cc9be001f96f000003ce48800d1809c05c093a8c0033088b1d0005d60000096806401e38c50004180000006049c000b28000000253d4b501404700b099d2304b2e42b893043a08601ca46a0b00032a0180190003002ae00100c39b5806a86106690120046401f902d00c300880a450333631e600e00f75058014e563585c960fc980583cc7b0b3450009f9a3202f000f80c7e1c0000540c770005c06c02ff00000378354400903f1d56da2c0140e4005e9cadb6335c4bc800cd63924700900d022327a00ceed4902003b000680e6b0000032cc5e13b6000291180680100040ec7340ad820600005f0000001080176050032900832416420080001dc3471c061c00d00f60800211c1550010c600039f00000000001908201e5856ca00054b55045c00000008030100310028301d35a69d34000001705e00c00b00800054e0000c038a00665f31771e1c004004d0c908945e5822833093417802087c00573555d8005d40d020002f3940000002d3f4b44c051f00ae0073e53d0057400380070000005a00555f582f2790806c0386008940f3ef40400bd73001000040007c0c25015034f742c043a00578002260d5c9c15305b37644100358039c1a0003ba4c12801e1000a40a804220000154b101d002fef00000904248091ccd34cd5f74dc4c07f68fd019455000000039825f9695603d98b31a000840aeb9002ffc409c06d0000008cc0700b5eb0d016c761c3a82500280000ab6a8ccd2f508000009c0807fb6e0278b1a1c68d000341ec543ecc8091c05bcb1a3c803f00000c940027b4914000000db8014002f00858c044f150007c9a0f90e00034000edcc63e3e8000000bcb01b3c0020028b80029100258e4e00300f9805ae8500087fe99eba9b6f00018794c031000033165226200764 6 0xedcba8743210dcba743210edcb98210edcb86420edcba9876543210edcb7643edcba986543210edcba876543210edcba76543210edcba98765210edcba876543210edcba76543210edcba7643210edcba843210edcba76543210edcba743210 0x16c1a02f05d4cf1752e7706d1da213f2b254c2c78e7247a4af9590fe1e5ccb8368ed11bc8a714227439 0x492da8e5b524a5a394b58286ac50c188882111122202044018870210e021fa003f4007e278fa021d4003a93c60968ac3a124702498cc72e98e5826cac4d9209b231361f2243a4484889081121b21a3243418868210d021e8003d06c490c89206124082484848880910d118002300044000e92f1900032000622189010120003a00073000de0018e183190c47810e7001ce043900072010e3001c6043800070010da001b41c3203064010c60018c00314085e800bd02178002f0006f800dc2c1b60836cbc61800c3311bc5e378186f020de021ba00374b86d960db021b60036c0868000d00219e0033c085d000ba02170002e0c46d178da021b200364086c000d8021ae0035c086b000d60219c003380866800cd00182042e4005c810b1001620c3881071000e2081c2043840070830d5041aa00354286a040d4061a808350086a000d4081a60434c0069830d2041a400348185f820bf0017e0c2f8105f000be06176082ec005d830a3041460028c0066010cb00196043280065010c9001928a2410c48070900c1200424000482288f4311e1c23c30478108f0011ef65c1e4b83d951792a2d4459a08b351156822a042d8005b010b50016a042c000580009b0213200264004c010970012e00258084a00094021260024c00472e98957312aa62578c32c1865630c903e5187ca18f90616e082dc005b830b404168002d02859840b306166082cc0859800b306164082c80059030a20414400288184d0209a001340c254104a80095061180823000460308b041160022e58bcc9979962b3265664095c692b1f242243cde467888b50d16a082c00058020af0015e22278344f090897f30ef661de4c3ae9875730eaa61d247d238fa441f4243e8407d060fa3215c602b8b457030ae0415c002b82856840ad0615a082b40856800ad32158602b0b456030ac04158002b0e8441c08835110bc61574c2ac1855730aac61554c2898f8121f0223e0407c068f80c1f0923bd2077a38ef461de883bd0c77898ef121de223bc4077868ef0c1de0e2ac1855828ab04156022ac0055848aa08154062a80855008aa001540e2a41854828a904152022a400548308a041140022974c22f1827b2d0f25a1ec9d3c93a6a21ed043c4c8388907122062040c0854000a80014e042980053010a50014a042900052000a20213c002780849000920d11c00220484388087
def as3 := bankPage 0x99bb8ebb84ab79bb6ebb63bb58bb4eab44ab3aab30ab279b1dab13ab09ab009b 0xa98b5a56412f2e291b1008a98b5f5a412f2e291b1008a98b5a452f2e291b1008a98b5a4443412e291b1008a98b5a4f43412e291b1008a98b5a5243412e291b1008a9988b5a43412e291b1008a98b5a44412e291b1008a98b5a52412e291b1008a98b5a413a2f291b1008a98b5f5a4136291b1008a98b5a4536291b1008a98b5a412e2b2a1b1008a98b5a51412e2a1b1008a98b5a45412e2a291b08a98b5a452e2a291b08
def ac3 := actionPage 0x12519c60a40197f811b18408ec0a478c10517bb06c03b6db10115b71200196900fd12b29a40196450f9102e96001a5f70ec0ca91ec02857f0d80b258dc0334e60c009a18e003344d0ad091c06c0353ae09807968ec03c2fa07f079202402a27c05f048f9940361da040018d99003613802300068f803c084000000003402c000 0x61000063ce00020a0000c02073ce38000d3800ca00700408710a34000e0042802820073840830000003030002c000400e2c610a00c10400c30070001675a5007c059500b1cf0087cc2800040060002800c070c0804161980000170003000c068824700d0863c030430400f00e3802d129200000c70a14d0020551860421cd68e0044cd4803035d420000901f1ca3d40005c87980103562ae0022c200128200c4c0a016022dd00a5c12090800081c07ca0000002420090180000182490ed01f78920045b14f00b5000805c000048e09a2d17802c00000116900007822490261092803af01a0823c00150913853c800025b00020440c00828200000b1835521c000010079d509b5a01a39e79b70e04b0030001020802c02403401452800081452800000800c518f38b1c218810500f14000018414900000a1800010cb00414e18000800f0c60044c021831924a00a0095590121cb00c01a00c00000700b04f00020061e6591804d150e00e18069c74078800474331d4014480047c43803861c034078c0ca00b08b0003911430040081422001003ce0081802000d10801832c020000021b1001401c02cb00500000b00000e00818e00b74b3d724768100000200a2400006c07cc08875d0096ca18c20000f5402ca2800167551c024c31704000e0001437963002800001800072d939c00078011f7005c308025d04570178000061918001e7c074f69e60b0120531c03dd00330050008400d0006000081d800018001a20b1083060920000020034972c01d50000004c57c01d104650001010014000e00000001600500f54b00671e71a00001a2c874000010c2c50c03801c56036d370e0002013c910318440014868918e1006160c51d90001d02197c009d0896ca54b14610902f0016486c00077807c90000020000c00051401006000003c0003e4800604001101701400a00b6cb000f8060000050001800110018e4d82005c9456200d87ac734000000fecb68300e0140dd4680d87001c4d4d1851000031988921831850213001001c000101879200f49f71439068629008078038020824100001b0822d631c0001800003805001402c008018234c00000e00e0003940426402c604014020f35501f00800f3400003c000001a18200054114900010235b50c00004225e0003400801d701368270030454e28631d00f0856c009528870410029300000930f08334000b3dd30171600420e0000c001e00308a31f39e5c0701b0f6125cd00020068728100900200008b080080392000200b4c0191c0200483100354f910401c07092c009428060071cd1c24364eec80200000063c01c03c92d43c00c370d4000d56400110000184030170000160c02845000445cf0050214882d528500020300000001f5c350b300000121000491f4f0018400191c04c00636da0177006c014009d6de48001f5406001470000006db0005400520033a59940c300008879901a3c054d000798f4048d0900980080cf75a0ee6549236c03025d96076c025f7007695c16c00015493820147004820002d8a12009780680bc000f08ea23000f5694224046d0006609009e900c0390002d8080749ae300200501160a56934a8dc8393c43ef01e032845b1b10000066f0006e00030ed36d8ea0003c0113f8070102f68001e00727f12202468234003f0072250012803809476010ee400023e1b009002a360000c600028200903364023e4c01c6f213b78058000000200000239003a30401cc1410050039cb1c0bc228d028b400c23672098ce6c00260c8a0b0120007c028b94000c35e01c87600f0200a0dc50001804800000052050289c71498d080302100508001f00000681d0062c2b43d000030000002653cd68002d796f080e80000c60000041a658038003aac003732834f00370001001100077c0160aa023040383f40343b00a581c401701300080f7aa2ff01002d61200002310035fa80c4096a000100580dc00040060160009f411502c500018000489ed9d8002b64d4ed7d2b5c2c0ba4083b54c0f31b44b803000ec91d000002d0eb50c32731ddc3d991cd08034000074cb60ff88b5e33ff33c0dc055934300088048095d3000016c092a00b9bb40002f00200e32a704f580001c001c1401c00c02183213c70133dd24014d200b8003500ed80000f8001f4b08af037200fce0001801ee18742038f00bd1503bbda74098098c0482a470d 6 0xdc8743210edcb8643210edcba843210edc73210edcb73210edc73210edcba753210edc7430edc73210edcba843210edcba643210dcba43210d9320d943edcba876543210edcba86543210 0x2da5b0b696c1f35b50f21dc3a8731462843c8750e5e6c4f8790ee1d4398a31421e43a872f2cf99f63ea7ccfb1f53e6b6aafd43a535d2a4547a8b02a04d439d71562a451813512a12ef 0xfc2d15c74298e053061267422e8e424107e800fb001ec8e30c6058800ad3a14a925a51cb4ab94155282924ed1c9d8112900252244a040940312204244044440088800fe021f6003ec007a800ac3a148702903051a18fe4f1f874284e050800a80d14c202847c4f868a70014e2428040503417299257264ae4495c592b931bf1637c6457830af2b14a402943c52800a502250004a01893821270224c0049808928012502248004900888001100221e0043c007d188bc2f1780c2c41058800a37b2e6f25cda8b9b41737b2a8f2551a8aa341541b2463248c1891821231b23032460188c02118061ee083dc6c580c8b006160082c03451000a27a2e2f05c5e8a93c1521224a204940891001226b22ed245c08870010e492128e424087b000f6001ea74278e04f43977832ed0e55e0cab2413e0c2460048418903290f061e8003cd94668c0b6001660c2946052000a10413c24274744a0e8925d31abc6215c9e2a93c482788c4f048950812a0224000480088f8011f0221a004344c76888ed4317c182c800590d0a4181480c29010520909c10138ba6315cb5aa96b482d68c5ad0ca4ab948552909052118a40111e0023c00474308c801190e23018460088c00118022180043008858010b001e486308004d8609a0013434264604c8309904132b05a958b52416a462d4005910ca3ac1465628c9051918a30011c1b23432468188d0211a0c2323e460748c0911810230003c41877020ee001303625c644b830970412e00258344a80095482ce8c59d609fab13f482728c4e47c918e9231f2343a46818890211206218084300883801070020a003c40078010ed001da0c3b01076068a20d12a0c250104a0008e00118ba63d8cc1a4166462cc904e1189c03113042260c42c1085811060020c004100881001020220200404088000100021fe003fc007c010f7001ee003bc0877000ee021d8003b00875800eb061260824c00468008b
def as4 := bankPage 0x9eab94ab8aab80ab779b6cbb61bb57ab4cbb41bb36bb2bbb20bb15bb0bab00bb 0xa98b6542412e28100908a98b5a45422e281b0908a98b5a46452e281b0908a98b5a45412e291b0908a98b5a452e291b0908a98b5a412e28211b111008a98b5d5a412e281b111008a98b5a412e291b151008a98b5a42412e28211b1008a98b5d5a42412e281b1008a98b5a42413d2f281b1008a98b5a412e2c2a291b1008a98b5a52412e2a291b1008a98b5f5a412e2a291b1008a98b5a452e2a291b1008a98b5a413b2f2e291b1008
def ac4 := actionPage 0xc91ece07c0356420b61cc693c0335a909b1abf93803550a08519388f803945f067193183802a3e1061172d9202143a505b152a91801436904914240b40312d604311a095c01529703d0f1e1540152580370e1a0a00962160330a949ec01a1c802f07909a001b177022028aab00280ff00401040f403c04b00000000a0019000 0xa400001cd0056c01801c0000114040341380c812c0000107f0c2c531520001100030068004000000330014044318d01e2870800190c318060307000f3c038f6882405860d30000001c50001ce0000007030c68000c878038c3cd54c4cb3010c81b128600250974a30f3402416800014580c03c06c100b01801609b03700001300330076002e01f38830962c89a00021780435f03cb14000fc34b50203c164700000000db0058bbebfc406c1515400c0454ca1ec000230001900001c551b87000412c9f389291a134c05c03fff3cc40ba8b143fd8bd14039b01604002730301d349033004f4d000400100300000121001800ab3700300c586005803c0782340000900f9c20f13a0000060f64000040c0000023000380f965c9007fc4000b18000a36ec068090fdc04825c9440307b0eac00001072331830000001680c15c06eb76c4823ce3ec74bd090cb100f028f704a10058c0c0f82b83017a410c03c188100514416b07b92fac07d2bc000900c0055c02fc08f1bc0061d001131ce03b0e1ef1c39400008c1acd7461003c074a3850f3000fa0684000b16000027a00180ac024000003b2e9020001000ed130002e0002e301f00002c900784ec6fc000b02291b002a0310a0077781b113400800010001b8a2a0b28a03e0251c33d90355c095500301179401a00002264064e01a03500527475b7000420009e53c400077e00003c000557b04a400187807832df9003c300300000e9404db2473fc297017a0058877271a08603758931128700c0020c01c0fcc1dd50028e180c1201b6270129ca09964824470d14030328000c38028c00010008f34604c44a1c02004460000000053400054401406c03163420080000080000ce34024e0000800871ce0002401c03402c71451051401c028d00900500c34d14324020e3c008600d21640e00000934928072000700a6807000031c03506c348a0d810000048200000900564355d18028e4800064494ca1400ad00000e2802c06c01c070048b01664000f5181402c800168200004d01000f78e2930003406061c00006cb4406d1ad000734f30f2827d3700c8000938014900d00004215319e0100000041cd0800000143c41c01c724804035424024600768000000208f3897ca08400300004038e0cf00328824000500700a2cb1c01cb00034a00d0c500b00e00e00038600534124e00828c00618000a2c01003482401472410093c00060411401800030003c000f0480001c034030e0000092062ca24f34500800000120504220f34910d30a4520004400805803510060031887d064000f01015020209a44000024254024e3de1400170006c539d3dd6800002c87c300d4da00200f5403c079300000e2400000c008000a2460001c820600e14901221a2830802403df00030a00904600e20644820e0001c07033000801ce00600c70408011930b30d000000e042037001000106d8340600700973a406fdc8addb79d2c000691001f00b48b026031006355f6b2003c0d950006870000117c601b4476c018f4d900020700060c5cf2989107093462400136631b90008c90144c9140692003a8068308019d0000000109ce0c302f512cc1ce4b1e0197892c0a400000001dd7a24e545814e201000f760000903403000932005980c000208294001100010001f45c0f30800403c0f41000007ae47bbbca24026f4c4d8201d0145b3012bd6b400137c93e2b00016e400c0d074e670b4890057cc011bc02c07dc00b8e000078000f02984e0001c928410020430b3cc3403000000043801801c63800400ca14910700000024c00000e3cd1000002cb24b00d1002481093c80000c034c10e080 6 0xedcba9876543210edcba9876543210edcba987653210edcba876543210edcba876543210edb73210edb632edc9876543210edb7321edb63edcb7410edc87653210edc73210edcb87653210edcba86543210dc843210 0x256dbfb43680585bfb43680ddd2ba52261d23a226e4d5d13a026a4ccfb9f5956e91d1ba27412a5d1ba1740e796d2d8a891622bc568a914cfb5458a914e28c503ed57ea2d44a8750a8d454812a84f9d47a8b0256d2d8 0x456400ab80156002aa0055000a980151002a0004e848998112c0225600458c474010df001a20033cb0668114b00296044ec009d8113a00274244c840992c12456248044280085011090021262398bc73010c3001865830420ad83154042a80452800a500149022900052000a3811460028c044e4009c8113800270244c440988312f0425e0c454108a988e52f1ca62344bc68800c22c1800c53810a700145022860050c08a0001400226e004dc189b021360625c084b8188802110001f462390bc72030ce0419c00304005f8315c042b81056818a78214f002880450800a10113f0027e044f8009f0013d02278004f0089b001360226a004d418968212d0621e0843c007c988e32f1c60c3341066800c00017c004d030700e0bd0017a382400048001330026418378306d000bc0011e044c000980112e0025c044b40096811270024e7c2f4f45e988bd2f17a182ec005d8d0b9181720c2e4105c8012c00214382e8005d1f8b92c172004ac008b801095a1b6002e0b05880114511ec6c3d9105c080b83a15e0444c0089801080016e0041418810210200168ca5cc308c379166522a0841c0081831006f1a2082d400598e8b0181323a25d74c82416c462d89052918a52b94255284044a8009501123002460c478108f0011d0023604468008d011120022400420088180103061fe083fd387ca70c00616c082d800590609a001fc002b8e8541c0a8
def as5 := bankPage 0xa4bb98cb8dbb82bb78ab6dbb62bb57bb4cbb41bb36bb2bbb20bb15bb0bab00bb 0xa98b5c5a43412e291b1000c4a98b5a412e281b11100908a98b65412e281b11100908a98b655a412e2811100908a98b65412e2811100908a98b5a412e291b15100908a98b5a412e29261b100908a98b6542412e281b100908a98b7c5a412e281b100908a98b5a4e422e281b100908a98b7b5a422e281b100908a98b5a44412e291b100908a98b5f5a412e291b100908a98b7b5a412e291b100908a98b5a452e291b100908a98b655a42412e28100908
def ac5 := actionPage 0x84304a0e401d5220832a48b0c00950707a2643a2801c4b307222be9e809c45f05f21380f40343c305b1db29ec0163810521a2c1f402032104a172899c09c2cd044142519c01429103e10a11e001624f0370d1d1e001620d0330a991600181c502907129f40a315c01e040c1b40a10f900802850f80b7054000000016809c000 0xf44034630030d28000b69120000400420035d0001d930d21a5084400006805007c00830060033c001014b2c200a08e05078260068b24000000c09b29d24c00c0050050800812c200038d28400008c24014b04c20000d4020000c96430000190c028f0003001813121c001b00a30338321924331b3400005c22c264f00810000100000800021220514500000f5d611c5c908610078030019d2c01442df59254070e00e70f0002c07803c00002c701e01101b00000201f68600d74030024000a15308510f3480082cc1c778c0041894c038a75600060001421d01e2808cb000000000b176572ea00460089f6c07fc3fd00b7f86400000009c07707dd7434578196c0500580ad335734000b2a60020003cc01901a31a01b78078000152002e1176c558f3406c08c0b2d740023540a5c0d031378901f280180038600000d9174cc3800e1050d00052b654001800f0c031478e7c00075c011350a0121c06001c05c001775a00354060069d01d3542c01c125900448301409820538a1575801400006d800029354039065b6cd4805c15400000000146c05407903002c40023d469129564f01874600000000360028109939e34039c0124000004800013c97002013c561e55600a0d67170874407d900428e00b70a24000200028000859005701a1c910400721f4004000405c074018c0d518068008500401311110a00068000b29248a0070c600000600064048f10000400a3c854001d01c00214460a2802402811c03932c92400c520018138e34028e3800050006800855ca00041a01e2cf14014300000008008c54a1821dc35c1001d818d58034e51a00408004b0007470c801f5963c00004401c05da00009d50700518901704b2de01600444a05321058100400a00c14e5800060000c97c078344034001600908100e3c02c028438901300028060224000b4400cf3803092003400c048021e64900901e30029b0cf3cf08408200538d00100b0000c314b4ce0000002d945a00004024a6880d814021848e2427c000400001450b01604f68058d48a18d40018b79704330000b00019828044028e40034034e79c70c59c4461c000200d0180015c000f0000401183dc6ca50014000000919420301f0003c244b7877990c000f48c00001338700000305c00e0807007136c000044b04601b00c01274a0040160cc74164c01e3003114cd5557c0089151000d00507000275e40d990178420373aa00000090e1c05444b5b14324dc8e733e4000761013c1501720bb8200144d02303435e58f54001d0000035c028e0151e301d028f0c1ba0001b602c0065cb10b5809c0940bc0024ac8e555426d500002ec806830bc680016c00a0b940c470255c0a6700515b40b7e16a101504000901a00201c1cf00f1846010800004ca5170870050412040110400802d110534968000a01000e38001610028700c00000d1063003c41c564058054038f 6 0xedcb76430320edcb873210edcb876320edca987653210dc987653210edcb987653210edcb731ecb7630edcb7310edcb6432dc743210edcb876543210edcb876543210edcba876543210edcb764320 0x12b254c39b21625fbba23a6730d49752d45104f825b12fdce99cc37a6f0d485c7ea744e51a72c25802d9bc20416a9644588710a2043f3f14ba8dc4579ca8c4d0999612b6563f5736732563f52d45a4b38ed9612b6563f5736d24e64b39612b1fc3f57367362043f87b0f0fb52ca5346e203cb5427ce22440878a91509f3a5b4b04ccad954fcdcd9ca 0x7421ce0438407b060f63a1e6f23401058800b1001980058408af060e7001ce0032cf464178c81c17a202f408af8613200264183980073060e4001c80032800b00015f002bc00574389a011340e266044cc3098801310e1d2043a43874010e80c1ca003943071800e3001920457000ae0014d001c40056810a60014c001c2583811864218c83f17a7a2f408ab001520029600374b06ca30c6101787e2e408a9ad124562480836c006d960d8002b200548bc6f160d72f18e382e800b181150001b8b436cb06dad0d62c1ac0453c00a780145001aa0850c00a08313e0024e08494b06d020d7001a858318605c801620428000500189e801260424800490006c020d6001ac0034c08ac001580229c0053800a68114c002980450400a08313c042780c4c0109803128042506239cbc73830d9041b200348b062860bb022ae004ed6892001175a1ac00340b067178c3
def as6 := bankPage 0x9fbb94bb8aab7fbb74bb69bb5ebb53bb48bb3eab33bb29ab1fab15ab0bab00bb 0xa98b65412e281b15100800a98b655a412e2815100800a98b65412e2815100800a98b6544412e281b100800a98b625a412e281b100800a98b7e5a412e281b100800a98b5a4e442e281b100800a98b5a4e432e291b100800a98b5f5a4136291b100800a98b5a4536291b100800a98b655a44412e28100800a98b6544412e28100800a98b5a45442e281b0800a98b5a4c452e281b0800a98b5a454136291b0800a98b5f5a41362e291b1000
def ac6 := actionPage 0xbb19c313411967e0b317bc93401b62d0a316b60b403159a09b14b212001b54909611af1980115160910ead1900114e308b0ca991c0154a40830a2596001d44d07908a08e80a43e1063079b8a803833905b059792001b2e804904938a00b1255035039009c0331bc01f028a8ac03312300a01850ac03b07200000000e8026000 0x1319044f38f64d3401000000020c000600000900000028008468e00001e04c34a18b00d58019608b00d04318100000930c01710505541e38d00d65871034005a39034c39e34001000018001800001018000f6525520000d039d6ce48e6400403c001f01a0000976176521cd01020335d28574039b00e51e21111500d4860000000187c805500501600c00d00e54019074408034064070c68000e2cd1554521d92801453095860006c70006001802c924074e0000140000050030cf3144de00d78c00008000538800a00018009001f0190c90c04003440c02583d818000055b45200f19600038104800b3ca0003c720008204000d08901b3000471442803113422402491c03c218f7880021cb2883800c00091007cf00801f2400000082c82c000038c0080000c40002091de28d28800d00100070008c1460001c010620700000d20000070738518c2800060011801803032c024200034010000d3000060800030001080c01803c028e0081470c040704001a18001114001700b3d10044081c000a4c53c66593dd3c810d0000070151c02800420010100de6805073804035006c01153c80983400c04573803840140101c07df4c010c0d400005924000b01000c00500a0000430041401871000c048000001221000b1c108e7876d300935d04e0010003100400000001d07cb04050040000000014b10000f1c000901a54a1803043002d614a0002114c244d00734348004d3c47c02d700720658b08b08e01008011e10030e70010008f21000a1c058700b00371800f0d061964029a3c30070005d408003501028029800020c9800000006004d10c06d169b0085951111bc3d971f18031d09014002a018008387781280fd000811bdc001c00000154c70601058000000911078009b01171670e4c324068f00400055e8020006d26403470161995001015d60141210070020802d560020001438074f01404000000d10001b21a0075d86cc2c70020020003d40120c80153830d200d09c0000172140095414d10092d30105064df10908c4842801090071002041c000244e00000000f00068c3d10800034da2c800004479524b00114054731504101405000924048108500a48f00901900500414c38c0c000674b7484000115403402800023851da00500740100000f7ca0465485d83cc74019c6404900400113c01400123c001500a0000000006801420006c00c05001c03555401000061420135806dc00075311e6c00c210b1c50002c010001f0c00861951c01472db01b04708801b6100034012c051749600014001a70548074038309901705c70d1820086027821960001807063801882406445d26010c71da1871ce01930e49318001100b0c90000020090071c300121940200021360501a00438800905904b01224250320088700000000001b00200705164024008b6130000c5140305019014482a4001260001e00f21c5510182005422883c6000000640245021053a4200a54b7826d001f08a00829b6804880054831c051d79b0000002d8580a433da10064e01b00401c3432d31690006005c000c00400e0130270003c05d70c04cbec610a6c00c50044df54059200a00f14761e0001805157db8450001c03400000005c06d11c100b6406c011b0c97d66851c070655d0002d32c0a803439412400103c00c70040c37404ca00301d0d44803dba9b6ce00300001b6001d444300f3c00060c61032d450b1803cd20038019c00a00301501315801c0c000001230d30e69701610518f00408141068511138301c4850152c40103800050060001c030038d6004491805402d200e7c0 6 0xedc9876543210edc9876543210edc9876543210edc764309875103210edc7430edcb4310edcb643210edcba43210edc76430edc76430edc7430edc98654310edcba743210edcb864210 0xb7d6e09011cb684808e11a240472dc5b423846add5b48884708d034b756d22211c2340d2dc5b423846cb095b2b21e41cb456828dda2378b604708d1162384688e11a23846da0161682cf51a 0x8be9a9302c260004c15470230e0101c0045f800ba1a92e2c25c004b8f4851790a04214005f800be8017c022f67c4d0c49a031343525e584bc00979a92d2c25a004b4f8961892c06258045d800b88016d2c250004a0e093a30da101b4005ec00ba1a9272c24e0049c08b92d1265624c58498009300179002e2584940092a30de101bc384940092be1226524474485a06e8e0d7001aeaa4a594940c1286824438488e8902d0ea651b230364006a2e993022f0005e008b78016f572b0aa56120ac23158122b0205615c94aa929482528c4a44894881293a23e7047d0c69060d2001a4045dc00b4ad1262c22000440bc84821095a1b00c5ec08bc80177002ec005d400b980172002e0005a180a99893306266624ac1895961150022a5843c008783174042e8045b400b681169002d2045a000b4189322f2640c4c810992c1265624c6245cbc8b831170422e583e8007d03173042e6045b000b60116b002d6045a800b501167002ce0459800b3189312f2620c4c41098989162f22c0c458108b160f9001f20c5bc10b781165002ca9053918a70914e1029cb04dd589ba4111462222444440889d10d3821ab03a95875000bf43158182b1f488aa911692203044198870e10e3a1e8d23386067000ad
def as7 := bankPage 0xa1bb96bb8bbb80bb75bb6abb5fbb54bb49bb3ebb33bb28bb1eab13bb09ab009b 0xa98b65452e281b10090800a98b6544412e2810090800a98b655a452e2810090800a98b5a452e281b15090800a98b5a45442e281b090800a98b5a4c452e281b090800a98b5a4e452e281b090800a98b5a50452e281b090800a98b5f5a452e281b090800a98b7f5a452e281b090800a9988b5a452e281b090800a9a78b5a452e281b090800a98b65452e281b090800a98b655a45412e28090800a98b655a452e28090800a98b65452e28090800
def ac7 := actionPage 0xb728df9f402165d0b3275b0e40196120a924549b40235a90a5214e9b00175640a11e4a9a009851c09d1ac51ec0184d409316bea3402346b08212382740263f90780f311b81a339006a0c2a1b812631e05d07a32780262ac04f049c1b80a523d03903950b803819502f010e17802312c01a00070b803a07e000000003802a000 0x6400077d000100654000c20000218c5d06403c00182c00972df2c046d43a0110000c001a41b2db01c5ce30002b01ac0c2ae0000195000000166c624f080f0061640102c70c2016cd01d0000c03c128018800118000000a2c41860000041000050461882c83420041c730300c2c400f04708800000030028a1040090003c400600230151601b0471cd08001700759d41400300b6800000431400105c01140d30070090170175093000dd20050058024560f1c424500a0013c00001c608e19701630850008074724000e48501f00168f2064001ce6d80140000005460123d20800c034f00520d01960200000018a10000e0040047150002d860f3c97c020649508c1185d704f35425f00000044000615a00201f1843000c07485802d62c000010e61048710600c5402de3c601e10a50038d4400060db68000615f54064170068000044e25364900b1c00ce58d3402d454d08301301b01959f74014000275c3c001c2c900f5d209e6c054234058044054000200060d2824c025031600800c00300e0003822d071d18001e0803c75dd79f50d00d19138000000f6c03007474430404401830000000153d130b7cb01600000e0d608808d00300a0c900e01629000c0380000b30000006516580004a5200201a80240dc078c028b53272000021000cc0bc600ac654405ab09c340096dc0b404c0121018000f321532392346800120004c01b202677709c03aea06c0215c31fc43d74450305511c02800177803cd7904cf0006d870060b2d105001e48c00038a01644000000001138d60820739339c5cf3c83093447c03535d12800050002c01dc00300024030000748000000a01e3dc48024b2c81d2fcd35329138c9c000039205c6002183cab5501b4c01c00007c10124c00082807006672985de0007ca3d200f00d0000000130056ce59b4000c77020135bf0011c00c07c084e68f7c044045a09b78070b6402c878000044302a70e0004198d3379003a8f302e0024000018059e1c001410502801f1405524400152db6954014c0a4044038000005c01c54d280217d4001d01800041300040229f1c0d8b54a2d024c61850005b6c401400600b0000050036133001ae15700d6d2018f117cc000000aaf419d109c5058024440540e6e98f00d5d02000001402c574000a2006c0865fa700040e00a6dd1cb5c846d0000023142c000310d014b0600344012658d00000000aec228c00a3973f401300a38d3004c000001979200001904867000086952eba05409570000010003c0b416dc0050046984d4f8c005000c80a46a600cf70726522188303664d0151026e4014442d1a00b00a19f8c120f7441c01a200b79abe4b4fbe9282000a642cc29f02d01160010044000c1c0011b40b3014000000d3134cd19700045600040018845c6977451060004de00300e3801c710010d4850070c01110c000871601c0063ca0563404490006c07080000d940365350000b78c4c00d51480060013c7016b0600c64531001d00d7b20990008adb0b01c3e6000fc04440e500b0ca3731001c0f2800902978082a77c140e9100054072b74db41be200d34001001c00014c9001403800143a6000033006fe4400e72000edc682c40a8c3400de00b00002a000023380941004a0e44dc13e04dc7b8020478a0983430de3b268ebc4005000580015f00102f76b80d43300b47351a800f700189b00100402e8401420800c001000068034000002fb0c28000f9b960001900ba7a76e036000acf2cc0001f756d27d0fe83be1f34234000050ff8b22332bdef6b6783b400014469372fd00000c01b00c 6 0xedcb987654321edcb74320edcb987654320edc987654310edc74310edc98654310edcb987654310edcb987654310edcb9876543210edcb9876543210edcba987654310edba9876543210edba9876543210edcb9876543210edba9876543210edba9876543210 0xb13270de9bc33e170144b195a238ce9612c057c2d825b4968ed1090050096d15a1b4023813824b45686d008e04e09411dd4b44d60ce8f01622bc46dd4812d60de1bb33a58078027b456819719d1a6236d25a2b4067cce88dba968a159e63786ec9908d04b692d15a0264238469bc04a668580af15c090af823 0x3260c634c4b0831612c2b000560e0981a930461ce8639c4073860e7551c20064800c59614f0029e0c63800c38216d2c29c00538bca58214b3525c86390307201191003225853400a68118b003165851400a28118a003145851000a20218706304085d0b0a18014346264204c8fc85230e6101cc0064000c78018c00312005acc4b0031605d2b65852000a416142002848c4c440989c12f461ca2039400c383184042e25e54810a916141002826a49d0c5e060bc0030c0460c10b982170002d4ac588bcaa021542f2a208544b0a3001462c27e004fc00c201182082f6145e4d0ac851592c27c004f928998a13341258943a0507400195042e4c854d8ca997953042a662540bca803150042a1104f61c9e9613d0027a0864408c80018e0031a0062400c201180062fa0c5d800b61895e062bcba568c4ab031562c29400528b09e0013c3825a8c38c407183188042d2005a4bc9d9613b04276004ecb09b80137561a60463810c5801880030c0060808c08317e062ee085a000b39895f062be6255c18abc393d2f274084e8b09c801392c26c004d818ca031920831e0463c10c50018a0030a0860c00c18018100300005fc18be03175042cc00598c4ae8315d312aa0c554bc9c1613804270004e0b09a80135
def as8 := bankPage 0x86aa7d9a749a6b9a638a5b8a529a4a8a428a3a8a337a2d6a22bb17bb0bcb00bb 0xa98b5d5a412e281b1411a98b5a45432e2a291ba98b5a4b452e2a291ba98b5a4541362a291ba98b5a45362a291ba98b5a453e36291ba9938b5f5a4136291ba98b5a454336291ba98b5f5a4536291ba9988b5a4536291ba98b654536291ba98b65453629a98b5a412e281b10080400a98b65412e281510090800b8a95a412e28261b10090800b85a412e28261b10090800
def ac8 := actionPage 0x1111bcf0d400b5e20fe19c813802c55e0e417c213002d4d70cd163b8f40324410b016358300243d508e162f830025366083142993002d2df06b142402c023276056141e82c02320d045141902c0231a4034141482409815c023141002419012c0140f0e2900a10c90100c079b4017084010030748408906900000001b8023000 0x1432c024010004000c0060450860001430040002412c73ccb40850cb51c0280007fc0004f1200001b00000b5800400007197c03c500a00060000e33ed4a1003413800001d501a1c650a94201dbc03b17124000050150300f550b10b034f071003c44817c024030058f70b18100001b461000a886515803803193c401c15400d0dd91303f18dfc05c03c0440000000233d8090b2090899f5fdaec0d63a000000240180262767408ca1180004120e7ec02aa00c7c00c5d5e84094085f02e46bac82f5828000280f09780250746a80003009b4034903200d4c9f80480bc067c0c9747b5470003d5808493005801003c06460070137cc24221a00035c84000000a70900008034094d8c00dd907e5010098a1f10000a04e004054e00001602501952f1000cc16f24074434628c8e000f6802cbb80e690291c154000004e3a100802801d0182cd01d19c00300e0296c510630e2c05b4f40180e7400bca8037a953405000580000dd2b00250007a3000001dc074098005c0c0d8071c00084500029d2c0006c9ce09003fcbc5201703a04af782e39ab700f0056afe709603600a14174099f0672800080151892950d1000ac5112ac9024dc0bc07e6000a5c24bcc00010000002c0297bf70009a2a400003e9ac5750d0480603424008000069bb2dfce1ee55e2806c884058a623fc0000e40007020d94800ad314d7ca3580004c00c07c070450034e00020900018229568040501901900d2c071200450044421014d3003501d100000114654038f0560002023c059a6405c05db00000015344019001701d3050012c81996c600008a14220f01b00f0d67d100030541a259540040e50000880c0303105a02cf8f3f31530002c00006c10273aa04c00d904e04fa47ab39c004a375df55db00040d00000e03d020291e2b94080dc038303703825c003d940004dfec4001c13a805402801c07c00053050853867d86c044424174d00020201300059f10e78040008654001b08775624059638400500d45200000934110b60239211801f00348801301268001a0000071890007dd30b60524001b6c058064518e3405c60163075000002c93080062150080001400030003d20003c314001504b0d751f24039538004064809101750f00101214079049c60571600304d0000006c029320778578000000001a1dd00434a2496c00000007c05d800218b74159c00814059000430f00c5d601500000001329050704d41724028028e54854d29c00e00000010f34b00005404039b00128801e6400033c031410f7806c45867c004921220030c11701e28808000238708f00f04000800a08a14a2c008d18b30d2c000218000029600000c4c97c23020003d150024128028800434700000000059031c0000175d32c024d2001cd0807077cf14069e5d51000000006d20007101503db0da74f4800006d565b0182c00160144c03c06ca24f3c031001150a5c001f14d01100074060301e0020422933cb49901d0c41006c864c00210528b2a16002dd21b30054f04f400bc014c280e0d0053412000040031d818900b51e2c6010000ccc0802003eb2308800000146401877800140090003c00aea8e0c01003c095d78085e000 6 0xedb63edcba876543210edcba8654210edcba76543210edcba6543210edcba6543210edcba6543210edcba743210edcba643210edcba543210dcba43210dcba432107643edc98765432100edcb9876543210 0x1cf13225f722a0d3e5d9722a0d3e80d5069f2ecadb56e9e5247f4fe5fc2d1344684cf9361201e659cb19602cc4805ab2147250c798e6f3dd2ae2594684b594626c2905009a12021ed351c96ef40d096c 0x7a800f43dadf795bed4ae1a15c352b76856e0477800ef011d1003a2046bc00d7801ac02356006ac08d0801a1023400068175a8352b66856c90ad9195b38a086f4100c8201104389f36f3e60c7cc10f9811dd003ba9c77000ee281aa4e354046a800d5001a90233e0067c08cf0019e58616acc2d2153232a60640a0881418f9021f2023b60076c00ec811c8003900070400d4001a70234c0069800d28119d0033a0c67010ce2eb4e6369490a9519528320c044180c7c410f8811da003b40076008eb001d6023aa0075408ea001d4023a60074c00e0011b9003720069008d1801a3023380067008cd8019b5e698bad3161582bab056560aaac04d51892a31154620a8d254ea429d4753a8ca744d4e8929d1153a20a740ce6811cd0139a0073400e6009ca003940672408e4809c900392006fcb0d1001a2023340066a1d43472348c468508d09d1a33a0165402348046100839b60536cc6d2d75a58fab21d56424ac841593daa77954ed4a9da153879c70d38e0471c00e3801c60238a007143ce2069c4023880071000e089199103330ecfa1d8ec1ae44855e24abd255609aac00396586f800df001bd00378006ec00dd219b90c372006d9a4d00e9a0003320c6615551232a210545088260504b72096c412468248104a19ca0c39400728d4db961b70036e0666000cc2eb035855692aac4d55abaaa4855424aa90ce4861c900392006d400da2a99b463362066c00cc019975e552baaa56154abaa94955290aa44d54892a9553348c6690ccd0819a0c3340066804cb801970032c0c65558bd0017a792dcac5b810b70016e2f2c65858c10b1801635a2c4ac588b0b1001620032800644b0ae0015c592b6aa56cb0ad8015b592b4aa568b0ad0015a432687e4d0f49a06134461d2863a44074860e9
def as9 := bankPage 0x8baa829a799a718a67aa5e9a54aa4aaa40aa379a2e9a24aa1b9a129a0a8a00aa 0xa9a88b5f5a4136291b10a98b5a4e4336291b10a9988b5a4536291b10a98b654536291b10a98b5a43412e2b2a1b10a98b5a41362b2a1b10a98b5a43412e2d2a1b10a98b5a5143412e2a1b10a98b705a43412e2a1b10a98b5a51432e2a1b10a98b5a5141362a1b10a98b655a43412e2a2910a98b6543412e2a2910a98b655a4341362910a98b655a45362910a98b5a412e28211b1411
def ac9 := actionPage 0xbf22389a80155f10b220b30ec0ac56d0a41f2d8ec0324d70931f2902402346e08e1926b1401542f077162419402c3ab07112a19d409436f06e0da028c0133360680a9e1900142fa054079b99402c27603d049999002c1f203603148e80191a7023028e07402d12001301880b003108d00201830280a402100000000d800b000 0x1200040f04030048714000474100800310b50000401360568e0482c025c05100a34700c00a4483da00201f6827cf28700070d01344a1c20103c075601a0025c068e00b4951c014029f0117510800002801c531409628e00631634101e01e4c00553812cc00048300050020000100940a74e6004001404002087802033c000a0890000003810c40071c10160127803575867802c900000168c0c07d10007427d138008c00105b4c061e0165480c800719f2d03807c000804004340000c6c05007196800041545c028320001200035e00060018219d4c01002006975dd00b5c408001418105145f48000001e7dc61f0170155c000000111e65e38e01600e00274748001700e0001801cb2d114a00200270200378048419930000700f7102400501820093402c77c00107944800c01070d300001e50c0000095d270001f01928418634000031600045605618778504b60d0852cc34d6801031803002c000058000001838000a38074b00000000628300034b14a34e09404d20040018030f2482db2db24e0231c50230c07f4000705025c44001c49b037c00e64002c4180ef9001000285f0030304065002e000020547580d805a2000004302f2a004a8094000012a02108700048071831f801d400041141211c680000340059801d0c10371e86180013492c22464810881c000c20000201860000301e00860a28004f28c5471ca2800021cb00f1401400163401003404093c700420028700104410c00028a00400200c1000001c700008a30a2c000104e00418000e3c038300010018f00220014014334d38018008f0830c00001c600d18720f00910400000800900600330730100030900d0021416802116563d628000d75b60a0ca00000b1800005c01400030166001850031005c05cf01f0001802517401003d50131c029839a01300015e60d40e25800b4d90022400cf0d73122121c044359d1801400c55485420000105c900038758a0c91c730f0014803043c02057802c16ce01f01b00000e14000b20044000300600014001f6c345e0421560001486d12c01804d734b00064011d00000001c78e45900200a00301f5400056071550000003ce5192c01910c614d7d90007d5e8601004550e0c01804105836006000c90405c030b00900235a1800402051801cb7dd0844c704700800404310000068e28224000e3154500002d278c0007c000c6114c000013dc3d12000fd800510160000000130009000170dee9b44aff053405b98001f20402000090075974054e00c0a100103700b02b0000006260296b0c48000013759c5571c61b02a2c028b272fc06a20cf21995380670003e0269d937601400a02e34cf641803dd1c038600c1402c00000005c018611d00014a01a00034d0002c738008a31838f0000003c065518000950e0087491c040701215e6cf5c001834d01c28310900501000801329e0001c328168e29f44028468d1805540003d134000064d24034050120044f0cf41e1c02061404907c221d00064001714044001a6c01420060181d239000158000000a7891850121486400182061c048000064401d2c000018a0062944c075d15e68268900a74400001a68800a6c704f0c020624b6920800917c018a00038018000610f2c000000734d0051403803ce00d14a 6 0xedcba65210edcba743210edcba543210dcba43210ed940d9320ed940d43ed43ed943d943edcb764320edcba87543210edcba7643210dcba643210edb721 0x2aed3fa7d49a925198c713a1cd0f3c8062e559aa8b50a9fd3ea4d21e31c0777450eb9545a8950a0440790318e2a45089c3f47e53fa793425dc878c71462844e8996b6d64638a313a2653f9d51462844e80f4fe754518a113a03c4e898eea2744c870e809a132 0xde829bc0b37134d166994c6af5985d926b441114002270044c3881c00fb001f50d3a2246da0572232c61058d029f9b90591a0b6c414408290cea061d40b376106e800dc011b65d608aec112166092cc4956626acd55218022e004440088518e9a19d3103a61874c20dd011ba063680087008fa001f4433c0006cd75a4abb3955672aec55558aa42c54658a0488001100021f0043204860010c0121300426047c800f9011f1003e2006c808d8801b10036000878010db420f003e0206c400d7811ef003de006b5e574beae87950a3a85c08f6801ab7b5d2f2ba5a974b42e97b5d0f2ba1a974342e8435a01e874350e8121d0043a008703d0d86a1b024360086c08f6001ec58670acce0019aac3135662690b111962002190643008860190b822170042c0c850110a0121100422006a018d3021a60034a0c68c10d1beadf7d4f23a8a0350e8ea170241600685eda23db286a5d6d4ba8091a0121e00416008280104802080040c008080100801f4003de007b800f6801ec00340f6cfded8f2f3066a5ccfaa9df5240122d0244e007f000fd801f90d3bc2276c10e4069c412376bcc155d82a6acd4859a2eb34496684a2202444007f824dd811bb0636a8e6710cce0899c0c3380066400f5801e9
def as10 := bankPage 0x91aa87aa7daa749a6aaa60aa579a4daa43aa39aa2faa269a1d9a149a0aaa00aa 0xb4a98b5c5a432e291b10a98b5a413b362f291b10a98b5f5a41362f291b10a98b5a45362f291b10a98b5a413f3e36291b10a98b5f5a413e36291b10a98b5a453e36291b10a98b5a4f434136291b10a98b5a52434136291b10a98b7d5a434136291b10a9988b5a434136291b10a98b65434136291b10a98b5a444136291b10a98b5a524136291b10a98b615f5a4136291b10a98b725f5a4136291b10
def ac10 := actionPage 0x9022c30dc09359d08d20c01180145610871ebb12801c50d0771db58ac03047d0741831ae0018435067122cb281a43c904a10a68f003432d0470ea29200152ee0440d1f0dc0152af0410b9a8e40152700380a150ec01f213028090f8ac031180019078c0dc02b0ff00606080e002b07e00303041a001503f00000001a0015000 0x10000f24004c08000f2401c400010038c0010400022c234030100c3400001082442071430070000001013ce00c0070c32801ca0000c304a24024e2c20003c028800610020034600d24e0840070002c810200700010a24c38b0000130110000c938064e14000400000b4c000031e2421c62c50d20000012020061c01c600a0000400cc08900008104a2c00cd18214304f48500438100000c01664041400000000219c6c658200610d04001f34001334001c48001279e0181192404c929614f4004c06c070b4840006c00400c63d02c009915c01169108c04709010600501070049d24779101b4480194d960330028b60074008078c00c00a00d71f01e0131c800901110001300060020059101900c7100150141181107802c000308a2462964000070807c001f40e70d7db64035a49354000214031e78008060be80580aa70154558b84fdac0d3a21ed5700800c1f600975a0c6453401d8003d00046d0004c0024013140980b400005ec690b1138201543403df00440488678470017080d808d6e6db0403a5584c0cc05c002de0e01860f0065c0012011000a15280ced28f68b02a000005b037180003c000640a01801ba2a2d06802f100959a8780044c20370000152d44cb71e00001501a2008543d78c010c240cc0024d2a5d536360a39d01638c060280280380ad17d66db5c200f0383ed00d0296803004c901be407cb28000928b28700034100400008304000328104e00000100014330500110000924334014608710114308e00020004000100f04000020020038d0c828400900f0cb20424018024114414200000f1400050c00003c22c424834c2092c42000c218018000338800500104314500504304e00c0001001400071470081430062c92c600a14c3c500024024430000400068001100d00a6ca00e3c039601028a5cb0000000000050c000041b1c02c039768238b2006c02801c01404167141421860cf0c014000211009c4404cc01118a50168934f68d15b28048024001600c3c00003410057436480057cb0002ce18b00101a10e38008014a5000000093c254300239c00b3cc5402804806d22dc00000700020d3cb1821000050000530dd7830d515218038000e2d300001c5561000190161d21461c804e24e24000415d45201200b0070487085c050e0000d700050060424040401205d2870181c848028000070a7835407c00010c518041320540774455b09700a00a4c06596c57d50003ce0170dd38000725d00744001e4190c011a38d3401406892400003826c00005d90000d428070a55d0c90146800040c00000151500060006875983400c65480113c801744100611400545318b0002c644f2144876c238040044300045f0dd10001a0002c45c40000526c31d25c04406c300269945c0145d34000000081150007cc0580090d811044d00030d30a0002cf2803402801c02c200600d0002cc2c00000060cd4ca2c024b2800033c90053470853400060c910f24014110f30e0021cc0040881c81893820040000003cd2c03401c300300728c2400003d42ca30c1403c800020f00c0c0 6 0xdcba630c84210edcb864210edcba843210dc765210edcb765210edcba6543210ecb73210ec73210ecb763210edcba753210edcba743210edc7430edc73210edcb6210edcb6210 0x90f13a1cd248750e61c526a494621cd2601b66ab9570adf44273ca78ff0f21dc39b6366ab856fadd5b6af529a4d46a8c47fae144287c4e8790e61c44c8730e22743c87313a1cc3889d0e61e43b8730f21dc39abb4fe9f526a492feaf55dab74f693466 0x492358d46a008c478fb089f6003a07471ce0e3862c86940830810c0e7801cf3a38aaec315586092cb1059692aa11d540122f0045e047fc00ff801d00239e0073ce8e21c1c40c3860073818e6821cd0c58e86ae8315d002421d40430809a4f7329ee1d3dc307b814e5801cb06394bad355d852ab0a1259220b252161232c21258420b084d5208aa44953c8ea784d4f08a9e0245c008b8b10900212023fc007f800e7011cb003960c72410e4861c0433481869000fe801c7123780071848df081be003f61a71c48deccaec685c326b464d31c7a32003f4047e400fb001c57b680f6c7d7584b52e50045a008b0091302223003fa007e9a0fb801f5103ae0071048dd069a102456008ac19150222a02452008a4091280225024480089008fc001f8023ee007dc00e1bdb3a79674f6c61e58c352e2685c40c8a0111403223044460c84c110983211044220c72010e4001c106372086e460fe8e9fb123700a6f800df031b7
def as11 := bankPage 0x929a8a8a80aa76aa6d9a63aa59aa4faa45aa3baa31aa27aa1daa149a0aaa00aa 0xa98b5a454136291b09a98b5a4536291b09a98b5a413628211b1110a98b5d5a4136281b1110a98b5a4136291b1510a98b5a43422e28211b10a98b5a43412e29211b10a98b5d5a43422e281b10a98b5a41362c2a291b10a98b6543412e2a291b10a98b5a4e432e2a291b10a98b5a5241362a291b10a98b5f5a41362a291b10a98b5a45362a291b10a98b5d5a43412e291b10a98b715a43412e291b10
def ac11 := actionPage 0x711f3f8f402e4260591f390340213c30551cb595c0103930511ab211c090363044192b8f40292e804216a895808e2be03e13a599819028e03c12a289800e264039101d16c0152250320e998dc09a1d702d0c9592001319e02a0a9192009615c021060ba700200fc00904858f003206600502829180100360000000154012000 0x8c2493c03ca3d745c00d39301d2cb0036cf5070007410003c300f00e6cc6580c000a65101f04000634f10201a25915e0000002800036006c77c02883916800153803020006076802dc50509b0191c03857d63d42ca7473400030000d93c03db00838c00065d58000055929c540000b9a5f2000016eae03b440a850009c90393e26c06c0115d4302cc008fe10002f000bc0a40c7201568d140f8031c823000800e0492df570ceb805b78a9c002c7040703b4024030224010420818000000018f08e08000300000400038224114000f0c60012001c02450061800c400038334e00d0001400402800000091093071800000083cc30900020d0c801b00201900000500420400200000e69b3c03470117ca31558000b60a15865a3004933cd7891070000010c001b14038d6415d739374001600700004009a00f4500006c23c068818a30f41400000a00031678040460e2ca55101701448200d00208b00300000534f00a14a0003020003c73452c00033800c320000928b0cd3001c81000000000833c62000ca00e38708034314d00224d3001000002401c824b00000c10000100500018110a0000000030000001861401861c13001c018d1030012557c020064550d00068e00f0021c078034030228a38050a74c00064f00001929971a24018660924664f00919c0132820000081cc1802001c028a30c00009d14400000020538038004338404030f0007053830000002c80c700a3c438020900f3880003c100c0c10903432823c91c01c528030d4c528f54000069c1cf28000000924800e04b08c00d40500000c00f25100314008e24900630518b2441481c00041ca00c38a34018a30900524e0000000c03000090003c900f00018628034400d3cc0041000062df10028319168b0090070000120006004c00000000092c02dc21464000021900400000f30171901d55814a0003c02dd34945244a3c279a01151700624b1c028e6d96c01d634d0d51c0000e00000395f00b8056e03b00d0006cde4c3c202d000882fc08358806b702b9d103d0007c99c1bdb5c003900602708a1800c705e016f15000d6ecacb8001b7c90022c101b081280182000f3b3000073c5586002203000ca5a5fc002e644003e0000131c0a48bd180d9606002912d710a0051ce0c00001800000c02800000002881cc30920724b34c00020018828614f18400d1810c03c200d0050c60c01800003c200d0c000d0483cc18004000900914b00c1450001c100600c286 6 0xedcba76543210edcba76543210edb7210edb6432edc9876543210edb721edb721edb643edc87653210edcb741edcb7410edc73210edcb76543210edcba6543210edb643edb63 0x528a4c25ecfd0606a0cc1959ea0a0cc17c3f87d0eed059f95d2ae54d29a514961f43b87367a54d418a914e2843c8a113a03c638a113a03d428a113a1e55da855069fd3ea4d46228407a8950a03d26a490f21cd26a491462744c 0x3276044ec00960092b00256024a60094c0922802450648808910191c82239063f0087e000e1832940452810a48193b82277004ae04954012a81252004a4049440128802500249e0093c092200244024860090c191c02238063ee087dc00e1002410047e387a400f3002400047c0079400f21f23f3d47e048f0011e0123900472048e0011c0122a004540478c00f1801e20046e7e840011b00210103c600784011a8020e024180083000ef8021d024140081dcd01b9a00003bc206c4011a0021b6841a0081c00f8001d9063ac08759957100228004300085d9501821db003ae0c75000d8aeb4f5761caac392165232ca02466008cc0911802230644008880010f802150242800850090280205003be0475c00eb831d3043a68670800d800232004600081000e93ea841d4501a86c0900801d1
def as12 := bankPage 0x919a87aa7e9a73ba69aa5faa569a4caa42aa38aa2f9a25aa1baa129a099a009a 0xa98b6543422e281009a98b655a43412e291009a98b6543412e291009c4a98b5a412e281b141109a98b65412e281b141109a98b655a412e28141109a98b65412e28141109a98b5a452e28201b1109a98b5f5c412e281b1109a98b5f5a4136281b1109a98b5a4536281b1109a98b5a412e2826201109a98b5c5a45422e281b09a98b5a4b462e281b09a98b5a45432e291b09a98b5a4b452e291b09
def ac12 := actionPage 0x781f4407802a4710731dbf0e801642f0661d3807802b3ae0661936a0c00639c06115b29e009336305d12ae1a419332a05011280f00282b204d0fa40e000f28504c0e220d010926a0490c9d8e400f23d03b0a9613c0291c203a09140d02891a703707908dc00f17a021040e1d40290ff013020713802a081000000013802b000 0x1b0002cf0414880025d05dd0000002930010150001800102c03805402c501c48b00e5c05990ce20000d7050140036507c02c52933160c94547c02c060c70510e0013cc01900031000041a69239d00000354b19c00d01c35c2103d020039f1152c200000a3811022c000038344a30814530a2cc14f0c63c001300920000010a00c0031c038018c0003401802440002000ce5da00c2c000c3530060004d508e30015a19400735a19e2973da00f0122c018544110000601505909a3805cb3480160004da0006444800cb0097803c05d700069e49678000044d14f00b7871c03801074590090001800000040004442c34855c00030071033c01800840000043c01411070001c61c73c000520000078004701044300a00100948008d5c72881d21c400930700000000018021a00300030024d1403c03403c700d2c50001c500028648000720028200d24720418008318f05d01100d34024070c0000160151ca01e0046df58b0950490055c900120e04001a1dd00b0080806d40c01c20002900955404d100001a10b0002cd01009244070000a1cc04841320764624000000901378100100104e00355500000030045c0002400cd30000028038c10c20a2c80070093cc30004d04a2003802c810e28000d3870000060440861860071041001400470800020021022c63400c500300b00500c28018000528a00000020f00c00e28b1c614c2cf00214c2cc68000000000301708001000f67652f0007242d14c000dc0001b34b1069009c000601b75b34e28000e00015f0045d045a6401c014c51c0045741403cb01259901009200028f24001647801b34019148501b3235892164110043804dc0000030401c61c00050471460870071800001440030022003020ce00830020500a00d2833c000008804d00c2093c018520a10000b20001701715f000ed70965c0200d5300059b00e00403a900980000180e039c0740e56f8011101e0ba00444d00880401b0071a84415d201d1c05c763385e655301dc001901bbc503b4c600c4c09c0e5f1de41c08e0173b468064140470010800349b6492800083182d90096400015c000018068301411c44030015300014000a14600318a04000d74c0094810110005c051b3880807992406130cd1d800918b2cd0000174000002923802dd01d7d834500329275d60001600000000710be9e0026402c0d91024000c045407405c8c324d3b7a33e00b08803803501f1058001890030316a4d7a1005863881003c0ff3b00ee9b890c0033040dc0a690000f434088080b0361e300e257e0fe095fa035000c2bb87000b80dc0ff03fb005000 6 0xedcba986543210edcb764320edcba876543210432edcb9871edcb98760edca98765210edcb9810edcbedcb76420edcba9876543210edcbedcb643ec743edcba876543210edcba876543210 0x12aa1d4388310eac7d883a2724ce9732ce4cac41d13926e8dc99d0b4738e319a2be5742c9b920215cce9752e65ccb813d38c5049edc0b436804f1752e6502ce0e01bf726dfdbeb4167ecf1b8b934a293097b934a293097 0x315200ca400144002870050c58a1001421628300506048dc091a8020d02500009e8112e002490040862a38094680280004fe009f8013e8027c004f2009e0012401236024640080c013a81272433d2187a400f481273433d0187a000f400274004e6009c80138a29eb0e3d6047ad14f5071ea023d48679c30f3801e7004e0009ac40f48026f004dc009a400f28126d004da0499c013381266004cc1c79830f3011e6003cc1c79030f2011e4003c8009b001318024e7946010a4cc54517a8a0651408a28c54497a890651208a240931002622c4c20098409258024b0249400928191d8223b0641e0883c00f018a822f50404978012f0125c004b804924012481248004900478400f0811d2003a462a04bd408327d044fa04974012e8125b004b600968092c802590248e0091c09230024606474088e8190002200
def as13 := bankPage 0x95aa8baa81aa77aa6daa63aa59aa4faa45aa3baa31aa27aa1daa149a0aaa00aa 0xb85c5a42412e281b1009a98b605c412e281b1009a98b6543422e281b1009a98b7b5c422e281b1009a98b7c5a432e281b1009a98b605a4136281b1009a98b6543412e291b1009a98b7d5a412e291b1009a98b5a4e432e291b1009a98b7b5a432e291b1009a98b5a444136291b1009a98b5f5a4136291b1009a98b7b5a4136291b1009a98b5a4536291b1009a98b696542412e281009a98b655a43422e281009
def ac13 := actionPage 0x451e3c9a001236f0431cb98d800c34b03f1a3615c01530c03d17b415008b2eb03b16318d400c2c703814ae0dc00e29d03312aa91c01625b03011270dc08e23102d0f229240102010290d1e9200101d10260b1b11c014195020091513001a147019078f0f00190fc00906088f402c0780040204a2009303f0000000124015000 0x1c4b049e00340e0e020780ab151c2194ca203ac0180602c80020ce3816700433004801300000184414053a16031905380c703c67600401816c1a8a0221ad724a67800000000080e0615a368006001e8200052800c609e0180aa4b5e16852040000230000014d12960028a05bd20204e728000008e43140b20000000c829c01010e578c800040360140000005b0607800038140001cd6bc000880e3a10068406290695348e0046010140319c02280068006028004ac06000446804e3350a2ac070a540180077bcc00008e40181001600000a3a00f0286300520020e00010278168401827a000188a01800e788cb701e00000840005034206a00d00126624e83904058167429607000903c41000e06b40440160581a16a8405a80b2000008827414c00ad206018e03cc0001e72040612807728001948d4ac0002c203b1e7000aa511805b404000601b00058080d012340d6d3191943409200055822b23aa02e12aa81e0201e00004ea448010c037d41d1006078000c18e62000c6f46001800e06673e80574001c3589235201000017cb50216d0674e58350003675814a071a0040fdf80179c8a0880139c720ee000003c7ae04230000ed4c0048008f700283c05a80e30000f001a084339733800000140043278114b00024e2700c0900ac109450319a0281c957d0002a05f1cd008a0003ba011d3004c26801bbe5449c8d3c028007de0030000bc520341c00000acc802c0000b396864fca000f680ca8c2e0798cd631e7100ea4b009508001a42700c6300000018820200e508000000e19b402208d0080401409 5 0xedcb7643ecb632edcb431edcbecb63ecb8632edcb741dcb7643edcb74310edcb6432c743210edcb76543210edcb76543210edcba76543210edcb9743edcb64320 0x2564a9858f1ce48f49bc59cb2cac9552a60b1c99612b2549dd3972a4b38eb9bc59cb2c3c8750e60d439796d461e43a87306a2043c87306e1e43b8750e694d26a330f22043c8734ae948989552a227be978c718798bb9552a20a9c6 0x14797283085065e98c0131802900c3ca04a1cfd08231e5103ca00cc80147812837d46000a380141061e4024fe009ec012f231e4103c6049f0112e0025c0051a009ec010800331004f4049e0011801277004ee00960112b00254064a2008a81112801e3006600894c012983250004520889001120128c00518049d8013b00265024c800990092a002540649e0893c191e0223c06456088ac00f10028b0051200a14b1420024d02510fa8c169180020e
def as14 := bankPage 0x919a889a7eaa759a6d8a63aa59aa4faa45aa3baa31aa27aa1e9a14aa0aaa00aa 0xa98b5a53452e2a1b08a98b705a452e2a1b08a98b655a45412e2a2908a98b655a452e2a2908a98b65452e2a2908a98b655a45412f2e2908b85a412e28201b111009b85c5a412e281b111009a98b654136281b111009a98b655c412e28111009a98b6965412e28111009a98b655a413628111009a98b65413628111009a98b5a4136291b151009a98b5a413629261b1009a98b5a413628271b1009
def ac14 := actionPage 0x8b1a4e15002f4b3073174c19002d42c06a14459b40a03cc054133f0b403233603b13390300232cd03412b307009d27602f112e8e401224002a0faa0e401220a0250d259640951cb0220ba18e000f19e01d099d124013165018079812801512600b071087c02a0a8008040b1ac412072003018417801802a00000000e000e000 0x3d60b40000612dc0d803fb0060239c26400c00390c000002124602e89e1c76a40000017232cf8311a0f40007030000f55840007035da71400060074c3ba0036140985032f40d40205147840007d80b100472009c50798c05a2144680034d6145bc560ea0001f78c00452c22d05400cb38030000059938914a80d000000c9e3c041b01e4db70079600b1800000000000c90042c07037403370144d50035db1002762050c801018001b00001259000010e0405006c303625000f75d0400022000090ab48045a0021c400001337564070009a1c00006cc78d74801a30d0157400090000170080150180064401d34512001551c80030c014025e01c4c039201e64814000058001004018d00001a04d7dc3ce4455540120030004d500031eaed02c00020e00400e01e18b00b00938d6402c0180b2801784d00030900d00b20000278d01d2d80c02530100c33143860d62c3a0010e3c36f402d00d0c32400006c00153403808c00047c33023c0008195a230d42484c000a54000e08a02705f0023ee28e1d000000028000c08055300b03d0338401001648120032d0680500ec0000402b5b5a78b6037000c2ca42200b3701d000c3300033178001147503b1bde2d00be40cb1e1b3de7802c006f74003dd93003ac0a290006000001cc1803873d530b68100c08300901514c0130813440060820000094001c654500570c18001e00a08000d0015c02c00d80c614138a2c634058501a0001803482c00853800000031442450050073c70001c914c1841c60002c32c100038030d64034730400014d04670630e1c00005c034018034048000d00055955500c7007c059c0951580154cc4d41c001800721875634a2cb0000021cc0060000c600224c05620d28c3c02c00000182060000042de38000210d0007801c711128500300038824b0ca10f24004028004924900020308c10a00038000900004700110500028000d00704018b1822823801c041f00704039d14501178040c1401c000600800b10000025b2800002051ca78a38014c00b2400021803cb3000002414401800442d214600528800300a3062c518e0c000f0060000cd0cb24b00700234a74029900020900020208024011c0004c039d0100003400053895c80143004003c00005453532c00000004c665100738048d0000043553d548c01e31b00d50868c08464600000928175a29035c1c138a4093d60075c00003c800000001110c68001f10000300314a00b7801800061091412813c56426cb00d11000978c28f5c000600e0006c100c20058001800d0d500a58701c00d01951320135e01100b00c24200f01e7d26516c80063400150086c861701e68300015441e0c054601928000008118400034000000e38020000a28624c00e34000d28000104b0061c1 6 0xdc93d943edcb876543210edcba86543210edcba8543210edcb87643210edcb98210edcb86420edcb87210edcb8420edcb98420edcb876320edcba9876543210c9876543210edcb9876543210ecb83210 0x5eaa8750a9fc06b9750ea153f80c855dcaec5d6ba94f21576e8556b9a02f05d4cf1752e6724d309f13c19ccd9732e066cb9970178718d209e0ca27a94c4187f0fa1e43ba594662089913137cb4967 0xbad4d219ba3337486248cc480181092d6105ac04b080161012c10058204af4015e802bc0257600aec095d002ba0253c00a78094e8029d063dc087b938ee001a900348c6cd9219b0033446628c6c452188882d72b5aa24b547560802c1005804eaf8095f0029c02534087bca4f6831ed043d83a6a800d50e9a3003460cacd59290ea23194463a850650a021a10034200675219ea431b636100cb6c0966942c62857c00acc0158802ac0255600a90014f0029c005360c82d58ea8e9b91d3460868000cf8019c4867690c641973832d90859c04b38115a002b40056000ab81156802ad0055600aa80154822a30054600a88114e8029d005340c82410cf0019e00336a4b2d3d65a925e4f4bcac958b5179d1fc2f4e0009c00136219eb103d600a6401480026f0c4dc867a8094b0026d0c4d6008fc40f3002990c4d2867a0014c0028a004d4189a10cf38129700504009a401338023e0052e00a58014a812910251c00a0439380126e004d0009980920812400047a04a50014a00265005240899001321fa3f3d47e00a4440f3061e6
def as15 := bankPage 0x919a87aa7daa73aa69aa609a579a4e9a459a3baa329a28aa1eaa14aa0aaa00aa 0xa98b65452e2a291b08a98b5a453b2f2e291b08a98b5a4e452f2e291b08a98b5a56452f2e291b08a98b5f5a452f2e291b08a98b5a45442e291b08a98b5a4c452e291b08a98b5a54452e291b08a98b715a452e291b08a98b5f5a413a2f291b08a98b5a453a2f291b08a9988b5a454136291b08a9938b5f5a4136291b08a98b5a45412e2b2a1b08a98b5a5145412e2a1b08a98b5a5345412e2a1b08
def ac15 := actionPage 0x8920bd8b00325610861fb98a009552207f1e348e801c4ce07c1d308a011548f0751c2b0ac01c43b0661aa78dc02b3ba05519a20ac02b339040189d8a402b2b802f17198e002a23a02c169586001020a01e161006c02b189015138a96c02212300e118612401a0d50090b8331801b0840050601acc014048000000030c018000 0xa000d63001e4988054814004031e517000300284081200340ef102208a3cb0c104900004045d2c03dfb0000618001d01ab057c000134f00bd5c0004030000308d87cb9000088c300d2424c7bd90000c0b400102270088dc0cd746f8069d00000600000020624910584921b01a45348078d00c3002460022c22840000003c00000c91852470000800082401c11090030001440090863000000082870800c420030300000c04025d00600a10b00130a1000000031c93402ca0000042c800904000200d2cf6c01c600b6c900000e34135230600800000510501400b38f2c701824404400d00e3400423c10073080cc1c02010083051c00002400000011c814d00f3002012462403062000000002403c00021d214400454100e3007c91081402c200000400031300054e3865c700000420000201814001828f08c24038030129215e30b30030800000908058014300531801b00054904000a01604724f50008101150e7857530403ce00565014b59400200600c0440dd1000004481072000002400005d001120e0130004d001a3c010e4c020020068300001b3d30cb00044a14d0000c14130111861405000000171c024174064601201f0001006c238920f00801c6db44b0004805080400175ce6d644054638400030b04020075f7de2030000085483dc48a40f20059a01b01300000a00f00300000128020029c4c20801003091c001925254064d19300070224665f01325f0104004895400000190801d70005c065c55b00049c0161c20006920ca5dd01004b1c001028b00f0186c044a7800c008514079225038f01468068030a00010035b38000020b50601979024900319800c00065c19a01b4987c501368415b7c008808f25231e08021128d08038075908000f00600004900428000510324d29600000a00470a04000101f0164d708e2c644e58000e00d58201524971801200220b1150c65400540090000007800072de1dd4d104048c0037800007810006002400c820020000010030120620f00b2880c028100010f04b0c000e34a2c02000090022400cc21d01c01254270000001c70d5c401a7c010c01d0c048000000060d58d2400d524025c09701b54134168828025c01700801c0102de18478058301810970000409d01500c00038800074a40051a24f1c264f01a4830006d17413506c04c00ca54051720500920f01864b0403c00c060008048048000201f01b4501401c648c44010b00004941570100004000054029c29a0d164601f19e00020314038204804201000b0001c92c001b61800b61f0047001d65df00b00438058144001500038000000001618474318908701e15738100018e4cb01e10200c01f01830c2804400115050d500574318901028e0000044830cf00008000b2d10000c038000000c04719664a3db30c0c140700f28000a0110dc0042db00000c00f48000074e2cd68b1001c04402cc00400035800b34900048028a1c04002c158628900b00f00010040d30700630b64c00069028200078708001808030014000c50404030f24001101f00a00000d3dc28c6c000040e3c334060010b24000014918008040000501f1c018b797084400797 6 0xedcba8543210dc843210edcb874310dc843210edcb8643210edc7430edc98654310edc865310edcb6310edcb6420edcba843210edcba754310dcba65320edc430d73dc3 0x101d0bad85aeb616b9f15b0b5d6c1f13e87ccf89f33e27ccf8a544a69456c2d8af4bb10a88c1155769fd3ea4966aaed45a854fe9f407774d1d4fa51287576a1d3fa78bb175aea54a9612b0e2b35576a1d3fa79019dcb4760ca952c256 0x48678bac89218d032da045b004b3c0166802cc0059200b180161002bf0057c08ad40157812aa5154aa29181905081f1003baaa76800e99d1fd383fa007407164022a13a3f29e74870e92c9cf2d39e747ece0fd969d0745728eae51d27062293a3f4aa73c00e7832e3045c604b2c0165812c80059004aa00154012a70054e628f8bd1f03204044080070c1971022e20259400b280962802c50258800b100953002a60254a00a94c51e97a3d064060880c00e1243174662ee2b59bd6b032d6045ac04b240164812c70058eb0b0559608fac11d58204a900152012a3005460c8081101001c07f68cdad19fd9536b2a295aa0cb54016393ac60258c00ae809513ca086f4105280419008e9b90037200a85a5071d1f67a5c0f0b804970082e00258600b0dad5cb4ab9495728eae40950002a03a3ea707d61173362e684500d8a00ad169022d2544e1489c00e2c3a888a465128c8a11393a27063ec087d8094f8029f433c0006cc00d90329c04538006b400d40329b04536006b800d6001a7
def as16 := bankPage 0x949a8aaa819a77aa6e9a64aa5aaa50aa46aa3caa32aa28aa1eaa14aa0aaa00aa 0xa98b6544412e291008a98b655a413a2f291008a98b655a4536291008a98b655a412e2b2a1008a98b65412e2b2a1008a98b5a45422e28211b08a98b5d5a45422e281b08a98b5a452e2c2a291b08a98b5a4e452e2a291b08a98b5a50452e2a291b08a98b5a52452e2a291b08a98b5a54452e2a291b08a98b5f5a452e2a291b08a98b715a452e2a291b08a98b7f5a452e2a291b08a9988b5a452e2a291b08
def ac16 := actionPage 0x8231c08e002a4f507d30bc0a40964b306e303706803241d066283541001a3cf04d253299402d34804a232f11c00e31e047222c09800e2f40441f271a80152b503b1aa1a6c01f25802b161ca681231ef028131919c0151b002510149a401517101c0c8f1ec01f114019098b1a00160d200c0505a6c02306900000002ac023000 0x5820070076841911000040170005d20075130003c05907061c10406180483950004051480000003c02131ce4c25470400c21d76c05070157117c02401851cb19a20500001d0965406c96ca1800000057960536400001d00c00190005911060000801c90000010041c700500320020600204518728c04024500000c34804028a04918614000500030310d00f0001c12cc00330000979f48070065600010200334f4c32c000a00025340024e08a51430a2424400002c62cd0004d671a00044848c1ce00a0081c324909e00c0c92004066c06913c00001112c03443810000070191cb15f00500d01e1cd3100161d324a0021000c045c1da20000e1052000c200000301f1c05ce09d6c600d6c01cf3531400000002000880c000d0133c225259d0064800d70030093c030054e49d0000044c62c001a79901a708196007384106b270320003473ef01600680b54008000074b0f7c0004000fec04b7240400305780006000175a3e0001401080140560158d7500340a4600403035a7c6004715100404140000d80005200000f4f1c0244b0832a14dc1f0b62004c9e0000b1d66c20423000030090033c030504000f0051c400f3041c61802c000800018008a2070400091820c700118000108a0c60020401c00001c60000000023000060cf0c208030034034030e20000004020a0190003cc1c028001228020038e2800120002c424944c20405d01541904f00019d38e0c064500000b7892c00006806cf00f01460000d00a24009e18064000a08a70324e61654050e14048a08201e6850430030564146d70040005805d81dd01f0082000402d65891c03a7d237ec000032000e4002e01702d4ce3fb51642954000003534143329380d61eed06941470307001f3018000a71f4876228050001e7c0000180387040552f5d8aad40c18e78c4091b00091c00000a2400cc18000d00004724200c2490c03460c02872c000b24400800a2cb14d28020000638e2090000000080001c814a00108738600014014c28f3402cb3c028010a00054300000034024038534928c38928000020e00400e1881c00040853164c01000c07d34847c06c04de6820ca60001f6c34004160004800000027586862406c11d30d76c000025319b50001500001770701d7c81490161400003c024700050a00000978900000c00d0040091801802400003cf0cd0cd18d00b2420023832ca34234000024c0400010072c308028700124000000c017ed668e5de74b0006ee6c060410300000914d39316f00718001601b04a54001b3802d73c01003c10004800808801c0002a0d00029700c1800da0160009c031b0001054cf5df6dc85400934025610020dd4ee4034028b6a11cb60000614a14300b01e1c1000580020420001e4600e08029974300000d09a00a00300094724004218000a3426de00100900020200700375c2ef2c800200e65e38020b040 6 0xedc76430edcb64320dcba643210d930d9320edb7321edb763edc8765310edcb8765310edcb865310edc3210edc865310edcb8653210edcb6310edcb8653210edcba865310 0xfa1f33e2b616bbb79cf222323bc776ee9dc29f50ca154225139e694b893f80ef55b028650aa12ceba2740e7ace39ea8950aa0a1942e7d2e954280cd5d76aeb53e7c46d5e8ba501e033b86aea7d0b8efa854fe9f21742a7d2a153fa7c85d0a9f4abb50a9fd3e80ea7cf8d42a7f4f92a25342f576a2d42a7f4fa03aa153e7c6e954285501e0325142e854f89e4 0x65f004bd40173002e5005c800b880170802df005bc00a9cc5200323200400007dc0150802a03a44ee881148e92bb2148642bcc340979802dd43488348b41916892220c40a0081484fe0c1c40438822674096da1a4b1d4222284430f9001f21835e086bd5da1243425764690c8d0d8b002dc005b600b68016c802d80c5ae00b5c316b002d60c5aa00b54014fa1a4a1a43c0c87800fa061f3003e6187c400f8802d23f3c2587840168802b92c3a404ad4015a801df68674e6ae1a15b822b206558e69343508801db1c35f0cc71218e40adc065b8deb58416b002cf0059c00af5cd5b232b646498de7cc40f9aa9da003b40cac41158801d90256800ad000ec37ae2005640cabc3109822076f4000075c74e88e9ab0056204ab800eb003010058eacb040160802bb0255af2820110402206563aa0075538d50e9aa6c68cecbadb175082d50055e04ab1d945852342043c56804acf6801d4
def as17 := bankPage 0x969a8caa82aa78aa6eaa64aa5aaa50aa46aa3caa32aa28aa1eaa14aa0aaa00aa 0xa98b654536291b1008a98b65412e2b2a1b1008a98b5a452e2b2a1b1008a98b5a51452e2a1b1008a98b5a53452e2a1b1008a98b705a452e2a1b1008a98b5a413e2e2b1b1008a98b715a412e2b1b1008a98b655d42412e281008a98b6a6542412e281008a98b666544412e281008a98b5a4e423d2f281008a98b65412e2c2a291008a98b655a452e2a291008a98b655a452f2e291008a98b655a44412e291008
def ac17 := actionPage 0x523dac86402f3f0049362abd019a3a204531282940143660402ba5ad401b31503b2523b500182cd0331e2238c01a27f02e1520c8c01623d028119f9c80132040240f1d9500101d401f0c9a95801219e01a0a9711c01116b0190a1405808c147016068e9ec01510800d028922c0a20a200601840a801f04500000000e0017000 0x40607c0106aa0cc7e5982642e05006c17000401dce6b828008100e1403b4a830008038000c80162d4179dab8a80a8ce8f43830000c0dd901ff3c00ae85e1dc8ae8300acb7a1b2c000080e8806d44008f001000608e006000605003bb00e004a917cc18f025884e00980ed083eec390d07b00daf77a0040d4c110281d1240c72812038000180b14020f1584236600002c503f426aa03136f0752000100900045fcb873c0f680a02040d42800e74077000f40320c0000617400476e039a0e8004b80c0600fab800c94468db803172aec800066c1b0402c7680b54c0f0240013580d8000101685819036c00e8dd9800c8a000d840007d9ac07410302a02ec0b102c035800bfc1d001aa806b13900202801f68007350afa248109744501b0018a14800079bc403a4900174000a0140040800b54a010000828059c240d04008c9e048000103e048194380ceea01590eccc80e7d83604101202000925c5b1feb0028d003e0ec720ea140081a719dc41904c30160120006280a02c09110072800000867018e05ac00000044946361c002b1206808020000104403a0a6000007a0c9030405800031cec0088121d8f0104e000070006d2a8211ad4a02c090180e21007011061898153520000e0281802b5e0010000014001c2801c0032c0c19c0203c00230a04900029c273810128000000c220c040140200ca0010e3194a3014e0010021a200021e940a20002003004062a80e441165413024510021700b2d601d50f5e040c40f45f0e00275014c03c1d070b19dc00383c00660f0161f6a400f46f31300004243d580a6000066f60809315033c4bbd140017038dd8007463418b83c0c800ab040d01e47581ce131e96804f0000d001415100000c2a0000000000001400684628460298656a061036205800a581c1db1e0020400ac0049cca332c412c2c28c0401800281391286920182000a007d40003ce02800ce4c529d8929d6180c00429ce7e400010e626c0054c44 5 0xdcba43210d930dc930ed973dc93d93e8262edb3edb732edcb763edcb41edcb8753210edcb8654320edcb864320edc76430 0x80f622884898cd02203aa150c94ce91a82ec5d0a2943ae757ea2d43a85021ddaa14a65daafd43a854fe03bc3774d2152a584ad66eafd46a8750a9fc07786ee9a42a54b095adb5aeb5b5eeafd46a8750a9fc0776ea9d1021eb3766ab9d72ae35c2b2563a2139e6548b8d119d50a532f65de94d265149592a2534a32a1d0b9f73ce76543a073ee79cecaa950b696c2d88a9146282f05087d0f9c06776ee9dc3b753ea110bad85af0e0fa1f1 0x175902bb204864024be40179802f25549e8c93d0d27882330c466008cc81160d22c06458248840178812da5958aa2b150d312ca5b514b6188800110012d8005b086980010fa1ad00658008b010d2f802160657e08afd392d0021a0042a9cb10195f272590443a0085031098e9ab1d34c04b5c016ba1a610c43818864096ab2a89184361886001098ea11005d800ae4010716204005d600ba4015c0020d2c40600ba80174002b70041e58800e918802e70056a008301966802b24e54c9c91c0102861f2043bc3a72074d3292a800540a4924e916801ff0c3f0aa73c0973022c800550b497000fc021d2
def as18 := bankPage 0x95aa8baa829a78aa6eaa64aa5aaa50aa46aa3caa32aa28aa1eaa14aa0aaa00aa 0xa98b6665412e28151008a98b655a412e29151008a98b65412e29151008b85a42412e28211b1008b85d5a42412e281b1008a98b65452e2a291b1008a98b65452f2e291b1008a98b6544412e291b1008a98b625a412e291b1008a98b7e5a412e291b1008a98b5a4e442e291b1008a98b7b5a442e291b1008a98b715a452e291b1008a98b65413a2f291b1008b6a98b5f4136291b1008a9988b5a4536291b1008
def ac18 := actionPage 0x611f3c15c01140805b1d359340163c604f1c2f0b402934b04a19ab95c09131804517291540112e503913a41e8020285032129f8a401d22e02c109c11c0171e90280e9911808e1bf0240c9711010e1950200a9411809016501c0891118010135015050c9e41980ed01004088a00160ab009018515c01906000000000e8020000 0xd0180e00c03740ec00c680350f0206020004500694294400007035c028d6b1826a01c5b18002700cc781967540089400042ea031e3822970084360108c640607845554f92000e004b08894100005782c01bc003834000000bb8801240059f205a9630500001d492b80feac0470a420440080c690350010320037406206d69c03a24067b400c82d3d80dd100418d1a063b601216e7b4822a1e0001c318c05418606000004d2e200000000c5800a0186d7108e5ac0c60001200064116000005781825800e01c0d494680014879927018063800d52d3055e606340105815380003bc08a000fe200ded9c4980000015b052408b000382a5046ab18400c2c1197402017fe9e8003a40d0d000554f006ba95e7536001ec00aa000faf04209c8c70801bd3b60d40cbd012006e8091c00581b20014f6800ec819f008404680b0735b8f008baacbf9edb065200540100002008a0081eb294017856010cc0428000a5219a12f01812d808119408001c60d92003c2045006698a0301404ac001800069c6b3b40b184053854d7818a01d6043c09308001800001089000037980500ca650c6028c882940028c007000f0242e4002003c02480630a4a0000690200403d25088cf580080288032800098044086020001385291814720000014602a02b080e9100004001d89c0f81000fd0eea58e2000021a8ae02dc8036c0051390640a053f11800833c020000c06813b080ba81250328548120000031084000000708600342700100000007952b72c2d00d460806703509039801182e20c49244000800a279a905410ecc0060d93e8a6000051ef50009f1e500084301d0480f3808a183e001a790f43603c1fc401788168040990000f3c01401c603d8cc4006b42400ab403e0160d8862000e6000000d4045206022732881e384409044207ed7f000cd09c6a68dc600039 5 0xedc6321edc9876543210edc9876543210edb7321edb63edcb853210edcb84210edc76309875103210edc730edc630edcb63210edcb4210dcba320edcba53210 0x12b254adc5b4b621c9f53e67c4fa9f3956e91d1ba27412a5d1ba1740e7ac449a81101d50a86432b696c43b8727ccf8c3c8727ccf8c3c8727ccf8c3b8727ccf8c3b8727ccf8d265149592a2534a27cd6d2d8af750ea15268cd5ee0388c 0x17f0623b004766a8e8b11d012fd005c6188e4011c8c1e1043c200bf4017e002fb025f07c904c5208623a00474188e0011c0d2360646c00b48711b802373f46c588d80176002d161506008d4b11924324005f20cbc4196628aca4e594a2975392eaaa5500466208803110022c300586aa95001179d22c10456188ac0972802e000596008ac4115179e4005f000b8c31150022a025c208b20016400229005ea00b800112979e5025bcb49701118002246f5c40cb19bd3e802230c4303a74474e43e2e000586f89ece91308225905eb12bd64146c4a8d8350e54898911340ae56c5cb029fdb13fa1a51204584c8982913119fc
def as19 := bankPage 0x90aa86aa7caa739a69aa609a56aa4d9a43aa3a9a328a28aa1eaa14aa0aaa00aa 0xa98b7f5a452e291b0908a9988b5a452e291b0908a9a78b5a452e291b0908a98b65452e291b0908a98b655a45422e280908a98b6545422e280908a98b655a46452e280908a98b6546452e280908a98b655a45412e290908a98b655a452e290908a98b65452e290908b85a412e28211b111008b85d5a412e281b111008a98b655d412e28111008a98b6a65412e28111008a98b65412e291b151008
def ac19 := actionPage 0x941b541b401e52508b17cd9f401e4cb08114c71b401d474071144007802f3e706c123b1280153a805f11b387c02b3270580daea280192dc0440c278f802c25803d0aa10f409d20102d0a1a07803116e0180a13038023105013080f1200100d500e060c1181900a500a0409118010075005020611801203f0000000130015000 0xb1527933931da00f01a01401a00574650000839b1d245848a0021c06cb74000c2da5563960c319100b0db34b0002c32000002c000b19124041401900764c68f14000000131e3df00518151d69238b49a01400d0000086105d41000000162805992cb01c14100038061650f00a0000c94ce01f0007c20001833c50930007404950153451ce0115d91c00036110d71404400995c02da59c0054c00050c70c00064c001410601500000024d7404802c641644035400500201048544b28015954d75601f01c4946174400000da2cd2060c06030002803d80192c01840896802c00081810004130020000000000800000c948004000d0020186c058900010220019c30644e59d74408100215d41c0d934e70000170c21e01a1cc0c76d434034244c0003566c010000a39f10c59230000314105304e38800020000908b34f00000024228314308038210030000108028800420d00f01a08d1844c111008a3091800042805d32001980137950c07c06da0001590137026c04c054000975b50034028c08060078f1507de05555e35200070034a00000538b00530e4464403490163c468060008815b01e00c11a6003903dd7d715b74000001425648035670500739700f60000001e58040004064e48000500301a00328334000530714719545c2dc50634e00b0401955004c02c40070007803d510934039b0020442800c0947259e5005e000873ff4000c8000001c180022094c8d7807570002f10300c093670208f0001830142c7f4054012ca4023c2550350000e4a8024002601576000a26f1cfe13c800078dbac0369f8034004d0300170000235e632610353a4464a55008c201550708300109d7c308001f2d200504301a2402801d71040001000141cf0000123c00844cc3145c908328000700801109700000001700904700528e01e39c00034268034f2890002cf7400000000007490c000f1803c018c2002150c80451cb00000e20001418c44c2c078409a2870013400c000008e01a18818118001229630100000301629334000000b01634044000f20600e01604519e10744000b1890191872c97c024008601500144034829f0193ec0c000064db00c48d402e75880836bf0007003bb000440ec500c50000b5c00196ed2c00c0109000d4201700ddc001df9630061bbcf00004070c686001700000078400005e5f00d64e75ab66e402c731978e4c800b31e00504d2c020028000a00f31500028300401208738404020000c18704000018300e2820021401020000090001c80053463063492053ca0081050002c90800800003000090c008b00000014b0003c12c024020020a34700004c08024904a10c14228c00f10130500a1020400091890002801871490002090090c000000d30000e3463c13c01c004910200d20408000a1c700038b7853c000000010b00960b0cb00a3800c430700e08000e00925804c0005111d2312244002240000 6 0xedcb876543210edcba87654310edba876543210edcba876543210edcb764320edcba9876543210edcb876320edcba987653210edcb876543210edcba876543210edcba876543210edb73210edb632edb632edb732edc987653210 0xa594a6932a253e7c6e9d29850944f889812f4b294d264a27d0f88987e44748a8ae15cfc9cc9b82bc570ad9150b06e08005653c25c4b097748e889b935744e809a933740e7899930740e789993087d0ecfa9f3 0x1998030b0261008b88116f802c4044fa089e4012c802520061204c18217c052f53351c14a34cd37002512046c00cb8098380307045c20cb78116f0227c064f0089e00128023260864a00c8401900030e0061204c10197e032e50059462a58193f97a66004ba0093c411c0131f0057200938b124ab2240063e00c78018e8031812600c0b780969012d10057062a6409318024d2c49004c6c118c003130456e5e9340125962470665404c8c018e0031b0063400c64018b803160062800c480188892ff065fc0cba8015b18a9831516009300125162460661a08aa001542b25304492009240122813210462000c340185803070060c04c14197e832e60454e00a98c54b83280044900091c01220332b0664e10c8809910230f0061e00c281184003080060a00c100181832fb065c808a94015298a95064fc089180123002430c5223890401208e1eb003d600c0031480628e00480007a80180062820047c007a0017f8628a0c502008f400f3812fc0c478008f0f4f3179e6
def as20 := bankPage 0x96aa8caa82aa78aa6eaa64aa5aaa50aa46aa3caa32aa28aa1eaa14aa0aaa00aa 0xa98b6544412e29100908a98b655a452e29100908a98b5a452e291b150908a98b5a452e29261b0908a98b6545422e281b0908a98b6546452e281b0908a98b5a4b462e281b0908a98b5a50462e281b0908a98b5a57462e281b0908a98b7f5a462e281b0908a98b5a45442e291b0908a98b5a4c452e291b0908a98b5a4e452e291b0908a98b5a50452e291b0908a98b5f5a452e291b0908a98b7b5a452e291b0908
def ac20 := actionPage 0x553abf8e011542004e39398f009d3c904b36349a8093390045332e9b009934504030ab15c0153060382c272600192bb03527a525001328202f2023bcc09424602a182240c01520702412a0acc0141cb0210f9d99801418f01e0c989a809415301709129f009c0ff00f058d1ec01e0a5008030697401c05100000001b401b000 0xe670006008000816d11c4008008520000b5826ac01624c558080101082b8e00054a6a8a02b800091b000100001c24bd2544000000080321f0b40d48ca0e84ec00260f0019634ad2a2e06dc0ca51a8201e702c0dc300c013804300b029cd010087a10268c007087a60007030000010c0017817400b240d7ac6d4800d58c0975800007c0e724a30008e554723bdfbed20000f8e800040520a1000102b100d5274800b20a30800fe8960a9bc018040fa00d0800709ceb0340c01c8e030800380b2d5a36800e0040020407000200346b29c05721811806628060a0002b44adad400900000200734800651e95901a8046008060034150999e3062c9801e182002d000f000e380d602d200016409da56b4e07000c5140e10000124c00014e4800032560790e0201890182079720d000c0023c0b0043802090096a0061c19609cc00c20002019901f480831e2400df58e00bf6c0000801db25382825c003810e403d09d010362e0301ed051201340d4010c0aa5f023800580fc02600016003c8040120400e040d010000a0240502d832388eb042b1880c600c51b1e91020f0a4604004068080695c12b0404980b72800200001800f4a5a013c003092e41942780eb280050081a781e0637da005800186002d600358fd04000358df80a702d2a33d40038c90400d0b4e40640e05740b4006059000000c100c40201d002a068520483750358065baa28f890001a7470fd23e005803d998005ac2103c06a2c5781d8b319783c000680620151e0313296a9100cc2e0090580004abb50c00bafcf2fce0594020018026800b5c88f0a800280dad8110600a5812004800e80877dfac030120485700055605e0002010999c4801506d8bb03002141cbcd84481e0040111004004485b020d078cd5e000ce8004806400c0988120d0c0d8022868180d67100108683f7802dd900015fca74881d3f7c00a63a002860769c004c082bc03 5 0xdcb74320edcb87654320dc98765310edcb98765310edcb731edcb8731e740e70e74e74dc7310dc98654310edcb87654310edcb8765310edcb876543210edcb876543210 0x87b0e8fa29f13025e9652ba527d84c898ba74b197aa1132261f991e22e2c0575887e6e65b59b937045c2c858b97682cfd9ea866e4af1171a774ee5bf3740e79ccb4660ec14dc9b831452ca5117b9768ad059e7e6e85d039e732d18dc95e2a845c6a0d3b45682cf3f67e6e81cf3993725708c529a51498fa09812f4a6945263e82604bdd3a52d554f9f113025ee9c076aaa7cd889812f4a69332b53e7c696529a4ca894f9f1 0x64e00c40013b833210061808b2c013b16267044bc188e4099300326004ca00c951935aaa64004c886798fcf30131e464d258978411f1f9e10064804c68018aa3268004c458974411e9c23a0262c00c580130003230062a5ea28bd351625b1047604c50018a002d02c4c20097c018981311045d05ea24bd42962590262000c40012c0130f0061e0095c118603306045c65ea08bd34802561c3c200c880187002c52f5025e9a0012d802551047400c301984822e0044f6009503115219e4006660cc1c01640227a564b800971592980253
def as21 := bankPage 0x95aa8baa829a78aa6dba63aa59aa4faa45aa3baa329a28aa1eaa14aa0aaa00aa 0xb88b65412e2811100908b8a965412e2811100908b865412e2811100908a98b65412e2915100908b9b85a412e28261b100908b85a412e29261b100908b85a4e422e281b100908a98b65452e291b100908b88b6542412e28100908b8a96542412e28100908b86542412e28100908a98b8165412e28100908a9a18b65412e28100908a98b654e422e28100908a98b8065422e28100908a9a08b65422e28100908
def ac21 := actionPage 0x5e28c29ac098417056263e1640983cf04a25378b402b34e04722b216c0133150461c313480082fd03e192a9b401c2a903916269a011327003214a10ec01a22202b129c1280191d7024109891c09918c019101107c0ac1080140d0e1980920d200f098a9dc0100a200c068719c09007200603041d801303900000001a0013000 0x2d5120042000800740d008f5b03ca4d6d103c003949105c0d026c0e780b47c0a0000e62179383b168cb0b80a411062000000792005c0c015c067465003c508000d14e00540c0366060407dfce000009643017440101443a3ea000f4ea3c9d1800000003b022a89a39a240100589158a80640bf580014bc0c01e76ed6b4834e484090000000192b4f6c06000003d800200cace0f00000e4ce4a87657cb44052a5e3e000276428132b980aec180039b58818000c3d823fb676c4a60d05c0200d4bb005c41809c4c1cb037d034007b8816206802dc4711200284002c0a181c000800a9d080016204700925a74f544302e0015c77d8a0003604822018e2d0140a2801982066d8000e19290217d7a04e205e2701c1012b6103d34b805c82c002429decb0003603cc00040e02404002c181d400e00225881858007108060447c2241c02c1a4291b0741143001869124b818000a05000268c001b9a9897a103400d80200014b6400b18ce05007e70b0903009630cbfbd51500001a80d169a43b9e0414775a84fe000c40dc34812b0000005400281c9880000000000540184080d4650040a005c7028192956e60809024a4000087bfc10000e31c0a681e42b406181ca018295380004020012613564d1f6db0494600020958000595f0562d011d920800d0e330146500a9e38ee016dc027800e81bc003d5002323ba0001c14000004d2df04801ec41c458d97d1c00a412a0016db9c08806614418387d20015403400001600a8090ac080000b323e5383d01240211000484b3011414800919c267810801000004c630348e0009700ccfacc0180fa103e06f9ce045471240c62c8003d402200d03d004a061600a072c4f581e003c0f0084001101081e098c104f41fd240e00cc0cbb2b66d8610000100a0040e100400f301055800ce1b7026c028083e83a109944908008e66e03ac0c1a000000d00ec01aecd18980053600649a 5 0xedca8753210edca87320edca987653210dc98765321030edcb987653210edcb7310edcb8765321edca754321edca730edcba9876543210ecb731eca7530edcb730edcb43edca5432 0xe80dd1732d05082d3a02e65a0a105a20416a2043d8787d84c51b8f11ca12412798e896e1e73985f88389fa5d46e22bce546266584ad958fd5a49cc5422644c4ad954e78b44ad954e78b44ad954fccb41672ca3b25539e398728e49c62d12b6553f3732d18e54b195b2a9fb3f373273258cad954e85cf0ec 0x7300026001ca64094c862970052e009cc0196862960052c009c8f93818a701e482249040196072ff0c5fe04bfc017f872980c53004a60014c062950052a009c40195803260052800a4c1192803250052458a45193821a703f4827a904019497a902c51a5e9bc711b83320005185e9b4b136aaa6410478188f0018f812ec625bc00a20b14031278314c604ca4018f002872c4fe909b84920202360265400ca80994003280063a04bac01758128b0051600a18b13f0032a0063000a2401421627d625bcc0b782941802832c4f800ca4b13da31e55a66200ca00174802852c508589e401978128f6250658a0d893c16278
def as22 := bankPage 0x96aa8caa82aa78aa6eaa64aa5aaa519a47aa3e9a34aa2aaa20aa16aa0bba00ba 0xa98b655a453629100800a98b5a412e281b130800a98b6545442e281b0800a98b654c452e281b0800a98b5a504c2e281b0800a98b7f5a4c2e281b0800a98b655a45442e280800a98b6545442e280800a98b655a4c452e280800a98b654c452e280800a98b655a454136290800a98b5a512e2a1b100802a98b5a422e281b100804a98b5a412e291b100804b8a965412e281b11100908c5a98b65412e2811100908
def ac22 := actionPage 0x6e30ac8e409f4080682cac20400e3de0622aa812001739905c28a292c09835105625209d0013318050211fa080132df04a1f1c11c09729a03c1e180a002a21c0351c1292c0181d40261b0d0ac02a15601f19878ec0210f301614052d40150b400e0f8424801307b0030a8229011a02d0020501ac4087018000000028c208000 0x1600150500b1bd203372c76ffcb20c0000000389998220fb1e80140400125058e002374a81c0abe804940720cc10425a06cb5d941802b56389a0180600000d01403038806804649d013ac0400000714275b12b02c00000009fc6927017008048d000000a06441e000001a0089800be3a004846179cc6098dc480f4500074eb40710c0064cf0006000020978c00000252ae048000000ec5a013b4c0d00a2c32d0098000f99702a40a7baaf00560e012001183020a07b9e7381203bdcb7a400d9c00001c91816c61bc64ac260000000049000a6380090000018d270382302943208007904000080028046b82021ca0010c058ce438dc80140540003000800000f0380f9a00803cc909c8613900034612141a0080b3a76b090003010e03906209e7480002204940120e80ee000010bf0000700000c4618c1b0040002336020c080004448073804308e0861003538e01c070282e181a01100006cc22000138f2b01dbd30822084c70140b3480600de049170408ae01ce06498017400901e2d780b029854880d16800f0000001406080e7940903b932100bb818e00220030150485148c02024605a81008017000f435aa05a80306710c940000002381001e8001028018143ca9b7a80020c0013f401523084016b5054ef496001a406e80000121403810626a481403080019000060a702f6d1809d19c9402927045c04904322d830000001f8335150381ca59140070ef3bc000000e000005036040000e7c0c5cd4b095a91dd09048003e60000d660480143d805e001f5000b30037010202c08c540377402da5601800100c4c02fa0582c01bc09780093000839a3300000501a622806df5c0481d5485a02a19101def7a06c0000fa38005390700c071801430760000f70041774d2002a16918c33f88001260783de034eb079e00f19b5a1760000a122a605e687818c01c0a001400358e03d023a4090300702c603384000c4a61d22 5 0xedcb643206edc76430edc98654310c310b6edc6430edc76430edc98654310edc98654310edcb7643210ed7437476430320 0x2be574ae2dd5b8b69678a511c2343c2da5b023445ada5b023445adb5b4b611108d1160696dada5b08904708d11606d6b88d1162244688b5ae2344588911a22c570ad15951a68cbe97b1562a4528a2a992ca57a072c257cac7f0fd9faba25a12162043f878b41522a2542954fad897eee88e99cc3525d4b514413e095faba03a2728d39732d05084f023 0x1d2f3434ec189d8013b2aa2f4645e208bc19a0ad2f42f5da08bb4b169802d30267e70b8cb165802cb4650420a08099e003392c59400b291940882810068400ce4b162802c54651420a28019c013362f5d208ba4b162002c4026805eae4115c962a800550ac8a419a3803400067e00cf8019d18b000660062bb01976302e12c56e00adcb153802a70267a08ce8019c17ab80457058a980153033460268400cf4019e0033b0066e00cd8c57f832ff315d60cbacbd5b022b62c54a00a94e96eab2450048a8c7fd0cff881ff0c3fe00cd4199a02334025e000bc00177812ee005dc00b5001992d3312c66204cbd597d002fa565da00bb41199803330466200cc401980332e005ee00bd8017a022d3005a6009d4019680274
def as23 := bankPage 0x948a8aaa80aa779a6daa63aa59aa4faa45aa3baa329a28aa1eaa14aa0aaa00aa 0xb865452e28090800b88b65412e2815100800b8a965412e2815100800b865412e2815100800b8625a412e281b100800a98e5a412e281b100800b85a4e442e281b100800a98b654536291b100800b88b6544412e28100800b8a96544412e28100800b86544412e28100800a98b6562412e28100800a98b8365412e28100800a9a38b65412e28100800a98b654e442e28100800a98b8065442e28100800
def ac23 := actionPage 0x5d21b98380233b40561fb313401736f0501e2c8f40953300471d260b40282b80431a2319800d29103a15a324009125e035139f91c09122b02d109b9a001b1da0260e9712401719501f0d128e40171500140c0e0a40280d8010090b19800e0ae00c060899400e084008030699008d05d00501830dc00e03300000000d8011000 0x82b50001c03000006c1fec16e2a58d019250000023876af8235001101c3d00de0b80400001e4a020a8e4229861e0a6b05d0101aa8f640ab4c004b00020ded3bcc0368041000003355313209201d028e9000c0e60a103d290011c21c00fab4b93129534005000001ccef03656bc150036e0154ea024bfa197d0810c015205000603585000506400103f6f82808b088a7fa0a640d0010e22cd70440003c04481dfc89e03880000221002aa52e806dfa0e00e02996007fad580d16cf9bc0c00018b3001634354a7a1200d4f90000c1942c63788e01e0c8017044004f89e626b000400029405806e28880015221ad0a00043404000000a79560f0c132300d00075275075cfc348040500e003c8008320b805249c60d80080744403c01680a058005000896804d120000204a080200284828423611e039000000a019ae127800ee1e00bb9307000abc5c6b24902410079c00301c021c50000007d610713102a405f4e0e8305b8000590a0017fb36800031a100cecf242021ce000e0052c8003807010002140d02da63e7001000e301a57800a0024d62de82980403d8b501058ac0c0508d0254000001000600ac8043ce078131294c05000a2800f01d405000e21142c832078de1980dc002a803d00043c40800c0c480902a90741e501402fa5b5fc60519204977e11c115c18556c0702f60e02a04035a7c0187bac3e5681501e5bd5c0080010000907061000034318078d8d7000a0340031d80280ae7244302005580e5384094200928c023b4010002908005099a202de0030e700800230e050c24309430014c000000380b7100f398c9029400002830002100c0301c041d20088000000e20149181a0610e830021000e82880638c02500007080202c00115af2800a700af1002002c004940a78003384e73ac0d 5 0xedba9876543210edc9876543210edc9876543210edc9876543210987510edc7430edcb4321edc765430edc765430edc76543098751098520b320edc6430edc643 0xb684808e11ab684708d1202396eada4442384681a7f0fddfaacf33e6743c05e054b716d08e11b6224d2c03746e43ead811c23445ad811a22c4708d5b6b611008d1160656dad8440234458195b6b611008d1160656c08d116b604688b 0x19a882351006a210d3009a60034c0667608cec019d98b192f63258c64198c823190063258c0c018181347355fa58bf4017e9f2d2315a40cb48d57e162fc005f8aea45214889291375fc6abf8b97f162fe025fc00bf8d57d962fb005f600d1cd57c162f8005f00cd0cbd7d162fa045f400be9697bab2f72c5ec00bd801a2962f5005ea8ca404148003483a5e4aaa31194621a8c1051818a300146003402c5cc00b99897098ad1065a2c49f009a28033f3a5f058b940172a428e1251c04d1801a3013440068800cf8b975162ea025d400ba8b172002e40068e6ab8cb171802e30068c00ce8b171002e2625c2c0b84b170802e10068a58b800170003442c5d000ba0b16f802df
def as24 := bankPage 0x95aa8baa81aa76ba6caa62aa58aa4eaa44aa3aaa30aa26aa1caa12aa099a009a 0xb85a50452e281b090800b88b65452e281b090800b8a965452e281b090800b5a98b5a502e281b090800a98b6545442e28090800a98b654c452e28090800a98b6550452e28090800b88b655a452e28090800a98b655f452e28090800a98b7f65452e28090800a98b8465452e28090800a9988b65452e28090800a9a48b65452e28090800b6a98b65452e28090800b88b65452e28090800b8a965452e28090800
def ac24 := actionPage 0x912d5b2380a255b0882b549340204fb07b2a4e0b401d4a4078244d308009489075224912001444d0721fc396c0144110661bbd23409f3b405d19361780a0354057152fa3401b30304d1128a3801f2a603c0d22a3002323d033099b9f801e1e30260514a7802217d01d018e1f401e12300f00870b80310900000000078030000 0xb0173d43086000005c62bf00221e2803130002400135d218a75447633e1407c04763c363c2800003c001929d0003c00002c43ca74565100e2c07c041f00401c00a00024800e09371108e27f0153d819b38075f09c7c00001004180170020000000804c000c1ce2850046840000001002150c00010005036451c22800001c100c30000625c39741500001c28a58c00d14010e7c72c001f0494494c019064620068031d0012c001901a50001b1550401162de0005db01c00000244008828144000730614004024d0153004c04da0000806001c374021200100f3590040000031c330b1450001001403552872803803852061400c114b18f00e04a00818028924700000234600d3441c80000023cb1033800000060000002806002cf34928728058c35820301201000100038000400000000a00901210228114000009b38a04028018024c250200397450008007010340000a8064070f4d030074b2db3c804024034400044068008330e69f5c01c421c08061971200338010c44040f00c54004230000001900019b65100a01b1974007d00050091993c02c70007160100000103000000130034ca31b0c46806052c94802920006c00080001991006912c224c3c778344000458100e30019011f0c50005cd5cd00578e2400005803c015e00021439a6400060007c10000001d745a0c070605648628000020035038041315454d0005004861404c03db45608744c34f54d5960190005060006920140907404c025559818400010b00a0015c000a20731e4d500044049918030b0037871c000201d29130b0173c001c0003d12130120d800060439b0195520020198487dd4d100e3403120001091172e618c2c0440740201f1800008500710001900000068000064b44670b6c8adff0774100b1000556013150d83950000406404819003d52d701b7004030002855c41082000405d310a00e7402090cd01e34071900000001638048068f75f01c00631748874201c7c02c279015500640000800e1c508c0000042800c008051e24b07008000d680109a4001c4cd749f40f970046910800006cd8e53a558c10d5805fd552ba43c9080005d00380f400cc000444900add000f89880005bcd000b5701502880f003000000d4620027c4c30000d400218b0157003cd00070000100001a20808c24020a00b78060964c00200030c00005d2c61c000c0001cd34024d60000000820a20b25604105819c08001401a70010c00631f00a00a2400510042800100000005c97830050c22010c07105020003192001803c510114031941f0012800077506442dd0000126ce1820000c010a04000b00d74a0000032002910832801da00700400014d34c78300605900001c0153031560132c800d68050020038001728c2000190070000153400051040160495013804c404810060050000d6c06d964000d00060400000a28b00034401a1000064051400c50df3552937400130d074001f50401208d7d01c72c00c06400007001ca6c00060023800c000b0006520004cd00e78008a41f601000 6 0xedcba987654310edba987654321edba98765431010edcb7430edcb9854310edcb987654320edba9876543210edcb987654320edcb9876543210edcb98765430edcba987654310edcba987654320edcba98765430edba9876543210edba9876543210 0x2ea358592674b00f010c09cdd1b911a0944682570cd51709c133a4c88b9061da28c4f09811a0901182211a15c130230433f603b563726e0cd0ee04857caf15d11608d9619a2be574ae0d011608cce99a2ba564ac0b111608e7e9b9370674cd0b10b2099f41b93706409788b0466e4dc13225e2c4458570a808df89972ba5709788b0466e411823 0x6a600d4001a7003422c64600c8cb19100322316380cc71197f882ff385fc8ca60414c0034b0667e58c84019098b1e0663c70bf5194b882970269e00d3cb192003242c64000c80e97e1c2fc4852c8ca58494b082965d52404d2401a4aea93006a458c400188003512c61e00c3c01a78034e0069200ce4c5968332d2c62a00c54b1870030e4647a208f419a0023403163e5ec7c198f8231f2c61a00c361d280334b2c61800c30d571a1a3e0c47c04d28119d00338566605ec60118c163130062658c2c018584353026a600d3401a6023370066eaccc0c5960332c2c62e00c5cbd89163120462400c48b1850030a0069614d14d194853292c61200c24f17c252401448000d2819a3033440066d08cb8c5950332a316500cca0b188803112c61000c2009a5853472c60c00c1931800b300425a498a64594c833520469400d28199f0233d0067a62c74198e97b1b2c63608c6c018d963050060a0cd5021a70134e0069a08cf0019e17b1a2c63408c68018d163040060874bed214a89295
def as25 := bankPage 0x7e9976896d9965895e7957795079497943693e5934aa2aaa1fba15aa0baa00ba 0xa98b655a4b452e2a29a98b654b452e2a29a98b655a4541362a29a98b655a45362a29a98b6545362a29a98b65453e3629a98b655f453629a9988b65453629b88b65453629b865453629a98b5a452e281b080700b865412e281510090800b8a965452e281b10090800b86544412e2810090800a98b65452e2815090800b8a95a50452e281b090800
def ac25 := actionPage 0x9f1d422e001541408c1bbc8ec0a43a808618b69b009a35a07517b08b00292df06117ab02c01c28b04917a582c01c23703917a002c01b1e602c179a82c01b1950221796024011162018179401000a14400b139221009e0ea008118b9340140ae0080a8bb8000709900509070e401505a00207810f001401e00000003c810a000 0x301d01e01e7c04c100000a0021c00006083902dc0174147c064c3d344324e41e00205874630c00129501c1400054470001d83430003c00009c06c000046920028002210402a4c0380581ec101b25b52400830c4ec0187815cf2401434077810102081c1c8039b6c00004ac1411d75c0bc939d00045fb00ac00006c03854d6a0020750778c68859028019650019301a28b3842c048320000001770a01800000000b3853404c065800001100a2590090150001800c815d1990802c57401800000006c83c570008501e2c07c300068001021d35f00c00d6c03dd3940001895c07ca58001768600361661b0000003125ca00a68950a08660900070048028a01760064100b3d600765000c5420116c658045e34628030810201100000c40d00474001b2d000d00d0001800004402402801904802580c01550080162401da3154cb6c168028948924c2800cf0004002c041924301b64961202100728050e68d141280009000000f510150050003006e334c31964579100c00002b12084001d24b09a2409840c50065d9f8f6c01c20072401cf00820770060054900e5562c73805c03870021421c054010e00a0001c00000031c80806800147c02da4405c04c000f19518715300035028014901044b7070803db41f6941c064069a3111080581420000577df7d50002cb6927406cc60001b00131600d28030a00700000000919104018000840e01a70045701d0191401cc74e00f5c00002c000800734514024901625c0041c814054a0041470043406403c028000210d00c3440c52c00001420071402c000028e0ce00f00400b00260f18a01960064500c2d02401863910031802050c400038000040074001100d00051a00f6800003d901f15c2401860030001d97da1101192803001861560001407c028c21a00908508e24740920001d0150031807dd44a30000b4401807137970000000000120d33d708065f30800540000024000e0001400070c228018428500904004204028030000920d0030c500314e00600338b0001c32c600c24020130020024c1003060060000482400070c00003800c11c014738400f00030814d00108d28000000040018120400011d2862c564f34904a3492c030000500918f4d134000300004000960700000010f00e05d18214c 6 0xedcb6420edcba854210edcb76543210edcba6543210edcba543210edcba543210edcba643210edcba543210dcba54321dcba6543edc9876543210edcba7432edc98765431030 0x403804ed9dabb3702a00ed9982f84a201b5c500ed5752e85ce84c30bb3426b796eadb44623c4708d0352c0598900b56264ec72592a190c99f26827c4c88e10c16812cb195a23847025047752c7b2e60ab856419d26434c610a313c26046885 0x2b3c81d790aced875db0139f006bcd52e9225d38c260684ce30381a07003a00073e00e7801cea739c007389ce1c01c3a7361006c29cd8001b00035d568a63b04066080ebfa197f40ce658e71244ae0681804f7401cc803970072c00e4409c800377006e800dc001ae0035a006b200d6001aba44ac0684e0d02821ef013de0473400e6801ca803930472400e4801c80038f0071c08dd801bb0036e046b600d6c01ab2f4b45d968b12d15e5a09ca91295293279224f09c9e1293c08e1001c2003820170000e0005bf8037f006fc08dd401ba97b552c6aa08d5401aaa6cb3489662f2cc4a59c3caf8395e00e0cb1b980373056e400dc815b880371436e018dc019b6c23a16e74246e850dc086381007026adbcb1b78036f556dc8cdb841b70036d5e71cb0e3925c709b8e556fe8cdfd0dbf8837f0c6fe00dfd75bf2bb7e556fc90df919bf21b7e126fc20df831bf0037e0068736d061da0813410068262cbcbd978332f0465f10cba1d971632e0065c00d50b1958032b006a458c9c0193803542c64c00c9801a781349
def as26 := bankPage 0x819978996f9966995d9954994c8943993a993199298921891989118908990089 0xa98b5a45432e2d2a1ba98b5a534b412e2a1ba98b5a5145432e2a1ba98b5a5345432e2a1ba98b705a45432e2a1ba98b705a4b452e2a1ba98b5a534b2e2a1ba98b5a514541362a1ba98b5a534541362a1ba98b705a4541362a1ba98b5a5145362a1ba98b5a5345362a1ba98b705a45362a1ba98b5a53453e361ba98b655a45432e2a29a98b6545432e2a29
def ac26 := actionPage 0x8e3122a5800e44a08c2d20a1001041a08a2a1f18c08d3f3088259da4c0103c3085221b9d000e3990801e9a1cc01136606c1b181d00242fa06a17969cc00f2cd068139520c0122970630f93a0c01425b0550c909980231f20400a0e95002518302f070c99002311a011038b9c80280a200d00869a809306900000000740a3000 0x3403400ca61c4c065800001459a00c3800001dc00e3c000109a01121e74934e1401c720d1c50003801c124908010300020600e1cc00018700600530d0000002801011802800801870070002cc00f00818014d08b1852cb28028d04014a2cb0000001400053800c00003040492c00090000041003801c00001c004414020b1c00c71c41cd0002c034414f0000c700c04f1050c000c10020008d00d0003c80011c83481c800008c0421891c708b0430c000030c0053800060031001c000524018e00c0000c000424700014700741140919c14b0121c001100701000f0112cd5ce0002c06413190c048a01a7060096400114000000124c028d4c164039f08414c44015b20c4c20001436d548000f00070001f79e50024000441e00e38018100e0032402402cc0c000018c0c01c71c00c72c01c010024000000e0c01c50ce10010000a20e00024700414008000734f0801410000000000801c42401c30000c83c30051c71071c614200c00f08018000e00930f34000000714000f00220b0051860053cf1c814018e34000114500100300210000735300038300038420654514400200a30025b04009520b11c00400e30b0000002130101101420152050d768b68029109d0803053cb00100070e70008019e28700834d00001000000704011a28018d00750901f00048200328f29301f00b00845f00e2800002000005c00002830c000000701165050000a15961f0005d119574b54f45f74028201c28f60060201d40f2890d628649719420001649c01238064668801f45a0140151c000360419a0000060004942192c05150020020006030da0005864970006401444cf41d5823c250000d0160002806dd0026800cb3806805d105f2c000c00855f00001f0802803c219b01c4506cb8400c03004c000000c08301401978000114408060384058210000019e7070110231190037842010187000004a07c098700d0047d303b01f02304ea034805000c00804410c04a1c1c78510014401d41900000030b78051a5800080053c010200010b00b5cb4006840dd2c200b00b4c85cd28b0191cb0001c001714000010834004e5c000000001604000f4423534000001c030a00c68908019134000911f78a28b28138e7800087cc1820120000141c931000101710200000400409d0005480d43c02dc01a1c03090022c47d60033c3013 6 0xed9430edc3d43d43ed43ed3edc3d73dc3d43ed9743dc93d943dcedcb764320edcba87543210 0x15e6adbd2634c658c3173323eae3d96ab74fe9e53b806ed6e3d5ba794ed752e7b8f65aadd3fa794ee01bb560771ed6dacab74ed8c315b8f6b6d655ba7700cbe5e9b9371e9fd3ea7900eadd3fa794ed752e85cf65aadd3fa794ee01bb56075e6add3fa794ed752e85cf7a69fd3ea7900d09de9a7f4fa9e403b934fe9f53c80684ef3de6bb76f2cbd96b26ed5c0b7662aba8cc2ea 0x3c36874c20da419af8235f026ca00d9409b2003647983c3aee809b1023ff0078000efc75db013605da02d52e5a25ca44b9469720d0141202b8c046f8080d0101202013c10078204f0001e0003be026bc00d7809ae8035d066b408d6819ac8235956948ad17075fd0cbf9066b0b12915a52244a44694836ff465fe833fd047fa36fe865fd033fa047f40cd5c11abaecff489468d28c0225033fc047f804ef401de813bc0077804ed401da803b30276400ec809d5803ab026b800d7009ad8035b639f4013e58e74244a2047fc0cfec01de013bb0077204edc01db003aa0075200d6809ac00357026acbd3f9767f2c4965792cad259564b24c964892c8f2591a4b0fc941e9283b250724a09c941292823250424a004480275e00ebc0dd7013ae0175c00eb831d6003ac0075004d5401aabcc121d7963aee809d1bdcd66a978d52ed69e4013c30074600e8801d08038b0071400d9001b180362
def as27 := bankPage 0x7e8975996c9963995b8953894b894299399931892a7923791a99119908990089 0xa98b5a594536291ba98b725f5a4536291ba9a88b5f5a4536291bb7a98b5f5a4536291bb88b5f5a4536291bb8a95f5a4536291ba98b715a4536291ba999988b5a4536291ba99d988b5a4536291bb6a98b5f4536291bb88b654536291bb8a9654536291ba98b5a45432e2b2a1ba98b5a4541362b2a1ba98b5f5a41362b2a1ba98b5a45362b2a1b
def ac27 := actionPage 0x5c213c95c02345605a1eb915c1114230581cb49240903f30561ab09200903c304c192a8f002834b04217a50ec0a82d303516a10a002226d033139d1a001123a03110191e001020a02a0e1392c0231a10200e0f02401c14d0160e0c01801b0fc0140989a5410e0d2012058621c01509300f028399400e069000000015c123000 0x6cc0055400007da6000d80e9aa50010011074c004818051651a800d84965b41401e0d601c0185b500003d1c8c0796600000068d32c4a90100f001bd9011168061ac0020098a000000856f0006018d450002a28c800240001cab08c000242001c637a44b78000009007a8085280d59d47584007200603544728cc598e00200071c0028088024651a96c22cc0230c02180c580e0001400116468c602140178c0084c4102d2e3cc147c9803ab6681a6000c4f1b02517dab56da2f25e40000b03f673b81ad801c0640370180008eb218004b989880006bc00c3800f83c00900ad832f0000000260d918e41e206801400003a01601194001000000175a7af056200692606db5281710207a88006044067010e98040b780b6802b52d0b15c40512e8070002817807c132a94088320280095d220746c0a9a60eec173541301b46a8363000007ec1500d12c8ea6281c6d100a81d7300000028ee45560181e205c5dc8c1409260d8081d8ea1000600a8200000c0004ccc22d0096a0000671002500c00808f00c0040000200025b02e0800b1008410c4578c013010a029da1a180009c0000684a94700008781a2411c00340c198ab1b400f18000003f10000150b059563d9c0d11040480e0028e057496b800e508a003643126ab680010080651842008e004a4001e60000ca200941801d00800eacc216da058329244e0b108a2980002c054fc00198a0001cf4d803000033100005c28035a7088ab2804501400000807240506800401a070000610ee009070000070c0052046705e71bc4002c0002c00700ef7148003ca05a9c04994b78007000cb5a00c03c00215c00010101d893b9a50140f2280b7a80d69c60009c0018a358c00194e002d22801c4400056302300127101001a00052c04005602018032ce000c003812062c6049ccd040a460120200007808002dc0498e77b401001c139ce81200a481c0090e08241f0641e001b51380b02700cfcd4526e0b381f296e002a27be486ac600400da0029e0240a883d8c01a00040ac80000778c0397f4b240e881a85e6c2841353620 5 0xedc6510edb6210edba65210edba6210edcba6543210edcba643210edcb6310edcba510edcba510edcba643210dcba54321dcba10ed430edc4320ed420edc9320 0x165ecb593006006aed5cab74ee9255ba7949a9255ba7949a9256dab7492b6d5ba4949a925d0418784668150295e93c1e23c27806682eaf35b6add24b9165aadd3ea79492023b627f56ea153ea79492023b627f50a9f53ca484fc9e56fa855069f404 0x1624eabc9d5693aab275264ea449d4793a8d2744e4e8949d1193a212740de9013d2017a400f4809ba80375006e60cdbc01e880372007a00adca2257c4465007a2d2e8875d124b91137228add039ba003718383600f4001e522bc90e792d2e8c75d1a4394127280adc5fe7ebfcee6d9b00cfdc01e6813cc0279200f2001d5813a9026e800dc009b705bd1087a006dbc01b7c84252a84a8af3039e6003ca697143ae290dec863d9007b2b0e4155c824b904672026e4041c80036d5d89686f6031ec003d85771eaae3d21c7a338f1271e20e3c09b58036b026d400da801e2803b1006d2bb4015e52aaca54894a8d29409e2003c40e76018ec009d8003b0026ce00d9c09b300366
def as28 := bankPage 0x819978996f9966995d9954994c8943993a993199289920891889108908890089 0xa98b5f5a45362f291ba98b5a453f3e36291ba98b5a45403e36291ba98b5a59453e36291ba98b5f5a453e36291ba9988b5a453e36291ba98b65453e36291ba98b715a454136291ba98b5a4f454336291ba98b5a52454336291ba9988b5a454336291ba98b65454336291ba98b5a454436291ba98b5a4c4536291ba98b5a524536291ba98b5a544536291b
def ac28 := actionPage 0x7e283f8680154dd07c24bc1dc0134a407a21381e00144680781d34a1c01442c06f193022401c3d8063132bb2401f37b04d11a60ec02a2fd04810220e00142c10460d9f1580102910440a9c19801125e03f081716801721903407118ac0271a402a058e0dc02313b01e04088ec0230d201002049200230690000000124023000 0x304800c08c00d00c20000d18810000000514500100004010010608030800028000014000038a34714000a1062c01050001473003c90030000013c72400053c614000400b1ce24d1c004620714900024800330030a04838000a38200d24900000900d00000000e00e0061803000172c50490053c93891400002072450081861c83873c10081803df3803481c400a2470000001cc00800724f08010b38014428c14114500e20808000404700100700020000d00b74011400000110f00801100000004a24a24004d0006882d114078064038a00244030770e51018515049d19705474000914020000d3495400086c628575220064078b4010061d13c02000254c94c094e00008f3c10051c6016600ed24c00c03dbf4605e04778578029451d00da401c55c00004c035c0002b17bc2c100e0180004c01de0170000381c04c0dc10175d96010080c01d6440280540021681e0a4ca74000075f0520000d71da00100019028001825e74058034001f2dc5402c05001ca049a40e510401d05d601b4bf051494363e5c00f580000517614400343e403e302d0380000030073820c02460020c938000018714304034400020c28430004400300b24114000e28c2cc3c200e1403c018b0000012451003011ca0001460000401c01400c728028430424b18024008608114800810410620928000a28c0002002c01800000002812400cb3c300814024000b0801c12012c118428304101400565200830025000011f60700038a04000b00069a29001a4ce10d01700f48c0c400005f0890ce6d76400000024400133c02500000007d901700220030d0406577007800472c048e05715f4400005956405130c800c01f0404097c011900f4480000047cf0003c63d100014825e6070001c07d52de01714105e6c83c05db3c00182990075c045e00300500f7c00020000406554000173da4896000080000110004cf2936003c10845cd4952c750008e4146c061000901a00001531810010319d0d900000d40030018308025538001e4142800db60601c01830001f0000007c66436005d74d118855f79a0800000000195847c000b00e5807966db41c01705e7c96c77c03471807c02c01c03535405130400051cb35e10438c01725e00058c00200000504a3481c00122c00004c578400e0003c07ce18a3c05800040004005060030115403432866431886c024f00875b11301938c14100018000914a7d50970001cc08a30324b4400066400006810000030001c215558001400000078c3495816494540886da71a0002400400005cc5407870036407c84c355000e01d5925005002dc3005c00030c01423004de00000d0c92dc08210001818c0005ca0c00003823c81c7 6 0xedcb864210dc76510dcb65210edc6510edcb65210edcba6510edcba543210edcb6310eb7310e73210edcba75310edcba743210edc7430edc98654310edc73210edc865310 0x524bd965ab856fadb43a735e7b2749a924998e31baf3de6bb7666cc597b2d64ed7d96ae15b6b655ca4d492f35d2b9f64e8646e8d909cf102e006006f3de68dd4ee93524b636c2d7d240016be9e53ba48004005afaf2b90008005c80069352400349a92001bd34fe9e001bd34fe9e001 0x31e734b8d0070c74df019c2823850070a06e0009c2003840088e18f350dd5863ab1d71600e0c19c0b4b631d6c6212991a49884932384241085ba03364062380c4101801f101b8100702bb3915e5a89cab12954932804e502449f1293e00f6401ec003d22c75c00eb8b1d6803ad5572a00e1401c081b7f106ec8cd6c41adbcca8798c23b04065fe83374006fa3edc849b9883736894f3108e3e1187b7c006f8bb38dee58b54b00482000f5c01eb08398006fa00df1a1bd0fb71068340906809ea803d50279c00f3809bd8037b026f400de81a0c82419027a800f5009e3803c70278c00f1809bc80379026f000de1ee543cca86a950d12a06e080cc1006820090406dfc8cbf9067f208fe419b802370717f0defe019fc023f8027a600f4c09e6803cd507549cea809d5003aa026ee00ddc09bb00376
def as29 := bankPage 0x86997d9974996b9962995999509947993e9935992c9923991b89129909990099 0xa98b5a45362c2a291ba98b6545432e2a291ba98b654b452e2a291ba98b5a534b2e2a291ba98b5a4e45362a291ba98b5a5045362a291ba98b5a5245362a291ba98b5a5445362a291ba98b5f5a45362a291ba98b715a45362a291ba98b7f5a45362a291ba9988b5a45362a291ba98b6545362a291ba98b5d5a45432e291ba98b715a45432e291ba98b5a453b362f291b
def ac29 := actionPage 0x532bbc9681113cc04f27b921c1133930482236ad40963510461db524c01331804019afa2c0192cd03515ab22409b27c033132795c01124903110a316409221302b0e1d96c0191c80290c1992009219202008941ec09b141018040ea6c09b0f000603090ac029075004028605808b054002018309800c03000000000d8190000 0x1c064212619c07000000bc1623440181ad001e2018065014d3ada15000f000a078100080c072762004090014b0046928040060203a8055b920104ba2506001f214940052309802ad980de1811f07ba088000db40e010e32833de0013880a090a322004002e400020b021d154c0b0802c000c3688805140758825399a0585200816001804501c03090208180005a00b4002000c7fe49d068348006e80c005c40fb807a81407eb50a01250015f0241ee5020a84bf49a8050390f03a9507a000287d840050015e007cfc580002c5281b214977500db480009301fc42800444088012e8000059f806a8e597208bcd845c101a84b121001812302c4d00145014881b80200c004040003c090080028d2d1814200d400000100100005ec000a46b16633cec02c0300028031a4490eb581c86b0830016948007303a020ca1002c40000803e242bdac4b8c2781884b40b000150680d6b440025af2b93e0240c5940a183625804f580070300702d6e3b0001000059d80019e0108063000c6b8a302c6a1192e00420318100640007d6e001f3f001969817180088d0180000905416081e926a4e0581d882b3180bbb9e0e3bad60540687e3101c4f68140d1c000e09c5834f000000680021fed40080e2c07c1b7333008b3805780107012cc840c30360304a6000269b6240022f870c0f00170000000000f802b2bb1b070027f3a04229600120be55cbe7824cc145900f0178601415c25ef0001cfe490f01e100004040c5d3f00502ecac4679b800027a0de41f00008b7c6fc183d6fd0431c00001a001c60100c3084a7200e500424000010104e31020024a5001800190000c0030020398ce03000400ae4ad2628c030006a680801bc460004803900004001b9ab48c01001a1 5 0xedc8765310edcb741edcb1dc3edcb7654310edcb65410edc3210edc865310edcb6543210edcb6310edcb6543210edcba654310edcba543210db7643edcb63c84210 0xa855069f21742b00dc2377632c61762ea33361a52404806e1141a823b8664948fbb93722cb56da7f4fa9e40476d73e9f4035d6ba06c06300379ee7c04806ed10a8ed0c74fe9f53c42a84e9fd3ea7885509d5ba7d4f292404a7d4f293215ab750a9f53ca4d492025cfa7d01201a15426784170018088569253ba4949005809 0x13a40074804e89cdc639b89106d200f8001e08139e73710a2e21e1b4083680273800e71a254023fd047300ce45a1c602369869e00d03411fe37bf8007be00f7801ed803b500736d0e2011b4033970472e04e6801cd32c190079600ee831d8003980672800e5c09c9804490079a00f2001de003b6007649cea801cb013926c9b0d908811fd803cc0878a00eec01ca013915d9ca912b41a0582409027be00f7401ee003d30079200ef401dc003b70474800e6c01ca0138f466f008d9801ed0038d1d79604e28e9be9c37d
def as30 := bankPage 0x85997c9973996b8962995999509947993e9935992c9923991a99128909990099 0xa98b655143412e2a10a98b736543412e2a10a99a8b6543412e2a10a98b6551432e2a10b85a412e28211b1411b85d5a412e281b1411a98b65412e28211411a98b655d412e281411a98b6a65412e281411a98b5a453628211b11a98b5f5d4136281b11a98b5d5a4536281b11a98b5f5a4136291b15a98b5a4536291b15a98b5a45432e29211ba98b5a4b46372e281b
def ac30 := actionPage 0x302128a8c01027902b1ca724c01124602619a519001021601816229d40231ad017151f898008195016139d0d400817d015121a8d410816501410990cc08814d0130f170d03091320110d940d810b1110100c918940890f600e0b8e09c00b0d500c080b1d800c0b1004060493402104e002038215400b02d00000001d008f000 0x4000a36984002c06400e000543324606b8402940602c80480c00344d1ad4221168694a049c4779ce0390ee0000a1ad0d1010f0002000000808005000070c06021030000c001e24980f5856702c03031261a9ae0346573c0129c04000800370003c082d9230266345e030680300000000a0186421012306000f9800e635ad1020002d3da40ccc920c44006681a000e0e7e01480037801bd302a24007707400088a1100d1180d018c82018051c053800700c071880400022118a3400611980700067118802800310020281631002508804180062188030800010a0188010146418025314052000419060005ae128602814002c096000028c6001ce05ac021a8c00180300840200240000001443010a029800001e0000ca1a424031e80840d6a40021cc62a5441018b600090380a38840101202ac006812309c0213d00021ba17c0003d43b8000383e0c0c05800086806f7a0017003cc01df7c6330016000c0602d00fe86803c0c568e003803582d03b5710665a64c0d940061880d000097a00c28ca901c00081a93080a604012b80c1a4830000020405421a5001c54a800020e12802840008434ce0180d 5 0xd43d43ed43ed943edb721edb63ed732ed3ed72eb7210eb642eb76432edc621edc9876543210db721edc4 0x99f2ea4346289f13a2644b5d2a0a53c6289f13a2644b806be974c8689f132259dc3b73a627c4e89900d412807404c9cf13225ee789912f73a4bc96b9d25e4b6ce83205f67017d9c05f4a693524a2f0ec01801a534a293003a4b491c3a5312d6f6cf59cb2d554da95a 0x203803650080c01010020006bf6006c6f7371fa6dbdc8f2b77600d89ee6e354dc7b9b6d536d0e5c07c31028621b00c0201804020080200ffc35fb003f6007ea00fd001fa803f4007e600fc801f7803f1007e000fb401f4803e6027d000fa009f2003e4027c600f8c09e7803cf107cc00f8409d3803a7
def as31 := bankPage 0x84997b9972996999609957994e9945993d8934992c8923991a99119909890099 0xa98b655a45362f2910a98b655a453e362910a98b654f4341362910b88b655a4341362910a98b7d654341362910a9988b654341362910b6a98b654341362910a98b655a4441362910a98b654441362910a9988b5a4e43362910a98b654e43362910a98b6543412e2b2a10a98b6965412e2b2a10a98b655a41362b2a10a98b6541362b2a10a98b5a4e432e2d2a10
def ac31 := actionPage 0x5726ba0e40183f904f23351e801f39c04d21b10e001136904720aa8b401a31b0451f268e00112e803f1e210ac0182a00391d1c0a80182580351c180a019321f02b1a940e00231b602919100e000d18f020178a8ec02312601c10883941110f30170b862901110c00120503b5401408400102011940a301b0000000108109000 0xf0202a100e0700cd13c0618002001a06802d024c202421000ad31c055800e01560029ab0104c025600b0047b81d5e40f2b1d01800001c08d5c2d0001918017aece053004c301dd280570001e00831beb673838029007bc1d05de11c402001b4183a0280038300758003010832a80301008001a362d2b2a000001e84802603961008e07252c32400150140fdb1100185dc005000c78180e806304000e001f500131272264c0006e1bd12800180a89fc826501000e01484d48c0002cc423c0030dc0580041a4630390508180024a2718255000f22c003a560003800280de818103c1c5e1916e8075a8003757c525e001ba4300c082c09f800b3940a06368829f47014003d90e000040058b18004a5405e43ab980693d5c58c443000c18000000005002000c01100e09201800847470a193f435194a00c00538004004400c0a03d661840e420a0001400082c000000200d201605002c19a40e24000448e072a66055d1f5e42e416000c0068bd9001801d40668891e402a801647a80c1e80202c302563a824cd80037941870428000020027903d800006ec880330c0550ce009c003980000005100050a4027b4006806634000508006da62028176ab3d1d4ac3f2c0036e0010190001899da0c976e01c0422055500c01a6e0000009870f3caea000005a8054712501da00027109ee2b6bc007160e98e000c005b4161002504cee4b884195000241a014035940102de06cecb0f9cde1140000e2d0000056a93a4a61c8d9381a0002db02800615000368023c9911e1e038a08a00768008538060038d000ac201c818c6f2826a5d014411807540023c05003a601540003c005b7dfc800002c0f487400235000cd00c1426b80544258d01bd5b399c5510149805400680ef701bc04046303f4e0055ecfa006124c82679d86000560000a0194c020460000c4000870004028466 5 0xedcb64320edcb654320ecb73210edcba76543210ecb73210edcba753210edcba76320edc76430edc76430dcba5310edcba743210ed940ed90d9320d9320ed 0x1602804d98a1939a72ce48ec18e2643a8711321c44c8750e2264388990e21d4388750e61c4628990e23144c87162243462833011e5284506a09409a33324f0974868c501201bca660664b91712dd21a313b876eed9da284506a04d193c0c60ba023d46bea1141a818ff13a260fb 0x74f5c01c323b7b0c6f60cf6401c188b770c6ee8ed710dae08b5c0c6b824f4001bebf4b07d960fd199f6332f44e0d7ac24f4435becccbd9397b271d5a20c1037c006f8db29c0a0bca3da907b444df035be0141d0082608f3801bd834370286601074020e0041b0083201060020900411006f5310a4020bcd4d78d9af312f64e5e804160082a20f2c11e5893ca0081e010050dd38036b0081c010150dd28036c0c6d00503001fe803f9006d200d9d5e7e2bceb4899a0103402060040b008140102401ff003fc007f600fe001fb813c5006d400da001b300408
def as32 := bankPage 0x86997d9974996b9962995999518948993f9936992d9924991b99129909990099 0xa98b696644412e2810a98b655d43422e2810a98b6a6543422e2810a98b6541362c2a2910b88b6543412e2a2910b8a96543412e2a2910b86543412e2a2910a98b8265412e2a2910a98b654e432e2a2910a98b8065432e2a2910a98b655a45362a2910a98b655d43412e2910a98b6a6543412e2910a98b746543412e2910a99b8b6543412e2910a98b696544412e2910
def ac32 := actionPage 0x3d20b390800a30903c1f318d000b2e803b1d2f91000c2c40391a2a1ac11129103318a50e801525202d17218dc016210021169b8700241a401d141995008e17a01b121592000d1530160f129980901230100b0da2801c0cf00e090b11408c0ab00b070811800e0810070485954010051003020315400e027000000011800d000 0x400c820008421405200e101821280e0094c3180c631c00380a039400008030000018c0000400000a2000e201000314a400800004c010066398030a002500c00d26f50140a8105013a7683440406000d80501e95f4a02944100109aec19b014c8fa607401ed4154a000200ae00014705221b8106b01f60000e6d4d00024758202b8f76958076380d0008d6800059500300005b0c7598a041004200097848201c2b2b00c310070056f0000e02060004800740f790a7080acb541401d7f22c00308edb810006e4505e05280a05a54df00000800001c00282bb27efa4e9c7434005011e901dc000000015fc42a0e5c0a0255a7800041c0721962020a958001000ed7b960729404bc00194033a4001a52b02020008400800700c0e038030254f48c6848167301223140c7180582a800300903e206fdc103d7d4a720029e0b8c00064c04dc000032071c0390000002311a59c980c98a4371a01c0702002e2e0028930200a3c4d0c013a8420d0ae16029d381a90639005800d10c000000001e653d281b40f01d27010062880f001ca39840280a0000012800000108000032a0492adc43ac2060102000006a100381e002062780c602d803b94e29800001c6020a00000850dc7004c00014733401209ce00ca6538a410002008800358802d2000028010aa081801842009402000063980258002305e0498820180e 5 0xebed43ed72edcb8753210edca754321edca740edcba8743210edc7edcb7430edcb43edcb654320edb43edb732edb72eda53dcb763 0x4a88982ac07ca807c0f254ca807c0f22844e8750e57728189d13141c4e898a0e274ba89d1321cbca8c513a264048c51422744c87301201bb776ced1d9a8142a18e1d43812c2561cc3812c2562744c8964b89644f89912ccc9988990e61c08a 0x10a801d300429008500109c01d23f4d67e9120100cade615bbb0074605095d6113ac200d80624f1401d1014260084c05090021201421008420103c0203814060080c0100801d0804260080800ffd69e40042510762010f8021200400737ec1afd80208003fa067ba00e610dbc803670084600e3402110041f0071801085cdfb003f600716fd2383e1895bcc0071401080020f00389
def as33 := bankPage 0x87997e9975996c9963995a99519948993f9936992d9924991b99129909990099 0xa98b5a45362b2a1b10b85a43412e2d2a1b10a98b6551432e2a1b10a98b5a53432e2a1b10a98b5a55432e2a1b10a98b5a534b2e2a1b10a98b5a5341362a1b10a98b725a41362a1b10a98b705f41362a1b10a98b5a5145362a1b10a98b5a5345362a1b10a98b705a45362a1b10a98b715a41362b1b10a98b5a53453e361b10a98b715a5141361b10a98b5a4e432e292110
def ac33 := actionPage 0x2d3e1b9d800f2dc0283a991d40102ac02437171d00132730223195acc0102430202f1414c08c21f01e2a922501121e901c24903100101b9019220e15000d1920161e8c1d000e1680141a89a140951290121587a901120f300d110624c0140b70090e0498c00e08d0050503c8809604b001020298800e021000000011400b000 0x3a40d11dad001a9024094858018140500010106d001006084a0a80469d205b4a0001666b4003ac0f000807a00a51c080bca649940d006d401a0000040196f000c01bd60014c202c401ac0018949001c00a80002907000855954c695e03314201c007a8202000f4800501082780a03052b00086018001b16000cc96800779d2048c80200e170040100a0610a60140d01da303c40098e0024042a5c0338400312003183000e04a5c00240f101ee781a042520200ec7951e00180b80e00306003c010780002c93625800afac0450383cecab0a7014405bc0010405014e101042038a0280006a0a011c406a80d011400980002c00601c10100431400409286818a0000959c405812d021600200f7000563c89480014a5030100f00004380ed3a80f0010e00ccf3056f7bca818007681a72800b000ca600e11800d50005180805808a6000a030e03bc6e28104080002b0003ac192006003caf0280001544020483b510408ef6ae400001432c6620008231e600000d00e8619e0700013000003d4008107681c07a00800008584e82bcdd15c00283e0cb80030280b837600008015280063378420a740bdc8ab3d9608a01173c0e001b83eb409a408420e0000002006102c2b4000352c60280a4280604ac00400004000b0980858107000004a4804a54801d43014e2 5 0xdc9320ed940d943e73e73edc3ed73ed63ed93ed973dc93d93e62dce3db721 0x1576a153fa7d49a02bb790318e2a45089c3f47e4d097721e31c4e899012e4d97b2d4fe9ed3c90f18e023b660957632c638c5132e4d97abb4fe9f53da79011db597b2d50e9fd3da7921e31c04784ed98255dab71f631c62af54fe9f53da7945d7dd5da7f4fa9ed3c808f09db597abb50e9fd3ea7b4f2023c276d5eaaed43a7f4fa9ed3c808ece9ed26a492301882ebcf79acd598b2f65aca593ac557aac556a7b4560fb4553a7229ed3b94f13e2644b8770e61c097 0x5024020480431688540102041e2803c37383ee70783e01883b102802010040218883b10678408f0809ff003fe007fa04fec31d832c1f0677600ee819dc823b90677008ee001fd21bc6007740cedc31d8003f9027ee00ec401d80042f437660ceb411d6bec71197fa3afe419d48042c
def as34 := bankPage 0x85997c9973996a99619958994f9946993d9934992b9922991999118909890099 0xa98b6545362f291b10a98b65453e36291b10b88b65434136291b10b8a965434136291b10a98b65444136291b10a98b625a4136291b10a98b7e5a4136291b10a98b715f4136291b10b88b5a4e4336291b10b8a95a4e4336291b10a98b5a4e4436291b10a98b7b5a4436291b10a98b715a4536291b10b88b654536291b10b8a9654536291b10a98b6541362b2a1b10
def ac34 := actionPage 0x4e1a380dc0973c604317341a001e36c03d15ae0f001b31b03714298e409a2cd03313258a0093294030112291808c27002d0f2091008c24c02a0d1e11400e2220260b990e80131e90220a158dc0131b0020091209c08c18c01e080e89c00c168019068a0e409412c010060586402a0ae006060201c02603c0000000310014000 0x1820311407080f785a01016d00000035ea00141088a07240140d4c000082800f00c0331da14010d6390002801fa0ab580000d8c6580321a8323000af0800699e32000068e934301600c8300086d88000540001de4540022028cf007e3824c17400487a0583c068740a3400d9c000b721006a27bcd22693c0011689ea2524000006830805701656501f98000481c04614a3000c00cac138c750000a9c2a36ca0065a83a1403000a998000080dd1c00ab5001a2e040000282ad33d801c8006a220d19aa70067100cd00c2a201c0620001002452400221cb480025810d199000250a408001ac004342033c0e0000001d07100680000f5a860739a0380074240f01de058060294a5010a00000679806100c0290006100031580580c3181407800010140030e00304401c06000a0504c121d47038055144080c08700e0309200056003d4d00164101c421ee802ce46000003421018e3e28000316340146230000112000001028ac080ce03808598cd280ab02801019407b8a03140c291200340d43c000304d1100422060000cc034e0490051800601800029e07a008021c80250c000c03a54853c02eb81f0010070dcf584090700a23c73008070026b380003016008120003057a401214061ac2a380ad1988401800e00002b4e62a400000003aaa18040000c1d003000840940006a980421540186a1d9240d006a20295809e105c003840000c00e3ac00540021405083b16d021e002e34640500c42c80003421401cd1000002d60020000012079c001056b3196070429094e0328440106b4a7001288e684005b4000050f280960086f3000b120a001d6048000008083140c008600016760200028002ba400680438338000d90123d010f7380c400000734f4100c78c96b400fc2ada8 5 0xedcb210edcb5210edcba7543210edcba7310edc764309875103210edb62dcba543210dcba310edc7430edc6430edcb63210dcba54321dcba210d920 0x340600bbcf61a8750d92e19a2743987113a1cc388730e2935248730e2935248730e29ed26a4945e31c4e87318e274398730e21cc38a7b49a9250eb0d21e31c05808a10d294327e1981a031 0x1562a9d3d6107aa18f552265094ca558a4010e019ec083d30c7a68cef50dde883bd0c77afd2c5fa33b441d0082c00f5c81be2ec516a838d10700a0a80415007ac05070020a003d50479e010dc020d003cf0283008f3801e7033cc0079600ec66611804170082d2af6a726bce48a8d866010540219804140082605045960c80410007960cf2401d82ac4d467ba86f7441ee863dd4973226e642db883b715d898af131562600438487b88cf710dee093dc107b818f716652acc5e008640502d19e3803c4
def as35 := bankPage 0x86997d9974996b9962995999509948893f9936992d9924991b99129909990099 0xa98b65413628211110a98b655d4136281110a98b6a654136281110a98b654136291b1510a98b6966412e281510a98b6965412e291510a98b655a4136291510a98b654136291510b85a43422e28211b10b85a43412e29211b10b85d5a43422e281b10b85a4e432e2a291b10a98b6545362a291b10b85d5a43412e291b10b6b48b5c432e291b10a98b7b5d432e291b10
def ac35 := actionPage 0x2e213696008c29d02c1f3311c10c2790291d3011800e24f0261b2a92c01121c02417a91cc08a1fe02114269d408d1d701d12201340921a101510998f402213b0140e1695818a11d0110b1399808d0f60100a1089810a0d800c080c92000f0ab00404881e401a05d001028511808d03600101020d800901b0000000090009000 0x481e06984e0200c03c0000c0000c875b047784c92918a00420300cf02c80401803040700000414c60298b22025100c018007328eb01c00780c4180010244d2b520019a0381602000f6000d5a920601011140b02a6003dc0180002a585639cb62d0c03502d01600292e000e079d0b39880700087bc43600c1401220000b02c036ac0049020294042004202ccb001070800a281ee0028e801ef78c00f39e9360030038afa8c000004280a014c025080f4548801da8d40803f400c04087a000b000d002c402c191eacd99829b3bdd530ef8d3c90121dd7000381407a00a95960044e07880cd8c0ef01a0c82020001e828802ae80780020a4400000e1b449181806a8061ac0602c07380ea020a70000001825001401ac02001c0024e038d04704e1000061bce6000400002019c29020050900400000724022380001c26025c06bd405000548182005e3711c90050b401c09ac0009800603b420571626a7328203900bf40725aba0d000d021155b0ef63009002387c26a00006381ac01de0000a8124ae00c0a01000380003a00c3806f5a4cb01540080e85b90001000088000800601400010023894618ce70106520080310c03940000c0000087 5 0xedb73210edb6432edb742edc98765210e61dc621edc9876543210edc9876543210edb721edb721edb643edcb7410edcb54210edb643dcba30db73 0x14144e8330600be8209c0600b68209c0600b61ec3b87200e7f4a99511385601001d3fe274398707cc4608a8790e61c0018790ee1cda0b3f2ba55ca9a534a292c3e8770e6cf4a98c7142272c7b0d25e02c0450885c33526a490f21cc8789d0e693439 0x88c00fbc0222803ed0088800fb801f6014403d7de00fa002219abe70088400f9c31f2814410083400f9801f21f4460088201100021f81437027d200f9401f19fc2c0085820fa401f08042900862d10a0021280408558ae010f01a19033dc467a886f5011e2003c4008720108c01ed00439
def as36 := bankPage 0x818978996f9966995d9955894c9944893b9933892a9922891b79129909990099 0xa98b654536291b09a98b655c45422e2809a98b696545422e2809a98b696546452e2809a98b655a4b462e2809a98b654b462e2809a98b655a45432e2909a98b6545432e2909a98b655a4b452e2909a98b654b452e2909a98b655a4541362909a98b655a45362909a98b6545362909a98b5a4136291b100fb85a413628211b1110b85d5a4136281b1110
def ac36 := actionPage 0x6520c30740243cc0641f400d808a3ae0621d3c91c00d38705d1838aa000f35a059113738c0113270490e349940212c40460caf8e801029403d0c2887802222e0390a239280931f502c099c87802318c02808968b001614a01d08100740260d800d080983401a08a00604871d401404e003020395c00d027000000011c00d000 0x7325b84e0321b914f47d83da699a250068005c7337e05880d6a98029001d484a2001596c17582e7000090221e003807d40660007b001c0583201d801a4e00300203c0578404020891800020044228c008001030c03800c030890000c0380049400500ee4292e2000b7806d0000842c05c82a005c08b4ea40011b01c0c5835d6ba60b0181300f668343480004d642f00673c40c0281e052c0075a503c01088a00755d94c118e8001b1d06000d00327000b5000a004c2658155d8582038009004065bc596d206cec56910d4001b9bc0eda186f1011005a64000048208046fa78c80605a0c376c010a96200b1b006030ea4398e000013800201c4a014c91140000065311405816260283904020000f34997000401300f801f40501a04c6c12deb0062127dde03820ae8140440b053cff99f4b38c03ec21de8e872460002e2b00000026003b6bca808005e801d250a40c02c1001ba3e008c4a00020407ebc0a6255318000065607dd970201502c0e003f75a4450a010079a072c007000000018d696016c00200ef5290c0338c7c942182c170140c82e03cc000ab6c0584e568133280023c007e4003cc52b49e3219438044f01d2005be004126b021291160281a32b404306a368000000fe00060020033b121064090000000c090a40a2fce0000049496a801cd4be806ac007f160536808b80f600ae1300d627ac68146b800c50080c3400071fe0388002943027a603000001cb0010c500a1cb8860001e03c7c0297102220aa6a60001728109024124001fcbe29c340000198003c0021d075ac95dc98c800248d4014f40f816d01220683203200004187001609ac0799d860001643500180885e92876000b01ac3ea8891419c81c75b00008c4801808504a1001806bc0003400014e402c0040d200380a038050380050066030001810622d060a0007144b 5 0xedcba76543210edcb43edcb943edcb9843e74ec743edcb764320edcba876543210edcb764320edcba876543210edcb76543210edcba76543210edcba76543210ed632edb7210edb6432 0x4b8df1bc2a86f8de1722aa01be76d2c80da9832223c85c86e76cded9015c2b6568ab9111981b02b0550a60ecda95c1fe1582a8537002584a89676ce004b09512c2584a896a854a693519a3145e80d9fa0c0d419832b3d4141982f 0x48fa111f0023c00477008ae011440a26034400683808f8c01ea00475008e8011c4023980472008d8591a8123517c71048e2051bc11d318c9106922632401a4800470008de011b802369646b008d6591a80235034430685400e9c01d2814677982600e34c64680467008cc0119402308045f027c204f6801c601464048c20117011c498c8c06916051e8023200463008c401180022e8045b008b40d1081a1000388068ac0115011bd8037b028f009164022b004530089e011380a26834410683a08de801bc834920690e111e40a3c82458008b0011481228004500089a0113002258343f0683608de001bc02c470088e0b0d0021a02c2b008560cf8802230e3f5007e40111401f8803f0
def as37 := bankPage 0x87997e9975996c9963995a99519948993f9936992d9924991b99129909990099 0xa98b5a574636281b09a98b6545432e291b09a98b654b452e291b09a98b7d5a452e291b09a98b5a504b2e291b09a98b5a534b2e291b09a98b7f5a4b2e291b09a98b5a454436291b09a98b5a4c4536291b09a98b5a4e4536291b09a98b5a504536291b09a98b5f5a4536291b09a98b7b5a4536291b09a98b7f5a4536291b09a9988b5a4536291b09a9a78b5a4536291b09
def ac37 := actionPage 0x37253f30c00f32d03423bb8dc0102fd03021b811c0932c402e20b589400b2a302b1d339d000e27902916b234c0102490261230a4c28e21f0240fad95800f1f20220d291640101c201e0aa396c01518301a081e16c01614101607180b009510201105920f00940c600b040c0f0016084006018617001604200000000f0016000 0xb489a7680846454a02cc8005aa0300000100589c005800724cc025cc01ce140409000460294c48840080ef0014c78d090280b020002040a794034352000000180812a48051d4e280055800840c401800039ca05180500820680000140c000004186028002304a310000315260180628ca03818002400081c0024820802038584590ec289c6029640b8072a800181e2001645800002c230012c53c200240910c0840de60002aeb9045810a01080000030200a3a844114c0301602a0081b94e02c207800900143001094a0a0000004054000009005e04b008108025284202862109220146a0000b021a0000a03b00d4280c308c0630205140d021c552c2d734cf0157f035cd68c0850001f81000000782e0a0280b000000380c109a060d4013fe21280c480c35f56400120701600028b02481699c02740a01f6f680ae2280003100c883103000014f104380eca853b54090dc109fe01800a8980b000006b4c10172d0018358026618800008c015a0010e3a204403db923c0005c1363be500009581d70322007f818bca052c03015337798b981807b4621cd030140668000000170016363d26501e0780825a740e100b003420d6c4f300002941000356b8cc029400685230b62bbc0d3b41a580e06d40a001e2609a01802000c0039220181ab489761bc03076f14178040060398b104e0608c6703400481800000009982291000000f109a1d8000bb8404052f580361800d029220750fc4139 5 0xe74edcb741edcb741db643d730d73d73c74310c98654310edcb7654310edcb7654310edcb76543210edcb76543210edcb76543210edcba7654310edba76543210 0x2e4d9eb3b670d695129e450690cf13a271c109712d011c109712d49195dd0b7cea5c10c112e25adf597a814fe9f53da79011db3ad704cb595dbea7f4a693525a48e144b896a4d4969209712d49a92d2412e25ae852612e25800dd08086c04b896a4d49294d26a494a693524ba14984b8960034a693524 0x1468008d00519919f6883e6028c60117919f6083e5028bef304c023d0045e047ce05174022e8045c028b4090780a2c80459028b001160122a8344e0483408f98023c80457047ca00f1c022a834510482800f3c027b004540689e0904c01e7004f6008a605140120c824120078c011440a27044370a86610fa402790144f0089e090601a0882411
def as38 := bankPage 0x86997d9974996b9962995999509947993e9936892d9924991b99129909990099 0xb85f5c412e281b1109b85f5a4136281b1109a98b654536281b1109b85a412e2826201109a98b65452e28201109a98b6e69412e281109a98b655f4136281109a98b6e654136281109a98b655a4536281109a98b654536281109a98b5a4536291b1509a98b5a453629261b09b85c5a45422e281b09a98b654b462e281b09a98b5a534b2e281b09a98b5a4b4636281b09
def ac38 := actionPage 0x2627388d000628202425b40e400c25e02123b012009022e02122ae09008621c02021298e408a1fe01f1e291841081e601e1ca50e000a1c801c1aa092408d1a1019191b8e8010171010189407c02210b00e160f16808e0e100b14089340930a800912850dc00c0840040c03b4c21105100204823cc08f024000000025000c000 0x8c4000e5100060100221daa780030000e701ef001001b0460254018c0e0250b3a8800a180780200346000127584012008703803010003b8080a001730685ac20000011980221c8008840028e0120010008b4816100127014200298c08002010e029022380e0318e0180610008231d28000056814c085604158069c0e58001024e060c0c6800b000600140c3014c030eb425006000d20189700ee31d204000459860300ec000e0101c149de47340002ca1298057008eec401d34801838013a2049ae4001100201128360051c90ad0057c0079280614170008518120000539ee72030dc63153f480a01812a0070000059c0c04b502470008a040214002026778d4000149080c0609670240d5c5822820d6a407504005d4024b2a00580f6001d07bcc06d40f8160b781b004cd0d8fba04840d4000204f081a0000032ad6501006008056b4a8200aa29065381404ac004e8d8982450262883f707026c8080a039a000a00002fa01082083c0001bd044864d77208c1c082a97801c6380c072e0001e0028a0032c43800401c400ac41134a078180000205012b5a400018c0 5 0xedcbedcb76420edcb8710edcbedcb98210dedcb7420edcb97420edcb876320edcba9876543210c987654310edcb987654310edcb643e74c93e740 0x1732e04f4e314127a4504f09d0c85cca019a2e65c0b816e27c4f49d8b93884f89d9c427c4ec2191113a1884ed29a514984c097ba14a44c097b383806fd86808df5911b636a4506786d0ac1541f83eb2f65aa053fa7d4f69e40476cea1beb2464445067dc9b3d676ce53f36c56c8a0cf 0x241003f1028fe18fbc01f78048400906012080240803ee0290018fb401f680480008fe011f839f9013f20e7e004fc031f6003ec028fa011f4023e004763f7de011d5e61c8047b028dc8cfb841f71c3e7028d6011ac0a3480469
def as39 := bankPage 0x87997f8976996d9964995b9952994999409937992da923a91a99119909890099 0xb8a96543412e291009b86543412e291009a98b8265412e291009a9a28b65412e291009a98b654e432e291009a98b7b65432e291009a98b8065432e291009a9a08b65432e291009a98b65444136291009a98b655a4536291009b8a965412e281b141109c5a98b65412e28141109b88b65412e28141109b8a965412e28141109b865412e28141109b85a452e28201b1109
def ac39 := actionPage 0x2b1bb90dc0932a60241b320780a323d02219af0d800c21902017ab91c08a1fb01f16270e400b1da01d142411800b1b901a122111800d192017101d12000d16b0150f1989c01013b0110e140ac0160f90110a941c01040ed010079298c1050de00d050e16420f0b1009030a12010f08400201840f00a002400000000e000c000 0x34c07000e4892900407019600000802940699213b52c3800010ccb5a4000140b6012002c1a0014d6940e21dd20900044c11fb40006f400100005641adfc260cc007c1700025004007316d00100501e37b9a0401209bcc0954ee21bd94a404c7c8004810aa805280072814b028054002f698091008d1800230020000c0084a100004181ae4280b038a00012d3bc0d6bdc0000007a120719634804051407100c8405a000d473800203c2b42c0b00c00000054a0800280c194820282072c0b0b4000002000008101083a9251a18800cc862d822004b5b94a780003a06440000024002040c3a9a4004460148022de400160220000316848002500002bd82021466100000ca042900400a068080009a528160010e02a5610c8c5020ee681803898532c0019c0003c0f680ef49908004c0384a00100018c0509c6e0140001c0620d8702032020a14a8056b8c44000003c407800a3b42c08008103604b0402940c7208d0100a001a60ac002a86f6b40a1000f038272a9e048123424c085f3f0709db035ea0003b0c65a0be002400c8160a0000ba7cfb1c0f00110c000c6a28f723a8d031e709b8644800393a0006006d204d01a6dfbb901fd00820004c50108d00001429816200001c403316d415e0 5 0xedca740edcba876543210edc743dca7543edcb74310edcb43edcb43edca5432cb74320edcb7654320432edca98751edca9870edca98765210edcb9810 0x21d4387930ea1c3c969f0e20d4187930ea1c41887b0ea1c41a87b0ea1c41a87b0ea1c34f8750e04b896b10744e499d2e659c991ce38c668b816525e6dcb816525e15cb816525e15c808840ae674ba973 0x52280233243f0127d20522c02458148900912011940a110042200916011842a2f8045f00914013dc0a44004f7009120107c027980488028720121c022c83478008aa00f9011ea80486457e81cfd009fa00486457ea1cfd409fa80485457e686fcc39f9863f3027e600fcc0242083f5
def as40 := bankPage 0x86997d9974996b9962995999509947993e9936892d9924991b99129909990099 0xb87b5c422e281b1009b8605a4136281b1009b85a4e432e291b1009a98b654536291b1009b8696542412e281009a98b6f69412e281009a98b8169412e281009b88b6543422e281009b8a96543422e281009b86543422e281009a98b8069422e281009a98b8165432e281009a9a18b65432e281009a98b65604136281009a98b6f654136281009b88b6543412e291009
def ac40 := actionPage 0x271db11500872880251c2d8dc08a26a0231a2912408d24301f19238ac01420701b151fa2000f1da019129e94810a1bc017101e94008a19e0140e1a12401116b0110c1691c01113800b0b8f8780a20d200a080f1c40890b7009068d8cc08a099008048b11400907e00603080d800b05d00401850d808c03900000000e8093000 0xf495a00000b3900d18924400af488e03a00d0190600000590630380308184304003acec0000f439e0009c06844f0800d4bd20600e00056060000590cd201406b020480007800a0858d0008001c0d1d8200ac2063480392022316d610002212007c0059c00d80d401a4f36033b25200692800cc0d995e0088d000010000621400100e3280003200418860200c51984001040008422080200040014c0000c0019240200a0016813c000002c02189080430000011c0060ce6130e06910e0152c10d000014001d42000a00004e780cd0100010146281e012964014a6025c62094ab7c1904e4ef01de078170007138019036c2e80f902bbb60160b81f6000600760377034675493817d00e439804989ab00002203b8e9d8a0fc403001b900380640c700003090450080400d802806618041118a0018a22106300484280e410c040000401060010e400c000000361403208ed318803800b50400010c749c05000a00a40030043715e6005610010e380e020160020ad0000731c0021c002a0a079c02621603898028006589a62840028c084830e121c200ba42802700c0d000076e4ec08000 5 0xedcbecb8632edcb74310edcb7654321edcb9743b3edca54321edca430edcba986543210dec3eca53ec8632ecb832edca754321 0x9612b2549dd397378b39658790ea1cc1a13025e554a889efa5e31c61e62ee6ec7e2ca58c75ca889c594758e99552a1e31659552a1e31659552aa5444f89c724c40ba95059474ca867e718b2cdd2ca58e6e9652c70ea1c3c9 0x9f00123431f80048a008580d1dc023b023e8007d00124002479648e008e80124431f700490008e2fd0e5721c814294085890fc449f89748e2c91c05238024701428008500123c02473f4390091a18fb40246063ec009100119c2a2f81423
def as41 := bankPage 0x85997c9974896b9962995a89519948993f9936992e8925991ba9129909990099 0xa98b6545412e2b2a08a98b655a53452e2a08a98b6553452e2a08a98b70655a452e2a08a98b73655a452e2a08a99a8b65452e2a08b8655c412e28111009b86965412e28111009b88b65413628111009b8a965413628111009b865413628111009a98b65413629151009bcb95a412e28261b1009b85a413629261b1009b85a413628271b1009b8605c412e281b1009
def ac41 := actionPage 0x522d373d801736f04b2435c8c01832703621339900262b50331c3228c01128202f1630b0c09424601e132e9900241da01c11aa8e010c1b60180fa612400f1890140da092c0921530100b9c92009211d0090b1507c0220b7007090f92c08f08a007050e20c006078003030713801503900101830e008a01b00000000d8089000 0xf6c1c07a25cbe0004000b543604c00880111480073c14d81a02a36004801020131b7e1263a025360a90fdc25a035599a836018000000d28afe60640043019781803371f8b24e04a80a004a04001e837b16800069602215d05c0000068002aa9cf803141299c1b07100f3278381e09001f0001b0010400c916226927818e9b97480006cf800001b01378018a15bc0097d2044e4020069cc40052c1002400c1060500000340f12c496bc200006a000cc081200b0a00390a00c0a0140f011864b9900023a41000034c8783f70008649bbe0818b000c13d04004c49059a00989d00004c001013fed47c00e000289272199ea000047416f203a00246a618f2394afa340e000041e98000dc0c020000000e60026008c91060063090324000002002ac199a006d0502404c000302ca519c4002021599403b869028a770002000022802b9960002cae0002192e70d000b36bc002c00a818e0167f301600386a548136b40009926034e050000a71830032005c00a3da8e4100794e023cc20394089529025a90204002400200e00088021c0058006000e701864100050a0c00386548060b48005f7a000002a8e803176e000fe0640068240049f35d707074024e44fd0c001dee3481a8e82560000903444db0128b41f6001b024840010e9ac000fa497800c12c2e00c100acc50140568060000043800f0bc0741960001a63b80030026000881802c02405100e00746000142c2000002345b00004ec90388000ce12bc45a900013d4000c0c03eba0204b5940961404404e061d000000f39cee01c0018440210003302e00000134650040028585000c5 5 0xedc430dc3dc93d63db3d943edcb8420edcb98420edca8753210edca8720edcba9876543210c9876543210430edcb9876543210ecb83210ecb632 0x58880900dcba9e508a0d41281500940d293f238366cc40276eed9dabb3764e5db4b02600a8541a8250094c890cd806fadaf283504a01d8aa543685509a1132c654be0cd93100e013ed77ea950da15426844ca8cd806ce93f21542884ccd9732e066cb99701785949f09e0605949f09e06027a1e43a87225ef5d168ef1c611c113ca726965198822626f9692cf378b3965 0x250a1ba7006d600da80a502b3b21d7563aea811b18035e006b8913ed2274804e1129a41132c0a63004a00093e01278024e8049b0092e01258024a80494009260d01939ce02361006ba00d6c0a4e02365006b40526811b20035f006b2013d52275094d3009385726ca24d8249b00936012641a03834022b6c050d8011b000360286ac00d58324121bf4009220120c3240a1bf30291a052080240014450e908011fc0a23093f202918012300a4080481008fc05110022200492008fa091f0023e1fc463d88c20fc831f9063f1
def as42 := bankPage 0x7f9976996d9964995c8954894d7944993c8933992b8922991a89128909990099 0xa9988b65452e2a2908a99b8b65452e2a2908a9a48b65452e2a2908b6a98b65452e2a2908b88b65452e2a2908b8a965452e2a2908b865452e2a2908a98b655a45442e2908a98b6545442e2908a98b655a4c452e2908a98b654c452e2908a98b655a54452e2908a98b6554452e2908a99b8b65452e2908a98b655f413a2f2908a98b655a453a2f2908
def ac42 := actionPage 0x851846a2801b4b608315c315c091483077103e2e809d42c06f0c3922801b3db0600b330b00283630500aad86c0282eb0400aa802c11a29d03c09248dc09326403207a08e00231fb02d061b0ec0141bf02205158ac02215901c031092801511a00e020c0a40220b400401080a0020054003008485c00b0330000000064011000 0x1f1090890004df2000101803406dc18050d5d500021100078068078064b71e01005d64075e00e3c80013086c20c000044300f1d20003c800d49a5c025e1c030904e3c500030038000008f1c51470cf0400000003c000928c18e08324018010c1000811e203fb10e7f040023f034896409ce1a900002940f0008fb2ca107d806d62c0f80b0d00bf8064003f000830013f40f4388567c8fca8084022603383660c5406403cf74000500065501208000a4c001101400900050000d68041a0123c10003c56803df7000171cf0192413c320b4055807007805022591570c06130952d058c01858c4c021c4400060001da64009f2dd64b3401990804c03d060300630400000000424801a00d0c00cd00c21f0005c04c63db4000000123d12540183c00450127da79069c6801472000501405890090000da10001000b0db10b0185182c12800005100000d73000c01000062c014b00024d0c10050127d550000000f54900300b3803d100e4450003c20051464400000090085991157d904505c0c030224c08044604001c24078601e0005cf2400050d10c024e01470510000001a0005dc50029700001d3802ca3800001151120000015420080000053007450120003c00022081530ca1c24836ca0071860c63c038700000014014600500f00700700d18000000500b38e0060091002c428000104000a1c82001c00402090000150000083de0001401c06c014b3d119b00a01400000069300c01964b31370c49509a04024a4d64056c60060030000080133865801ca04020464a74b3c968a5c07490000141dd40844500b05e3c03000052544cd75000000900019064004b30001e20a00031800000b01e3504960c000331250b0402405c504130900821428e0c50070000091c01810080011c40006800c20591c800318624125520340d14010100f01008060024005048620250025c00938118028a0001cb00008021100c40025200228b00528700800e08800020168000f00e2c000020871c20b01b2c800920874328900b0001092cd1c624000734001b0400030011d22cd7c808475000c2061c000e34034011d7c001325d1006801803c61407047db3cb3800113806c050e0040000094080003d900c64b00a28200910058c2801c000b44001d2860003cb24d08f00600000b60d00000700044701a00334238001d01c00100b7000403400c82c00cd1810464061556004430cd4070061c020500a1c76c13400022400133005890c008000404b00718b0000040800050000050c81c000200704400024700510014600030000a00100924e34500000e0070002892492483852c300d24f0000030403c114e200009240 6 0xedcba85310dcba530edcba85320edcba86530edcba8543210edcba843210edcba843210edc6430edc76430edc98654310edc98654310edcb865310edcb85310edcba530edcb420edcb64320 0x80900df2a5042a84cf818f53ea054021542701201b3b502a013f2514a0854f81d67e0ed1d9a5042a84cf81948088550a9f23e0220f91f13e07c4f80883e27c10d9f13e0220f89f053ea796bad7 0x3b4d80096615095da10083f70072856e28adb1004b2007260137802533049b0093601255ee130342606848c0e4801c927360286c0db3f5de5e36cbb02966ef1d089e18eba900722012c81255804ab0494001280024e0049a0674208e7c01cfb1b926072400e40a1b714356069a80d2dc025aa9cac04954012a8124f8049f00930a71884a052ebde577bc08e7801cf0038f0696c092d8025b044b402968012d01a54824a9009520d278124f0049e0673a08e7401ce8038e02962acf3811c68037b069b2012c40258004af009500129cc622834230071200de80a57024a80094808e3001bc834d80299a012b80256804ac0094601288c622034220471000de00a558ebcd567783aef011c580377489dae33481a69004ab00954012a402533049b28936df250124a034210470e00dd81253004a6049260124dfe133dc267684ce3098a1b70036e3a82e75059d1c6a938d
def as43 := bankPage 0x87997e9975996c9963995a99519948993f9936992d9924991b99129909990099 0xa98b7365452e2a1b08a99a8b65452e2a1b08a98b5a53502e2a1b08a98b5a57532e2a1b08a98b7f5a532e2a1b08a98b715a53452e1b08a98b655d45422e2808a98b6a6545422e2808a98b666545442e2808a98b6a6546452e2808a98b65452e2c2a2908a98b6554452e2a2908b88b655a452e2a2908a98b655f452e2a2908a98b7165452e2a2908a98b8465452e2a2908
def ac43 := actionPage 0x4d3eacad001434e046382b34c01630c04031293900142d003a26a854801429403320a730801425802e1c26a4411122502c1aa48d000b20402a18a211410c1e0027169f91400d1b9023141c95800e18f021119796811115c01f0e931a40111290170b8c9b409c0d50120687aa8097090010040415c01105d000000022001f000 0x40068acbb45e03c1a8d400018186a80d45a400003bf34b20042b0409759400f50a000000482345a70e04236d001502417a57dab6a6bf001b00000060208dc00caab200320d8277082dd2606d02017f897a8a40d580046038504025663c0000005ac1e076260381601c00d91e307a3553600084c039000003c40081890365003210b816d58a1070000541a5f4007e64002e70afe0fafee22222ec4f0a025c0000003a0800018044e47005220153a400092a4d6c1026001c50002b5ceafa82a008007701807000c2840b43400081000140403402111e000045201030056c2804010000080a003c2700420388c239c20020a0084403a446680000000d01ce4009692980078025001070b8e46b1e0099e018080000e700000494601a840188630380a39c4f3816c030003000e4ada4500000014c50003325294a861680a96140f600052140802c02181b31800f1a1a003c405a403400007246c380027818f0012b02ecb03009966c002fe1061e001c04c88a07c412001691a00099cf3901f70344010304a410d0000007000108a75a5609001430ca4002609b4e000d200053f9c52071a98283cc00e00b80c038192280d65aa600241302a9b04779103000001f047c8a09839b6e4199776804020c0b280606bda18800a1006aa5c0e012db081e601c001000712c40000015bd04790083a0007000000dcf300032140f4152578004001d201fc05d402280ce9a031b80000481d02a04050003800c629e0020afefbd0abf6e1e2c9012a504780d809178123e81070507f1fc19 5 0xdb93d93ec977474ced73ed732edb63edc732edcb875310edcb85310edcba86543210edcb865320edcb310edcb8530 0x93300df72f954a8710ba1542679068c22806d994528843885d0aa133d8790ee116ba172664b98688c9982302602a8d1da0340445af3de6b9371acd598b2f65aca593ad5586aec0d716d1150a6c4aa94c8b5c9aad556a1d3fa78c09802b554280900d3da774a9442554a69450120173a2a81eb9e73a2a81ead85ae0800fb9e73a14c2803d50685d0a9f23e2a050c2154267c8f8bb776ced10aa133e100ddbbb6768ecd9529e42a7c066a804a49450aa139f901201b3b53ea7941a18 0x1498518ba00f0801dc28ca2518b42700c41fb803b72b6c450d60026339cb9469728d1b155da803b5009c00525c024ba7bbe0077c00ed0026f81495798080901012002b3b2007640524de60237c041d75600eac025e9638d0097858e30025d803a62c712012e8025c803a52c710012dc01d2004b600734c7140a1e493bc92876e4eedc19d1823a3007320d2cdbe54063f900730dee240a5900397489de0d3540268aeccb57996012d4025a0049d0492c01259ce4a37c940072a9ce1d45b0a7361
def as44 := bankPage 0x87a97e9975996c9963995a99519948993f9936992d9924991b99129909990099 0xb8a95a50452e2a291b08b85a50452e2a291b08b88b65452e2a291b08b8a965452e2a291b08a98b6545442e291b08a98b654c452e291b08a98b6554452e291b08a98b7e5a452e291b08a98b895a452e291b08a99b8b65452e291b08a98b5a504c2e291b08a98b7f5a4c2e291b08a98b65453a2f291b08a98b6553452e2a1b08a98b885a452e2a1b08a98b7065452e2a1b08
def ac44 := actionPage 0x572fb1ac810a37b0492b2ca6801d32404128a716c01d2cd03527228e401c279031251f11c01324002d231a12809420402820959641151c50251e9391018c1a10221c1195018c17d01c180d224014141018148b1d020e11701411099cc18e0ed01110058a00900bd0090803c1009807500404829c80100450000000254117000 0xc008101d1c610f0c90002000081cc00d10c01201301108a833780fc064c7c04910e702d005608d0071509a10044901d000b800115cd1007501bc0411f3000010c800000c62df6801083eb0004e880400c40fa0000066f0981c001135200054670b60f00008b0c00960c258400460038511b18c00a4536800005c21c905e6000007544de54010600200000a00030b4407c06560090183cc5530020000001cb00300744b01a4451933d51c64837d959504035148721315400a20005f5000160000030830803d801d0006805c80000015c600000c00201000c00f00404000100000118c08514500c14228e24000c2420c00083c034014000c14b24900100030e04228f71505b68001b0083c000000701700608001700349d00c10e3017400014c001901425510d2176da0d77c00071013c534000c01b70724d0000095cd0003da0cb2cd3013480003c040724518000644700000008a34b38018d00f3c90493463050000002430000050002040000030ca0c018500500e3843c600008c14000f00d00c08c00000000d00414c00e1cc1c51472022800000025034806000180160047002820135c014060038438060034f50900001318755701c4d308101c1874ce10038600a08900238000d20b3451002001480002063c73002850080090002c500738000010020010400030d08f00900d2090c01c010028f0080051800853c934034000104810128028900f20838000004008c0082470022001c024000f1c300924e3c908000401f01001f00810059a00000f45d5c060a28010000800a28061854608049370001969201400048d4050077c544059a04041550329a4022c000000208a0c90c000e0000080050051000c900e0081090000863c51c320110d0072400006800111cb2c100f14b00200900001758700f0430c30000002803da08300200004801b0c00033da0800d71c40ca083005340 6 0xc0edcba86310edcba854321edcba8310edc7630edc9865310edcb8531032108510edcba5310c310cb6edcb4210dc93d3ed963 0x2e95c8b1d5763db0458ca7d281f114574ac7bb86aeb1d6329f42e3be02c0442e854f8a1742a7c4f91f13e0228f91f13e02290e1f23e27c045526a487c4f8526a48870f89f054aa8d5029f53c944f89994407c8f89f011822802d26a48888f99f23e27c16c2d7bcf61a02403730da9a2305608c0951a834ac9548b0d1abd576adacd54a34466c037dcbe552a1c42a84cf20d1 0x468e7070344a06aabdf007bedf34842692accb0099601319ce5d234ba468e4df03842072abde007bd02e8019d0004b35195ca31904206003dd0674450dd0a1ac004ca5395aa32b5763ca9c63518c62502c4205803e0577beaaf7c01ee014b0108345efb401ea814ad0094a5efb001ea014aa518c0f0ff041fe003d30294eacf3801e7014a61d79a00f35da6c3b48b107f600f24adc5143740099a01294bdf7003c70094805288120f803c63a82af1050420a004ca519460527d462d883f80078200ef555da8149b117ec00f0001de0ebaa46970052651a34003b9
def as45 := bankPage 0x87997e9975996ba962995999518948993f9936992d9924991b99129909990099 0xa98b8065442e291008a9a08b65442e291008b88b655a4536291008c5a98b65412e2b2a1008b88b65412e2b2a1008b8a965412e2b2a1008b865412e2b2a1008a98b65452e2b2a1008a98b65413e2e2b1008a98b7465412e2b1008a99b8b65412e2b1008a98b5a512e2a1b1208a98b5a412e291b1308b85a45422e28211b08b85d5a45422e281b08a98b5a574637281b08
def ac45 := actionPage 0x4c3c2109400d2fd0493b1e09800d2d60433a188ac01d27f03f361720c0082670382f9535001622503029933100161e301e269099402417701b210e2d4011144017198cbcc09310b012158ba080100db00d110aa4800f0ae00a0b89ac800b08d006070924410a06f004050591c08a051002040289808a0330000000214011000 0x680c3598a018c0000003000ac000263a0af02405295225814e3800728042000010140002001000c011c460a541004e63024001856f000a057aa11800019871b4402880418400103c21a92000004d14082c026000022b143198000182a4284e0001d01d0b19045031a4301e03816041c0011c624880060cf58c4e0001590010000000544dfb838a214600234e0017106c63cb202d04c0800d92d7e05e400200de0341d001200400e980000006029f8d109755bc0e18c00fad4b001ef0286b1640a2e0750371400088003c439cef383a20201c1c4c2a00020815f0bc8068ae1202c0d823fd20e0d03c00540e07c0002bc186c4028c00006a001800363cc002e890303a3323f10d9001a078156f011c0006007b690004021c100581e448e5024005008c658201018b0043d0240000095880008e168001450480006500edb80f07460101e48016302a94327d38060102a271980715a91b1240006c00dc04a920680a00018079400709c621d20295802a8050180c02c604018502da5610033806032402019e0008ca3940702ce0001c5020ab100ad3880b01dc3018801a00632409024800000a00900700c13ac0001403295407900003c040000d01400738a4501a97acc04184603c071240000cc0300a0001e50000b2a0c40180000c0c501647ad2a418ec02c0002c4258160004053ad61001c70200048c00 5 0xedc63edc530dcba6543210320d930d930d9320dc930e82b252e76edb7321edb763edc74 0x21c1f18707c5dba819111914fa5139e694b893f9111de3240553ea19422834a273cd297127f2223bc6453ea15422834a273cd297127ef55b02c750ca1542477808a7d42283502944e79c72e259ac450d9b132244c778ed1994fa513a8740bd1792e4a212aa524a29409892e070a9551aa053ea792899c3321aea1cce9732e23846f89312151a564ab0f21dc3986f0d578acd3e67c6ceba2740e7ace39eb7d67ace54b7e6e78db15b 0x1358020f00412628be0d0e40208af456438ac34f5c61eb833d7047ae871c032068040d5d7b6871bc32060040c1a7860cf0cadd491ba95b99aa73356e3d29c7a438dc1902c0205aebdb439d801354026a064d3009a61d3483269014d2009a4012850e368040f0e81c190380a070040e0c81401028026a21c69008120134d0e35864010c7fc013490e35064050c7f800fe19e480d4310c7f600fdcadd4834c20498400fac1260834c00485a00fa8fdf0963e10097a58f680a5c004b8
def as46 := bankPage 0x86997d9974996b9962995999509947993e9935992c9924891b99129909990099 0xa98b5a51302a1b1008a98b5a512e2a1c1008a98b5a422e281e1008b8655d42412e281008b86a6542412e281008b8666544412e281008a98b806a422e281008a98b8066442e281008b865412e2c2a291008b88b6544412e291008b8a96544412e291008b86544412e291008a98b6562412e291008a98b8365412e291008a9a38b65412e291008a98b654e442e291008
def ac46 := actionPage 0x3321a8a8c00b27f0301c27ac800b25e02e192718408724902b16a515008d222027142215800e1f8023121e91c10d1d10210f1d98800c1ad01f0d9c0cc08a18f01d0b1716809015f0180912924093126013080e8a00930ed00b070a0a402108a008050711800c066005030491400c042002010291000b021000000009400b000 0x7800039803398e03a58602c085900b6018202d4501c00038a041562015a7101603b86031003400c64800200446580a510406580a3019e1024097100540120290016818000185001202956078005410c0218001bc0060400300cc2384502ce07258303169280ef0300701de01b1425a80003d603b00569d6a3000038007024846350618ca300067000c02008001440480e0014030000948c2031c00014c00846009060184c2018c010c0428009ebca00012990000038271856ab01203a47868dd5580e02e80044e231300c38218d8009070c10180000400a942f1a8c807160d9a4506400025e929de740080d4c604980f02c08401a00a0a800000034237b580080250380b5808d00500010c01a40752940028c5180004200061411014e0314271a81268088a2d40014e00014541ca5001a05a960908000b9c90040e02db10000100caf680ce018c102d254012f040e77a00a4200c0010201c0f105e67ac000000842c6641c66038000040048c8659961300063a400018490350079d2021c0403d806844009c0f101e60146848000501e3280a0108e50000049802004860040818c0401403 5 0xd74e77edb3edb732edcb763c7eb6dcba873210edc765430edc76530edc76543098751098520b320dc630 0x5439a12f25dc7f8a313d51a564ab4d6684bc9772023fc5189ea8d01a029b72b254ba059a8fa543a173ee79ceca8740e7dcf39d9552a16d2d89552a1d039f73c90a554a85b1146282f05087ce1c1f43e67c61c1f13e67c61d4383e27c21d4383e27c21d4383e27c21c1f1 0x34c4049880d32412638042e5f9b4590b4025e804292c84601370025e004282c8440136c025d8042a2c84001370b20f804db2c83c012dc0213804b10a94ec517c020e833da029ae012c04a1b8041c317e005360026c014d6009ac012bc0a10004200083601364320d0041a009b0012a0020c854a70094e01060026b80414
def as47 := bankPage 0x88997f9976996d9965895c9952a94999409937992e9925991c99139909a90099 0xb86a65412e28111008b86665412e28151008b88b65412e29151008b8a965412e29151008b865412e29151008a98e5a422e281b1008b8a965452e2a291b1008b8625a412e291b1008ab8b5a412e291b1008a98e5a412e291b1008b85a4e442e291b1008a98b5a4132291b1008b88b654536291b1008b8a9654536291b1008b8a965412e2b2a1b1008a98b5b512e2a1b1008
def ac47 := actionPage 0x4628a791808e2a9042262415c00d28203d241d93401324903922978f009221303321910b40211b002f1e111c010919502b1990a4400817d028178d91800b15c022140d9c000c13801c100da0000c1140190e0a91800d0ed0160b0a1840890d20100a058a401c07e0060a01820118036003058124400702100000002c800b000 0x2409701603800c400000b0ac180ab0054b02c6011cad40000514e00000641c0642c0d5888101c000004e6150a7a40a001e759beb95f40021bab2228901e305813a83e006de000200010520358315ca67a010544092020f038140c1e57b5e0039c110000000060600a14800081ab4140001c0c200cb20c047022aa3024100e07214b019ff6800107060056605000200151f09606a9a57d40e0782d000012a9c35940d0000e5169ac3c6001c2023a0831c0c0340900de01342050c004b0002ace0208e002860500eb380201012b0000819d2d7800061d420380138027004c7000e34050938c400000803844100e20a80349c00628c8009000006502c000244270141000251ac044840043c0a01da0000c303c00038e2081a31040008c0d0140608006080c94900008048080e0224cd000e0180004b400428041384600004395ea00c2070100039ee000000814071c606c0611144521848224400000071c0a181df02c2a1a8000016a01ec333d2000d0011ce0011a04300228165f01e11e1c03900000c406804718060580000a0e0004600000d009e068400280c460ca305c4cc80264a0a00014301180035a0600ca2bde70000e281055880569c40580ee180c400d0031920 5 0xedb732edc6321edc9876543210edc987653210edc98765432100987510edc7304dcba54321dcba32100e7 0x3a073c4cc984ac952b716d2d88727d4f99f18727ccf89f53e740a564ab952fd5f9a46b1126e38ac7542a1128a173e30f21c9f33e32121e43b872b3550a9f9090f21dc39542a7d4b2468770e4f99f19090ee1cacd542a7e02ac7b11226322a14a2748d417428750e684bc9771863045189ea8d01a02 0x32488648c0088800fcc32218044335884591080a6c864410088234f8419f086440008807cfc8c5f9074420c8840510802210643f0087e05374021ead43b2c874010f04a19084320c86401364321b804375a9a0ad3401a670243b00876010d81268004d00699c090e8021d00435009ae010ccbdf8834cc5a982ad305563c23478438f040f5869eb033d65d8eeaf1dd563ba4477468ee871dc4a1e0843c0c878010f10e3d86432008640d320126380430
def as48 := bankPage 0x83997a99719968995f9956994d9944993b9932992a8922891b79129909990099 0xa98b654c452e290908a98b6550452e290908b88b655a452e290908a98b655f452e290908a98b7f65452e290908a98b8465452e290908a9988b65452e290908a9a48b65452e290908a9a78b65452e290908b6a98b65452e290908b88b65452e290908b8a965452e290908b865452e290908a98b5a532e2a1b0a08a98b5a452e291b0c08b8655d412e28111008
def ac48 := actionPage 0x6f24d40e801047706a21ce1b009842f06420478f409a3e10601dc19700953a20591abb1b409835a051183616801c30604b15af9741182be04212a91b401a27003b0fa29b401722b0350d1c9700981e302b0c958780a816b0210c0e8781260f90140c0783801b0a800c06862cc1950690030203258016027000000011808d000 0x4062d202b8001a06002c0c300e0300206092f7a92928003718e7285a20411e81ba001a655940000013fb9a37800d500a64bec081f931ac14005e3dc403883a002bb0b4000b00200ad32028ca00136780b954ff10000b40ca00100040ca0d0dace00ca72cc06a4653840002da03d06100040500001b90da800a0fc01018143381703c0b0356d028007814a02a2ad8004881a9001fc181c0346823102ea2700b81d363c770441c3b5405068000040cfdf315fe0082cd017f102418300c403519a800700082063ffb8fc50200022f722c03b48d801f404282a005c006b8a2a80a002f4007d07919ac30000db8280000249041001c301a60428e03340e398b97af2b4837f000013a191680007c5660080203001d6d54183a4035e0a62f300006ff40a00002053a0507a0036f8af0073280478814f0295e74623984ba11865b8009b680023a4fe00004f600000e34c09502500654e600200234202d03bd8e80017d0399f9000d1a7e00080c01120002208c36b01a750881c97a570084d600003e68e8b0010959a001130b24800157e03a064eff038206800001c0e4ff8040140f5e8005076cd8e098c006bc040580006f116eaab03ce09380f9055c8240a00800edfa30015800ca01540c00000d315000ee00fad89b120704a6d80054984a44c1bcc413246e09dea048065f032f6b000ed8ad5a007703cd0202035d8b8819130005bd4021084805060dd42068193c01c1030ca22400280860040028c090350101402df0160300a7a8092000571440314c032464021a30080048403330e005c0200223ba445000c2019201940d783e0dd5813458c003e402090048eb00140680031138000c1c0c5166480e038e07a1a602400034000b1e80086a05d8069400200067803189520aa4103830c01a800e41c40000aa2b50290000014421c79cd40182600436e0254a5898357818f80e0403067d81f000cb02015438c003e604812d281a0510fa00000021004187b3830df81be7bce4420a9000006008000400314ad63d290140020c6f00020 5 0xdcb9854310edcb87653210edba876543210edcb87654320edcb876543210edcb876530edcba87654310edcba87654320edba876543210edcba8765430edcba876543210edcba876543210edcba876543210ec7ec7643edb632 0x3e425c4b4046a6a78d809712c7c04b896652a78f809712ca814f1f013025c4b2a053c2604b8967c8940f809712c949281f013025c4b2503e47c04c09712cfbd281f012e2584b897ab155ea1d3f60ac095c2a34dc9592ad78a5349966ab7544a854fa53740e7899930 0x4e6008b00139402528045e008ae8cfb01a58824b1068ce0919c022b43c4f069c601154320d21bed569ec053881254004a4048c2011700229ab4f6009c80928c025180460048b60116c0229004e30a9ae1522802288a4374a7e0013d00271034d8069ac012881a4583489008b401140127a024a706910c717c122fc3c4f0089e0538c2a6c9a48d349040113889f0834e7049c4013881a57824ae0095c0d1941232004640089a0d3c42272814e50495a012b4c63f02463008c6011304a1f834e6049cc013982272014e4009c80d2b01256004ac068c40918802310044b029c2013840a62804c500986052fc025f8044a009be053795a67804cf5697c012f95a24804490487c192340222803f4
def as49 := bankPage 0x86997d9975896ba962995999518948993f9936992d9924991b99129909990099 0xb88b6545422e280908b8a96545422e280908b86545422e280908c5a98b6546452e280908b88b6546452e280908b8a96546452e280908b86546452e280908a98b8165452e280908a98b8565452e280908a98b654b462e280908a98b6550462e280908a98b6557462e280908a98b7f65462e280908a98b8465462e280908a9a48b65462e280908a98b6545442e290908
def ac49 := actionPage 0x4736ae92809233f04334ab11c09230903c342387c0232a003a2ea2ac80082880342b9d9a801524902c291996001520a01f28128b80231a101c258f95820e177018228d19400f14a0161d8b29000f11d013190925000e0f300f1187bcc0120bd00c0c8628c00e0930070704acc09106000201832cc01003000000000d8090000 0xe783660000a8b500000008014d013427b580038806c00278222e354871cc00000092401684067340740540101a0614207318c280040000000960605a7514ee234050b9c8d9b940013063400ac8023c38f635005b418a800c02e1f8cc07d800061df071817d805f300000cc403a383301480a00e1601b07d6459800e2c00c8c6d9a800014807a8400140f4814b000253ad2338004967cc601b905006fe2a5180009c68008e7bb37493656a019c0800040200d00013bd3401f4115024047141002c0900c02e066900031241c5809103cfbc9020201d0000ed782400021972400e2e0a0481002c0a0020fd800078018bab4db3c07a81cc480600b5a6a0c1ed00007a47061561038000022621c887edda8604a757de846e95c40000007000089a9339ae91035cc10004110065804e420ee0880068184014a3030c0001a000c404ad20088403840279dc5320a6108455980028400008cf000a200107201a003c8e01de001d02609e10000962989031c80382a539a3098e003400608e0481400112003c031140b194654918a02c400000032c0100188017eb028098801a644a2081e000380005a00000a8732900372b146779622333a018520181c119c02038e570169118005000a301c0280400016441ae003c40625c5200015bc0902dc0002c20846c8a160011a0484ad5810701c0d01102c8da918008f400908015001e0055455180033c0ddb4a909f6e300a0000092800340c6731407380c708c43284e02bce870008311000012700000 5 0xedca754321edca730edcba987654321032edca875321edca8730edcba987653210ecb431ecb83e740e740e74e74e74e74dcb730 0x39d1be3405739d1be340570ae7e4f9dceb97604778c518322a3404e39d36c6d4680560a8e75810d00ac150800567e4340678cc158fc8750e41a033c6628336c6d4ae1151a01582a8540a6fc9ceb97686c11811b636a455f939f73ae5cdb1b535c54ca91151a01582a8540a6fd1f939d72e6d4ac1572ac45c2a3f47e4e75cbb0236c6d4c511708a111f939f73a6d8da9891d415c2a0530a27c84b896 0x52f40a3a964676082291208b23309445407c2053b80277014bc00978051d0023a16465009e0011c01a77004e806976631d0023796464009e0053ad224080473008dc5918c4a221d442009de053b40276804ec009d4053a40274814ba00974051c802390046d2c8c4013b8023896461009da091a8023516460009d8011a402759645e467dc013a8025c1646b008d0053a0be389645c009d2012e402361646a2c8b6013a01a6d98c903191e59168027380459
def as50 := bankPage 0x8a99819977a96da964995b9952994999409937992e9924a91b99129909990099 0xa98b65422e28100806a98b5a452e291b0807c5b865412e2811100908c7b865412e2811100908b865412e2915100908b88165412e28100908b8654e422e28100908b88065422e28100908b86544412e29100908a98b65452e29150908b85a452e29261b0908b8a96546452e281b0908b85a50462e281b0908b85a50452e291b0908b88b65452e291b0908b8a965452e291b0908
def ac50 := actionPage 0x3a2e371881902e50312a352100172a0030273398c00628e02f2231a9018827602d20ac0ec0902460291da919800e21c0271b2595c00d1f5022182299800f1c8020169e8e001119501e15198e811016501912939700161230180d932840061110130691b8c0900e100c030b9f009a09300601858f001a04500000000ec017000 0x3000148880480c20800468141030040000419824001e9500a01108738109c1cfe61c007c1000801357b4d380e378d20e9cc0300050128e003820880f39c03381e00640902403038e042ce00300103c0801c42081c5280007adc029000624a00a5ad039402800261c87401c019000334e3701cc001460016d6a58933c0a20169000ae700085000002c0d380c07358f600091800d00c003992861d6d73400301810000002c05294e052c0713c0603801229e31ac83684070000b01fc56088f01fcb504007044050cee781400a0047814869420000005840a134ee50042089c0000225810a0290040c6c00089300c63ac005b16319d404ac00000e848da64000020009624002880040002105ea500ab0228100816808c0ccc003b40800a8f628200200f12822000965016cc003318c00481ed32000591e00000b49420400071214413c0a501c0058ff04403038659008f32400049a8320a033121011204b8615803d03813002041e00006d52480004a8500780b93ce07479ac83945d97279c0001522181a6a000053d003a0e0eeca3854f2e8c0004dc096df5002820493d508405c000021d19bc0401400f7ba0828fd510d260f68002007c40107ce0e80113b471402af05000024000b0a0e920e5058b021a30391c2882138080060022380000000182c07800f014c8030686162f 5 0x746543320a320dc987653210ecb731edcb730edcb43dcba7432dc98765310edcb987653103e70edcba8765310edba87654321edba8765310 0x26e4ad954e85cf28cab54a6932213e87ccf91f17405ccb414213c08dfaba03a2728d39732d05084f0238787d84c4aa7e65a0b39651d92b6553f368c72a58cad954fd9f99cc87b0e8fa1f413025ee9d2c65ea844c5887e6e79cdb6b686c088b8d013b74ee5bf3740e79a3307604628a594a22e21041dd36aab1d4f89812e1f0f889812e7c44c097 0x29f0c53ccb279804dd609b4013681a7a024f4069e6093cc0279004ce00998053000260004860090a013c40249004ee0092001238b2459648a467e2c33cc026e0048f2c91c59224027380487009e2011f51a422ac7c008f886fc8fdf90047b009d65f244be419647a1088601394026697c8c2f902011e8023c88442009c60d2c0be4000478068cc21104c63f97c7f5d8f8011dc4a2008440
def as51 := bankPage 0x85997d8974996b9963895a99519948993f9936992d9924991b99129909990099 0xb8a96545442e280800b86545442e280800b88b654c452e280800b8a9654c452e280800b8654c452e280800a98b8365452e280800a98b65504c2e280800a98b7f654c2e280800a98b84654c2e280800a9a48b654c2e280800a98b5a51362a1b1002a98b70452e2a1b0803a98b5a452e291b0804a98b5c422e281b1004a98b5a432e291b1004a98b5a4136291b1004
def ac51 := actionPage 0x5328270e401332d04b27230a00212ca045251d92c01428e04023980ec01425203822928ac0a01f20351f9019408c1ce0321c8d99408d1a702f198c18c00d18002a160b1c809114d025128a1c800f12001e100795400f0f30170c851d40110c000f088321009508100c0683100089066007038218800e03c00000001d0014000 0x50cc0014603754b6e5a00206018800029a7601cc51dec436c04226e124001800062a015a8073040a692910000799411eac401081700000b0000218a0b00606d0800007020004068b13214a03c0c40528d7c2002d911ad882989f66c033040d60017174070681011b40031896b81c035125595f0519500a7a6c7c220018020000dc002840cb7412861960701c00de008080f34010000012918017b006491e954b0000c1001b89c08a74163424022940528809140000de51a40c1800e60000500d47a16001120a8001488010000000dea281267292f0004e5000b288016a8e0b240201989518817a1400240d0b5606980362809014207a8004ac60319ed500000000e7300b021c1380a03352e2b40c5a4e40016a40000014a3000a528c000300029c0329c040252978c09081c000c034ac041b002024e45080048060029285348700d080000101c60481802bda0020200180d108420018001c000084830d08300033188a00824499e07810030000034e6501b0528054140d72caf43180004c1002a0011401b9c2013ae49bc045ae6079c2181680782806ca0f881204a0201400b00c90380ca500016c1023802c14095b920030a37822b0001b608004281500000090f7026fe3812023840acc0030145000a520442100050008601c6610041000e0004000140703c0c031006800228c027a8e039dc05b0054350540020e81607800070800523600334e22c000601f68140400718809a8b9c023c5d80ec605607 5 0xedc765430edc65430edc98654310edc98654310edc9865431098520cb310cb6b6a5ed743ed6437643737643 0xb5c4588911a22d6b88d1162256b88b11223445ad95ae8784588902cb656ba201162240cad95ae88845889034b656ba2211a22c4481a5b2b5d1208d1162240dd438a314227c4eb6d6b6a1d3f54c87d0bd78a53499672a2540a7d29da09592a628d298a30f21dc3a8734a6934518790ee1d439 0x3a9b2592c002582448d1291a053f4027e974bb2c976052ec025d964af0095e0d3f4027d18cbc06978592b80257014fc2c95a012b522460948c029f6013ecc65d17cba06974092e8b256004ac009fa592a00254004fc2c94a012940a7d164a400948013ecbe5c824b92c9460128c027d18cdc069b8592880251034f9049f2050c002180142e0085c00fac027c814f500992013200263804c400984093dd5a7b004f6029e8ad34002682b4c100982013e15a1e8043d009ee053cc021d8043a0085a093d8027b034f20086c010d411f5003ea
def as52 := bankPage 0x8aa9819977a96e9965995c9952a948a93f9936992d9924991b99129909990099 0xb8a96550452e28090800b86550452e28090800b8a98465452e28090800b88465452e28090800b89865452e28090800b8a465452e28090800b5a98b65502e28090800b8a9654536291b100800b86562412e28100800b88365412e28100800b8654e442e28100800b88065442e28100800a98b5a4a2e281b0800b85a504c2e281b0800a98b5a452e281f0800b88b6545442e280800
def ac52 := actionPage 0x4d35b02c81872c404332291f809b2730412aa83c810a25503227219f401f1f802d239a9f80171b30241f13a7801b1620231a92a4800714d0231592a8000513e020128f99800b11d01d0f8d19408a0ff01b0e098dc08a0e10170c868d800d0ba00f09069c000f08d00a05849d000f06000502041c400d0390000000120013000 0x724b20b00004004d2800010080c02cf00a0002800d530a5d83d64570000180846806550000046c91000000cb00008334e7c000601c70020108b24400200c1d500500001108c74f3c944e0c00006d244800b14000100004570001a18900c48058418a000e6c02b00066f0206cae6c769000513b40033dc0c800120292c00352fc8e158802f0192c0c45f80010a6802105d02cd29c3c0a003208002c5403801cf80fac04001e95627c040000f39000100700b2c43c00146040401020000490007870c601b65d00340308035100901118e4c050f4cd00038841264f00000c55079901235138e01e0000400000102401033030140005c919755300321121954000d40300224000770610000d00b00659764058054000024b31d39a0002c30040000041010c60060c028b00200a10108d1c004024008000d0000013001c03460040001c81431cd20028f0c020a14010000a0003c00000c00c034010b3063471cb08d1c70081420c10c00000070001c70091402c120f2c718014104200028800b00c14700300a0c20092041c02c00401060000073800093461802ca24600000334008020c28f00000c0843000ce0002802ce10128110018000918f3c00090001003431400060002001000023031c61860c118b24c00034200228400d2800401800021802802402c00c504a1c000700024e0020010020080020863000183801000c834c0073c01c000604b0020002802cf20500c20040834d28e18d00e08a34028c10200010c 6 0x30edcba987654320b0edcba98765430edcba987654310edcba98765432010987510a9820edc6430edc643c3105edc65430 0x27eb2c604b18cd0d01802744b88b1073f5ab2c73343b8420249facb1812f958c674cd12f1a03005d09d12e22c41cfd33a668588830b2099f41b736c6409788b0466dcdb13225e2c4458570a808dc1b523806688a9041d82744bd889371c560a7941e2603f04e03ab6d6c22011a22c0cadb5b08804688b032b604688b5b023445adb5b4b611008d1160656dada5b08884688b034b6d6c2202aa234458195ae23445889 0x280004ff009f8633c01a78164eb009d6593940272a344410888113fc0a7f824fe009fc093ec027dc14f2319de0d3bcb276804ed2f9d2593a41274804e92c9c801390b271804e33c9b2951145222834fd009f5093c8c677034ee2c9d0013a0b271004e200a006b364b26c804d9009fa59360026c164d7009ae5936c026d964d6009ac63374be6e834dd049bb1133a1e67164ce0099c013f0b266804cd46922212465e6d324da8899859300026018cbd0697a592c40258b0418
def as53 := bankPage 0x7a8872886b7863885c7854884c8844883d7836782f7826991ca913990a9900a9 0xa98b73695a452e2aa98b655a534b2e2aa98b65534b2e2aa98b655a5345362aa98b655345362aa98b70655a45362aa98b73655a45362aa99a8b655a45362aa98b706545362aa99a8b6545362aa98b6553453e36b865452e2815090800c2b85a502e281b090800b86545442e28090800b8654c452e28090800c6b85a50452e28090800
def ac53 := actionPage 0x613aa425000d35705d342235011132404f30a01d001c2d004b299eb8c09229a03c269c99001d24303b231b1cc00c21f03a1e99a4c10e1f50361a9820c0901c502d17151d801c171022141398c01b12000910929c801f0c30070f8c8b0010093005098bb0810907800308070e4010048001060192c010018000000030c008000 0x4000530d00a0072811000002c03410073813813cd00018900b0072491c01cc18e15828034d00d3cb78610d0400cc7c02040086c00006d300000500500d0003035800107c001f5c454100c0c000014018000074b41655e00449639048179450a50000044079201500524008a5160137902150064824523400d73da71248000000031201a65000644919d00d40001800f0002d82c060e0000007802cb5404120120402860d700f01121b3cd34d7831c56801463d840024041b00010525f7000000410cb00600e3402c02400007002007cb29754f70000518060b00e69d7df5ce00028b7c60007c46dc00025e4ce3400800000000003403802ce30418c18f24b00c10724c1cc20b00034908f2c40001402c010d2c01c41820c30031ce00000004434008120700210000828000524428000030c3870011c000b2491c71032052c008518e00534000f3c00081c058900f59b2cb10001901100c0011860cc00001d74800001034020e10319600330300854824058421c00004c50a74079c2800013c038018800414000000a0051d70050c81cc1120020021c01820c009811250020b4c50002d000000000c7801c600011014000000411420100000000528744500439228331248014d68000c000012761f800007c46d901a00406200001401e08400f29500a54008ca7a00009d01f40d600232040007a550000e61d34157c050000000074045e05c44cd4015c2c060b30200008430314024400018a0053cc30a0002400042000422063ce00100000000504928200a00a00d14a00b0003c018700a0063cb2cb0403400001c00020c20050001003801cd24e00a00000108b10500330914e00300d2c230608c00f0091cf6990c540000e5cb0000000825cc00010000e54f0085c941c0080113850042411cf30800e00e00b00e00910f0090070c034e 6 0xedb3edc3edc3dc3dc93d63db3d43ed9643d93dcedc987654310a1edcba7430edcba984310a20 0x24abff7c0c5109a1142064465595766ec9d837a63caa14027f4fa970878ca7fefa9ae35b5009fd3ed95766ec9d8367600bf94c2804fe9f52490f194ffdf535c5009fd3ebae4268450820932632a4abff77c84d08a1041264c653b075c84d08a1041264c87bff7a2ce53e213424845ffb394f884d09211bcb792ec5bab0d616c208e046e19aa2e133a4c88b90920a3b45189e1302341182211a15c13021856cb0f319a314608be8d01802744b88b 0xa9a2b5891db123b6200a98b560748c0e0d6edc6dd035ba00a64014c402980052f00a5c014b402952751200a24054a402930051900a10917f802e9835b508b280563802948052800a4e0149402918051a00a300145c02838050502a48054898efeb1ddb29b64516498efea45fd29b680d6d09ec9015921da4c014980a8f0061006b6c0149012918052304a4001480028f8051e04a08014117b02aee0558be8af7d126fa245f41fbd83d7b04ef6095ec00b9c1944002880050f00a1c0343402868050c0ca12014243283005060ca060140c0281164f1009e201404027f964e7009ce59398027300501
def as54 := bankPage 0x74886d7867685f8857884f8847883f8837883078288820881888108808880088 0xa99d988b65453629a99b8b65453629b89865453629a98b6e69412e2b2aa98b6545432e2b2aa98b654541362b2aa98b655f41362b2aa98b6e6541362b2aa98b655a45362b2aa98b6545362b2aa98b655145432e2aa98b655345432e2aa98b736545432e2aa99a8b6545432e2aa98b73654b452e2aa99a8b654b452e2a
def ac54 := actionPage 0x33382299c00d28502c371e8a001923a023371a820013201022341a9800071ec0212f1829400b1cb0202a14a9c01119801f279195808917d01d248f99000b15c01a1f8d29400f12f0101c8999c01c0db00f198818c08a0bd00e1406acc18d09600c10851cc10c07200a0c8321010b0510040601b4c00e027000000030c00d000 0x2c0000005081c110d8378804588e00212c00c00000a730040000000380c02cae000205006021000001e25bc65631c35010b3104869c0002d6f1a8e04b4c5b85e26a80943d0702406208ae225e480000023170040803980a15a0031c0e80a06836808171515c003d0001183308673000000065200403940708c092a04b530c10180030000681a0384af015ef01540741e6e840870960001027ac8bb880a00c00003e80380f000ce100182302d480035bc282800d01c635ac604a060000c20184c1bc40215a0001605000f2800220064620c501e0262984b8160038c0a354e284004b8097b04b60000755c00040e06408021c602de0018130100c700e8001380b4e0aa1604840301c03050431a400eacb100185bae409a4070010229db27200b0306009480380013000c03400708021906238002010c60140059000480a860006480803a802200800000202dc238c0e38dc2029c803c400014f034c4000e26b94440000290206000f48027034c000d0e42c2068141011aa001a0070c0c85b9581db882cb5787ba9460050000200901408e01ccb0007029e032c005b4016100f664001828851a4d0186080981 5 0xedca510edcba530edcba510ed430edc4320ed4320ed20dc320edc9320d43d43d43ed43ed3ed3 0x13b18f31a6306502c0c61857f96f2dc5b49e13ab0d05de437662aa00d19982784b2002815009f8d193c23635c3082c5fe70c9e13a05942d7f9c32784e8163b4766ec540a804fc43c65061059001e9b5d502a013f2e75ca47c8d8e11af619cab6867ec057faa94fe9748d8d762cc558a2f65d4b946bb886ecdd593b155ca7648dca27fef65c0b7f696c517c2f6556638748d5738dd5953274fa9f13d9da3b263892919 0xa960953402a68254a00a940152412828050543ac61958c02b19ad4b2ca960152d56a4a354910a920151002a18054200a8201500028b0153e0ca2a014555effa45ff00a7e014f8029e8053c0ca280145032898051300a74014e56ac4805387bb8857484029b8053600a6a014b80295a8d1206b6e014b4029614520
def as55 := bankPage 0x70786a6862885a8852884b7843883c7834882d7826781e8816880e8807780078 0xb88b65453e3629b865453e3629a98b654f45433629a9988b6545433629a98b655a45443629a98b6545443629a98b655a4c453629a98b654c453629a98b655a54453629a98b6554453629a98b6559453629a99b8b655a453629a98b72655f453629a9a88b655f453629b88b655f453629a98b7165453629
def ac55 := actionPage 0x54143f8a802038a045143d014113351044133a09808d32a04111b50e80922f403f10b189c18e2ca0390fad8a001b2790360ea80ac01024902f0da28ac01b1f802b0c1d8e80111c50210b190a401a1770150a150a001a12901107111a00900f9010048e15800d0d200f028a12000d0ab00901040f001e05100000000a001b000 0x1175c80001c00a7400268a0e8084088400d017348c0058600a0f905e5e8d1b1801f1befca0030074cb7d02a0008a001440b10b3c8f63480172da61680006832f0300e009206a8609cda190000002f268180065c03d0aa8bc00003b908140295e1001600008300006311601880029c4400847698ae0212a000030008a001cd3816012c420012a00080005c97002d0b802794e501c0339de001c810000f0952911823180800000300806400a611d0503c47080c00a1e8411a9088a73000303d60780c01bc0168069681880340c500003bc06035605246068000015a4281012b00d00900315ad195005000031d680218b02d2100066181c9000c06800533c0000161580600300358cb2081a0be00aa18c0da9b81a6e07816cd017d801c04a34001c402276e0730bf80000692a1a80000380100206998160040380005026039d850280003c2639c0f029e07200a59aa862caa1000e2295ae39e00ac00c2544500064826000860580000280a3d580c101e03cc003e4000265322934c0004b55e31dd1f280c59a40fc9c40000000303a3a8b30042a800008060003b1002f16070d0240c0240b18000aec6807dc65e9124a8a03f5310152ca83d1521600004f5888001200561200183b700013000ae35005afae0152002cc7080ea1000039c0502c0000840010e30ad85124400a8020040978060014c028de00000f001210a0081004d32ca0000e0383e03a4e00281d22c832a8e2400024df8604c00388a070001029247186a07c1b040e902a82001c0282e341e600003980d7bd80eb4140e4153dafdcdd2f87003cd04860800c00001240327004034ac0e0ef292001700040002c05da4c01409050c56fcb304400c9800f1819 5 0xedcba54321edcbaeb7310edcba75310edc6430edc76430edc98654310edc98654310edcb865310edcb85310edcb6510edcba530ed6210eda65210edcba6543210edcb6310 0x2f2d0b0140017198e0000040000100000400001000824008000020000080053084031861058001048cd1963280020a19404800ce21940481702c 0x2f57158ae20159402b109d5704aaa01555269389d272fa1a5943412868050d2ca160142cb2850050a06acc0959802b30456402ac8015901aaa0255400aa863430be861650c06a180943002860fd5398ada01581a2a70155f00aa20d70c02af8055e00aba0154002a70155c04aa00151c1ae10159800ab80156c02ad0054600a8a0556402a7ab5261da4ce36cc1ad98055900ab00155c02a6b7d0704a0e9d41002822c5f857bf0937e122fc09df812bf00355402aa805543da0c5f41812833fe047fbc0536d0a2cd0354b00aa69766856cd26d7017ae10f57402a9bfe046dc08536c81ad913d9a02b340153c0aa480508
def as56 := bankPage 0x7678706868886088588850884888408838883088288820881888108808880088 0xb8a96545362a29b86545362a29a98b655d45432e29a98b6a6545432e29a98b746545432e29a99b8b6545432e29a98b696545442e29a98b6a654b452e29a98b74654b452e29a98b655f45362f29a98b6545403e3629a98b6559453e3629a98b655f453e3629a98b8465453e3629a9988b65453e3629a99f8b65453e3629
def ac56 := actionPage 0x4822ae05c01f29103c22ab01801325803b222905010824003a21270900892250391f2491400a2070381d219180081ef0371b9f8d00091d40351a1d0d408b1b3032179b94c10c18f03016170e409015f02f131399c00e13502a100f9a000f1080250a0bb200150c9009080891801c0750010284ae001802d000000016400f000 0x7570d90100056812806c66854527c001b15100001401b00078a00c4950066d00075c004000074001f00344b08b78408f0001425cb49a0023082001c171950004040238074010600000000e0c400b5042060080455cc24501700010014701e3c229f2c54010411810402c00000003dc0440c40001871c00010050800000400040060060000060031040800420c61011460001c01c500100030514024514d2413451c000014508728000400000934030700008200030200034f2cc0c03800800400041c110100514500000210010314014000700208014314f1400400001400000470081ce00620018000704104000000a00000204000028500018f0080020c22460c11450c30ca20904a3c80010002c00002c00091003c700a24000900410004024c00500134028028200b00028c00038d14400020400330c0460070082c00c700300000a34b08114d20e0007074851cc39000020f00019a6405c90041800c918200015460241700624000e40e4c00142c100800f0072571400110150000c500e5800c00197c958600548c70501044719470f0000181cb002381468380163340ec03c02c000047d01301100044491e00f01d000a8a4d40060164119c07826fcb2100196802d0140088c371b7d010000ac2014030fb23028a840131c000e21435120e45e0513912c028a00f0030847c120500000738225e3000004803c601e00038160178f18b0c84c000001e5c01c00001010c034b0c118200d0002800c020300b34b0001c730a0060081490000070001c8 6 0xedcba40edcba4d743d732dc732edca53db63dc732dc2edcb86420dcb6520edcb6510edcb6520edcb50edcba510edcba7650 0x1098954a025572a5d4a04b172aa93304b1091f01109f5280954fa9ed2ea5025802404000bcb25a3746c05c0b2f2de4b0f61000800b2b42a71ce29c338236328196184008009f93ec31861bc942a7dc6e8d91adf198d058004005e4a1742a35863 0x6b780d5e422ba0157400ae49156812ac0055806a78094a002940051d06ae6095cc02b98457102ae2015c41aab8255700aae0d49c12938052700ada015b002b595d4c00ad4015a402b38056873a2401448eab00655103ac40159802b0805562fa200944002e6835630ca9e87420328443df986bf3097e60efca4df948bf2277e44afc805a401aca0159402b23c56155ac20958402b097d0f2ca1e0943c0287a1d063fa0c7b41832832350343a062140c3281805a523ad60158c42a6b753823a708d414428280562
def as57 := bankPage 0x76886e8867785f8857884f8847883f8837882f8827881f8817880f8807880078 0xb88b654b452e2a29b8a9654b452e2a29b8654b452e2a29a98b65534b2e2a29a98b655045362a29a98b655445362a29b88b655a45362a29a98b655f45362a29a98b716545362a29a98b7f6545362a29a98b846545362a29a9988b6545362a29a99b8b6545362a29a9a48b6545362a29b6a98b6545362a29b88b6545362a29
def ac57 := actionPage 0x553241a6001238d04d2ebf1d41123570412dba0a801b3060402938a4c00f2d903925b39e801529a038232f16400e27003320291b001622e0301ba42680921f802f19a091c00e1ce029141b2ec01518f01e1017a1c0181470190c929e80151080180a0f15c00e0de010048a2e801609c00b01051e801505d00000000a801f000 0x8ed09ea0000c568160b9734364009000a0032a6301324163703072a10d014140027c0083b2000064403938c5a4a7228624501600300006d31059f0f5c003b01f065ce01402538e00dc00fc0047e000594054b211481c2b0009c0140cb4ea028003824721af50010d041b58f0464b811580179018d0008548000034290000000c01080051000040cc161d200246a3b8800011798006a02a4975a000009280600dfc0770e8c000058400000603f03775529001a568008b298c038e02b408000030004270000381a7000470a9403a56011d28629806481a00011039e0a039388c0c220323080005572011660741859b69691110701239580f37e3100c0375047b4085000904ac05037b02404f0000d7732e4dfe401b30204e480405b81b57c0000020001c510129114874846240002500020012f580004100059abd6a41a38333075680762023660d800607d990166a71780000000d3e3ad34b765da00000c953200ec50252004c0f701a3cd4c30518026c002b249002a04000ab100092a9895c4c45803074e0ad8186b5df1440a0038a02000058191a40007d200451c03cde78006000138198c415e0277c3b4400009480002f48ce85bc040016d001a101c03008600010063404018615ac20034c743798a18040240528000f8373099805bd608bc085a00000003481c0b8306469034353a92fe69ac180640770180602809a000068001be83bfca00010d1964c700ab05864774064805607d81018004814d0040205fc6e02409a5f602cce437f200284a8000c83c003d006c0603596093c030000f0036037da122cfd1800cd741bd00a16dc010d37d33814da00e 5 0xedca5421edca0edcba84210dc3edcb543210edcb85310edcba6543210edcb654320edcb310edcb6543210edcb540edcba54310dcba530edcba54320edcba65430edcba54321 0x4007feca94027f4fc9f4ec92c654a013fa7e4fa4b09535c50161a003ff702d71952804fc9f6f2cfb800ffd098eb0c29f90b213422005d9bb276284d088007feecdd93b176084c650610009f509a1105cffdd8bb075eeb99d2132903d4308009f7001ffb3a50085831861800ffd09a113180b00027e4fa84d08863800ffd9d27e4fa9f1099d505c0b0003b176084d0899205800200213 0x182a51454a00a62c1480a2902ed7675ad2a75a5eaa0095404ea6e014dc0298005784eaee015dd42b42756802ad0015a1429b2753602a6c014d802978057781b7c0d6f802ba8057400a38df450428a0057363baa516689ecd1459227b240d5c196a80651502ade017400ab70054f56a4c01498028c835bd00b4c1168c0ad18057200ae201494128c0051873a0edf41db2e10057000a980148442898056f00b9e015b802a68054a00a4601480028ba75046dc080d6d00ab836d6c0aa82015bc12b70056e04ab20156402a48252900a520149002910051e
def as58 := bankPage 0x77986f8867885f8857884f884788407838883088288820881888108809780098 0xa98b655a53453e361ba98b6553453e361ba98b7365453e361ba98b5a58533e361ba98b715a5345361ba98b705a5445361ba99b8b705a45361ba98b5a58533e1ba98b654b46372e28a98b696645442e28a98b6a654b462e28a98b6545362c2a29b88b6545432e2a29b8a96545432e2a29b86545432e2a29c5a98b654b452e2a29
def ac58 := actionPage 0x4337a29c80092b803a3021bc80162760342920b88092240032221f38c09220a02f1e9e1c800d1e302c1b9c98c10c1bf029191b94810b19e013159a1cc0a013e012111825018c11a0110f968cc0081020100d9510c0080ea00f0b9012800e0c000c088b1a800f093009058799c090063002050187001a015000000028c087000 0xd2780074010068c00114042018e794100b40003400b1404002625f820100ac33a2200007cc000b17e098000364b401800ab6a48a2008c817020df5380cb80007440300405c00001800505bd5086480b1c4300038acc6689b0002a50000682c40031603a4c1037a0690000006c0204f00131131a4400002002c3394003540080e060000001e039c47501690180f001a048801000e01140a39c4000840281e033000018c25014301ca0280e710140009e53980108040108cc0008739080008400100a001001f00097800b4118000a8b024f0141f002e0076a525cc068c05758f2db1701df800e020280b9a001d00014d001ff00743b40c0d1a099241621291a4eb33920201a00000a034c8000277880502c415bc8130006298010008320400280c30144000c0139cc618080398a10940001c0051c0062d23001800240a1b1a0424c403c40001a63ac0b405602c8bd2b41901800d05a87d00a6000031880e02c0028ab0981cc704a034000000023c8c2800102800594a118100794e5328400000000400701e53480d2818abe6b102dc0f0e110001d2a4404001e2b90d481e05ac0218000000004f4c04817dbd5871815953d047976ad0060420e00386800123299870080c 5 0xdcdcdbedceceb6e3edcedc4eb4ec2edcb875310edca754321edca740edcba8743210c42 0x2c355ca76931258ce197796f2586b094526bcc783ce59a129b49a930898cea1742a4c49692b25249c5985afb14e20a3c433af2de4b2d656ca593b23572a9d27a4b35c89876a7b4ee92d24498924fe593a7b4f29da0a4135ae9ed3b422842f2de4bb56eeca593b23618d910a17c1b0298520a00ed0901f03c9782783b074a010aa13004dd9953155d49fc96376654c557527f258baa7dc207b8f65c0b2a33063896127 0xab7b51af68058556a76ab4ed1e9da353b02a1c0162c32c38058700b08ab4611a8c01d0d1ca0e2141c02c51658700b0c8d468028881d0a02a120142402c48050802a0a0162076930150480bd0536d0aed92f6135dc26937ad22f5a3deb46bd63f7ac7af58edeb1cbd6277ac4af588deb10bd60561402c281d8402b080361002c20150200a04015f002bd8057a00af2f7700aea615d2175ad8eb5a84aa08156b00ad6c552986a50053902a70014e176bb00532
def as59 := bankPage 0x7888708868886088588850884888408838883088288820881888108808880088 0xa98b7f704b2e2a1ba98b5a58532e2a1ba98b655345362a1ba98b885a45362a1ba99a985a45362a1ba98b705f45362a1ba98b706545362a1ba98b736545362a1ba99a8b6545362a1ba98b7f7045362a1ba98b5a5350362a1ba98b5a5753362a1ba98b5a5853362a1ba98b7f5a53362a1ba98b715f41362b1ba98b715a45362b1b
def ac59 := actionPage 0x23409a8c418725502139193cc01022501c32173900921ef01a301590c08b1ce0182d1399008a1b00172b11910089195016278f1d4091162015230d25010e1380111f0ba0c01010800f1c8a14c30b0e700c178829008e0bd0090e86c8c00e093007078538c0100630030383a0c00e03900202020cc00901e000000011008a000 0x21000601046300022184a21001a02e70c9cc90000200011c284020109a000f037114000005153028990240e980046881f681c300c5b71ce004040dfd70b037f9940b00120041231aa20a000f71c2100406084e6000073bca039c401000400020014202b1c03080521cc301c003a86e0002d0804111cec0140400c803000049c0200843700064a40a0040f1004800000005230bd23024802800021006029eb0080800460480e048cc07880000006200004200e021400b0081b803794c519900280007bc0650166030ee01c0f700a26008102000428406250b4040b0800d010e402401014800902001c07095200180020403081400396c004b0600803fca6a00c9c2040029091b4e04000f00383aa97fdd160054160280930005a80129eeb7d4810ad1e369c003680893c2732800008004420110040586a00380cc4120000150c8093644e00de60004238c080008008003100006006b220cf015c071c0529c00088003008401c0020080000033800400400080005986c01dc23bc003182248802000c0 5 0xdedcdc93ed3ed93ed93ed963db93d93ed3ec97e74ed7e74e62ec62 0xb594ed7bde5b8f65acad91ad3582add50a4f4960637c2241a6f2d84800ffdb4b02602c014da8049c930890cdab74ec668cab9af5d09a1141444abcd3ca76be1ffaf7426845051e119b259ffaf742a84d08a0a3c2335ffb6542a84d08a0a3c244abcd3fa794ed7bdcdb8f31d80b005fe8e4fe9fc225796e3daab5165acad91ad3582add50a4f495b6aa0358540895e5b8f65acad91ad3582add27a4b031c51120ed71ea9d3fa7b4f29db005fd4ee9202ea774901702c 0x2a58054a802950059346a8c054a0028e0851400a4c0548db2e28052106a420547c0a8e8059246a8a0148442898058802a4001639a2b38051c00ba40546c028d8151a00a340174402c48051902a2e01630028a81513
def as60 := bankPage 0x77886f8867885f88578850784888408838883088288820881888108808880088 0xa98b625a4536291ba98b7e5a4536291ba98b895a4536291ba99b985a4536291ba98b715f4536291bb8b65f4536291ba99b8b654536291ba98b7f714536291ba98b5a504c36291ba98b7f5a4c36291bb85f5a41362b2a1ba98b6545362b2a1bb85a45432e2d2a1ba98b7369452e2a1ba98b65534b2e2a1ba98b885a4b2e2a1b
def ac60 := actionPage 0x252ca58d808a23a0232b238d008a21c021292191000a1fe01f261f19400b1dd01e251c0980891c201a231792401a17401620131a40101440141f1089408b1230121c8e95008a1050101a0d14c00a0e700e170a99400a0c900a1207a9808f09c0080d84a5810b07b0070982a1040e0510020280b9001101e000000014410a000 0x1a4080000000900530005802e09c20081ea024c81180030001300eb00080309c5700c061c0901ce030066000a9008600000600462001e33040c02188028ed030034a8003a88201de058c0c4816501500580c0008006800e0182019c082b00743800010091b120001a0000e00114a000005000468c0023908381c0101a0085cc3200f000a32a1a9514af4dc865040b03007a9402002d74b4037140060001ae9646a00020006fd07979a713100000025280a02900130000000c00980402801010c5219242808f280005bc0650c030806603880215a00000a024e00352000124230a04a98f19d811200050d230000c601005a46031d006a56a0807d003c090001011ac075c06805dfac183b20bd8c79062c09800366688480a824c60480e4481a76814c010030001379c2020c0802c0301c00394a7001c26980400102000095b046380ee4a01bd2c0e0149c01c001d0a7481e0001a09a8009c920065ad0046ba032e2be7f7a8a0180041008408001010e0010e318005010a4 5 0x98751032108510eda51ecb632edcba6210edcba5310edcb6c310cb6ed420dc9320ed9430edb3edc3d 0xa48004005240020029dd24002002e6a9b42218c30801a77492bcd6dab74914da110c618417001a77492e6a0e02c0040053ca4d49000800a854fa9e52427e4f2c2401800a04890d019a18c1802eaf356de931a632c618b9991f525a133ff62c84d089e119b796c24007fedf191b21554a013fa5f4bc44866d5cab74ec668ca 0x168802a90055102a9c0153c0aa68458c00a980d53122a622d4c12a981d531b2e10059a00a980944c02c48154a00b300152002a38154500b180150402cb2ad4846a90054f5a2bd8854102a6601655ceb3a8d6702a602145876c40152d
def as61 := bankPage 0x7998718869886188589850884888408838883088288820881888108808880088 0xb8a95a5045362a291bb85a5045362a291bb88b6545362a291bb8a96545362a291bb5a98b5a50362a291bb85d5a45432e291bb88b65453e36291bb8a965453e36291bb88b65454336291bb8a965454336291ba98b65454436291ba98b654c4536291ba98b65544536291ba98b65594536291bb8a85f5a4536291bb8b75f5a4536291b
def ac61 := actionPage 0x3f1cbca0800732403618b82240962e2031163316809829a02914af0e001625802611ae188106246025112b05800822e01e0ea616809b1dd0130ca291c01a18f0100b1d0ec01515000d09998dc11411400b08958a000e0ea00907900ac0100ba006060c0e0091087002040812001304e001020412000d027000000012000d000 0x180820106a314091bce160140040a6da1e8461e705400fa01a94496052513bb00903c904e9b01c16e000c000b54ec000773d84ec006e4007c471864001f40002201ac4a003e08be7201ee0001e002857624e6f882db080410ea70028002000002487015699808014a66812d019c0be807e8000348000000603ae179aa0210067b0c511bc2082e933c0b01d6c00007100e0508885b46c500070800530040200e031c412800030080601000000d00005c96413c80d288451800900c093000e7181938040000205200b234c03c4649400a980c5001ec2bc03554e4a802001720a801b4d403002ab143e000156ba807a8c002b21e07ec00780458355baeaa002a26bc42c1a90037cea8c00474004b300060bbb9800011800041f05d2002f5c9812200001a6008019160001d2cb8233cdd56836080097812118101401c04814b284070250e08c0b02000001a020000000094214d08047080e001489000205980059540421415b120080421a4e05a5e3395200002c0000602d806000e5000e038203a44c0000001543490007314c2b500300020008140042081a04800d42c09001636316d19ce80112010c2273064400090140038003299404954c025c001d80180c60a980000015a86070c62000000316c098604ac000104a480823ad48200a021d607a8201800900c00604e82800020909010474a904014043a40f50403101201800c09d05 5 0xc0edcba6410edcba54321edcba41010db7643edcba54321edcba10edcba543210edcba10edc76430edc98654310edcb8510edcb6510edba6210edba6210 0x5cfb1b56d808a10c60b400dcfb1ced162ac442a3b431c018008550980142a84c00d5b81c4485086305b492f2d0b8dd1b000c988dd1b000ae400200172001000004000010008280080041404c00800ab74f293524ab74f293524 0x20edf0057506a7e096d5bed9805a300b280163802bb0057468ad20950002cd0059200ae08d570129f2edd800b26055d402baa455b46ab60d4f4129ec35e783b7d036f802b68056313ab2215652694a352913a52214a576eb9658b00b16af5c956b90955810ab0914a11a940952810a5001581eeafb455f5dbacd5579a2af0155e04aa40556c02a4015586fa28094500eaaaad2546a4a2149402a982d53
def as62 := bankPage 0x7888708868886088588850884888408838883088288820881978118809880098 0xa98b654536282111a98b6e6a41362811a98b655d45362811a98b6a6545362811a98b5a51362a1b12a98b5a4136291b13b85f5a4136291b15a98b654536291b15a98b6e69412e2915a98b655f41362915a98b6e6541362915a98b655a45362915a98b6545362915a98b5a4536291b18b85a45432e29211bb8a9654b452e2a291b
def ac62 := actionPage 0x1922298d80081d401820a88c84071bf0171fa58980081a70161ea289808918c0141ca210410717701219219c4007162011161e99800914701015188b008d12000f129695000810800e10949100080f000d0d929900890d500b0c0c0f408e0ab0070b058b401a05d002068325419102a00104809140080120000000244006000 0x738e0004000000041902010a0401e1180e20148600020008a710002080c139800280c700000200a509c4830c00780060216001920298005bda47b8cb1884400c033800408c01000600808219d0850001008040006001c41034400292020000500e06ac44510011800a081a30014f6802008127000803340a68006125a010100308c00000119c40001260100301128308a00800101c800040500005015250000103c01608080298c230a321de05396f30005a81c67400078eabfc9ceb00000340d00c0203c4e06ca860069700ce282f261d955801bcac0b383e0020001b80b4d880000006800a001852802469425de4a0128670062a02c0b30068880000488b507c0380101017c000a2580041d81b500102ad0e064000032a02000421410040e028605018b2200122800000800288f4014a62d66 5 0xe73210b2e76432eb743276edc621edc987653210d631c621c621edc9876543210edc9876543210ed531db721c 0x4441782d1360b81689b05a26c16d3f8db11e2352689511e1cc3886d0d294d26a2f0ec018010060067c3e41142200acfa872004004fa8728300a80100000c00800006006ecdd1ba1736d9d7602e00c00d2570e94c4b58694b1e9c232a3324b4958f9 0x2d8005af00b5c016b41ac18258304b040d60402d5815a800b58016ac02d5015a900aa4016a402d4005a702b440769402d281d9b00b360165c42d580595
def as63 := bankPage 0x7888708868886088588850884888408838883088288820881888108808880088 0xa98b8265512e2a10a98b655341362a10a98b726541362a10a98b756541362a10a99c8b6541362a10a98b706545362a10a98b716541362b10a98b746541362b10a99b8b6541362b10a98b746551432e10b865412e28211411b8655d412e281411b86a65412e281411b85a453628211b11b85f5d4136281b11b85d5a4536281b11
def ac63 := actionPage 0x15251e9080081aa0141f9cad000d1830121c9a99000a165010199899000b14400e16169d000912900b1214a1000f0fc0090f9314c00a0de0060d1194c00c0ba003091020c08b099002070f10800a07b002060c894006069002048b0cc08605700203090d0086045001020609818802d0010103894007018000000009c008000 0x306012100102503340777470000ca700a8d49000605200f4992b00d5db450c2f83358278068e200000b90030fba0009f201f00055060d080ab0d0e064850d3999cb099080abbf04000a0e60d5a85000d158cd017ed0006b190500119900a03000b981060904400065005644002a7e20332003d7c0040520c0029c10800f5f07005d60f664024c70b0c40085f20810b358ed9a00040704307053603743050603100000610002030036055361573613000007012204604030207016404001110f0b08700e80d2c045e0892226055502300700650006164980353000400a00065e570 4 0xeded73ed63edb3ed53d963e62eb2e52c7ed732ed3ed72eb7210eb642eb76432 0x2744ba896f16c34868c503de0bc06d0bfd4da804991f2311642c435c6b47c8c4590b10d71ad22a4346238a70c8d91a7fe9f93e213418828c79649149302502e0592292604a05c0b23e29b2784e83a0630c20ba5344c896979cf12f73a4bc96b9d25e4b6ce82fb380bece02f 0x2db805b602b681945402da8651400b681944c1ac921d470ca2a056c8028a805b300a2c0145002d90158c00a26016c402d8005ae
def as64 := bankPage 0x77886f8866985e8856884f7847883f8837882f8827881f881788107808880088 0xb86543412e2b2a10b86965412e2b2a10c5a98b6541362b2a10b88b6541362b2a10b8a96541362b2a10b86541362b2a10a98b6545362b2a10b85a4e432e2d2a10b8655143412e2a10b8736543412e2a10a98b7569412e2a10a98b8273412e2a10b88b6551432e2a10b86551432e2a10a98b6553432e2a10a98b8073432e2a10
def ac64 := actionPage 0x32399939400d26d02e349729000d24602c319598c0062340282c9329409020402328112500901d4018250e99401b183017218b9d800c15f0171f8a90810614d0161a8928c10d1260121607a4c00e0fc01012861cc10a0de00e0f8598408a0c000b0b0424c00f09300307819d401b042002028028c08d01b0000000140009000 0x384b50019c01d348010cbc0ca2860000005050aa08cf72b201b0e09281d3c47c06edd2b920d03600481436b142580007c0603d273804029d42001c6c01a002d4503c008800f4800b92a08938c00ad89481d21000b0680118062b0282011e0014c74800f600e0baee04286013551700b1018050600ff1c60000353838b8c00006dc0f00a0a5873a804a21d4800fc604a2fb80002829701016350af368002000507a150804ea02a00480f00140589e448c00080a00280f381a002c0203d003a523310013100030400010a3284047012e020040016c02d807950e0bc6003407624001a006580e01980a00000518062012f1b4000108200120684e74346d000ec4192a001800144100c0d0350f11cea100e0030803240a1888360000194047148008060081007092312c0700c0018c230382a580cb0000019000594e078ce001d0030000f190b61060d835b014082eee010016ce7e080029800e0dbc0303b00181a072513034180012bb016100010882a664c8006c000156e1280a501c019800700a9501e02bc010000948cc0388e0100e1010271840301446000a200800 5 0xed940ed90320d9320d920d9320dc9320edd43d43eb3ed43ed943e73 0x58890d18a0cbca58aa1141a8250268ccc93c25d21a313ca660b15621992e45c4b74868c468c9e06305d21a31401508a05401a327818c174868c4a0d40a803464f03182e7a8d7d62a84506a06002814fc714b206305d1fe2744c1f733e5d4868c513e2744c896ba5414a78c513e2744c896be974ac48f918e311642c435c6b4e88b913225bc469733e5d4868c513e2744c896a0274c4f89d1316228250161a43462828f15b42ff554a012f45c89d13225af7 0x5b943af80150c02dda1d7a00a881950002df0053f00b68016c80aa08053e5bbfeb777802df2459800a7a016f402de005b602b6a016d40ad9805b300a840550002a00053c00b78014e802dd005b80db62014e002dd8651600b74b5625fae2bf5c41fb188781802dc815b700b6e1f6c436d8815b100b62016e402e5805b8
def as65 := bankPage 0x77886f8867885f88587850884888408838883088288820881888108808880088 0xa98b806a432e2910a98b8069442e2910b88b654441362910b8a9654441362910b8654441362910a98b656241362910a98b836541362910a9a38b6541362910b8985a4e43362910b88b654e43362910b8a9654e43362910a98b654e44362910a98b7b6544362910a98b806544362910a9a08b6544362910a98b716545362910
def ac65 := actionPage 0x1d11b28cc00921901c10b08900082010190f2c0e400f1d40160ea786400f1a70110da30a401a15900f0c200d808a13b00d0a9d8d408a11d00b091b8d010910200b07980dc0880ea00906130e808e0c0007048f8dc08e096006040d05400807e005038b050008066004030805800904b003028485c1090300000000164090000 0x301802190c6010243000000004210c01146510001394003148200800000a003087600000200e48d26015a6601c03b4090300e7980079de040100001833a809015600a4490246a32c0e0204003460080000302f02408039c019d80181004800d1152e03400589c02080041043001ab2bc076280010000704cb0a006025810104f52ccb0382d51d08000ca01d2a00800380a0100630348e109000808c2a4c0000ee000000008178c6300cec000a02040601c801812431006000467880c000000112f00800024e031ce3085250800068005080e74000b03c072b80001421180806982f711e01b4670008000040188c008009008a7000010000310163028004800411c02294053880029480280410008008c0020087014410080008c6038c052900010c0701801004060182018020280c428000300007148c0184719843238e101160381600140068042480e101000581a7281a01a80070140003a7499601354a 5 0xcb7db63edc765430edc765430edc76543098751098520b320dcba310dcba543210dcba310c6430c643edc643edc5430edcb63210 0x21cc3812d0e04543a8730e21c4398710e000800870004004380020023144c87118a264388c51321c4388710e21c2774980b816001 0x2e2805c400b7e0157c2aa7015c106b44015780ae1005c202b800170002ae805c300aa40170802a80554e00a9d335b656b6cd5c18db82017040adf805c000b7e0d66996a800515
def as66 := bankPage 0x7888708868886088588850884888408838883088288820881888108808880088 0xa98b5a58533e1b10a98b5a51362a1c10a98b5a432e291e10b85a4e432e292110a98b5a4136292510b8696644412e2810b8655d43422e2810b86a6543422e2810b86541362c2a2910b88265412e2a2910b8654e432e2a2910b88065432e2a2910b8655d43412e2910b86a6543412e2910b8746543412e2910b8696544412e2910
def ac66 := actionPage 0x171f223cc01119e0151d219041071890141ba10c418517a0141a1e8d4008162012179e14400714d011159d108007138011141b0d00881200111219110088108010101412808d0e100d0d9215000b0c000c0b8e12000a0a2008088b19808c07e0070688914089063005048591808b042002020315408c01e000000011800a000 0x57800f180d702080603608401c6000f5200998143b09a00034e69d8f9b220004621100300ce001023004001802008801010030844100c0109c002942200020010000186529c02000a6280610046021c0500004014a50040001c05018203940130000010e42808600803010c0308c41008439c0031865000061000220ca300180300006094319cad6bc002b86d0040d128a3401a0201e7000ed0b40a329004004b480007bc080148000046181c36b58538cc0025a0018e80b0000006050180100006b800781a1780645a50063528694ab41800038402904301c0e00000100052b0cc00881001a00200218100631e64810038040014e74052618408588005808d7180f088c8000611ade03a4004a0002b0071810e000ec200e0500007858522c0021004 5 0xedc77db7212ebed43ed72dcba873210edc7edcb7430edcb43edb43edb732edb72dcb763 0x5e5bc965ecad94b2764ac8d4aa614a29341338419a9a47e89d1328ec4e8730ee1c897a7549a92523a2f2a2260ab01f2a01f03c9532a01f03c89d0e57728197513a2643979518a2744c58b18a2844e8990e562c3a8702584ac398702584ac4e89912c9712c8990e61c08a 0x358604b0c0d64412c7815c90bb36015f402bd8057900b74016dd86a50858c00b98016e1ced886db100ada0171402b639db100b62015ac02e20056a
def as67 := bankPage 0x7b7873886b8862985a8852884a88419839883188298821881988109808880088 0xb8654136291510a98b65432e291610a98e5c422e281b10b8a96545362a291b10ab8b5a432e291b10a98e5a432e291b10b87b5d432e291b10b8a965453e36291b10b8625a4136291b10ab8b5a4136291b10a98e5a4136291b10a9925a4136291b10b85a4e4436291b10b8a96541362b2a1b10b85a55432e2a1b10a98b5b51362a1b10
def ac67 := actionPage 0x22220e8b401a13e01e1f0d98800c11a01d1d8d8c000410e01a1a8d1840860fc018188d1001850ed016168d1001850de016158b0900070c901012891900080b100e108611808909600b0e061400070810080b8614000706c0050906140007057004080289c18903c00304821c410502d002020094c0080150000000104107000 0x5000207c00075ae12809191e0000064b41f01967280074a02092ce8e81a00000100a9f000c00340b0308a51d00a1628414a75908420100300060000218c60000a00280001d800bc2218000084410008060180401e55802101d800044020020184220806008804004030844100c04214400800101c00094870000d280801b08f00007481000008140dc0035211014000cec19d4000083480062000409885384a03004020005000e0204c429c2501802010002800701400118e720c0110020008000080248028480a0680287150003c28001af00d0128006000e0110023000a2008679c051980621c07000031088018067000811802000c01 5 0xedc9876543210730db73d210987510edc74300e737 0x21e43989d1321d439870252cf4a989d61a4cc6e0cc0c00152689d0e61c52689d0e61c52687361a4cc6e0cc0b800d26a490e61c526a4913a1cc38a4d492274398714fa93524a2f4021cc38b0d21e311a527e1981855d8cb18e3144ca7f17e2744c 0x15aa00b540169c02e6005cb7db8e0171c02e50359604b2c01659f6e4015c600b900571922c9a359343b262564c42c98659300b860168812d0805a106b320967802cf0359905b3e016701acb805c100b2c216301ac80258f
def as68 := bankPage 0x74886c8865785e78586850884888408838883088288820881888108808880088 0xa9a78b6545362909b6a98b6545362909b88b6545362909b8a96545362909b86545362909a98b5a53362a1b0aa98b5a4536291b0ca98b5a533e361b0ea98b5a4536291b0fb865413628211110b8655d4136281110b86a654136281110b86966412e281510b86965412e291510b88b654136291510b8a9654136291510
def ac68 := actionPage 0x3b1f389700912be0381db30ec01128b0321d2d07001e23102c1ca786c01c1dd0231ca28280131a401d19a118c010174017161e1d8091141011119d24819110e00c0f1a9540100de00b0d169200890c300a0b1311c0890a8008091011808a08a007060e98c007075005038c15408a057002010597400f02a00000000ac00e000 0x1fa000f70010a028305c015580f031bd3a2647800f90100002ae582fe61403049cd0036c000000800309dea49126d35406b804b000e2b9a50037f2840d68261734029840001862001a05a817000e010d820141c02004000007bc0902549010ed5844700389a31801fa432048069404328007a0462201958d805302772d20155ac01400014030000600105301af6800d2b80e8100e2a44e401a8000220102b5080b000004806438400081607800d4cd8ef0000003a818406001d04ac0d03d25701e02201300c6d3c7c9114a00201101c0e2000a0000a79469010001a5c05bda22b80003827491ad21002201e063c0006c006b180039807988d519e251807812403000400000000ee28b5c5150011400784164d82e41bcee80fc1f012358034efc03f1e93001af19160002038000181002000c020880050b00169018007a0ab4040501dac00103424e00004f0ac20410c013c0c4000040d03018cf3880078c0730007200e039c08118c00098048162001a9004e80002941c2b481445b96b03de0280c923800000e00902830120300c0010455280c01c000b000001ab22185721281adc5d2bf9008000000d002de0964d019bff80c001c1d039ee00fcef300b00408681494880500dce2a1a0434005ada200084581403b408 5 0xedba76543210edcba765430edcba7654321edcba765430edcba76543ec7ec7643eced632edb73210edb6432edb742e61dc621edc9876543210edc98765210 0x25c4b0950020004b0950002584b540a7f4f69e3026014fe9ed26a48524a4031b715faab554aa75029eced98f4fe935240060068289d0660be8209c0600b68209c0600b654ca889c2b00800e89d0e4f988c1150f21dc398700061c801 0x983c02ea035bf04a9c057582ae1855ab06bb40975402ea8355d04ab8015701af5045d802bb00d69c12ad8055b06bb20976402ec845d702bae0175c1aad0255a00ab40574c02e98158d00b1a0560002c0005d100ba00573c02d00059d00afe0573802e701d7e02afc035f802bf005cd06b4a0167c02ce0057d00b60016b802d7805ad35b58016b032d5015c302b56016a4fad8005a8
def as69 := bankPage 0x7888708868886088588850884888408838883088288820881888108808880088 0xa9a28b65452e2909a98b65504b2e2909a98b65534b2e2909a98b7f654b2e2909a98b84654b2e2909a9a48b654b2e2909a98b654544362909a98b654c45362909a98b655045362909b88b655a45362909a98b655f45362909a98b7b6545362909a98b7f6545362909a98b846545362909a9988b6545362909a9a48b6545362909
def ac69 := actionPage 0x2321be0d408829d0221f3c1500892820211a3aa8c18d25b02017b914c08924001e14379cc08c21c01c10b61cc08b1fb01b0f330d800d1d401a0dae8e408d1ad0180ba89300921770150aa28b011413b013091d0ec10f10e010071713000f0e100c05111300120ab008038c0e801506c00502060f00910390000000130013000 0x41c0031046009e001caa0240f38c43019800000818100594470940d025c910c4a035236ac00001481808930161000cb5080e6892268400409260014000061015ec008a00858503400001a069807080820804a01ccb21d45019e04000c43c0038000011430014a2002b68166509e04800f08004624e070dc040145004007a142080a113009008005b48f004014812b3016e08065000c00016070007035005846000142595ef82dc020000481a6000cd1000a208003800016c017281630144329e020580024b6518005b41100004001f00008104e8070044196b910c466814edd08204029158a00302a045a0011a071cea09c0048120001440382001141008052a12800009689ec6a40c0000075aa0a78d8d9e7fb6000990190000a448110064fc383603bc0331a000de001540221ad5e1e07740790000601c0d71c0072c8d000602521411a0f35a613401120a0400600800b0010bc800c02000481405a92602d4301000028090200f420cd2094be50007190090813b808030020703c4188f0f380076c1206c0fa0404c946008200000931a12800f400380089c054a80e28c00ee8073b42303801d380a039e0438002b307 5 0xda543d730d73d73d73d73cb7430cb9854310edcb76543210edba76543210edcb7654320edcb76543210edcb76543210edcb765430edcba7654310edcba7654320 0x1c032912ae00718bf12c256c33fc758e9dc03295009f4900e370438c4b095126e09300e312e2584a89369a9f89009712c2544989612a0044b095003000d789612a2580009612a0004b89612a0004b89612a0004b89612a2584a80012e2584a800 0x93b7e0177802ee815db00bb80159c02ed835c400bb40176402ec0054800ba80d57c12af835d600aa4018441aea0055100c220575412a80054700c220175c12a30054600bac1570422d10060f00baa0d7081ae000545
def as70 := bankPage 0x75886d8866785e8856884e8846883e8836882e8827781f881788107808880088 0xb88b654b462e2809b8a9654b462e2809b8654b462e2809a98b8469462e2809a98b65534b2e2809a98b85654b2e2809a98b654b46362809a98b655746362809b88b6545432e2909b8a96545432e2909b86545432e2909b88b654b452e2909b8a9654b452e2909b8654b452e2909a98b8265452e2909a98b8765452e2909
def ac70 := actionPage 0x2a24acacc00e28b0261fab28c08e26101c1ca899401921601b19289c00081fe01a13a72cc00c1da01911269440081c20180da49d01891a70170aa318c00c183015091e0e808e159013079a8dc08e12f00f071387801a0e100c050e92800f0b4009030b11c00f087002028407801a039001018209008901e00000000d000a000 0x16e5b4015014c700c00100af2020001a0331a5620a548020818004a580300290000500425e81001a900280cc0008c1084500b80021e0513400006cd25c300005001ce094e030844e94a570404e00e03140262c489e4427982843004036200700001043300c6018e5000000080201c86389a0481a04300042c02600c01b40148180235cf3140d02023300e0010031002501803280841898e00028715803000d101cb3300d5a8a039007318c0014403908038d00201c010007400001080001c004040000126700ef0004002d204340800064609ad485aa2006000101214205b80028cc02a8002006b2000b00c44028025016006002600070f32c2b4ec681e0020062e1000341001564325e00240e1881d0000c680032a8f07906c50c204106f02c0e9814f3900203849380033b90840008a880000c02510e20294b68004001ec4852002187034002ad0d03402009a1100007914c4180702c00100030e404600ac481a04b9a00ae8a000062c3c05b5a068006375ab0338e3101c4800b500230049e00c605242c136e70000890005000c0200e730000100a0014831986600060300a100880280c310005010a000c2009c20 5 0xe74e74ec743c933e740e74edca754321edca740edcba876543210edca754321edca740edcba876543210ed43ed43 0x6f6c81401b3222330360560a61481db7b640a00888cc0d8154298520765707f8810ac15429b0030e4507f0b716c2d6c33fb74ee99bdb20554a012f11119839c668cc17c2f5401b3222330298510a06aca69111982704db2912c2559489612a25994a8012c25594a8012c2544b32912ad3594895 0x18de806bd00d5ec02f3a45af12b5e756b002f3165e400bc85d78cb2f1815e300bc6015f00abd0057a00bca0179002f1805e200bc3276fc0ab6a45ae12b560578002f00156c00ad80d78002ed8356a02bbc916b44ad5015df00bbe017740aee005dc02ad2015a402f0005df
def as71 := bankPage 0x7a8873786b8863885a9852884a8842883a8832882a8822881998118809880098 0xb8a9654536281109b8654536281109a98b654536291509b85a453629261b09b8a9654b462e281b09b85a504b2e291b09b85a504536291b09b88b654536291b09b8a9654536291b09a98b654536292609b8655c45422e2809b8696545422e2809b8a9696546452e2809b8696546452e2809a98b8169452e2809c5a98b654b462e2809
def ac71 := actionPage 0x1922b98dc00d225015223207c01a1d701420ad0e810c1b30121f268f40101830121ba69c008417701018249d000b15600d159e97009311d00a14190ec0940e100712938ec0110ae006118c8b808e08400610098d818706f0050e0611c1090540050a0620000404800205022a000c024001030190400700f000000018c005000 0x180002840000000188c1080e001d64698eb09c21480883800000ec0e9ac08ec23001a0e5582624b410120800282ad40000660000e0000ce3c601c120b6ec77a08c7040833011030c068000035ea6b5c000821011202812039804719c619040205a76000032000582005344f0289b0a4010240a130ed0040002d44080c060000000c109462011065186e000ae1800b000090140e480002810a39233f480b50760387400001100a9f563dfcad8ea80000455a04c008801e43c1a8f22e380000114500009034c01a01530020200a7d80000197e000080100d1902acb800935bb224420f5e050001c29803ac0d70d9002031501606b616034007808d82dac0340032dab801c0001a0024077804b000c2003606956c489ac41107230601a5a0318060800200040298ae300013bd65024a2011c338000000a018107018020140239cc031c031880c20227b86a8000040bc00ba9400690b01808004a0294452802400007180c3004c50a005200c340186001e7 5 0xedca870edcba9876543210c987654310edcb987654310d730edcba7654310edba7654321edba7654310edcb9876543210edcb43edcb943edcb9843b432 0x1982741689d12e25801dd0a5225ec337d6404506606d07d742df3a97043044b896ba0b144b8960f625c4b00112e2580089712c37c6f0aa1be3785c8aa7ceda5901832223305b86e7ceda5902c4306444790b91021b8668cc1542a5bdb202223303603b 0x1d6c00ad8075ad0cb5a056b402d6805ea00bd27f6c002ef025ac00bb0096a802cc005d604b520d57822f4835a804b50017a402f4005e52cbc60978c02f4005e7
def as72 := bankPage 0x7a8872886a8862885a8852884a8842883a883198289820881888108808880088 0xb88069422e281009b88165432e281009b865604136281009b86f654136281009b88265412e291009b8654e432e291009b88065432e291009b8a065432e291009b865444136291009c5b865412e28141109c7b865412e28141109b865452e28201109b86e69412e281109b8655f4136281109b86e654136281109b88b654536281109
def ac72 := actionPage 0xa1a2f1c408616800a18ad8cc007153009172a8d800813b00815a78d820812300714248d800810b00712a00e40880f3005109d11800a0d50040e9a1180080bd0030d9689c10d0960030c150cc18308d003091319008507e003080e8a4007069003050e18400505a003038a0e0007045002018592400902a00000000ec00e000 0x41106007000031070763001050554403004120270066010020e2560c0351003f410cd7c4407d0066009070c4058371810230bd00c2020a000394030600275b0020901b208440e0081600d090400548256000947f2085763090c060060ff40f0004c1f5c7a9046020b0080a9b04c800f780a31320403000200f80a090e70c102400608389c02042d963656013000001320b000bff99060f812a50c00453056006e0f70083b6b03ed95c464063fd00a00e4f0ba0a00f00960ec300000b0f 4 0xdec3ec8632ecb832edc743edcb74310edcb43edca43cba7432432a432edcb98210dedcb7420edcb97420edca8753210 0x12aa5444f89c724c40ba95059474cdd2ca58e6e9652c70e1e4b4f8750e20c43d8750e20d43d8750e1a7c3a8705c0b292f39c718cd1702ca4bccd1702e05b89f13d2762e4e213e2767109f13b0863304e82d 0x32d7065ad00bc00184802e28161200bb4016bc3ad7015ae
def as73 := bankPage 0x7788707868886088588850884888408838883088288820881888108808880088 0xb8a96553452e2a08b86553452e2a08a98b8a65452e2a08b89a8b65452e2a08a9a58b65452e2a08beb88b65452e2a08b8a99a65452e2a08beb8a965452e2a08a98b6557532e2a08a98b8465532e2a08a9a48b65532e2a08a98b746553452e08a99b8b6553452e08b865413629151009b86f69412e281009b88169412e281009
def ac73 := actionPage 0x424415b5009429d034411418c01d2460303d1320800e21c02e3811a8c08e1f202a3410a0808d1cb0272f0f28c09019b0242a8ca54013162021250aad009013201a1c89c480101020111688b080110cf00b1007b4801009f0070b8724400e0750030686a8400d04e00205010ec00c02a00102801481070150000000140007000 0x4003f000000000164baa034fe4c0e9a302df336e1aed60002f5ebc9670a20e7c247b24300001a0403397e01d5b26081240c9cd018701aa000000380a1040e0b9660d9c08002c012764048ba00037b02e0b98f6028030501d0800deb942180060008f081870300400083000e50000031000781a50b028000071b400020050384730948400cf6b4060002e314a500001300006000449001681c07102d588c0001203900d094c00340f22806180cf39c000000f0084001ce32958002c042148423468018e003c05681c803d8798000058fb502007b96583f07005c0002cc00c000300ad84001989d200273f7c05b066a940800000000a000e037115a601e17ade412c0f582c000b216801f2800a62a20b02760029f9014b9500a0212000006401e4a503936c122e405b530e001ef0240003bf8066e8e9cc38f406f8000758e0018b502d60162a00b7a0ca800bb800031a705c00979ea58000882cf06cb59a80063a2694b84b9d8a08004209a8000a36a00003c4c08d82000020288501d68130e673c40300a313800001800a005681cd60cca684ab2800000024010070000948c033b0c168524681e95b40f0000a0284608c0001c0230005110020102600c0200c0200c2000ca218003 5 0xdc93dc3d3d53d3da3ed953da9374e774ccc9876543210b3 0x587732da581300542a094027f4fa94c890cd7d6d7962283504a01662a31d23a0670cd19832943a7e43685509a113d4764c7912510a1c929152264488890f8d8a1d3f27d43685509a1131e44943a7e4fa86d0a21342263c8946c50e9f93ea1b42a85109a1131e44af2de4b0f61ac2475818e55c5341674ce54fa694a244866b9872ace592b02600bf95929f4787fc8ad14820e29bf3696ced01813004d2945030e850e9792ea5c4a894d28a503feaa954aa8546a8950a9f53c94d0343c87225e6ec7e2ca58c75ca889c594758e9 0x14eff29ddc12b66bb68d5ec70253700a60014a00307005f902bf0017e002fa815f400be8057b002f62757706a6c094d802978052700bf0094b802970052506a74014904ed88052d00a46514101a9c8053400a449181922f08051f53bba014cc028e8060d00beae14d4129aa7d2a00a540146c0305005f400be0017b402f58053b04a56014613a890060c7bb740d6e81adc3051700a2e017b002f58051200a0ef76e9c6dd1450500a0a017a832d7805e8
def as74 := bankPage 0x76786e8866885f7857884f884878408838883088288820881888108808880088 0xb86545442e2908b88b654c452e2908b8a9654c452e2908b8654c452e2908b88b6554452e2908b8a96554452e2908b86554452e2908a98b8365452e2908a9a38b65452e2908a9a68b65452e2908a98b65504c2e2908a98b7f654c2e2908a98b84654c2e2908a9a48b654c2e2908b86545412e2b2a08b88b6553452e2a08
def ac74 := actionPage 0x3526b08a001a2a3031252b0ec11027302e24260a811024302923208ac0191f8024211b9280111c50201f970e40111920191e928a401814a0171c9011400a12c0151a8e110109111013180b9540880f9011160911400a0db00f140790c00a0bd00c110618c08d0960090e0498c08b0750060701b9809303c000000038c094000 0xf6bd2603d20295a078dc04380b000e4000000280b73de070cc3020200002a024e03a1820bc0c701e003c0052ca6499c01001b52806a00e06080d58c68014040000740801faca302044030a88b5604000039808181402380c6340102c06000c7400056b10a01183784015894038006900223246aab8c9100154580c18001b9d001a094e820402c0b006620192778c5404c6042fa30002c700000800006b8814400903a02820017960623ca055801df00068001db806912006d4092dc001820081e30b800004077a8c2398c02b06f624007008a088e119800480004b804000ad134003d0f8d1220829bc6a80744c0a026b8f00032085c0001d00007468b57006c072880188002120680a100180429070a90c5040801ce002c040280000000380a500c0519c68380213888060000414c70000a3a005000e1010e5581650b00700460300ca001c84000820404780204b4c0000002980440c05000ce2190471840180a3480a6018ad019206010859800001c00000670de0030ed1042f0806771dc0001a0681c03380a4a0006142a0100334e80000005b4003a140d2de60780390005e800002883085a04fc162812001c174a3e5580190000002c0010006bb3aa4801bef22da01e7399ed001367bfc903698079d4b25b62140c 5 0xedc65430edc98654310edc9865310edc98654310edcba85310edcba8310edcba831098520b320b8610cb310cb6cb6ca5edc430dc3 0x7c4f81f13e0220f80883e27c10d9f13e02210d9f01107c4f81f0114220021f01142200221b3e0228440043e0228440043e0228440044407c4f808a110011111f13e022844004b10b156229e508a0d41281500940d293f238366f2c007feda581300542a0d4027f4fa94c890cd 0xb020060402ad4015a802ae8360400bfa0d5b002ae015ff31b5a0156c0aff005fe06ad2095a402ad0356b00ab25153582919452353bbef56d44ada8055871bd8df7b01af6025ec06ad0095a002ab8060400aa0c153802a71454d00a9a017fc02a4015fd00a8e017f812b38054600bfa0d71402a2a1d7c00a86015081a9c0053100a52c145ca28294504
def as75 := bankPage 0x7988718869886188598851884988418839883188289820881888108808880088 0xa98b5a532e2a2208a98b5a452e292308b8655d45422e2808b86a6545422e2808b8666545442e2808b86a6546452e2808a98b846a462e2808a98b655746372808b865452e2c2a2908b86554452e2a2908b8a98465452e2a2908b88465452e2a2908b89865452e2a2908b89b65452e2a2908b88b6545442e2908b8a96545442e2908
def ac75 := actionPage 0x2e28abac800d24002b252b1c400822802a23a90d000821002921a69140881f80271fa411408a1da0241d2115800b1b90221a2018800a19b021151da9418e17102013990e400d14a01f119512008c1260190c9428808a10800b09101e001a0ba007050b228013081006030811800d05a003010412008f02d00000000a008f000 0x94003801525c8498000b4006000d401ae601c94954f00003680210000002c08024096292b03c0f0900431c0001407018e0080800900059c8900005081401808c019201a50771d01000a700de00816038043680030382412cec0000b0008d19860001082046e42400001033346002c000180029c6f004c6334e00802263c013b008000e07800003c0610106018ed2812f0396f21d213000d00c08680a178d601240202849420a003c6b4000f600021ac007800c0018c681a040ca01816b48d400090a52086114047014d01c001136a2000f040604940e401eb501690001d02fed06c2000080788fd0290101000083efd05983381b8fe20280262500219819b80e0b0028f1987350108c600006c0040119d2207f41eb8000f18011001107cc00014b0035390380528004cfa71fa48820a96800f280aa0000a1b00000c41601805b58068801300c00314050408080204a40001d8b0040a09c000a8c203cc06000a480c378967038c042c06239003800032407011e008546481e00040f0000b4082f 5 0xecced73ed732edb63edc732c7edc74dcba87310dcba8310b0edcba830edcba85310dcba30edc65430edc76530 0xaad5569a532604c015b2a146080900d26a49481deacc4d8945ce8aa07ae79ce8aa07ab616b82003ee79ce8530a00f5ceae04821082083a7e4e74d99b224038c298520a214141a153e2a050c2133e33f1953005eeb114fa9e4a07c066cfc676b114fa9e50686200c007ca9410aa133e063d4fa8042a84cf91f13e0220f8088 0x15f300be20160003042fdfb00afe595b4b2b60057b2cad40181c02bd1656900c0e5959c03030057900ae6256f576ca2bd9400ae4a34dd3a9b8060b04c0a018141afc805f804be8017d1cef637dec06af0015c53ab428d364ea6ced81042d90057076ad4015bc1ab68055f60a9c2570cc6d70055e
def as76 := bankPage 0x7a8872886a886288599850984888408838883088288820881888108808880088 0xa9905a452e291b08a98b5a4a2e291b08b85a504c2e291b08a98b5a4535291b08beb85a50452e2a1b08b8a96553452e2a1b08aa8b70452e2a1b08a98d70452e2a1b08a98b70482e2a1b08b85a53502e2a1b08a98b5e532e2a1b08a98b7045312a1b08a98b5a53382a1b08a98b70452e2a1d08a98b5a452e291e08a98b5a452e291f08
def ac76 := actionPage 0x273f0ea000091b60223c0e98008a19801f388c9d000b17701d360c14400716201a310b28808814a0182c8a248007135016288920808911a01424882080890ff0122007a440890e400d1985b500100b400a1404ac800d08d00910831cc0890720070a8230800d04b0050681208089030003038098400701b00000001c4009000 0x30018458c0112c005140201c01099405ad4640d40798c15880460060014293ac0800c00289e31896420000034060344b50067280a000c2c408831000621805010010884038080100001000e000e702d2331c00234001000032d273154d6340548009501403000400020100ee0158d0042b5812a02806000800040201dc02b1a00856b029406004701180180402bc041b40022de00680f6dc0805811b94077343d664145b000c618031816301cc57df006400128007002a4b909300016800c001a8035cc039292a9e00006f001e011c0328020180aa0196a008ea78181001c032d4a1b8c001d00030000a4097180d428cd4800002540500c001000080403b805634010ad6000846020402800138005180c030006181474880029082020270984e00006 5 0xc3104a3c3e6e66ec97ecd64ece675 0x2bbd26a48ad54fa9e52a916acd26a48878f89f04407c8f89f011822802d59a48878f89f0ba171e3d4217b0d994521c32845ac339a6d4d0580aa34aa45866db5b595bab6d3f4b48710adb5b595bab6d3f4b48710adb5b5b6b2b756da7ea8d0e215ba172664b4464cc11813015468ed01a0222d55aaad3fa78c09802b55428c101201b6b6b2b6d3f5468710ad56aab4fe9e302600ad950a6d4d895529db4b5759eb35385468710ad26a49481deacc4a349a92522a40ef50f1f1 0xc120580012e3ab5a000b3a0d8041300835c604b8c0166402ff97daf00b300d7f012fe2ada300b280d4c802ca8059306bec016441afb0059002bec0163dcf03a360746bcaab63802c7015f200be2016340af7815ee00bdc057dc02c1afdfc00b04c97f01ae480581
def as77 := bankPage 0x7988718869886188598851884988418839883188289820881888108808880088 0xa98b5a532e1b0c08a98b65452e290d08a98b68422e281008b8806a422e281008b88066442e281008a98b654234281008b86562412e291008b88365412e291008b8654e442e291008b88065442e291008c7b865412e2b2a1008b865452e2b2a1008b865413e2e2b1008b87465412e2b1008a98b65452e291708a98e5a452e291b08
def ac77 := actionPage 0x2b309a2480901e00242c172580941a4021299714000718f020269618800817701f25148cc18716201e231410400615001c211111800913501a1f0e91400811d0191e0c0940081050171d0989410a0e7014188824c0080cf0121305ad400e0a500f0c0438c08f07800b080320800d05100403002980930180000000180008000 0xc818d00120090406000a6a2656144b334600adc803d007800940062150c0174809801b2ada0698c0454006ec40023258f60002416702e4000037941df00000033975c1909c23000c41804100460200a63000200060014a51006049803304a0284a00006000c6401cc131c01280a428821110c008000018a06010e03c020008c01dc0521a031d20024c40280000c00008432382401808215430000410c0000460014e6100e0318402b400010e229065380a6288a02100318007029a00000b010c0390002106c488000a0076814063e6cc80d9003206a40345ec000360d936c4e01c738008490b0720ca8120033be80280b1020a9c0014a2001c00c87606918000000700c079824024401a540018ad010a610180325404180003c20070ab3db00565e004400d64005b86f000a0001830516459f40c82417fd89081ca01c820000302c03105002980120104 5 0xecec7543c7eb64987510a9820dc630edc63320dc930e82b2ecb763 0x2be551a814f55b2b55648d117a8a4d894928a502624b8498389b52aa5439e4832aa543a073ee79214aa950b626d4a873ca2a1d4383e27c21d4383e27c21c1f18707c64446453ea49289cf34a5c49fc7758aa7d42283502944e79c72e259ac44c89412263bc768cca7d289d43a05e8bc972510955292514a04c497038598af55aaa053ea78ce1391261aebbd26a48a7d4f295 0x58315b048060956c10018215ae8805d104b96018300300305fb00bf6c173c02e7835cc02b94c5718b2e3165c52cb88c572432e1805c300c080170802e0805c400b808779832de805bd43bc4016f10ef2065b90cb6c8778c32dd865b500b660182c13050060a00c060180802fd005a602c02097215ad08059e
def as78 := bankPage 0x7898708868886088588850884888408838883088288820881888108808880088 0xc7b86546452e280908b88165452e280908b88565452e280908b8654b462e280908b86550462e280908b86557462e280908b88465462e280908b8a465462e280908b86545442e290908b8654c452e290908b86550452e290908b88465452e290908b89865452e290908b8a465452e290908a98b65532e2a0a08a98b5a532e1b0b08
def ac78 := actionPage 0x3035322cc08829102e32af15800a27302b2fac99400c24f02a2aaaa9000c22b0282628a5010a20d0251f2738c00e1e302119a5acc00e1b901f152424c18a19b01e13a08dc00d17401d121b8e800d14d0190f151b401510e0120c8f96c0180c600f0a0917401209000907029b401505100303811cc11101e00000001c808a000 0x7088004ac20700400204e000a0298804a587281a909827038804bc02024a1080000000208160034e0100e939440000c001cc2301a002c685940070000008a0200694b1e1000a51004e4a40213886224006806713d80680e06912b689400248802800880af001a04b5e050009018146a8061b38062060315e020c2a00000b2c00028e705407a00173f00002088f80c0800a2138a035200194e30198d010c1481e0698463b820580a00002048020725850000902c0521d0262c61720000bc8761800384010000059ca01900b4800c585806bca01000a595a74a40ecc7463740d679653000d2940051400459605f9a9d82190000008280ca9e9301e008011366420488b07007183ee6a202d618cb818c00240008ed03400002a0602000656c802ca531c03f9ed3f78200000283acb83a04e0bf000009000003c4324220a8074001772a41200040f11b35c819fafad04f445802f000000328e302665b40021c06a00b719133016a0034ac7240b900820f000041c05a5601b869289480200e000001108a69c637856a034c803400418e0000ef00405001806a0e420180000014a0e870920000e51800649800 5 0xa32ecb431ecb83e740e740e74e74e74dcba730dcba984310edcba87653210edcba876530edcba87654310edcba87654320ec7ec 0x3f27cee758118a31260cc09151a0271f90d019e330563f21d4390680cf198a0cae1151a0208408560aa15029bf273ad0d82302600454410817e4e7dce9ae2a65488a8d01042042b0550a814dfa3f273ac098018a22e20840845088fc9cfb9d3686cc750540a6144f909712c7c84b8966a6b154f09712c1ed5029e13025c4b3e44a07c04b8964a4940f809812e25a63b02600ad550a6d4a7716a8a6d4d89a517a2c 0x5e600bd05978012f1805e32cbbe01788b2ef235af00c0c5979002f08060700bca5978cb2ee18de82cbb60176802ec805ff00bbc017611ad6afe0f04bfc017f802ef825dc00bb80175c02eb0a5c34ab5cc183c1b02005fd06bc00176c02ea8060e00be6017c802f8805ee00ba6058340306805d2
def as79 := bankPage 0x7a98719869886188598851884988418839883188298821881988118809880098 0xc2b865502e28090800c2b884652e28090800b88365452e280800b865504c2e280800b884654c2e280800b8a4654c2e280800a98b7045362a1b03b85c422e281b1004a98b65432e291004a98b5a4536291b04a99a65452e2a0805a98b65452e290806a98b65432e291006a98b5a4536291b07b865452e29150908c5b86546452e280908
def ac79 := actionPage 0x2e2a9ba4800720402d249ab081091e902b21981940881d10291e959940891b60251b149c808d18f023181318c08917401e161091400c15001d141090000713b01a128f8c800a11d015100d9500100ed0100c8b1d400e0c300a09091d001208d007070810820b06c002048615009103900103810a808d01200000001c8006000 0x480050000012d03080007a54038003030001048058560694e06802958c0a309e07000971c8d0000b0194c18146000a058c88180436000001d01114051b860000c010180000613ad40230ed280272152803828114e0010080012b28c0008160280096840e0100a001041ac0c02523001a402d200156c2bd40424006a86118c0510c00000c00140139c203006030c8000c0021c04210672040030c8710c070380070081401aa5000a380c0080ed41c60201c3600076a0860000213480038c2680003340e6800800d4d23400301c408dc5003cc0818e681ea020e41a0a0001236a5e046000010800006e030020040a62a8c1052d624c0481e0004af1800022080008001a80260168390e2020a2000002a0c001800505863814039c026a5c3300622940002c2e08c053b4a03880a4100b0240a1000002d400304059800100651ad4a020e01280d000000244f0140d33025 5 0xa1baa9820cb310b6ca5ed643737643ed5437543736543dc9876531032 0x1c1b52334454841031d82744bb866a06689792422e420818ea1702744bad95ae8784588902cb656ba201162240cad95ae8884688b1120696cad744422c4481aa7f4f69e215b412b254c518750e04a53fa4d4904b896512a010ea154267aced28b4a49404b8961260e227c3a8702529fd26a4800c009f412ef9dceb0231460c6809c 0x3099660400c08597fc02ff97e0704c0e597f802ff165fd00bfa0584002c88059000b1e0160c02e5006127db900172003088160f00b420167802c10061000bee097d802fb005ef06c24c183c03078060160bf8017f00b09005c900b8c0d83c13078059902b020160402f5005e7
def as80 := bankPage 0x6c8764875d7757675077497742773b7734772d7726771f771877126709980098 0xa98b846553453e36b8a98b6553453e36b88b6553453e36b86553453e36b89a8b65453e36beb88b65453e36a98b6558533e36a98b7165534536a98b7465534536a98b7a65534536a99b8b65534536a99a8b65544536a98b786553453ea98b6558533ec6c25a502e28090800b8b565502e28090800
def ac80 := actionPage 0x553c1110c08623404e3a900c808821c044348f3081121e6030330e0c80161a402f2e0ca8c10c1800272a8b9c800e156025250a2cc00e12c02421891c81091110221e081c818b0f001f1987a4410c0cc01d1586a0800a0ae01b12051cc0090930120a843c800e06900007029cc018021000030120c00600f0000000188085000 0x100388004940000c09018c3000082086001400480ca594c0088066b400c80005a5204c8167800888119ed96d064896fc0002e86f33c0002c1b8118045eeb00800000006a80c74002001c60d807a9781c812003e00d0840319ec8795208600b813b4805488014240d02d20528004180d62c6000101001cb124022940ad81bc0f0a40420c1ec00061e6017a0502b1902e9f4790c80006e9cb4006040d8002d20681625180059d4a0a0005814b500022b405021e0000cf00505014090080d000af0900038ce400008601482984701803380006004521808004e0014a05b1633800c619a01b00e32002500090bc00391e0090cb018200000012400300007b500098a7180a00002c0388048401004e23100004c0f6ea0000d1b00016064c7903f0b9d2718008183c09ff7a680020664030aa001c0002a0003e209680b91c0099dd0ba0000178646fc090340336ef899202b950c88001c8a780020030e33880f0040310c0031cc00000310020018a0 5 0xedcdcdcdcda3daedcececcecea5ededcca110 0xb02cf157249b0aa60885e3bc1636c6586a2731a0ea9849244065dd8b7561af15098d91a93aa093d2760c69108d91ae35275412634885e3bc5616c25829ab314880cb0e61253aa4a492920fc8490589d5252494907e42482c4ea92924a483f21242382e058bf97e29a530925020730c30cd3da7a41682904800bbb602bfd129ad351f2be26e6cf18e90e1e230c32de3bc575edcd84b0760a14b836a478c8a8ec13a25dc1b5222a3b04e897 0xc5c01874330d2be8348d06b19355f26a4e4d48c9a018617b33ac63d49c7a3f89c4f138662000c4019878030f0061700cee018c03b178662f02c5e018bc0b170062e00c5a198a80315076260cc4c0589803130761f0cc3e0587c030f8061600c36938f813160062c04c56018acbf0f1661e00c38018a8030d0162500c4e0188c03130e61400c280189403121464200c44019b807100062000c3e5f874030e8061543c28218517b44aee8949cfe919fc7f3f8f67f13cfe259fd0f0c8661900c3201860070b8061700c2c87850330a00614
def as81 := bankPage 0x6a7764675d7756774f77487741773a7733772c7725771e771777107708870087 0xb8a99a6545362ab89a6545362abeb8a96545362aa98b655350362aa98b655753362aa98b655853362aa98b7f6553362aa98b846553362aa9a48b6553362aa98b746e41362ba98b716545362ba98b746545362ba99b8b6545362ba98b7465534b2ea98b736550453e36a98b7a6553453e36
def ac81 := actionPage 0x1c2e179d408e1a70182b1599001416b0182693a5000b14a01723119d008912f0151c9034c20b10e013170eacc00d0e7011138d1cc0890cc00d0f8c20808b0ab00a0a8aa8c08a08d00909090cc2870780080807090087063007070509000804b00605830d0007036005030294408801e002020108c08500f0000000108005000 0x1094003200f4ac0803c40500801016000841008290012010923030e00ac803006400008608ef181cb20040380e0008073340103000388e0080c032003001e068105420a0200c302d006000f034cd010606856a01409001470002063ca758440404e52818601c00d1c27e000005c01001835b2ca28300604e5040a500000084265012a000072b920129c730000085004140050020280010180340043000a2118c41802953ce348062308403b860000020818a01465034e9000603a42300100009ef01c841a804029ce3016619400004050000100c640980021ca000000280030900629006010201008328c86000c001c0031000380003184100ce52840029cc00808501003000c51088301020180e100043010a019c0000c0400001088460040400c00 5 0xed953ed53da93ec97e74ed7e74e7e74eb2ec62ecb2ec52cedbdc 0x9f109211420824c610f672b093e21342484635a7c42684908a1041263087cc6670bfd7f2fd3f443ef1d856d8c258429e4d0940d514e29843c655e3b0b60a3a40b712ce0878ca0e61259c336600bf97e1f9222ce19b3005fcbf11d1f922344e07b896cec017f263490810732754920b13a82c4ea0b14d0610589e92e25b49e0d986a09bad35d2504c 0x2bc845190813210064200c80019ec031f8063e00c6c019e80b1d0067100c7a018e003118067800c7401890031a8163300c68018cc0318bc63803c5601884031780619
def as82 := bankPage 0x686761775a7753774c7745773e77377731672a7723771c7715770e7707770077 0xb865534b2e2aa98b8a654b2e2aa9a58b654b2e2aa9a49a654b2e2aa98b84734b2e2aa98b6558532e2ab88b655345362ab8a9655345362ab8655345362aa98b886545362aa98b8a6545362ab89a8b6545362aa9a58b6545362abeb88b6545362aa99a986545362aa9a49a6545362a
def ac82 := actionPage 0x1b2e939d00151b901a2c929081881a10192a9210410718c0192811944004180016251198008716b0141f1030c00d144011198eacc00f11700d148ca9000f0ea004118b18c0150ab00310098cc0880930020e880cc0890780020b069cc00905d00109850cc0870480010583a0c00b0270010301950006015000000018c007000 0x8e620076602040005014580061800907820100091c4665e81b2741f003601481d793d7681d782dc20082000840010000008400000294c000040010221886039c0300043010e0108010800128821100200940901400200430974000008084cb02440000e570c02524e6001280a0082800a480041b8c0000a71a8802b16cb0000489e9011000080f21560281a02bd003944f0000bfb2e302ca54a400039c96008900060614cc02c0a015c7400e21800051c00015400140401403244e4038c101d080000020000014b02b9601810022800780000000000ca3008e001023198a508c6030082000000046500001014403006038800280e0300a052c000284700408689200180500c60088231040508022020883880b028404200a00140198601b40d115202000b0002728080310e0009a0381ed204035004d52922000ac 5 0xedc3d3ddedcdc3dc93dc3ed3ed3d53ed3da3ed93ed3 0x7d4d71adac25009fd3eaa91cc32c6533e4f444087b4c4f89e8ec18c5e8bc96a98c24648af1d85b0530e3a40b6f4c78878ca0d00daf1bfd6cec017f2985009f52490f195615b3b005fca613fa7d49243c653ea6b8b094027f4fa9e8730ca5343986527c4268450820931843d3a91121f1ad3e2134228410498c21ed9108a1041243db7b644f89ed3a98c 0x192c0b248064900c8ea18c53b188163100c6201924a311006484ec64018c803238063700c84018e80312a465308c8c059004b1a0067c00c8a0591003220063e02c7a018f40b138062702c8401910032100622
def as83 := bankPage 0x6c8765775e7758675087497742773b7733872c7724871d7716770e8707770077 0xc5a98b6545362b2ab88b6545362b2ab8a96545362b2ab86545362b2aa98b846553362e2ab8655145432e2ab8655345432e2ab8736545432e2ab8a973654b452e2ab873654b452e2aa98b77734b452e2abebc8b65452e2abebca965452e2ac5a98b65534b2e2ab88b65534b2e2ab8a965534b2e2a
def ac83 := actionPage 0x1c389890c0041b301a35161d400c18f017321319800c16b0122f1019801412f0102d0f9040041230102a8e14c08710e010258ca8c00a0f000f220b1cc1080d800f1e0b2002040cc00a1809b0c00a0ae00816898c00030a50081207a5000a0870080d05a9000b0660070a0418c006054004050229000e02a000000029008e000 0xc00294040002020501409600012b2a54d018204058f0240e000085880900d8c18080001ed7b56e01ce0489270040e0002b0080f018e8a00ad001aa000a46a0064006f01980001002808d008400280039a07299606b1a4780c0680e0100c40804031ca00140300880380c330c43280030014c00088000a05a4600000a180034004843dca024a0300000248d48580028c238800018e1110800180012de68480503d010200f8b14250062400000106100c0c40400001000990c52049424047b56000c004000d0010018127100e47800b01001000e733c0113dc24900000d20014012a80f1000ec900d000e370da5009ee804080000600007738650290744e6041cc70282000abf002e0001fe6b0050000e4a1d1b3480034b9 5 0x320dc320dc9320edc320ed43d43d43ed3eda3eda3ec3edc3edc3 0x10f194184163fe5029f8878ca0c20b14027e21e3283082c7a6d7561a815009f98f3085688017291f2363846bd8672ada19fb015feaa52e91b1aec598ab145ecba9728d7946f65bfb145e8aacc70ca7b2e05bfb4b628be17b2c2556638748d56283285a46b7bcdd53e213422840c610f8d6f79baa7c42684908a1031843dbd31e550970878cabc6ff5bd31e550a013ea5c21e32ac2b7a63caa14027f4fa970878ca 0x64f0cc66018cd5f2a2465400c9e019383b1a0663402c68018d00326a8e3261c480193003250064900c90a38c40326296375dcd0c1890a312146225dcd0eb9994f3309635
def as84 := bankPage 0x687761775a7753774c7745773f67387731772a7723771c7715770e7707770077 0xa98b8965453629a9a38b65453629a9a68b65453629a99b9865453629b89d9865453629a9a49b65453629b89b65453629a98b65504c3629a98b7f654c3629a98b84654c3629a9a48b654c3629b86e69412e2b2ab86545432e2b2ab8654541362b2ab8655f41362b2ab86e6541362b2a
def ac84 := actionPage 0xc20a309008716e00b202105008715900a1f1e89400614700a1d1b91800613500a1a1899800911a009181611408710500517120a01120cf004168f8540070ba003160e04c0070a5002140c90c08908a001120b10c2070750010f0b1804840690010a88a54088051001058529c00e02700103021580060150000000190087000 0x1086080041100000080308a02040700c00084802140301486000c001c40014e100005180820018d480e9194000856b5000002481785e1180a00340750c203946051c475a560314ad0002118c00020ce014006800b01d07300a500c0518184309ad60ded1806032c0001828100843280061cc0208060086020003010a001c6018c8201023000000800000c620140708004008a320c2100c200004039860300032140301c0301c2700c6000c4100404004ac28040590072000b01da0491a95001e801143815800001b000e1800fa6922602d4055e17818c8152002c001000a1816d10dc5501e03000030402019211802609524 5 0x8510b320b8610eba531edc510edca5edcba530cb310cb6cb6ca5ed430edc4320ed4320ed20 0x824000004120014c2100c20013b18f31a6306502c534a603082c0c61840000041a058008004f8134008005fe5bcb716d2784eac3417790dd98a9a33304f0962c3502a013f1a327846c6b861058bfce193c2740b24faff3864f09d02c 0x165700cb00195c03120265700cae0989403128065402ca40194c032900635
def as85 := bankPage 0x66775f77596752774b7745673e7737773167298722771c6715770e7707770077 0xb88b6545443629b8a96545443629b86545443629b88b654c453629b8a9654c453629b8654c453629b88b6554453629b8a96554453629b86554453629a98b7a6559453629b88b6559453629b86559453629b8a8655f453629a98b6562453629a98b7e65453629a98b8365453629
def ac85 := actionPage 0x200dbb0a000c22b01f0d3686400c20701d0c328a00131ce01b0b2d0ac00d1a701a0aa786c00d18001809a20ac09214a015081d0e800e12001307190a000e0f600f06148a40910c300c061300c0040b7009040e92400e08d003030b09c19005d00301878dc08a03f002010485808702a00100828500870150000000054087000 0x9b0108dd48000c81913000f8d00091380080d10009c0d90004808730005960009fa9000d501a10dd07c0ed06360450887b6d01a4610d973709010100e1000160800d990305c0080542b0a0c08800ab7de783090800d520a04800e0a31b05020b60f2d9cd8840a01838008b3092098102f0c8cba0005000007005a8b88b050b403960060520c6e9a000007bd07101700507d9030eca07800123c071980008007ef0510310030ea00a0b9807e0770f60aa60d0f5c0020e060b69890b60996b00008ca0bfe701764200037500003ab4073442964009fa0f10000000cd002ffa905d050000ea401dc82202ca0d43020de700eb995043adf270b860621e2001400e002c10260b302296304003171024007400276345460457570000704240211040401144753022300 4 0xedc65430edc765430edc65430edc98654310edc98654310edc98654310edcba85310edcba810edcba8310cb0edcba6510edcba10eda6210987510321098520 0x100000000800002000000010008240080041200000800412044008000020006501200200000000 0x65806cc60598803310366200ca4059500b298065300caec1908a32138e3406c68e389dbf138362704c4e01a3403320065058c88939104f221f6263dc4c63898bf130362604c4c0198c0b2c00662
def as86 := bankPage 0x6b7764775d7756774f77487741773a7733772c7724871d7716770f7707870077 0xb89b6545362a29b8a46545362a29b8655d45432e29b86a6545432e29b8746545432e29b8696545442e29b86a654b452e29b874654b452e29a98b846a4b2e29b86559453e3629b88b8465453e3629b88465453e3629b89865453e3629b89f65453e3629a98b8465593e3629b8986545433629
def ac86 := actionPage 0x36212791800a1ce0311ba32e409119b0311b210500061890311a1f090006177031181c914007162031169a8d008714d03015180d408713802e129694c08812002d10959081081080250f9209c00b0e701d0c101d000a0c90080a0d11801708400404892e0091051004028591c00a03300101050c418402700000000a800d000 0x7900039c4200000288a7415c60000468006714804806fac8fde8c0360300daaea45c00000675ec00381a001c35000a01498be1c0010c0018040180012000038c013002000ce50000501ca0000e02810220020280a0080820004000c800000601c0630c4c514e748c0800000030a00bc0602000008ce181410010010d21118640004301c2600400180e018040010e1ae185e00ba003dbf0000581e0001a2810eaa013618010e81890b0db003b107da05817a18020048007d97d070010572538d4331800000952025a0656e0560068188c8010d01a506c00b912701c2068ec020040a00005a5bf06fc3282c0501b22806007c1440182ab1a4544003f400b7d26049c9018e348da00000f581e06a4800006c51c06008a00802400c40029600bc020000169004029210000b1ac0411d00000a033440 5 0xdcba30edcba5430d743d732dc732db63dc732dc2c7edcba10db50edcba0edcba510dcba760bedcba75310 0x13ea1342218dff3fd6749f93ea7c4264981702c000255280955ca9752812c4247c04427d4a02553ea7b4ba94096247258254030010013ed940cb0c6184160009f93ec31861bbf4267dc6e8d91adf198d0580040058c93d1ac31cfb434070c7000 0x33c8065760c8401908031d0066673c62018c403330166500cca05990033218e2f2fc5e0d8bc1317c3e4584c8a939144f22a362043c402188033100066f78ccaab9941332806652fc5c598b813170062e85c5b038b4c7168362d43c4c7f898f7130662646c3e8787c430f8661f00ce02195d1b128862500d1c01994032834658
def as87 := bankPage 0x6d7766775f77587751774a7743773b8734772c8724871d7716770e8707770077 0xa98b5a45362923a98b5a533e3624a98b5a45362925b8654b46372e28b8696645442e28b86a654b462e28b86545362c2a29c7b8654b452e2a29b865534b2e2a29c6b85a5045362a29b8a9655045362a29b8655045362a29b8655445362a29b8a9846545362a29b8846545362a29b8986545362a29
def ac87 := actionPage 0x1a2f231840861a10182b22a0400a183017292210400417701724a025010915c017231e8cc00514d017211d10c00513e0171f988e408a1200161a96a9008710b016161524c00b0ea015131398c0050db01310929481060c900e0d0d9e801109600e0b0992008907b00b0708a0820706600203851dc01402a00000001e800e000 0x80373003180026800540000000202046c0046800800114c6008a0008a018020190050002038067201a9018a20810c00020024a0581e319000014a338083010e408c0600041010e1100814a0202a98003860030001816620c2502ce0009401a420200cd000014180e0000038d810bd6f0890d080e018001124000016a0100f3800658d667000c200000046002025239406140d04800185a0503a01a41f02a017f80b029200000c832a25912d28000c012e03c0f4800e001af001a01888002082494e76080f0000d6112b01dc00100b53b72001e303240cb900bb005a8147641ab08c0090fe6640b7e7800401807827ab90190001d068d904c0c4a40b6018020163e80086800700d6f120a9000e6399a9 5 0xcc2edc4eb4ec2dcba87310ca42dc3a20c0edcba43210dcba8310b0edcba40edcba54310 0xa774de99524a3e0badbd7daa754a99d319d931a9bd24a3e006c310a17c1fc360530a41401da1203e0792f04f0760e9402130053edee3db7b2f59c0b2a33063896586702d71952c3584a013f27d7acbfcc90ca0c20027daff1941840058d9f6b0d612131d61853f2164220067dafe5e8328318610580027db3a584a010b0630c2ff9fea1342263016000 0xcd2059800f148062806cbc0192c033440e4f06c9eab9180323006406fc68218d01b272ee4657c8c019c813338066706c8a01910131e8063d73c4edf89db33108633
def as88 := bankPage 0x6d7766775f7758775087488741773a7732872b7723871c7715770e7707770077 0xa98b7048362a1bb85a5350362a1ba98b5e53362a1bb8715f41362b1bb8a96553453e361ba98b8473453e361ba98b7f7153361ba98b7f7054361ba98b786553453e1ba98b7873453e1ba98b655a58533e1ba98b6558533e1ba98b7045362a1da98b5a4536291ea98b5a4536291fa98b5a53362a22
def ac88 := actionPage 0x1a2f0c9040051590182a0aa9008a13b016268a1c418912001625088cc00610e0152087a480070f90121f078c00030f00111e068880880d80101c061040870c300d1a061000040b700b1504a8c08e08d00a1083a481070780050a8230c0110450040881904005036003068110400402a002038098428501b00000001c4189000 0x18c0100445000800048f5240502580784c6028440010423c24030e0000a052006000cc01c204a0a02002040d22014472988001ca0300802000200d2d1810051540481e900064284403000419c0000c0000ce019c830008000482100201800009c040080210403000c3000c2000013a400004035a4834a5a8014eb6ac004000001920004004b4c00818810d201a040001a90080400004944004454008000911cd705772000e0640b065750000a0108007cb7db0141030318020088a0010000900100c802800101c00300e01808121882000a052006000cc01c204a0a02002040d22 5 0x6ec97ce62dcecbedbdcedc675c 0x2b653ca7684ee6dc798ec05802ff4727f4fe112b8954e9ed3ca76c017f53ba480bac24d998ce61a029b49644c65b0e5767ba9d9fbb234f29d9ee6e8c70620c3a134224ac939250c212b0e3be312c2549a5f4918e31b18e318175e3bc5612c1379638434640c70c60c417565a6f4d909d37a4947c4b539a6f49290d1f00370ea9d33a654c5802fe 0x5905a3330064002c76018e403359666a46c6c078b00b120162200cd4ab8e00f0f0062103c38058600335a36231cc462188c0f0b8164302cc20d9840b1e00639
def as89 := bankPage 0x6d7766775f77587751774a7743773c7735772d8725871d8715870e7707770077 0xb18b5a4536291ba98e5a4536291ba9905a4536291ba9925a4536291ba98b634536291bb89b654536291ba98b5a4a36291bb85a504c36291ba98b5a4d36291bb8a96545362b2a1bb8a965534b2e2a1bbeb85a5045362a1bb8a9655345362a1bb89a6545362a1baa8b7045362a1ba98d7045362a1b
def ac89 := actionPage 0x14288d10000410b012268d1000040ff00f240d1400860ed00d220d1000040e100c1f0c9841850d200a1c081a408d0ab0081a0810028509c007178615018708700514061c0185078005118594400306f0050e051c40040630040a841c808605100407031c8105042002040119008c01e001020090400500f0000000104005000 0x2010c04014000802010c04014000880400c0710004100073800008043010050002600c000000430443001b4080080540e0174103920410430014a055e07bf21079e0010030000600822208600000a400292b500304027202002002000c0014c0135c108ca7000043846029c070004102c2a00d040000b3812063c42004030008e100403902249005700020108503860000e013c03014686a0224006300401114002000120c60080222800400024 5 0x5edcba5310c3100ca3c3d95366 0x53ca480040053ca482584ad3ca77490a4147a7949000800b9d736d95750280014da110c618417001a7949000800b9a8380b00100173ae6db2aea05000800b084486606305b611be320554978890cab9af59d7365414648895846d2bfd4da4c22432961213422828f0912ad94f29da13ad94f29da13 0x172d8365100cba0595803360065c02caa0196c1b2881e5e6ccc4098cc1b2b0265600ca80794403288064646ca4218cc1b2083641
def as90 := bankPage 0x697762775b7754774d7746773f77387732672b7724771d7715870e7707770077 0xb86e6a41362811b8655d45362811b86a6545362811b86e69412e2915b8655f41362915b86e6541362915b88b6545362915b8a96545362915b86545362915a98b6545362917a98b6545362918a98b6545362919c2b85a50362a291bb8625a4536291bab8b5a4536291baf8b5a4536291b
def ac90 := actionPage 0x181d2a0c80051a40181c270980061920181b2409800618001818a215000517101817a009000615f018151e15008714a01713978f408c126017131187010a108017120b8b00130cf0120f0899818f0a200f0d0611400d07b0080904210012045006060318800603300504800d800701e00302801000040120000000140086000 0xc03080453802020c0000080008e6280e1200a000000280401100028480008441802029ce3014406804300020008c018820380401a402280030046103040180002157e00064101407042002808404000018a3814b4acc0314ec089813ac6958c000000f00146124010384012d62290000000762549200005b860301eb0940b03580381cd4898c4914c001403012538087206605a801324a0004c002405324027b0800546a608006a42021c0c001e0180c00394002cc040024385c2329c07200b2112a682c0a027390a190000721d7fb1445782c0882168800138001bca003d4c011fe00436000c0002405098644a08100c0f0000f385e503800001033a00100860200a00044020060388002080039c00 5 0xb2e76432eb7432d631c621c621edc9876543210edc987653210edc987653210ecb763ed531edcba1987510 0x9b05c0b44d82d1360b67c3e41142200acfa8733ea1ca0c02a0040180100000401801672c4185aae0c6185060150020015faba55c1d4390700c6186adb652242843182da480040053ca482584ad3ca77490a4147 0x2cc6019c813388067100cbe0196803380065e00ca2019bd1b3721e6e10cdc199b8072c8065900cd0ab9180331ab65d02cac019b55b2e01655
def as91 := bankPage 0x6b7763875b8754774d7746773f77387731772a7723771c7715770e7707770077 0xb8a06544362910c5b86541362b2a10c7b86541362b2a10b86545362b2a10b87569412e2a10b88273412e2a10b86553432e2a10b88073432e2a10b88265512e2a10b8655341362a10b8756541362a10b89c6541362a10b8746541362b10b89b6541362b10b8746551432e10b8654536282111
def ac91 := actionPage 0xa2c978500061410092b160cc00413500827949cc18612300824119d808910800720901cc0870f30061d8f9840870de006190e24c00a0c0005168e1400060ae005148d10808509f0050f8b29000a0810040c8919008706c00309071d0087057001068594c00903c000028420c08702700000831080070120000000058006000 0x13440070000060021500022030636000100237f107100ba2020b30e00b0e8c08085a17000e00405108220a57000371003560300072404603073000a425cba00009008f20000d0d90cb60017041305550005030000515165150500a806f8c2000b503b00000e0fd00800502a43450a0a00f428600602e00450b4030e4502700020370e0d43a2004090d8743422ef37034300d5907700070500170720044000320450000130171030404 4 0xc543320320dc9320eb3ee73eded73edb3ed53eb2e52c7e73210 0x21c4622780ba4346252268c9e06305cb0d40a7e38a5903182e8f918e311642c435c6b4e88b913225bc469761a43462828f15b42ff55497a2e44e89912d7bce897512de2d8690d18a07bc1780da17fa9b4991f2311642c435c6b48a90d188e29c323646a4524c0940b81647c5364f09d0770c6184174a689912d2f111 0x3278064e0cc6ac3890033b066340cc66018d4031a00633
def as92 := bankPage 0x697762775b7754774d7746773f77387731772a7723771c7715770e7707770077 0xa98b654536290da98b65533e360ea98b654536290fb865432e291610a98b73432e1610bb5c422e281b10ad8b65432e2910a98e65432e2910a99465432e2910a98b68432e2910b8806a432e2910b88069442e2910b8656241362910b8836541362910b8654e44362910b8806544362910
def ac92 := actionPage 0x12191399810e12000e1492a4808d0f900b139009408c0d5009108f1880090ba0060e0f1400870a50060c8f0c000209f0060b0e8c40040930050a0e88000308a003080e90008407e002068e8c0004072002050d0cc086060002040b09000505100102880d808703c00001058d400702700000830540060150000000058087000 0x86030cf600003c2e050e00d455600519709e080c9e0913290480950d9008007b91b097665ba007080c2a705000684764135039e804b005505c006020f000520200114b00fd17bfb607730170342021000751000120232200031000011101003007043210016511100120010000400053412400021404500000372363008028070a4690008207c66b1065071030000006077012400306054004050500120730200003000361 4 0xec7543eced632737cb7db63987510a9820c6430edc643 0x6decc93204b05c0b26b4c698af9957a994ca9912500100113a2643a8730e04a45b89b13225ad6b3d2a62744c87024e1c09389912e1c0938990e049c3987025a1c08a870004004380020021c438 0x33c8067800cc001954033b80e2900c52018a01b3802e5b00cb6019d8033a006767dce6019cc033a8067400ce6059d4033180662
def as93 := bankPage 0x697762775b7754774d7746773f77387731772a7723771c7715770e7707770077 0xb88765452e2909b865504b2e2909b865534b2e2909b884654b2e2909b8a4654b2e2909b8654544362909b8654c45362909b8655045362909b8846545362909b8986545362909b8a46545362909b8a76545362909a98b6553362a0aa98b5a53361b0ba98b5a53361b0ca98b654536290c
def ac93 := actionPage 0x1a23b20d00871ef01a21301501061dd01a1caea4c00a1bf019192d1cc0081a701916ab94c08619501915280dc20a17701913a38e410915c018119d13420e13201510178ec0910ff0140e918f008d0d80110c8c12c00e0ae00f0a0617008d08700b078494c00c063009050414408704e004020318800c02a000000011810e000 0x8a4000a011c2011807004023000f10001110c4280860012501c0002c04038ac500a4100000300549d6a5a86033dcb021c001961000854804040ca600c8000c001080018408604040100012000125830040051c405840001d402a0000300948c0228ca300464300c76f1685816f045c078012d340003580f01801ac20039c45a056e8540070004906a40120680c058005280060040700cea030c7005ae48980628433ac06000c3131c0519a0080a20248003060105c0034a0005805f40058016004ef90040525ac01545002e170d48400ecdb0f6002803000738d8f029c2028041814500186040ef002c61004c01800414ef008400002a414802806b008e0480056940420800014020980001c8730000204a079921309880300830009000081800c3800b1012721800204e003140000a030005618c0408e7228053bc0c0914b010e0 5 0xed43d730d73d73d73cba7430cba984310edcba76543210edcba765430edcba7654310edcba765430edba76543210ec7cecec7643 0x1a6b2912ae00718bf12c256c33fc758e9dc03294fa48071b824c038c4b89612a24da692012c2544989612a0044b095002b0c4b0950f425c4b09512c2540009712c2540009712c2540080066ec017f2654956a6d3a6b4d08baa853da76cdd9b228756ce4a4147 0x3330065400d180994c03298466302d180d98803290468c04cb0019f0031e0063b00c72059ec033d8067a02cf0019b403360066900cf4059e55b2e0065c
def as94 := bankPage 0x6c7765775d8756774f77487741773a7732872a8723771c7715770e7707770077 0xa99a6545332a08a98b6553382a08a98b8465533e2e08b8746553452e08a98b8474532e08b8654536291509b8654536292609b88169452e2809c5b8654b462e2809c7b8654b462e2809b88469462e2809b865534b2e2809b885654b2e2809b8654b46362809b8655746362809b88265452e2909
def ac94 := actionPage 0x928999cc0871470082498a0808a129005229810400411d0021e17a4408b0fc0001b1718410a0de0001a120a810a0c0000198b07800b09f000178a90400509000016090cc10308700012879cc0850780000f079c000506900009862cc10904e000070594400503f000040399008702a000010218c0880120000000090006000 0x950901d08070b6000ad5450050060b00bd015030d3a721103d305003506110060004530200ae240c1f0f0a0db70cab02304250904516150000e42807000e415900c0b100a0f64264f3f097020d00c50e8ee007200fd9fca047e0db1230023002005040153033125600700b69e0f9001a60d1045510400002260b8609070005304ab20c07d3e7c235730000040310080510205183300701d070a03c600086c00070024c852040070707425162250 4 0xd54ececcc987654310edcb9876543210b432432c933e740e74ed43 0x8d8a1d0da134227a4ec4c6600bf95929f4d49a528b3663eac8ffa874bc9752e2544a6945281ff47e82103a003fe7f84b00312c334660aa152c806603b6f6c80888cc0d817c1db0030e4507f0b716c2d6c33fb74ee99bdb20554a012f11119839c668cc17c2f54011119820028850356534888cc13826d94895 0x68400d060b8c813190067f00c620189c033f80623
def as95 := bankPage 0x6b7764775d7756774f7748774087397732772b7724771d7716770f7708770087 0xb865504c2e2908b884654c2e2908b8a4654c2e2908a98b6545342908a98b6545392908a98b65453c2908c7b86553452e2a08b88a65452e2a08ac9a65452e2a08a99a65492e2a08b86557532e2a08b88465532e2a08ae8b65532e2a08a98f65532e2a08a98b6b532e2a08a98b8477532e2a08
def ac95 := actionPage 0x2b350c11418717d029320a98c00a15f028300910c00714a0272d8894408513b0252a8818410712602227079c400711101e2306a080080f901b1f0620400a0db01a1b851c80870c60191784a040870b10111203ac800d08a0090c82ac810d06300709019c808a0450050500a0808a027003010020408a0090000000080003000 0x1ca00026480c70196901d210100f180075002003d4d00401030c069187400e0200e2100a219806018c60180000046008c2100e000c03000040186700845100070346010dc511c03138800140a384603000042c005ada210940599850018102820100034004b0810b70003080082856240800081074b407281007812500000490082a5c0090080300f200003246707c29a002038040d2c007000000009bac862a080058c67cce602c0f50252501d73ecc77800048400a8343d7808580364b440008003816000c20088050142a32ce10154310002000c0500017802d0180a0ace8404063346000c00101a000c6039002014ea2acc7009e00008100067 5 0xcb310cb6ca54eec33e5574e7ececc 0xf808a110011101f13e0228440043e0228440045109404a83700ea2134a502580dc03acb578ac94f06a07201df2369600a8548253224335662a31d23a0670cd19832a3628743684d089e83af1b19528743684d089e93b161a3ab8a682ce99ca9f4d2944890cd730ce592b02600bf95929f4787fc8acc6600bf93525146881a633005fc9a934a5146881a633e5600bf95929f45a7fd841ff 0xca80999803298065260cc2019f983300068704cfa019f403258364a04c940191413248064900c880190c03208068b72c98e19301b260264c4fc8e0191c031f8068a00d0a01a0c033f8064d04c90018f53b188168600c7805a18031d8068600c7201a15471902e32
def as96 := bankPage 0x6a7763775c7755774e7747774077397732772b7723871c7715770e7707770077 0xa98b6545362906b865532e2a0a08a98b65532e0b08a98b65532e0d08b865452e291708a98b65532e1708a9905a532e1b08a98b5a532e2308b8846a462e2808b8655746372808c2b884652e2a2908b88365452e2908b28b65452e2908a99565452e2908a98b68452e2908a98b6c452e2908
def ac96 := actionPage 0x2f358f11000d19b02b318da0c00d1740292e8c98800815c0232b0b9c808e13201e2608a98090102019230798828c0de01520079800070c90131e071041860b70121b061882870a20121683a5410a0840101182a8808806c00f0f8011400705700b0b80200007042007070024000702d00404001800870180000000200008000 0x6c00020615a002d40030a0501e230d832b5601a4003988749c000006002c0a60000198ab700001050b725690002a48c0d000e000ce3301201916030c02204405388520000410000218d791ed020e0005c103c00285090014e182206806673c40e27a02f16f020ae5452848001ca176003c0c801b0fc0000003621602010100c0111080300e0000601882910402404023000712822080e0000a908c8020ca0200073000001021200053a16260064794000180350003321202080000c2d580000000050920280c3185c60040f7a56f0800d00008101e9505800108c084080800018144035a238002790002806708c06001e211000728c002c0c204604000011480000c4010430800032c2110020199e0189401140248001000e8 5 0x7543ec7ecececb763eccc7edc74baa9820 0xba05389612b31d8130056aa8536a6c4a69cd35a6a4d299d152714e09ad352694ce8a9662bd56aa814fa9e3384e44986b66eb515a2b35648cab454fa7b4ed1a232a9b4cd1ea2c73ab81208420820e9f939d24038c4007f0a414428394706d95b1b4e5eaa79281151d07c045088008b2d5e2b253c6649c0920d4af15929e528910cc9381241a94425012c254490375109a52824025c4b049037 0xb460066100cac05a1803430068400cf801a2c033d8068060cfc019f9833c0067806cec09a2803450068800d0e019c803450068200d02019f403388168004ce6ad9b403362fe7e00cd25999803448066700cc401a2013410068200cbe01a2013408068100cb40d9d5832b0065600d000d9d1832a80655
def as97 := bankPage 0x63665c7655764f66496642763b7634762e66295623661d6615870e7707770077 0xb8786553453ec0b88b6553453ea98b847853453ec0be8b65453eb89e9a65453ea98b786558533ea98b7a6558533eb8a98b6558533eb88b6558533eb86558533ea98b8478533ea98b7a655853c7c2842e28090800b865432e291004a98b6545362904a99a6545362a05
def ac97 := actionPage 0x262490ac800a16502423108c008315c02321908c04821560211d8f20c18a1380211a8d98c007123020190c8c800411701f178b8c800410b01f158a9080070f601b10092cc00e0cc00d0e878cc0910990080a87a0010808100708871041080690070485a0c10705400603048c808703f003020289008c01b0000000114009000 0x1be0a01000008c5cbbaa8a0140748837d81e2000021006608801081000a80d00068008a95ac0001d2d40d4001144000233a04210007004c0110400000100000100851180000020100031102000400010a000885000c30040cf0c1960000004008010d0f4c02d40c01e633e55900000780e8316255a0000248f2124100000720e14b800f0580f1400610014880a00c1a703c6400ae711a0500e603008080e7015012880038400280c11100100021010214a5200016901c67001a800180008820080539084000c2018031804830080000a6398a72808022067010e0010800980029080701400314b1bc2e034004286002020 5 0xededad43dceddcedcedcccba737643ed543 0xb01359f2be26e6cf18e90e1e230c32b7862442e69bdf18747a35c6a864f75b898b21741e17bdd6e262c85b1b1920b2eacd592360dbc10c0c3786ef58bb15611bc31b2183143082cbaf6e6c24d2724618c29802fe43c30a744901181635a668cb87c0dd1a62744bc3a8702504b0954fa84d08a0a 0x35b97ea000d405fa64034c8069543d1e21a3d63570069800d4009a78034f0069c00d36bdad927510fea213d4401a75174da1e9b0ed3619a6c0b4d8069b00d348ba3d0f478768f0cd1e05a3c0347866b800d7003a58034b0069500d1e019d403462b65d00cba0190c132080641
def as98 := bankPage 0x6076597652764b7644763e66386632662c66266620661a6614660e6607760076 0xb87a6553453e36b8846553453e36c7b86553453e36c2be8b65453e36beb8a465453e36b86558533e36a99165533e36a98b6d533e36b87465534536b87a65534536b89b65534536a9a49b655336a98b84745336a9a49a655436a98b787350453eb88b786553453e
def ac98 := actionPage 0x162b0c108084117014290a90c00510800e26099880080f000c24898c00830e700a238808c0050d800820069cc00a0ba0071b862440870a50061705a4408709000513849c800707b0030f042441080630030b831c800704e003098210800503f00208018c4088027002058114400401b00104000c810400f0000000200005000 0x304005411350051040b020302008a06053d0202bf00308000f1400001023150704570060000100e00701a019e280043302e00701010b10870572100059301010e0087037740002850100310000800076f5464060020b0b054d00076134810fc000b74000c040060f123501000050330000140100370002300303302230200062004050145002504060040060c6a55070d00 4 0xdcedcdcedaedccceccececcadb 0x2eb4d7494132c0b3c55c9267cbe2530924880cb6e29d8f7b714176126acc522032c398499a9316623e34c69892423140935262cc47c6ab54ba2744c7e53aa4a492920fc8490589d5252494907e42484705c0b17f2fc534925020750c2bf1242054088e0fc82b4f482d049ed0010b9868c3bb9445f137363643861865 0x1a6c03500669c00d5401a68fb4c9ee9931d325fa652756166987bd5c01a780b4e0069c02d5201aa403510e68f00d1e01a880f4f00696
def as99 := bankPage 0x5f66596653664d66476641663b6634762d76267620661a6614660d7607660076 0xb8655753362ab8655853362ab8846553362aae8b6553362aa98f6553362ab8a46553362aa98b6b53362aa98b847853362aa98b776558532aa98b786558532ab8746e41362bb8746545362bb89b6545362ba98b84734b3e2eb87465534b2eb8656453453e36
def ac99 := actionPage 0x15208bacc0080e40131d0a1cc0090c901019092080080b100f15889c408709c00e12081c408708700d0e869cc00607500c0b061c408706000a0a0608028205a0090906080002054008080608000204e00806848cc10404200805828900050330080480890005024006040084000201e006018014408500f00000000c0005000 0x80c59d3030d2f40a0200cb0a00086bb2bd9002ef0009e55730008000b900a3900d58703f0cfbf053890101801000e0cdbf053890101801000e0cd00079ff0070b9f4d05bf053890101801000e0cd023001002001002001300600154330630000042037407602103070005520002003600102400000300000271f04d90820 4 0xe74ed7e7cce74ceb2ecb2ec52c 0x6d8c258429e4d0940d514e29843c65474712ce0878ca0e61259c336600bf97e23a3f244662b365fcbf1392634913159b2fe5f89c931a48712c017f263490810734c566cbf97e23744e7e5c91f91500b05402c4ea92416275058a68162be4f49712da4f06cc4d3182c 0x35e016ac00d5801ae40357006a202d5e05abc035d806af00d5c01a5c0356806ac00d5609a5c0355066a800d5019a8403508069d
def as100 := bankPage 0x61765a7653764c7645763e76386632662c6625761e76186612660c6606660066 0xc5b86545362b2ac7b86545362b2ab8846553362e2ab877734b452e2ac7b865534b2e2ac2b873654b2e2ab88a654b2e2ab884734b2e2ab86558532e2abeb8655045362ac7b8655345362ab88a6545362aac9a6545362ab8a56545362aa99a6549362ab8655350362a
def ac100 := actionPage 0x6240e08c0030d2006218c94c1040c60051f8c1040040ba0041e0c0c00020b40041a8a9cc0060a2004180a144083099004160990400508a002130998008407e0000f0820c0090630000d870c80840570000a061c800604500008848cc006033000068410408302a00005028cc10501b00003021040830120000000190006000 0x40010045226402016104010031050046003200090015601a00801037a047002545700303212001505270300033006000863b2ca9002e9000ee55730000025010201180014402f02802094f0231001720300200040030733100037152230046000030733100b0a02356032008f57 4 0x320320eec333edca3c3ed35ed35ec97 0x6502c51e43c65061058c79842b4400c50650b46f4c795428e4b843c653da694bd15498c552398658ca5e8bc96a98c24648a61c746f4c78878ca0d00d9b220921ed9d7f29851c924878ca5343986546b42284104a7522243e35a11420826633385fcbf4fd10f 0x14755a96ad4ed5601aac0b56806ad
def as101 := bankPage 0x5b6655664f66496643663d66376631662b6625661f66196613660d6607660076 0xb28b65453629b38b65453629a98e65453629a99065453629a99265453629a99565453629a99665453629b8a365453629b8a665453629a98b68453629a98b6c453629b865504c3629b884654c3629b8a4654c3629a98b654d3629a98b847a593629
def ac101 := actionPage 0x12150b9400050b7012138b0c40830ae011130b0400820a800f118b0c000309f00e110b04008209900b0e8b14000508a0060a0b2401870750060989050005066006088689408405a00507068c008305100304869400040450030404054005036003020290c007021003018104c00501200200010c00830090000000008003000 0x23000244005320000202310000010040263000000010023000244005320030d5090690004ae225f20074010004054043040623260205031011000043120000504261200040014604010106017004700047240300010200320121031011000020020300 4 0x1b320b8610cb310cb6ca5cb 0xce187b0a55818505012000255d533828e0019c30f614ab030ab9558a35218710de1842e829000824002e614c255b73314c41201600041a0580080000082809000 0x6b404d4c01a98035a816b200d4a0dac4035a026a400d4801acd1b4fa1e9f10d3e19a7c0b5a806b200d4601ac4035f806b0
def as102 := bankPage 0x60665a6654664e66477640763a6633762c7626661f76187612660c6606660066 0xb86545362919a98b65453e1aaf8b5a53361ba9905a53361bb8a96558533e1ba98b8478533e1ba98b5a533623c6c25a50362a29c2b88465362a29b8846a4b2e29b88465593e3629b87a6559453629b86562453629b88365453629ad8b65453629b08b65453629
def ac102 := actionPage 0x10198ea1000f0cc00c170d94818a0ae00a150d9000040a2008130d9000040960080f8c9c80850870070e8c8800820810060d0c0c40040750060b8a8cc0040690050889988006057005068890810504800305080c400403c001050680c4030330010483858005024001040105400501500102808c408300c0000000144004000 0x300959009404000282ff2805080882800052920320036080770085485441006301802200072806011dc02140050045014c00000701045014c000007010e9008000100028803100020002200003000003802620400010a60000b60007581431800b78000100420040001427300c0088c238000004200080019401098a60000211862380a001ca000000084a0000000080218400014211800008807 5 0xedcbeddccca1bac7bcb0987510a98207c 0xafd5d2ae0ea1c8380630c2f7dc93736e0c7ea753b66ccd6a753b66ccd6c13796364346306305d34dc9d4ca6289c9090f1ced91799111cc18416247258254034fb434070000005cc2984ab6e6629882402c 0x236b743d6e21adc335b806b30cd7001adc074f8069f56d4a05a8c0352816a303d3005a9c035b006c100d6001b000358006a7
def as103 := bankPage 0x5a6654664e66486642663c66366630662a6624661e66186612660c6606660066 0xb88474532e08a98b65533908a98b65533c08b86553362a0aa98b6553360ba98b6553360cb8654536290da98b6553360db865533e360eb873432e1610bb65432e2910bd65432e2910a99473432e10b86545362917a98b65533617b86545362918
def ac103 := actionPage 0x191c0f98408712c0181a8f0c4104120017190e8c4004114015168d14c0880fc014150c8c40050ed011140b8880080d500f120891810b0b400c100790808909900a0c06a0800907e009098694000506f0090886880002069008068690000306000705068c0003057004020399800c033001010288800801b0000000094009000 0x660020420501021622250203700703242003330001410a48000003800d23487012e1e23303004000213002441522000624005202412755032ea00a050070b76970f000e02e2a0bc00e7e0044300c550f0fa70f70000163005c0130042d0585000a1052040021365002001000004100037000210110b66c60003b7e0f0a610b095000d0007581e0024414320006350052034127755670165030060506500672601 4 0xceeec7cecec7543ecececb763eced531 0x11fa0840e800ff9fe4de9a133ad2562ac19bb005fc995252684cc8a59b3356649901702c98498d30a259ad31a62be655ea653224a8b71362644b5ad0e049c4c8970e049c5a896b559cb10616ab83186166ccd400800 0x351306a700d7a05abc0357806bc02d76ada940352806bb00d6401aec0353806a302d5201aa4035d006ba00d7409ae4035c806b400d7201a980352006b1
def as104 := bankPage 0x5f55587651764b6645663f66387632662c6626661f76196612760c6606660066 0xb87a655853a98b8465593e01a98b7a65594501b86545362904b865532e0b08b865532e1708c7c2842e2a2908bf65452e2908b865453c2908b86b532e2a08b88477532e2a08b86553382a08b88465533e2e08b28b65532e08a99565532e08a98b6c532e08
def ac104 := actionPage 0x23248810420510501d23080c00050f601721880c01050e701620860900090cc0151d851882060ba0121a8418800909f011178298c10708a00e1382a0000607800c108218400606600b0c01a441070510090b0188000204b0090800988107036007060010400402a005040010000401e00302001000040120000000100006000 0x603000314052320f00180509300860046003700134b0005551655200005020250031756005000500135617036e0b59403438000c53000607d0850eb703010a06000e8900006b5000605740a90701707000406560870600ca010a0c939060d0900f2302003340501022670605070067300003506110041120000600041120000600014300030600050403 4 0xc7643ececcbaecece 0x274490118164f7726dce7ac906e62584aa734d69a934a67454cdd6a2b4566ac919359666cb07b8dc1a0af1592944886649c0920d4b2d5e2b20d40e403cc67cac017f2b253e8b5161ff6107fe632fe564a7d34a5166cc7d591ff66cb4d19a3266cb4d19a3246c8d515a2a 0x1b04035f80e9400d2801a4c0349006c000d7e03a4403488269000d2001ad4035e006be00d7a01ae4035b026be00d7c01ad0135e806bd00d5ea3aac175582eab04d5601af80353006be00d480dae98351806a3
def as105 := bankPage 0x595553654d65476541653b6535652f65296523651e55186512650c6506650065 0xa99765453ec0bea465453eb8656458533eb8786558533eb87a6558533ec7b86558533ec2b87865533ec2c08b65533ea98b8478533eb88b8478533eb88478533ea98c8465593ea98b8665593ea98b8467593ea98c7a655945a98b7a655947
def ac105 := actionPage 0x111c050c00830930111a840c800308a00d19040c000407e00d17830c820307500d16020c800306c00c130098c00705700c108014408304e00c0f8008000204800b0e8008000204200b0b80180003039009078020008502a00706000c000302100504800c000301800403000c000201200201800c000300900000000c0003000 0x301000207070042015000001230655431050603102061000e00010313720d05177001006502100001000120010725600404006db5090db7608014064400014064400010112014064400014064400 4 0xdadcededce 0xf75c6b70862dc485b114c21018d8c90597566ac916f0c6c860c50c20b1f09842fe394304c167b349c8cd2722614bf90f0c3349c918630a600bf90f0c33c1c73709ece41b94f2722c3277c5e6e13d247372 0x1b343362006cc43d8a19b140362806cc00d9619b400368006ca00d8601b240361006c800d8e01b0c0363006c2
def as106 := bankPage 0x53554d65476541653b65356530552a65255520551b55165511550c5506650065 0xb86b53362ab8847853362ab8776558532ab8786558532ab884734b3e2ec76453453e36b86d533e36b87965534536b08b655336b28b655336a990655336a995655336a98b6c5336b884745336b8766553453eb8847853453e
def ac106 := actionPage 0x913829840840780081282880002072008118288000206c008108288000206600710028400020600060c829c010405400609021c4005045005080188408303c00507010840820360040681040082030003060104008202a0020581040082024001048108008201e00103008c400500f00001800c418300600000000c0002000 0x404ca0038008080001000040001d45a2201c001541b806810102800980c00400010000404480c2488613202019201140088 3 0xcccccd 0x4c566cbf11ba273f2e48fc8a80582a0162be99b20db131352698c164d4988f8d56a9744c7e6353629829859ab3566b30112a383f20ae60a9319334def8c3 0x6cb04d9601b300362806cf02d9c01b3c036721ec5
def as107 := bankPage 0x4d65485543553e55395534552f552a5525551f651a55155510550b5506550065 0xa98b847a5901bf65532e08b865533c08b86553360bb86553360dbd73432e10b865533617a98b785319b865453e1ac7c284362a29bb65453629bf65453629c165453629b86c453629b8654d3629b8847a593629
def ac107 := actionPage 0x1013068c00040a200f11868c018209c00f108608418209600f0f058c400308d00e0e0488808607b00e0d0488000207500d0c0388808606300a0b03880006051008088294808703c00807010cc10502d008070100000102a0060501100003021002010120000600f001000108008200900100010000010060000000008182000 0x6701204104020103100002031230310062000343013100010000010052030333210500030050410050017002000a050090300de108e8c0721650000004036000001430000114801140405030e5027002003000100020 4 0xecececedcbacb 0x4f391ee459b2d3466b4958a684cc8a531a258b4b559b3359a532defb926e6dc18f8f61b63319c30f614ab15caac51a90c3886f0ba0a598a62 0xda203b0c0361806c200d9e01b380367806d001d8801b103368006cd04d9e01b3d1b66a1ecd10d9a19b340367006d1
def as108 := bankPage 0x4a44464442443d54385433542e54295424541f541a54164411540c5406650065 0xbf655336b86c5336c365453ec76458533eb88478533eba8465593eb88665593eb88467593eba7a655945b87a655947b879655853a9967853a98c847a59a98b867a59b88465593e01b87a65594501
def ac108 := actionPage 0x101400800001066010140080000106300f130088000205d00f100098018305400f0f0088000204e00e0d808c000204800d0c008c000204200d0a808c000203c00c09008c000203600b07808c000203000b068008400202a00a060004000202400904800c008201e00803000c008201800401800c010400c00000000c0004000 0x4200705080600004104a04128020304128104a04360020160005800120720401ff70006430 3 0xc 0x7bae36664826c2c45308409a4e467838e6e13d9c83729e4e45864ef8bcdc27a48e6e51a5b0ccb9dd175c64f191ae3e7bb936e73d648373 0xcda801b4c0369006d300da401b500369806d200da201b280364806c800da201b1c1363006c6
def as109 := bankPage 0x11330d43094304540044 0xc17853ba847a59b8867a59b8847a5901b8785319
def ac109 := actionPage 0x3058000000101e00304000c000201800302800c000201200101000c00030090000000080003000 0x1004040100011a700203080 3 0x0 0x13ba2eb8c9e3235c7cf391ee46694cb 0x1b4c0369006d4
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def compactStates (i : Nat) := (if Nat.blt i 880 then (if Nat.blt i 432 then (if Nat.blt i 208 then (if Nat.blt i 96 then (if Nat.blt i 48 then (if Nat.blt i 16 then as0 i else (if Nat.blt i 32 then as1 i else as2 i)) else (if Nat.blt i 64 then as3 i else (if Nat.blt i 80 then as4 i else as5 i))) else (if Nat.blt i 144 then (if Nat.blt i 112 then as6 i else (if Nat.blt i 128 then as7 i else as8 i)) else (if Nat.blt i 176 then (if Nat.blt i 160 then as9 i else as10 i) else (if Nat.blt i 192 then as11 i else as12 i)))) else (if Nat.blt i 320 then (if Nat.blt i 256 then (if Nat.blt i 224 then as13 i else (if Nat.blt i 240 then as14 i else as15 i)) else (if Nat.blt i 288 then (if Nat.blt i 272 then as16 i else as17 i) else (if Nat.blt i 304 then as18 i else as19 i))) else (if Nat.blt i 368 then (if Nat.blt i 336 then as20 i else (if Nat.blt i 352 then as21 i else as22 i)) else (if Nat.blt i 400 then (if Nat.blt i 384 then as23 i else as24 i) else (if Nat.blt i 416 then as25 i else as26 i))))) else (if Nat.blt i 656 then (if Nat.blt i 544 then (if Nat.blt i 480 then (if Nat.blt i 448 then as27 i else (if Nat.blt i 464 then as28 i else as29 i)) else (if Nat.blt i 512 then (if Nat.blt i 496 then as30 i else as31 i) else (if Nat.blt i 528 then as32 i else as33 i))) else (if Nat.blt i 592 then (if Nat.blt i 560 then as34 i else (if Nat.blt i 576 then as35 i else as36 i)) else (if Nat.blt i 624 then (if Nat.blt i 608 then as37 i else as38 i) else (if Nat.blt i 640 then as39 i else as40 i)))) else (if Nat.blt i 768 then (if Nat.blt i 704 then (if Nat.blt i 672 then as41 i else (if Nat.blt i 688 then as42 i else as43 i)) else (if Nat.blt i 736 then (if Nat.blt i 720 then as44 i else as45 i) else (if Nat.blt i 752 then as46 i else as47 i))) else (if Nat.blt i 816 then (if Nat.blt i 784 then as48 i else (if Nat.blt i 800 then as49 i else as50 i)) else (if Nat.blt i 848 then (if Nat.blt i 832 then as51 i else as52 i) else (if Nat.blt i 864 then as53 i else as54 i)))))) else (if Nat.blt i 1312 then (if Nat.blt i 1088 then (if Nat.blt i 976 then (if Nat.blt i 928 then (if Nat.blt i 896 then as55 i else (if Nat.blt i 912 then as56 i else as57 i)) else (if Nat.blt i 944 then as58 i else (if Nat.blt i 960 then as59 i else as60 i))) else (if Nat.blt i 1024 then (if Nat.blt i 992 then as61 i else (if Nat.blt i 1008 then as62 i else as63 i)) else (if Nat.blt i 1056 then (if Nat.blt i 1040 then as64 i else as65 i) else (if Nat.blt i 1072 then as66 i else as67 i)))) else (if Nat.blt i 1200 then (if Nat.blt i 1136 then (if Nat.blt i 1104 then as68 i else (if Nat.blt i 1120 then as69 i else as70 i)) else (if Nat.blt i 1168 then (if Nat.blt i 1152 then as71 i else as72 i) else (if Nat.blt i 1184 then as73 i else as74 i))) else (if Nat.blt i 1248 then (if Nat.blt i 1216 then as75 i else (if Nat.blt i 1232 then as76 i else as77 i)) else (if Nat.blt i 1280 then (if Nat.blt i 1264 then as78 i else as79 i) else (if Nat.blt i 1296 then as80 i else as81 i))))) else (if Nat.blt i 1536 then (if Nat.blt i 1424 then (if Nat.blt i 1360 then (if Nat.blt i 1328 then as82 i else (if Nat.blt i 1344 then as83 i else as84 i)) else (if Nat.blt i 1392 then (if Nat.blt i 1376 then as85 i else as86 i) else (if Nat.blt i 1408 then as87 i else as88 i))) else (if Nat.blt i 1472 then (if Nat.blt i 1440 then as89 i else (if Nat.blt i 1456 then as90 i else as91 i)) else (if Nat.blt i 1504 then (if Nat.blt i 1488 then as92 i else as93 i) else (if Nat.blt i 1520 then as94 i else as95 i)))) else (if Nat.blt i 1648 then (if Nat.blt i 1584 then (if Nat.blt i 1552 then as96 i else (if Nat.blt i 1568 then as97 i else as98 i)) else (if Nat.blt i 1616 then (if Nat.blt i 1600 then as99 i else as100 i) else (if Nat.blt i 1632 then as101 i else as102 i))) else (if Nat.blt i 1696 then (if Nat.blt i 1664 then as103 i else (if Nat.blt i 1680 then as104 i else as105 i)) else (if Nat.blt i 1728 then (if Nat.blt i 1712 then as106 i else as107 i) else (if Nat.blt i 1744 then as108 i else as109 i)))))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def compactAdvice (i tok : Nat) := (if Nat.blt i 880 then (if Nat.blt i 432 then (if Nat.blt i 208 then (if Nat.blt i 96 then (if Nat.blt i 48 then (if Nat.blt i 16 then ac0 i tok else (if Nat.blt i 32 then ac1 i tok else ac2 i tok)) else (if Nat.blt i 64 then ac3 i tok else (if Nat.blt i 80 then ac4 i tok else ac5 i tok))) else (if Nat.blt i 144 then (if Nat.blt i 112 then ac6 i tok else (if Nat.blt i 128 then ac7 i tok else ac8 i tok)) else (if Nat.blt i 176 then (if Nat.blt i 160 then ac9 i tok else ac10 i tok) else (if Nat.blt i 192 then ac11 i tok else ac12 i tok)))) else (if Nat.blt i 320 then (if Nat.blt i 256 then (if Nat.blt i 224 then ac13 i tok else (if Nat.blt i 240 then ac14 i tok else ac15 i tok)) else (if Nat.blt i 288 then (if Nat.blt i 272 then ac16 i tok else ac17 i tok) else (if Nat.blt i 304 then ac18 i tok else ac19 i tok))) else (if Nat.blt i 368 then (if Nat.blt i 336 then ac20 i tok else (if Nat.blt i 352 then ac21 i tok else ac22 i tok)) else (if Nat.blt i 400 then (if Nat.blt i 384 then ac23 i tok else ac24 i tok) else (if Nat.blt i 416 then ac25 i tok else ac26 i tok))))) else (if Nat.blt i 656 then (if Nat.blt i 544 then (if Nat.blt i 480 then (if Nat.blt i 448 then ac27 i tok else (if Nat.blt i 464 then ac28 i tok else ac29 i tok)) else (if Nat.blt i 512 then (if Nat.blt i 496 then ac30 i tok else ac31 i tok) else (if Nat.blt i 528 then ac32 i tok else ac33 i tok))) else (if Nat.blt i 592 then (if Nat.blt i 560 then ac34 i tok else (if Nat.blt i 576 then ac35 i tok else ac36 i tok)) else (if Nat.blt i 624 then (if Nat.blt i 608 then ac37 i tok else ac38 i tok) else (if Nat.blt i 640 then ac39 i tok else ac40 i tok)))) else (if Nat.blt i 768 then (if Nat.blt i 704 then (if Nat.blt i 672 then ac41 i tok else (if Nat.blt i 688 then ac42 i tok else ac43 i tok)) else (if Nat.blt i 736 then (if Nat.blt i 720 then ac44 i tok else ac45 i tok) else (if Nat.blt i 752 then ac46 i tok else ac47 i tok))) else (if Nat.blt i 816 then (if Nat.blt i 784 then ac48 i tok else (if Nat.blt i 800 then ac49 i tok else ac50 i tok)) else (if Nat.blt i 848 then (if Nat.blt i 832 then ac51 i tok else ac52 i tok) else (if Nat.blt i 864 then ac53 i tok else ac54 i tok)))))) else (if Nat.blt i 1312 then (if Nat.blt i 1088 then (if Nat.blt i 976 then (if Nat.blt i 928 then (if Nat.blt i 896 then ac55 i tok else (if Nat.blt i 912 then ac56 i tok else ac57 i tok)) else (if Nat.blt i 944 then ac58 i tok else (if Nat.blt i 960 then ac59 i tok else ac60 i tok))) else (if Nat.blt i 1024 then (if Nat.blt i 992 then ac61 i tok else (if Nat.blt i 1008 then ac62 i tok else ac63 i tok)) else (if Nat.blt i 1056 then (if Nat.blt i 1040 then ac64 i tok else ac65 i tok) else (if Nat.blt i 1072 then ac66 i tok else ac67 i tok)))) else (if Nat.blt i 1200 then (if Nat.blt i 1136 then (if Nat.blt i 1104 then ac68 i tok else (if Nat.blt i 1120 then ac69 i tok else ac70 i tok)) else (if Nat.blt i 1168 then (if Nat.blt i 1152 then ac71 i tok else ac72 i tok) else (if Nat.blt i 1184 then ac73 i tok else ac74 i tok))) else (if Nat.blt i 1248 then (if Nat.blt i 1216 then ac75 i tok else (if Nat.blt i 1232 then ac76 i tok else ac77 i tok)) else (if Nat.blt i 1280 then (if Nat.blt i 1264 then ac78 i tok else ac79 i tok) else (if Nat.blt i 1296 then ac80 i tok else ac81 i tok))))) else (if Nat.blt i 1536 then (if Nat.blt i 1424 then (if Nat.blt i 1360 then (if Nat.blt i 1328 then ac82 i tok else (if Nat.blt i 1344 then ac83 i tok else ac84 i tok)) else (if Nat.blt i 1392 then (if Nat.blt i 1376 then ac85 i tok else ac86 i tok) else (if Nat.blt i 1408 then ac87 i tok else ac88 i tok))) else (if Nat.blt i 1472 then (if Nat.blt i 1440 then ac89 i tok else (if Nat.blt i 1456 then ac90 i tok else ac91 i tok)) else (if Nat.blt i 1504 then (if Nat.blt i 1488 then ac92 i tok else ac93 i tok) else (if Nat.blt i 1520 then ac94 i tok else ac95 i tok)))) else (if Nat.blt i 1648 then (if Nat.blt i 1584 then (if Nat.blt i 1552 then ac96 i tok else (if Nat.blt i 1568 then ac97 i tok else ac98 i tok)) else (if Nat.blt i 1616 then (if Nat.blt i 1600 then ac99 i tok else ac100 i tok) else (if Nat.blt i 1632 then ac101 i tok else ac102 i tok))) else (if Nat.blt i 1696 then (if Nat.blt i 1664 then ac103 i tok else (if Nat.blt i 1680 then ac104 i tok else ac105 i tok)) else (if Nat.blt i 1728 then (if Nat.blt i 1712 then ac106 i tok else ac107 i tok) else (if Nat.blt i 1744 then ac108 i tok else ac109 i tok)))))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def compactLinks (i tok : Nat) : Option DagLink :=
  let c := compactAdvice i tok
  if c % 2=1 then some ((c/2) % 2048, c/4096) else none
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def compactHint (i tok : Nat) : Nat :=
  let c := compactAdvice i tok
  if c % 2=1 then 15 else if c/2<16 then c/2 else 16+hull (c/2-16)
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def compactCut := geometryOrMinor minors compactHint
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def compactCheck := scan (fullMask 25) T diagonal compactStates 1749 (dagMoves records) compactLinks compactCut

end Rep9102.Final9102
open WordEngine
namespace Rep9102.Fast
open Orbit Project Final9102

def forceN {α : Type} (w : Nat) (k : Nat → α) : α := Nat.rec (k 0) (fun v _ => k (v+1)) w
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
@[simp] theorem forceN_eq {α : Type} (w : Nat) (k : Nat → α) : forceN w k = k w := by cases w <;> rfl

def forceList (ws : List Nat) (k : List Nat → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun f => f [])
    (fun w _ rest f => forceN w (fun x => rest (fun tail => f (x::tail)))) ws) k
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
@[simp] theorem forceList_eq (ws : List Nat) (k : List Nat → Bool) : forceList ws k = k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceN w (fun x => forceList ws (fun tail => k (x::tail))) = _
    rw [forceN_eq,ih]

def tag (g : Nat) : List Nat → Nat → Nat
  | [],_ => 0
  | n::ns,w => (if w.testBit n then 0 else g &&& w) ||| (tag g ns w <<< 25)
def wanted (g : Nat) : List Nat → Nat
  | [] => 0
  | _::ns => g ||| (wanted g ns <<< 25)
def unionTags (t : Nat → Nat) : List Nat → Nat
  | [] => 0
  | w::ws => t w ||| unionTags t ws

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem pack_cons (g n : Nat) (ns ws : List Nat) :
    unionTags (tag g (n::ns)) ws = (g &&& coverAt n ws) ||| (unionTags (tag g ns) ws <<< 25) := by
  induction ws with
  | nil => simp [unionTags,coverAt]
  | cons w ws ih =>
    change tag g (n::ns) w ||| unionTags (tag g (n::ns)) ws =
      (g &&& (if w.testBit n then coverAt n ws else w ||| coverAt n ws)) ||| ((tag g ns w ||| unionTags (tag g ns) ws) <<< 25)
    rw [ih,Nat.shiftLeft_or_distrib,tag]
    cases w.testBit n <;> simp [Nat.and_or_distrib_left,Nat.or_comm,Nat.or_left_comm,Nat.or_assoc]

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem pack_good (g : Nat) (ns ws : List Nat)
    (h : ∀ n ∈ ns, g &&& coverAt n ws = g) : unionTags (tag g ns) ws = wanted g ns := by
  induction ns with
  | nil => induction ws <;> simp_all [tag,unionTags,wanted]
  | cons n ns ih => rw [pack_cons,h n (by simp),ih (fun j hj => h j (by simp [hj])),wanted]

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem unionBits (t : Nat → Nat) (ws : List Nat) (b : Nat) :
    (unionTags t ws).testBit b = true ↔ ∃ w ∈ ws, (t w).testBit b = true := by
  induction ws with
  | nil => simp [unionTags]
  | cons w ws ih => simp [unionTags,Nat.testBit_or,ih]

def without (x y : Nat) : List Nat → List Nat → Nat
  | w::ws,t::ts =>
    if w == x || w == y then without x y ws ts else t ||| without x y ws ts
  | _,_ => 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem without_eq (x y : Nat) (t : Nat → Nat) (ws : List Nat) :
    without x y ws (ws.map t) = unionTags t (ws.filter (fun w => w != x && w != y)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    by_cases a : w=x <;> by_cases b : w=y <;> simp [without,unionTags,a,b,ih]

def kept (ws : List Nat) (x y k : Nat) := keepWord (k.testBit 1) y (keepWord (k.testBit 0) x ws)
def combined (base tx ty tz k : Nat) :=
  base ||| (if k.testBit 0 then tx else 0) ||| (if k.testBit 1 then ty else 0) ||| tz

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem childTags (t : Nat → Nat) (ws : List Nat) (x y z k : Nat)
    (nd : ws.Nodup) (hx : x ∈ ws) (hy : y ∈ ws) (ne : x ≠ y) :
    unionTags t (insertWord z (kept ws x y k)) =
      combined (without x y ws (ws.map t)) (t x) (t y) (t z) k := by
  rw [without_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  simp only [combined,Nat.testBit_or,Bool.or_eq_true,unionBits,List.mem_filter,Bool.and_eq_true,
    bne_iff_ne,insertWordMem,kept,keepWord]
  cases k.testBit 0 <;> cases k.testBit 1 <;> simp only [Bool.false_eq_true,↓reduceIte,Nat.zero_testBit,
    nd.mem_erase_iff,(nd.erase x).mem_erase_iff] <;> grind

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem insertLength (z : Nat) (ws : List Nat) : (insertWord z ws).length = ws.length+1 := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change (if z ≤ w then z::w::ws else w::insertWord z ws).length = _
    split <;> simp [ih]

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block_of {lo n : Nat} {f : Nat → Bool}
    (all : ∀ j, lo ≤ j → j < lo+n → f j = true) : treeBlock lo n f = true := by
  induction n generalizing lo with
  | zero => rfl
  | succ n ih =>
    change (f lo && treeBlock (lo+1) n f) = true
    exact Bool.and_eq_true_iff.mpr ⟨all _ le_rfl (by omega),ih (fun j a b => all j (by omega) (by omega))⟩

def direct (m g : Nat) (ns : List Nat) (i : Nat) (s : RowState)
    (finish : Nat → RowState → Bool) : Bool :=
  let fuel := s.1
  forceList s.2.1 fun ws =>
    let n := ws.length
    dagStateOK m ws && decide (n ≤ 64) && !(ws.contains g) &&
    (fuel == 0 || forceN (wanted g ns) (fun full =>
      forceList (ws.map (tag g ns)) fun tags =>
      treeBlock 0 n fun a =>
      forceN (ws.getD a 0) fun x =>
      forceN (tags.getD a 0) fun tx =>
      treeBlock (a+1) (n-(a+1)) fun b =>
      forceN (ws.getD b 0) fun y =>
      forceN (tags.getD b 0) fun ty =>
      forceN (without x y ws tags) fun base =>
      treeBlock 0 2 fun op =>
      forceN (if op == 0 then x &&& y else x ||| y) fun z =>
      z == 0 || z == m || ws.contains z ||
      forceN (tag g ns z) (fun tz =>
      treeBlock 0 4 fun k =>
        let rest := kept ws x y k
        decide (fuel-1+1 < rest.length+1) ||
        (combined base tx ty tz k != full) ||
        forceList (insertWord z rest) (fun bank => finish (gateToken a b op k) (fuel-1,bank,(z,x,y)::s.2.2)))))

end Rep9102.Fast

namespace Rep9102.Fast
open Orbit Project Final9102

def linkCode (c : Nat) : Option DagLink := if c % 2=1 then some ((c/2) % 2048,c/4096) else none
def hintCode (hullAt : Nat → Nat) (c : Nat) := if c % 2=1 then 15 else if c/2<16 then c/2 else 16+hullAt (c/2-16)

def dispatch (bank : Table) (count : Nat) (moves : Array WordMove) (ms : Array Minor)
    (hullAt : Nat → Nat) (ad : Nat → Nat → Nat) (i tok : Nat) (s : RowState) :=
  forceN (ad i tok) fun c =>
    if c % 2=1 then dagRef count bank moves (fun _ _ => linkCode c) i tok s
    else geometryOrMinor ms (fun _ _ => hintCode hullAt c) i tok s

def fastCheckWith (bank : Table) (count : Nat) (moves : Array WordMove) (ms : Array Minor)
    (hullAt : Nat → Nat) (ad : Nat → Nat → Nat) (i : Nat) :=
  match bank i with
  | none => false
  | some s => direct (fullMask 25) T diagonal i s (dispatch bank count moves ms hullAt ad i)


end Rep9102.Fast
open WordEngine
namespace Rep9102.Fast
open Orbit Project Final9102

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem getTag (f : Nat → Nat) (ws : List Nat) (a : Nat) (ha : a < ws.length) :
    (ws.map f).getD a 0 = f (ws.getD a 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using ha),List.getD_eq_getElem _ _ ha,List.getElem_map]

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem direct_pass {m g i : Nat} {ns : List Nat} {s : RowState} {finish : Nat → RowState → Bool}
    (ok : direct m g ns i s finish = true)
    {bank : Table} {count : Nat} {moves : Array WordMove} {lk : DagLinks} {cut : EdgeCut}
    (sound : ∀ tok c, finish tok c = true →
      (cut i tok c || dagRef count bank moves lk i tok c) = true)
    {a b op k : Nat} (hab : a<b) (hb : b<s.2.1.length) (ho : op<2) (hk : k<4) :
    pass m g ns bank count moves lk cut i s a b op k = true := by
  obtain ⟨fuel,ws,history⟩ := s
  change b < ws.length at hb
  simp only [direct,forceList_eq,forceN_eq,Bool.and_eq_true,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨stateOK,width⟩,_⟩,all⟩ := ok
  change ws.length ≤ 64 at width
  have nd := (dagStateOKSpec stateOK).1
  have ha := hab.trans hb
  let x := ws.getD a 0
  let y := ws.getD b 0
  let z := if op == 0 then x &&& y else x ||| y
  let rest := kept ws x y k
  have fields := gateTokenFields (a:=a) (b:=b) (op:=op) (keep:=k) (by omega) (by omega) hk
  obtain ⟨kE,oE,aE,bE⟩ := fields
  have nop : op ≠ 2 := by omega
  have output : (if op == 0 then x &&& y else if op == 1 then x ||| y else m ^^^ x) = z := by
    rcases (show op=0 ∨ op=1 by omega) with rfl|rfl <;> rfl
  have cell : childState m (gateToken a b op k) (fuel,ws,history) =
      (if fuel == 0 then none else if z == 0 || z == m || ws.contains z then none else
        some (fuel-1,insertWord z rest,(z,x,y)::history)) := by
    simp only [childState,kE,oE,aE,bE,show ¬ b≥ws.length by omega,decide_false,
      show ¬ a≥b by omega,nop,beq_eq_false_iff_ne.mpr nop,Bool.false_eq_true,
      ↓reduceIte,Bool.or_false,Bool.false_or]
    change (if fuel == 0 then none else
      if _ then none else some _) = _
    simp only [← output,z,x,y,rest,kept,keepWord,nop, Bool.false_or,beq_eq_false_iff_ne.mpr nop]
  rw [pass,cell]
  by_cases dead : fuel = 0
  · simp [dead]
  rw [if_neg (show ¬ (fuel == 0) = true by simpa using dead)]
  by_cases stale : (z == 0 || z == m || ws.contains z) = true
  · rw [if_pos stale]
  rw [if_neg stale]
  have all' := (Bool.or_eq_true_iff.mp all).resolve_left (by simpa using dead)
  have A := treeBlock_at all' (i:=a) (by omega) (by simpa using ha)
  have B := treeBlock_at A (i:=b) (by omega) (by omega)
  have O := treeBlock_at B (i:=op) (by omega) (by simpa using ho)
  change ((z == 0 || z == m || ws.contains z) || treeBlock 0 4 _) = true at O
  have K := treeBlock_at ((Bool.or_eq_true_iff.mp O).resolve_left stale) (i:=k) (by omega) (by simpa using hk)
  rw [getTag _ _ _ ha,getTag _ _ _ hb] at K
  change (decide (fuel-1+1 < rest.length+1) ||
    (combined (without x y ws (ws.map (tag g ns))) (tag g ns x) (tag g ns y) (tag g ns z) k != wanted g ns)
    || finish (gateToken a b op k) (fuel-1,insertWord z rest,(z,x,y)::history)) = true at K
  let c : RowState := (fuel-1,insertWord z rest,(z,x,y)::history)
  change (basicCut g ns c || cut i _ c || dagRef count bank moves lk i _ c) = true
  by_cases closed : basicCut g ns c = true
  · simp [closed]
  have openC : basicCut g ns c = false := Bool.eq_false_iff.mpr closed
  simp only [basicCut,Bool.or_eq_false_iff,decide_eq_false_iff_not,List.any_eq_false,bne_iff_ne,
    Bool.not_eq_true',bne_eq_false_iff_eq] at openC
  have len : ¬fuel-1+1 < rest.length+1 := by
    have l := openC.1
    change ¬fuel-1+1 < (insertWord z rest).length at l
    rwa [insertLength] at l
  have pack := pack_good g ns c.2.1 (by intro n hn; simpa using openC.2 n hn)
  have memx : x ∈ ws := by dsimp [x]; rw [List.getD_eq_getElem _ _ ha];exact List.getElem_mem _
  have memy : y ∈ ws := by dsimp [y]; rw [List.getD_eq_getElem _ _ hb];exact List.getElem_mem _
  have ne : x ≠ y := by
    unfold x y
    rw [List.getD_eq_getElem _ _ ha,List.getD_eq_getElem _ _ hb]
    intro eq
    have eqidx := nd.getElem_inj.mp eq
    omega
  change unionTags (tag g ns) (insertWord z (kept ws x y k)) = _ at pack
  rw [childTags _ ws x y z k nd memx memy ne] at pack
  have good := sound _ c (by simpa [len,pack] using K)
  simpa [Bool.eq_false_iff.mpr closed] using good

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem fastCheck_sound {bank : Table} {count : Nat} {moves : Array WordMove} {ms : Array Minor}
    {hullAt : Nat → Nat} {ad : Nat → Nat → Nat} {i : Nat}
    (ok : fastCheckWith bank count moves ms hullAt ad i = true) :
    scan (fullMask 25) T diagonal bank count moves (fun j t => linkCode (ad j t))
      (geometryOrMinor ms (fun j t => hintCode hullAt (ad j t))) i = true := by
  cases hr : bank i with
  | none => simp [fastCheckWith,hr] at ok
  | some s =>
    simp only [fastCheckWith,hr] at ok
    have top := ok
    simp only [direct,forceList_eq,forceN_eq,Bool.and_eq_true] at top
    simp only [scan,hr,Bool.and_eq_true]
    refine ⟨top.1,block_of fun a _ ha => block_of fun b hb hb' => block_of fun op _ hop => block_of fun k _ hk => ?_⟩
    apply direct_pass ok _ (by omega) (by omega) (by omega) (by omega)
    intro tok c hit
    simp only [dispatch,forceN_eq] at hit
    split at hit
    · apply Bool.or_eq_true_iff.mpr (Or.inr ?_)
      exact hit
    · apply Bool.or_eq_true_iff.mpr (Or.inl ?_)
      exact hit

end Rep9102.Fast
open WordEngine
namespace Rep9102.Fast.Packed
open Orbit Project Final9102
abbrev SlotTable := Nat × Nat × Nat

def entry (q : Minor) (t : SlotTable) (j : Nat) : Nat :=
  forceN (unpack t.2.2 7 j) fun code =>
    if code = 0 then 0 else
      4 * ((unpack 0x3ff0001f84210fa10847c84213e21085f08421f83e007c00f83e0003f8c6318a5294a4a5294a318c630fc210843f084210fc210843f0000006318c6294a529294a528fa108423e842108fa108423e800000318c6314a52949f2108427c842109f2108427c800000318c6317c421085f1084217c421085f10000007e108421f8421087e108421f84000001ff8000f83e007c00f8200000080000020000008000002000000ffc0007c1f00200000080000020000008000002000000ffc00040000010000004000001000000400000100000040000010000004000001084210c2108410842104210841084217c000001f0000007c000001f0000007ffffffe000000 25 (code-1)) &&& q.mask) + (if code ≤ 12 then 1 else 2)

def index (t : SlotTable) (v : Nat) := (v ^^^ (v >>> t.2.1)) % t.1

def validSlot (q : Minor) (e : Nat) :=
  let v := e/4
  if e % 4=1 then availableB q.mask q.raw v
  else if e % 4=2 then !(availableB q.mask q.raw v) && oneAO q.raw v else true

def validSlots (q : Minor) (t : SlotTable) :=
  t.1 != 0 && treeBlock 0 t.1 (fun j => validSlot q (entry q t j))

def tagLookup (q : Minor) (t : SlotTable) (v : Nat) := forceN (entry q t (index t v)) fun e =>
  if e/4 == v then e % 4 else 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem tagSpec (q : Minor) (t : SlotTable) (valid : validSlots q t = true) (v : Word) :
    (tagLookup q t v = 1 → availableB q.mask q.raw v = true) ∧
    (tagLookup q t v = 2 → availableB q.mask q.raw v = false ∧ oneAO q.raw v = true) := by
  obtain ⟨pos,cells⟩ := Bool.and_eq_true_iff.mp valid
  have ne : t.1 ≠ 0 := by simpa using pos
  have cell := treeBlock_at cells (i:=index t v) (Nat.zero_le _) (by simpa [index] using Nat.mod_lt (v ^^^ (v >>> t.2.1)) (Nat.pos_of_ne_zero ne))
  let e := entry q t (index t v)
  change validSlot q e = true at cell
  simp only [tagLookup,forceN_eq]
  change ((if e/4 == v then e % 4 else 0) = 1 → _) ∧ ((if e/4 == v then e % 4 else 0) = 2 → _)
  by_cases hv : e/4=v
  · simp only [hv,beq_self_eq_true,↓reduceIte]
    constructor
    · intro h; simpa [validSlot,h,hv] using cell
    · intro h; simpa [validSlot,h,hv] using cell
  · simp [hv]

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem oneWeaken (base extra : List Word) (v : Word) (h : oneAO base v = true) :
    oneAO (extra++base) v = true := by
  obtain ⟨a,ha,y⟩ := List.any_eq_true.mp h
  obtain ⟨b,hb,test⟩ := List.any_eq_true.mp y
  exact List.any_eq_true.mpr ⟨a,List.mem_append_right _ ha,List.any_eq_true.mpr
    ⟨b,List.mem_append_right _ hb,test⟩⟩

def fastPrep (q : Minor) (t : SlotTable) (extra : List Word) : List Word → Option (List Word)
  | [] => some []
  | w::ws => forceN (tagLookup q t w) fun kind =>
    if (kind == 1) || extra.contains w || ((kind != 2) && availableB q.mask q.raw w) then fastPrep q t extra ws
    else if kind == 2 || oneAO (extra++q.raw) w then (fastPrep q t (w::extra) ws).map (w::·)
    else none

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem fastPrep_eq (q : Minor) (t : SlotTable) (valid : validSlots q t = true) (extra ws : List Word) :
    fastPrep q t extra ws = cheapPrep q.mask (extra++q.raw) ws := by
  induction ws generalizing extra with
  | nil => rfl
  | cons w ws ih =>
    obtain ⟨free,one⟩ := tagSpec q t valid w
    let k := tagLookup q t w
    have avail : ((k == 1) || extra.contains w || ((k != 2) && availableB q.mask q.raw w)) =
        availableB q.mask (extra++q.raw) w := by
      have ext : availableB q.mask (extra++q.raw) w = (extra.contains w || availableB q.mask q.raw w) := by
        simp [availableB,List.contains_append,Bool.or_comm,Bool.or_left_comm,Bool.or_assoc]
      rw [ext]
      by_cases h : k=1
      · simp [h,free h]
      by_cases h' : k=2
      · simp [h,h',(one h').1]
      · simp [beq_eq_false_iff_ne.mpr h,show (k != 2) = true by simpa using h']
    have gate : ((k == 2) || oneAO (extra++q.raw) w) = oneAO (extra++q.raw) w := by
      by_cases h : k=2
      · simp [h,oneWeaken _ _ _ (one h).2]
      · simp [h]
    simp only [fastPrep,cheapPrep,forceN_eq]
    change (if _ then _ else if _ then _ else _) = _
    rw [show tagLookup q t w = k from rfl,avail,gate,ih extra,ih (w::extra)]
    rfl

def usingCache (q : Minor) (t : SlotTable) (fuel : Nat) (ws : List Word) : Bool :=
  match fastPrep q t [] (ws.map (· &&& q.mask)) with
  | none => false
  | some adds => decide (adds.length+fuel < q.low+flatCount q.mask ws)

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem usingCache_eq (q : Minor) (t : SlotTable) (h : validSlots q t = true) (fuel : Nat) (ws : List Word) :
    usingCache q t fuel ws = cheapCut q.mask q.low fuel q.raw ws := by
  simp [usingCache,cheapCut,fastPrep_eq q t h]

end Rep9102.Fast.Packed
open WordEngine

namespace Rep9102.Fast.Packed

open Orbit Project Final9102



def cache0 : SlotTable := (281,5,0x74080000000000000031500000000001a80000000a00000002c000000000000010800062000000000000000000016f400000000000000c000000000000000000a0000000000001240000001c00000003000000048a0170000d000c3a0003b00000250000000000004300019800000b800000ca07c980050000000000001400000000024000000000000000000118000000000000000006c0000054020000001e2d0000000000002b00000000000000000001f0000048004c000100000000bc000000000000000000110000000000000a401c00fc900060002300000000078000006db9148880000000d10420238f0038681)
def cache1 : SlotTable := (319,18,0x37000000000000000001f800000000000000000000005e000000000000900004f9c0001a5a0000000000000000015002000000000400002347000000000000009a000000000000000170054000000000db900000000000000000000000000000e780000074b0000004800000033000000200024800128051000000001100000a00000000000000000008601400000000000000000000000006610000a4014180003800f8000002c000380208000000320000000000000000000340001d800000000000003500e8000000000000000000000000305c01300c4000140000000b000000000000000000992c0000000000080001206000004f4000000000000000011000000000000100001e0f0038681)
def cache2 : SlotTable := (305,15,0xdc041000004a000000000000007e0000000000205a940000000000000001501143805c0218000024000000000002000000000004200000000000000000000000000000000000000402c00000000000000cc0000002300000030000000000000000000004b00ac000120000000000297600000609113e00000000139400014003900000000002900007c0000001b140000000000003418000000000000920001700000380000000000000000000000002100000000000000000000200002c0320001e800000013000003a0000000000003100026809e000000000000a20052c0000012060010000000000000000009c011000000000011908e0000f0038681)
def cache3 : SlotTable := (333,5,0x33000060000026000080400000000000018800001780420048000900000001bba00000000001c0000000000000000000110000005510cc1b007a01f008a000000001f80012803c0070000000000000020000000000000001a000000000000420e00000000118000000000000580000000000023000000000000238000b0000000000000000006a024000148000000000000000003e0004100000004c0004f0000000000248000000000000e800000000000000036000000134000006400000000000000000001402b0000000000138000000000000100000000000e680000000000000000000000000022000000c000000000000000000000000000000640150000000000600000000000000a0000000271100016800000010000000f0038681)
def cache4 : SlotTable := (307,8,0x100011000000000000000000000000000000000000027000004c00000000e0000000000000000ad1000000000000290a01600006c0000000000000000000003000000000000000000000000065a8000000002c0000000000000000000000000000000219e0000064023000000e00000000000000000001300000000000c40341800000000000000000000000000008c000000000056f4f1400000000000d4779040005c000000000050300000000bc00000d8000008000000000000000000000000000000000011dc300011000000013000293e7200000000000000000003e9400001380009200000012d8128a00000002c0000001500800000000005000121c000025f8010de681)
def cache5 : SlotTable := (350,8,0x7c0000080000000188000840000000018000003800000000088035780000096000000065200a0000008000000000000000180000000000000000000000000000000000000000d800000680000000a80000000000000000000000760000000bc000500000000006006601580009c0006800009000003e000000000000000000000000000095380000000032000000000000070000000006c0000000000000000000000000001e800000000000000000000170000000000000000000000800014000004c000000000000000000000000000800016800002680000000000b0000000003a3c0000014000007e00000000000000a4000013d5130000000000003000000000000000000000000000006e000000148012000000000e40000000005000800006017263a00010000000f4a38681)
def cache6 : SlotTable := (344,19,0xb80000000018000000000000190091b0000000000000000000001a00000000000300013000000000000000034000000000000000000000000000000021800000000000003200000000000002000000000000000000000013c00000000000000000a20000001180000000035000001c0000000000001e6e000000000000000140052000009abd88000000003a00000180002000000000000016000000000000050000000000250000000000000000601e4000000000000002c00000148f2c00000013000108000000058000000000000000a40000000000000000000000001f00000000000000000000000000002e00000009c01300000000002200000000000ac00466000000002280000000000e119200000095a00041060004e0000011002000000012a1000000f5438681)
def cache7 : SlotTable := (339,17,0xec000000000050f0000011c000000060000000000090000a20000000000001000000000002d00000000c000000001880000000000000000000000000000000000000000000000001500000490000000a00004e0002580000000001040000000000000001f0000000000001d0000bba000000000000000000000008c5000000000000028000100000e0000000000000000b000000000000002a7d28000000000000000000000045000000000c13005e94029a4000440000000000000000000000001c8000b001c000104d0000000000000044000000000000000000000b8000000000000000000000000000004301080130000000000139b160000000f558000000000000000000231e00026120001f800600000000000000080110064000000001030000000038681)
def cache8 : SlotTable := (347,9,0x973d48000000240000018000000000c802200000000000000011a20000000000c01c8000011800000000000003c0000000340000000000000000000000000000000005600000825c0000a000154e013000000000000003d000001d000000008000000002280360000000cc0007c00000007c48000000000000000000288000000000000000000000000001000000000000000000000000108028005804300840001600000694000000000000000000013000c000250000000000000014000000000000000000000a40000000d40073800000000000000000000000000000000000000003c0000014000007602480000003a000000000000000000000000000000000004a00000000004d00000400000012000018000024000000000000001100000006c0001000dc00f5400681)
def cache9 : SlotTable := (187,9,0x640410000d00000000090bc034360000000000000144002011c000840000038027004c01e002c785804a000000001b1400000007600000000002c00000050000022a00000000000000001700000000000e40529475f80973c000000000000000000110a8a0000013000120000e839700840000114000980193300024bd00016800025a800c0d180401004300018400000411000000000e0010000000f0038001)
def cache10 : SlotTable := (166,13,0x2e00000000000000000000001b8400000004c0002000954000001f801801794000003600e000000f8000008401a00000000000000007400000000080001680005428000000007801480800000000000003c7c0000000013008988036e80190018500560800076d12000000000000198000000120001e98002402a0000000000000006b800000c0010000000f6a38681)
def cache11 : SlotTable := (241,10,0x530400000000000000000000002e0000000000220000000003c000000000000000004f001400000d000000000000000000000003200000003a0000000000000000000000004c000000000a8000000800000000000000000000000000000000000014000000000640000000000000000000bc000000288000e00009000000012800000b00006601bcb0000000000000000000000e0000900023930000c0000000005a00000620004600013809a00000510801700200121658000000000006d400000006119d0c21c0000000000000f3438681)
def cache12 : SlotTable := (191,8,0xe40000002080000000000a0000a400000000010000f9100000000000000000001e8c00ac00000b00000000000011639646b40000000017000000000024809c00000012c000000040008000000000000a200000000002000021000000000002c03b00000004e01200005401300c6680600003a0000000a002180000001f001800014000008d28012000000006a4000000000000000114afc00000b80100e000000038681)
def cache13 : SlotTable := (213,7,0xa8009010800014000000101b80000058000d8000000000092000187a0000000e558001300000000000006c0000000045000000000024000000023000002600000008201e00000010000000000000e800000000000000038000050000035a20000000000000000044a13400064000000000d0000012004f280220000000000002800000000000000000000c000000600003807c00000000002100000460000180000000000000330000011000004f7400f90a40000f0000681)
def cache14 : SlotTable := (197,2,0x193400d800000e006c0000098000000000000000000000027800001045000001400b000000000000001300000003c0002200008c0004aed080000000000d40002b38000640000000b805100000050cfc00096000000000f490000000000000000000000105a1300000000e0000004f5100014000b0000000000000000000005e00b4000000008601cd20000000000000a00000040000038011c00000000099000000000000800018000000001)
def cacheOf : Nat → SlotTable
  | 0 => cache0
  | 1 => cache1
  | 2 => cache2
  | 3 => cache3
  | 4 => cache4
  | 5 => cache5
  | 6 => cache6
  | 7 => cache7
  | 8 => cache8
  | 9 => cache9
  | 10 => cache10
  | 11 => cache11
  | 12 => cache12
  | 13 => cache13
  | 14 => cache14
  | _ => (1,0,0)

def cachedMinor (idx : Nat) (s : RowState) :=
  match minors[idx]? with
  | none => false
  | some q => usingCache q (cacheOf idx) s.1 s.2.1

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cachesValid : treeBlock 0 minors.size (fun i => (minors[i]?).all fun q => validSlots q (cacheOf i)) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cachedMinor_eq (idx : Nat) (s : RowState) : cachedMinor idx s =
    (match minors[idx]? with | none => false | some q => cheapCut q.mask q.low s.1 q.raw s.2.1) := by
  unfold cachedMinor
  cases h : minors[idx]? with
  | none => rfl
  | some q =>
    have lt : idx < minors.size := (Array.getElem?_eq_some_iff.mp h).1
    have ok := treeBlock_at cachesValid (i:=idx) (Nat.zero_le idx) (by simpa using lt)
    simp [h] at ok
    exact usingCache_eq q _ ok _ _


end Rep9102.Fast.Packed
open WordEngine
namespace Rep9102.Fast.Packed
open Orbit Project Final9102

def cachedDispatch (bank : Table) (ad : Nat → Nat → Nat) (i tok : Nat) (s : RowState) :=
  forceN (ad i tok) fun c =>
    if c % 2=1 then dagRef 1749 bank (dagMoves records) (fun _ _ => linkCode c) i tok s
    else if c/2 < 16 then cachedMinor (c/2) s
    else Geometry.rectangleReject T s (hull (c/2-16))

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cachedDispatch_eq (bank : Table) (ad : Nat → Nat → Nat) (i tok : Nat) (s : RowState) :
    cachedDispatch bank ad i tok s = dispatch bank 1749 (dagMoves records) minors hull ad i tok s := by
  simp only [cachedDispatch,dispatch,forceN_eq]
  split
  · rfl
  · rename_i even
    split
    · rename_i small
      simp [geometryOrMinor,hintCode,even,small,cachedMinor_eq,bankCut]
    · rename_i big
      simp [geometryOrMinor,hintCode,even,big]

def cachedScan (bank : Table) (ad : Nat → Nat → Nat) (i : Nat) :=
  match bank i with
  | none => false
  | some s => direct (fullMask 25) T diagonal i s (cachedDispatch bank ad i)

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cachedScan_eq (bank : Table) (ad : Nat → Nat → Nat) (i : Nat) :
    cachedScan bank ad i = fastCheckWith bank 1749 (dagMoves records) minors hull ad i := by
  simp only [cachedScan,fastCheckWith]
  cases bank i with
  | none => rfl
  | some s => exact congrArg (direct (fullMask 25) T diagonal i s) (funext fun tok => funext fun c => cachedDispatch_eq bank ad i tok c)

def cachedCompact := cachedScan compactStates compactAdvice

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem compact_from_cached {start count} (h : treeBlock start count cachedCompact = true) :
    treeBlock start count compactCheck = true := by
  apply block_of
  intro i lo hi
  have v := treeBlock_at h lo hi
  rw [cachedCompact,cachedScan_eq] at v
  exact fastCheck_sound v

end Rep9102.Fast.Packed
namespace Rep9102.Final9102
open Orbit Project
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem valid : ∀ q ∈ minors, Minor.Valid T q := validCuts masks (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block0 : treeBlock 0 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block12 : treeBlock 12 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block24 : treeBlock 24 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block36 : treeBlock 36 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block48 : treeBlock 48 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block60 : treeBlock 60 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block72 : treeBlock 72 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block84 : treeBlock 84 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block96 : treeBlock 96 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block108 : treeBlock 108 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block120 : treeBlock 120 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block132 : treeBlock 132 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block144 : treeBlock 144 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block156 : treeBlock 156 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block168 : treeBlock 168 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block180 : treeBlock 180 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block192 : treeBlock 192 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block204 : treeBlock 204 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block216 : treeBlock 216 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block228 : treeBlock 228 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block240 : treeBlock 240 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block252 : treeBlock 252 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block264 : treeBlock 264 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block276 : treeBlock 276 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block288 : treeBlock 288 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block300 : treeBlock 300 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block312 : treeBlock 312 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block324 : treeBlock 324 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block336 : treeBlock 336 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block348 : treeBlock 348 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block360 : treeBlock 360 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block372 : treeBlock 372 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block384 : treeBlock 384 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block396 : treeBlock 396 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block408 : treeBlock 408 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block420 : treeBlock 420 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block432 : treeBlock 432 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block444 : treeBlock 444 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block456 : treeBlock 456 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block468 : treeBlock 468 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block480 : treeBlock 480 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block492 : treeBlock 492 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block504 : treeBlock 504 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block516 : treeBlock 516 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block528 : treeBlock 528 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block540 : treeBlock 540 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block552 : treeBlock 552 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block564 : treeBlock 564 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block576 : treeBlock 576 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block588 : treeBlock 588 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block600 : treeBlock 600 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block612 : treeBlock 612 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block624 : treeBlock 624 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block636 : treeBlock 636 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block648 : treeBlock 648 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block660 : treeBlock 660 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block672 : treeBlock 672 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block684 : treeBlock 684 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block696 : treeBlock 696 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block708 : treeBlock 708 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block720 : treeBlock 720 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block732 : treeBlock 732 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block744 : treeBlock 744 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block756 : treeBlock 756 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block768 : treeBlock 768 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block780 : treeBlock 780 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block792 : treeBlock 792 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block804 : treeBlock 804 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block816 : treeBlock 816 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block828 : treeBlock 828 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block840 : treeBlock 840 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block852 : treeBlock 852 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block864 : treeBlock 864 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block876 : treeBlock 876 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block888 : treeBlock 888 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block900 : treeBlock 900 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block912 : treeBlock 912 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block924 : treeBlock 924 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block936 : treeBlock 936 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block948 : treeBlock 948 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block960 : treeBlock 960 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block972 : treeBlock 972 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block984 : treeBlock 984 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block996 : treeBlock 996 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1008 : treeBlock 1008 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1020 : treeBlock 1020 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1032 : treeBlock 1032 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1044 : treeBlock 1044 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1056 : treeBlock 1056 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1068 : treeBlock 1068 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1080 : treeBlock 1080 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1092 : treeBlock 1092 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1104 : treeBlock 1104 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1116 : treeBlock 1116 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1128 : treeBlock 1128 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1140 : treeBlock 1140 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1152 : treeBlock 1152 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1164 : treeBlock 1164 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1176 : treeBlock 1176 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1188 : treeBlock 1188 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1200 : treeBlock 1200 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1212 : treeBlock 1212 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1224 : treeBlock 1224 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1236 : treeBlock 1236 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1248 : treeBlock 1248 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1260 : treeBlock 1260 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1272 : treeBlock 1272 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1284 : treeBlock 1284 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1296 : treeBlock 1296 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1308 : treeBlock 1308 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1320 : treeBlock 1320 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1332 : treeBlock 1332 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1344 : treeBlock 1344 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1356 : treeBlock 1356 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1368 : treeBlock 1368 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1380 : treeBlock 1380 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1392 : treeBlock 1392 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1404 : treeBlock 1404 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1416 : treeBlock 1416 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1428 : treeBlock 1428 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1440 : treeBlock 1440 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1452 : treeBlock 1452 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1464 : treeBlock 1464 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1476 : treeBlock 1476 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1488 : treeBlock 1488 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1500 : treeBlock 1500 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1512 : treeBlock 1512 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1524 : treeBlock 1524 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1536 : treeBlock 1536 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1548 : treeBlock 1548 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1560 : treeBlock 1560 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1572 : treeBlock 1572 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1584 : treeBlock 1584 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1596 : treeBlock 1596 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1608 : treeBlock 1608 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1620 : treeBlock 1620 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1632 : treeBlock 1632 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1644 : treeBlock 1644 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1656 : treeBlock 1656 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1668 : treeBlock 1668 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1680 : treeBlock 1680 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1692 : treeBlock 1692 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1704 : treeBlock 1704 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1716 : treeBlock 1716 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1728 : treeBlock 1728 12 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block1740 : treeBlock 1740 9 Fast.Packed.cachedCompact = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem scanned : treeBlock 0 1749 Fast.Packed.cachedCompact = true := (treeBlock_merge (left := 876) (right := 873) (treeBlock_merge (left := 432) (right := 444) (treeBlock_merge (left := 216) (right := 216) (treeBlock_merge (left := 108) (right := 108) (treeBlock_merge (left := 48) (right := 60) (treeBlock_merge (left := 24) (right := 24) (treeBlock_merge (left := 12) (right := 12) block0 block12) (treeBlock_merge (left := 12) (right := 12) block24 block36)) (treeBlock_merge (left := 24) (right := 36) (treeBlock_merge (left := 12) (right := 12) block48 block60) (treeBlock_merge (left := 12) (right := 24) block72 (treeBlock_merge (left := 12) (right := 12) block84 block96)))) (treeBlock_merge (left := 48) (right := 60) (treeBlock_merge (left := 24) (right := 24) (treeBlock_merge (left := 12) (right := 12) block108 block120) (treeBlock_merge (left := 12) (right := 12) block132 block144)) (treeBlock_merge (left := 24) (right := 36) (treeBlock_merge (left := 12) (right := 12) block156 block168) (treeBlock_merge (left := 12) (right := 24) block180 (treeBlock_merge (left := 12) (right := 12) block192 block204))))) (treeBlock_merge (left := 108) (right := 108) (treeBlock_merge (left := 48) (right := 60) (treeBlock_merge (left := 24) (right := 24) (treeBlock_merge (left := 12) (right := 12) block216 block228) (treeBlock_merge (left := 12) (right := 12) block240 block252)) (treeBlock_merge (left := 24) (right := 36) (treeBlock_merge (left := 12) (right := 12) block264 block276) (treeBlock_merge (left := 12) (right := 24) block288 (treeBlock_merge (left := 12) (right := 12) block300 block312)))) (treeBlock_merge (left := 48) (right := 60) (treeBlock_merge (left := 24) (right := 24) (treeBlock_merge (left := 12) (right := 12) block324 block336) (treeBlock_merge (left := 12) (right := 12) block348 block360)) (treeBlock_merge (left := 24) (right := 36) (treeBlock_merge (left := 12) (right := 12) block372 block384) (treeBlock_merge (left := 12) (right := 24) block396 (treeBlock_merge (left := 12) (right := 12) block408 block420)))))) (treeBlock_merge (left := 216) (right := 228) (treeBlock_merge (left := 108) (right := 108) (treeBlock_merge (left := 48) (right := 60) (treeBlock_merge (left := 24) (right := 24) (treeBlock_merge (left := 12) (right := 12) block432 block444) (treeBlock_merge (left := 12) (right := 12) block456 block468)) (treeBlock_merge (left := 24) (right := 36) (treeBlock_merge (left := 12) (right := 12) block480 block492) (treeBlock_merge (left := 12) (right := 24) block504 (treeBlock_merge (left := 12) (right := 12) block516 block528)))) (treeBlock_merge (left := 48) (right := 60) (treeBlock_merge (left := 24) (right := 24) (treeBlock_merge (left := 12) (right := 12) block540 block552) (treeBlock_merge (left := 12) (right := 12) block564 block576)) (treeBlock_merge (left := 24) (right := 36) (treeBlock_merge (left := 12) (right := 12) block588 block600) (treeBlock_merge (left := 12) (right := 24) block612 (treeBlock_merge (left := 12) (right := 12) block624 block636))))) (treeBlock_merge (left := 108) (right := 120) (treeBlock_merge (left := 48) (right := 60) (treeBlock_merge (left := 24) (right := 24) (treeBlock_merge (left := 12) (right := 12) block648 block660) (treeBlock_merge (left := 12) (right := 12) block672 block684)) (treeBlock_merge (left := 24) (right := 36) (treeBlock_merge (left := 12) (right := 12) block696 block708) (treeBlock_merge (left := 12) (right := 24) block720 (treeBlock_merge (left := 12) (right := 12) block732 block744)))) (treeBlock_merge (left := 60) (right := 60) (treeBlock_merge (left := 24) (right := 36) (treeBlock_merge (left := 12) (right := 12) block756 block768) (treeBlock_merge (left := 12) (right := 24) block780 (treeBlock_merge (left := 12) (right := 12) block792 block804))) (treeBlock_merge (left := 24) (right := 36) (treeBlock_merge (left := 12) (right := 12) block816 block828) (treeBlock_merge (left := 12) (right := 24) block840 (treeBlock_merge (left := 12) (right := 12) block852 block864))))))) (treeBlock_merge (left := 432) (right := 441) (treeBlock_merge (left := 216) (right := 216) (treeBlock_merge (left := 108) (right := 108) (treeBlock_merge (left := 48) (right := 60) (treeBlock_merge (left := 24) (right := 24) (treeBlock_merge (left := 12) (right := 12) block876 block888) (treeBlock_merge (left := 12) (right := 12) block900 block912)) (treeBlock_merge (left := 24) (right := 36) (treeBlock_merge (left := 12) (right := 12) block924 block936) (treeBlock_merge (left := 12) (right := 24) block948 (treeBlock_merge (left := 12) (right := 12) block960 block972)))) (treeBlock_merge (left := 48) (right := 60) (treeBlock_merge (left := 24) (right := 24) (treeBlock_merge (left := 12) (right := 12) block984 block996) (treeBlock_merge (left := 12) (right := 12) block1008 block1020)) (treeBlock_merge (left := 24) (right := 36) (treeBlock_merge (left := 12) (right := 12) block1032 block1044) (treeBlock_merge (left := 12) (right := 24) block1056 (treeBlock_merge (left := 12) (right := 12) block1068 block1080))))) (treeBlock_merge (left := 108) (right := 108) (treeBlock_merge (left := 48) (right := 60) (treeBlock_merge (left := 24) (right := 24) (treeBlock_merge (left := 12) (right := 12) block1092 block1104) (treeBlock_merge (left := 12) (right := 12) block1116 block1128)) (treeBlock_merge (left := 24) (right := 36) (treeBlock_merge (left := 12) (right := 12) block1140 block1152) (treeBlock_merge (left := 12) (right := 24) block1164 (treeBlock_merge (left := 12) (right := 12) block1176 block1188)))) (treeBlock_merge (left := 48) (right := 60) (treeBlock_merge (left := 24) (right := 24) (treeBlock_merge (left := 12) (right := 12) block1200 block1212) (treeBlock_merge (left := 12) (right := 12) block1224 block1236)) (treeBlock_merge (left := 24) (right := 36) (treeBlock_merge (left := 12) (right := 12) block1248 block1260) (treeBlock_merge (left := 12) (right := 24) block1272 (treeBlock_merge (left := 12) (right := 12) block1284 block1296)))))) (treeBlock_merge (left := 216) (right := 225) (treeBlock_merge (left := 108) (right := 108) (treeBlock_merge (left := 48) (right := 60) (treeBlock_merge (left := 24) (right := 24) (treeBlock_merge (left := 12) (right := 12) block1308 block1320) (treeBlock_merge (left := 12) (right := 12) block1332 block1344)) (treeBlock_merge (left := 24) (right := 36) (treeBlock_merge (left := 12) (right := 12) block1356 block1368) (treeBlock_merge (left := 12) (right := 24) block1380 (treeBlock_merge (left := 12) (right := 12) block1392 block1404)))) (treeBlock_merge (left := 48) (right := 60) (treeBlock_merge (left := 24) (right := 24) (treeBlock_merge (left := 12) (right := 12) block1416 block1428) (treeBlock_merge (left := 12) (right := 12) block1440 block1452)) (treeBlock_merge (left := 24) (right := 36) (treeBlock_merge (left := 12) (right := 12) block1464 block1476) (treeBlock_merge (left := 12) (right := 24) block1488 (treeBlock_merge (left := 12) (right := 12) block1500 block1512))))) (treeBlock_merge (left := 108) (right := 117) (treeBlock_merge (left := 48) (right := 60) (treeBlock_merge (left := 24) (right := 24) (treeBlock_merge (left := 12) (right := 12) block1524 block1536) (treeBlock_merge (left := 12) (right := 12) block1548 block1560)) (treeBlock_merge (left := 24) (right := 36) (treeBlock_merge (left := 12) (right := 12) block1572 block1584) (treeBlock_merge (left := 12) (right := 24) block1596 (treeBlock_merge (left := 12) (right := 12) block1608 block1620)))) (treeBlock_merge (left := 60) (right := 57) (treeBlock_merge (left := 24) (right := 36) (treeBlock_merge (left := 12) (right := 12) block1632 block1644) (treeBlock_merge (left := 12) (right := 24) block1656 (treeBlock_merge (left := 12) (right := 12) block1668 block1680))) (treeBlock_merge (left := 24) (right := 33) (treeBlock_merge (left := 12) (right := 12) block1692 block1704) (treeBlock_merge (left := 12) (right := 21) block1716 (treeBlock_merge (left := 12) (right := 9) block1728 block1740))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem completed : ¬ RepSizeAtMost posted 14 := by
  apply lowerFromTable (root := 0) (s := (14,[31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856],[])) autos (geometryOrMinor_open valid)
    (fun i hi => treeBlock_at (Fast.Packed.compact_from_cached scanned) (Nat.zero_le i) (by simpa using hi))
  · decide +kernel
  · decide +kernel
  · rfl
  · decide +kernel
end Rep9102.Final9102
end PEqualNP.Outside.L_meta_18006

theorem PEqualNP.Outside.L_meta_18006 : ∀ s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => decide (u ≠ v)) s → 15 ≤ s := by
  rintro s ⟨C, hmono, hs, hrep⟩
  by_contra small
  exact PEqualNP.Outside.L_meta_18006.Rep9102.Final9102.completed ⟨C, hmono, by omega, hrep⟩
