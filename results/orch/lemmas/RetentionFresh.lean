import PEqualNP.Defs.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_2592_aux.Extended
abbrev Sig := BitVec 1024
def zero : Sig := 0
def one : Sig := BitVec.allOnes 1024
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)
def bit (i : Fin 1024) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
abbrev Row := Fin 1024
theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩
def pins : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc]
def initial : List Sig := pins
def first : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def target : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
end PEqualNP.Outside.L_meta_2592_aux.Extended

namespace PEqualNP.Outside.L_meta_2592_aux.Extended

def retentionRows : List (Row × Row) := [
  (0, 0), (0, 0), (0, 0), (0, 0), (16, 528), (128, 640), (128, 640), (16, 528),
  (16, 528), (48, 560), (48, 560), (16, 528), (16, 528), (272, 784), (272, 784), (16, 528),
  (16, 528), (64, 576), (64, 576), (16, 528), (64, 576), (16, 528), (16, 528), (64, 576),
  (16, 528), (20, 532), (20, 532), (16, 528), (16, 528), (65, 577), (65, 577), (16, 528),
  (16, 528), (72, 584), (72, 584), (16, 528), (16, 528), (18, 530), (18, 530), (16, 528),
  (4, 132), (512, 640), (512, 640), (4, 132), (0, 0), (0, 0), (0, 0), (0, 0),
  (4, 132), (32, 160), (32, 160), (4, 132), (4, 132), (260, 388), (260, 388), (4, 132),
  (4, 132), (68, 196), (68, 196), (4, 132), (4, 132), (20, 148), (20, 148), (4, 132),
  (32, 160), (4, 132), (4, 132), (32, 160), (4, 132), (5, 133), (5, 133), (4, 132),
  (4, 132), (40, 168), (40, 168), (4, 132), (4, 132), (34, 162), (34, 162), (4, 132),
  (1, 33), (513, 545), (513, 545), (1, 33), (1, 33), (128, 160), (128, 160), (1, 33),
  (0, 0), (0, 0), (0, 0), (0, 0), (1, 33), (256, 288), (256, 288), (1, 33),
  (1, 33), (65, 97), (65, 97), (1, 33), (1, 33), (144, 176), (144, 176), (1, 33),
  (1, 33), (5, 37), (5, 37), (1, 33), (128, 160), (1, 33), (1, 33), (128, 160),
  (1, 33), (9, 41), (9, 41), (1, 33), (1, 33), (130, 162), (130, 162), (1, 33),
  (8, 264), (520, 776), (520, 776), (8, 264), (8, 264), (136, 392), (136, 392), (8, 264),
  (8, 264), (32, 288), (32, 288), (8, 264), (0, 0), (0, 0), (0, 0), (0, 0),
  (8, 264), (64, 320), (64, 320), (8, 264), (8, 264), (48, 304), (48, 304), (8, 264),
  (8, 264), (36, 292), (36, 292), (8, 264), (8, 264), (9, 265), (9, 265), (8, 264),
  (32, 288), (8, 264), (8, 264), (32, 288), (8, 264), (10, 266), (10, 266), (8, 264),
  (2, 66), (512, 576), (512, 576), (2, 66), (2, 66), (130, 194), (130, 194), (2, 66),
  (2, 66), (34, 98), (34, 98), (2, 66), (2, 66), (256, 320), (256, 320), (2, 66),
  (0, 0), (0, 0), (0, 0), (0, 0), (2, 66), (18, 82), (18, 82), (2, 66),
  (2, 66), (260, 324), (260, 324), (2, 66), (2, 66), (257, 321), (257, 321), (2, 66),
  (2, 66), (10, 74), (10, 74), (2, 66), (256, 320), (2, 66), (2, 66), (256, 320),
  (1, 17), (512, 528), (512, 528), (1, 17), (1, 17), (129, 145), (129, 145), (1, 17),
  (1, 17), (40, 56), (40, 56), (1, 17), (1, 17), (257, 273), (257, 273), (1, 17),
  (1, 17), (65, 81), (65, 81), (1, 17), (0, 0), (0, 0), (0, 0), (0, 0),
  (1, 17), (5, 21), (5, 21), (1, 17), (8, 24), (1, 17), (1, 17), (8, 24),
  (1, 17), (8, 24), (8, 24), (1, 17), (1, 17), (10, 26), (10, 26), (1, 17),
  (2, 6), (514, 518), (514, 518), (2, 6), (2, 6), (128, 132), (128, 132), (2, 6),
  (2, 6), (34, 38), (34, 38), (2, 6), (2, 6), (258, 262), (258, 262), (2, 6),
  (2, 6), (72, 76), (72, 76), (2, 6), (2, 6), (18, 22), (18, 22), (2, 6),
  (0, 0), (0, 0), (0, 0), (0, 0), (2, 6), (9, 13), (9, 13), (2, 6),
  (2, 6), (8, 12), (8, 12), (2, 6), (8, 12), (2, 6), (2, 6), (8, 12),
  (2, 3), (514, 515), (514, 515), (2, 3), (2, 3), (130, 131), (130, 131), (2, 3),
  (2, 3), (32, 33), (32, 33), (2, 3), (2, 3), (258, 259), (258, 259), (2, 3),
  (2, 3), (80, 81), (80, 81), (2, 3), (2, 3), (16, 17), (16, 17), (2, 3),
  (2, 3), (20, 21), (20, 21), (2, 3), (0, 0), (0, 0), (0, 0), (0, 0),
  (2, 3), (10, 11), (10, 11), (2, 3), (16, 17), (2, 3), (2, 3), (16, 17),
  (4, 12), (516, 524), (516, 524), (4, 12), (4, 12), (144, 152), (144, 152), (4, 12),
  (4, 12), (36, 44), (36, 44), (4, 12), (4, 12), (256, 264), (256, 264), (4, 12),
  (4, 12), (68, 76), (68, 76), (4, 12), (4, 12), (16, 24), (16, 24), (4, 12),
  (16, 24), (4, 12), (4, 12), (16, 24), (4, 12), (5, 13), (5, 13), (4, 12),
  (0, 0), (0, 0), (0, 0), (0, 0), (4, 12), (18, 26), (18, 26), (4, 12),
  (1, 3), (513, 515), (513, 515), (1, 3), (1, 3), (129, 131), (129, 131), (1, 3),
  (1, 3), (36, 38), (36, 38), (1, 3), (1, 3), (257, 259), (257, 259), (1, 3),
  (1, 3), (64, 66), (64, 66), (1, 3), (1, 3), (20, 22), (20, 22), (1, 3),
  (1, 3), (4, 6), (4, 6), (1, 3), (4, 6), (1, 3), (1, 3), (4, 6),
  (1, 3), (9, 11), (9, 11), (1, 3), (0, 0), (0, 0), (0, 0), (0, 0)]

def retentionPair (i j : Fin 10) (d : Fin 4) : Row × Row :=
  retentionRows.getD ((i.val * 10 + j.val) * 4 + d.val) (0, 0)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma retention_samples : ∀ (i j : Fin 10), i ≠ j → ∀ d : Fin 4,
    let a := initial.getD i.val zero
    let b := initial.getD j.val zero
    let p := retentionPair i j d
    bit p.1 target ≠ bit p.2 target ∧
      bit p.1 (bin d.val a b) = bit p.2 (bin d.val a b) ∧
      initial.all (fun c => (c == a) || (bit p.1 c == bit p.2 c)) = true := by
  decide +kernel

lemma raw_pair_witness {a b : Sig} (ha : a ∈ initial) (hb : b ∈ initial)
    (hne : a ≠ b) {d : Nat} (hd : allowed true d) :
    ∃ r s : Row, bit r target ≠ bit s target ∧
      bit r (bin d a b) = bit s (bin d a b) ∧
      ∀ c ∈ initial, c ≠ a → bit r c = bit s c := by
  have length : initial.length = 10 := by decide +kernel
  obtain ⟨i, hi, ei⟩ := List.getElem_of_mem ha
  obtain ⟨j, hj, ej⟩ := List.getElem_of_mem hb
  let fi : Fin 10 := ⟨i, by omega⟩
  let fj : Fin 10 := ⟨j, by omega⟩
  have different : fi ≠ fj := by
    intro equal
    have ij : i = j := congrArg Fin.val equal
    apply hne
    subst j
    exact ei.symm.trans ej
  have dl : d < 4 := by
    rcases hd with h | ⟨_, h⟩ <;> omega
  let fd : Fin 4 := ⟨d, dl⟩
  have ae : initial.getD fi.val zero = a := by
    simpa only [fi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some] using ei
  have be : initial.getD fj.val zero = b := by
    simpa only [fj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      Option.getD_some] using ej
  obtain ⟨diff, same, rest⟩ := retention_samples fi fj different fd
  refine ⟨(retentionPair fi fj fd).1, (retentionPair fi fj fd).2, diff, ?_, ?_⟩
  · simpa only [fd, ae, be] using same
  · intro c hc hca
    have h := List.all_eq_true.mp rest c hc
    simp only [Bool.or_eq_true, beq_iff_eq, ae] at h
    exact h.resolve_left hca

lemma first_left_retained {k U a b d}
    (ha : a ∈ initial) (hb : b ∈ initial) (hne : a ≠ b)
    (hd : allowed true d) (raw : ∀ c ∈ U, c ∈ initial)
    (tail : Live true target k (insert (bin d a b) U)) : a ∈ U := by
  obtain ⟨r, s, diff, same, rest⟩ := raw_pair_witness ha hb hne hd
  obtain ⟨c, hc, hdiff⟩ := live_row_difference tail diff
  rcases Finset.mem_insert.mp hc with eq | hc
  · subst c
    exact False.elim (hdiff same)
  · by_contra absent
    exact hdiff (rest c (raw c hc) (fun eq => absent (eq ▸ hc)))

lemma first_operands_retained {k U a b d}
    (ha : a ∈ initial) (hb : b ∈ initial) (hne : a ≠ b)
    (hd : allowed true d) (raw : ∀ c ∈ U, c ∈ initial)
    (tail : Live true target k (insert (bin d a b) U)) : a ∈ U ∧ b ∈ U := by
  refine ⟨first_left_retained ha hb hne hd raw tail, ?_⟩
  have flip := (flip_flip hd).1
  apply first_left_retained hb ha hne.symm flip raw
  simpa only [bin_flip hd] using tail

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma raw_bin_fresh_samples :
    initial.all (fun a => initial.all (fun b =>
      (a == b) || (List.range 4).all (fun d => !(initial.contains (bin d a b))))) = true := by
  decide +kernel

lemma raw_bin_fresh {a b : Sig} (ha : a ∈ initial) (hb : b ∈ initial)
    (hne : a ≠ b) {d : Nat} (hd : allowed true d) : bin d a b ∉ initial := by
  have dl : d < 4 := by
    rcases hd with h | ⟨_, h⟩ <;> omega
  have h := List.all_eq_true.mp (List.all_eq_true.mp raw_bin_fresh_samples a ha) b hb
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  have chk := List.all_eq_true.mp (h.resolve_left hne) d (List.mem_range.mpr dl)
  simpa using chk

end PEqualNP.Outside.L_meta_2592_aux.Extended
