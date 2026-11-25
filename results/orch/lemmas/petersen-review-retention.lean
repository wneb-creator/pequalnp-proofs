import PEqualNP.Defs
-- Live, bit, and the Petersen tables are adapted from L_meta_6581 (Apache-2.0).
namespace PEqualNP.Outside.L_meta_1884.SignedFloor.Extended
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
end PEqualNP.Outside.L_meta_1884.SignedFloor.Extended

namespace PEqualNP.Outside.L_meta_1884.SignedFloor.Extended

def rawPin1884 (i : Fin 10) : Sig := initial.getD i.val zero

def probeStart1884 (i j : Fin 10) (d : Fin 4) : Row :=
  Fin.ofNat 1024 (([0,0,0,0,16,128,128,16,16,48,48,16,16,272,272,16,16,64,64,16,64,16,16,64,16,20,20,16,16,65,65,16,16,72,72,16,16,18,18,16,4,512,512,4,0,0,0,0,4,32,32,4,4,260,260,4,4,68,68,4,4,20,20,4,32,4,4,32,4,5,5,4,4,40,40,4,4,34,34,4,1,513,513,1,1,128,128,1,0,0,0,0,1,256,256,1,1,65,65,1,1,144,144,1,1,5,5,1,128,1,1,128,1,9,9,1,1,130,130,1,8,520,520,8,8,136,136,8,8,32,32,8,0,0,0,0,8,64,64,8,8,48,48,8,8,36,36,8,8,9,9,8,32,8,8,32,8,10,10,8,2,512,512,2,2,130,130,2,2,34,34,2,2,256,256,2,0,0,0,0,2,18,18,2,2,260,260,2,2,257,257,2,2,10,10,2,256,2,2,256,1,512,512,1,1,129,129,1,1,40,40,1,1,257,257,1,1,65,65,1,0,0,0,0,1,5,5,1,8,1,1,8,1,8,8,1,1,10,10,1,2,514,514,2,2,128,128,2,2,34,34,2,2,258,258,2,2,72,72,2,2,18,18,2,0,0,0,0,2,9,9,2,2,8,8,2,8,2,2,8,2,514,514,2,2,130,130,2,2,32,32,2,2,258,258,2,2,80,80,2,2,16,16,2,2,20,20,2,0,0,0,0,2,10,10,2,16,2,2,16,4,516,516,4,4,144,144,4,4,36,36,4,4,256,256,4,4,68,68,4,4,16,16,4,16,4,4,16,4,5,5,4,0,0,0,0,4,18,18,4,1,513,513,1,1,129,129,1,1,36,36,1,1,257,257,1,1,64,64,1,1,20,20,1,1,4,4,1,4,1,1,4,1,9,9,1,0,0,0,0] : List Nat).getD ((i.val * 10 + j.val) * 4 + d.val) 0)

def probeEnd1884 (i j : Fin 10) (d : Fin 4) : Row :=
  Fin.ofNat 1024 ((probeStart1884 i j d).val ^^^ ([512,128,32,256,64,16,4,1,8,2] : List Nat).getD i.val 0)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma probeSpec1884 : ∀ (i j : Fin 10) (d : Fin 4), i ≠ j →
    bit (probeStart1884 i j d) target ≠ bit (probeEnd1884 i j d) target ∧
    bit (probeStart1884 i j d) (bin d.val (rawPin1884 i) (rawPin1884 j)) =
      bit (probeEnd1884 i j d) (bin d.val (rawPin1884 i) (rawPin1884 j)) ∧
    ∀ q : Fin 10, q ≠ i →
      bit (probeStart1884 i j d) (rawPin1884 q) = bit (probeEnd1884 i j d) (rawPin1884 q) := by
  decide +kernel

lemma rawPin1884_mem {a : Sig} (ha : a ∈ initial) : ∃ i : Fin 10, rawPin1884 i = a := by
  have he : initial = List.ofFn rawPin1884 := by decide +kernel
  rw [he] at ha
  exact List.mem_ofFn.mp ha

lemma retain_first_left1884 {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat}
    (ha : a ∈ initial) (hb : b ∈ initial) (hab : a ≠ b) (hd : allowed true d)
    (raw : ∀ c ∈ U, c ∈ initial)
    (run : Live true target k (insert (bin d a b) U)) : a ∈ U := by
  classical
  by_contra hmiss
  obtain ⟨i,rfl⟩ := rawPin1884_mem ha
  obtain ⟨j,rfl⟩ := rawPin1884_mem hb
  have hij : i ≠ j := fun h => hab (congrArg rawPin1884 h)
  have hlt : d < 4 := by
    rcases hd with h | ⟨_,h⟩ <;> omega
  obtain ⟨hp,hbin,hstable⟩ := probeSpec1884 i j ⟨d,hlt⟩ hij
  obtain ⟨c,hc,hdiff⟩ := live_row_difference run hp
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact hdiff hbin
  · obtain ⟨q,rfl⟩ := rawPin1884_mem (raw c hc)
    have hqi : q ≠ i := by
      intro he
      subst q
      exact hmiss hc
    exact hdiff (hstable q hqi)

lemma retain_first_both1884 {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat}
    (ha : a ∈ initial) (hb : b ∈ initial) (hab : a ≠ b) (hd : allowed true d)
    (raw : ∀ c ∈ U, c ∈ initial)
    (run : Live true target k (insert (bin d a b) U)) : a ∈ U ∧ b ∈ U := by
  refine ⟨retain_first_left1884 ha hb hab hd raw run, ?_⟩
  apply retain_first_left1884 hb ha hab.symm (flip_flip hd).1 raw
  simpa only [← bin_flip hd a b] using run

end PEqualNP.Outside.L_meta_1884.SignedFloor.Extended
