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
lemma rawPin1884_mem {a : Sig} (ha : a ∈ initial) : ∃ i : Fin 10, rawPin1884 i = a := by
  have he : initial = List.ofFn rawPin1884 := by decide +kernel
  rw [he] at ha
  exact List.mem_ofFn.mp ha
end PEqualNP.Outside.L_meta_1884.SignedFloor.Extended

namespace PEqualNP.Outside.L_meta_1884.SignedFloor.Extended

def adjacent1884 (i j : Fin 10) : Bool :=
  (([50,69,138,276,521,385,770,548,104,208] : List Nat).getD i.val 0).testBit j.val

def sharedProbeStart1884 (i j k : Fin 10) : Row :=
  Fin.ofNat 1024 ((0x9024000004800068226090000900405000414040020601000000140405044410240020400000000140505045034340000004810444140400006030000000004050445000404006070100068000240d06000024002240008920400340c06040020400002098060400000c0624002010480000000048004083224b020000000000000000000000000000000140500045404006060500000014040504441024002040480000014040504403024000000001144414044000643400040800405044400040000603000c800000240c06400024002242480060400240d06000024000c08008160400000c0224002040080a00000048004082220a020280a00000000680002822a0a00000000000000000000000000000000014050544502400224048000001404050440302400000068000541405000060340004080000114440004080060b0208828000240c06000020002202088a00000240d0608002080080a0a0022400000c0a20002020080a00000048004082220a020280802400000480002822208000090240000049604002060900000000000000000000000000480000000048d044832240000004812400340480006830000408006040044800408006030208828000000c86800022002222088820400240c0600002000080a088240000000c0a22002020280a0000000000c082a22a0202808024000004800028222080000900405000414040020601000000140500045416240020400000000000000000000000000004810445000410006830400c0800405050000040400607000a828002240006800028002202288820400000c1604002040080a088060400000c0220002000080a00000048004082220a020280a82400000000002a22a08002094050500000404006060100000415044500041224002040480000114048004403224800000000000000000000000000040800405044400040000603000882a002240c80000022002202088a6040024800600002080080a088060400000c0220002000280a000000c8000002222a0a0280802400000480002822208000090244500041000002260900000114240d04400024002240c800000340c05000030340000004810444140400006030000000000000000000000000000008828000240c06000020002202288822400340c0000002200082a08826240000000220002082088a00000248004080020b022280902400000490000022209000090040500041404002060100000014054504541000002052480000114240d044000240000004910445340410000030000408004050444000400006030000000000000000000000000002088820400240c06000020000c0a098060500000c0000002010882a000000c800c0822002020a82882400000680002800208002090140500045414000020100000014040504441024002040c800000140505445030000000006811444150440006000000c08004150445000410000030008828000240c0600002000220000000000000000000000000080a088060400000c0220002000488a000000480044832208002284812400000480006822000000491044500041604002040000000114140504445034000000480000014040504403024000000481044414040000603000044800605144400044000600000c868000340c06000030000002088820400240c060000200000000000000000000000000000 : Nat) >>> (10 * ((i.val * 10 + j.val) * 10 + k.val)))

def sharedProbeEnd1884 (i j k : Fin 10) : Row :=
  Fin.ofNat 1024 ((sharedProbeStart1884 i j k).val ^^^ ([512,128,32,256,64,16,4,1,8,2] : List Nat).getD i.val 0)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma sharedProbeSpec1884 : ∀ i j k : Fin 10, i ≠ j → i ≠ k → adjacent1884 j k = false →
    bit (sharedProbeStart1884 i j k) target ≠ bit (sharedProbeEnd1884 i j k) target ∧
    bit (sharedProbeStart1884 i j k) (bin 1 (rawPin1884 i) (rawPin1884 j)) =
      bit (sharedProbeEnd1884 i j k) (bin 1 (rawPin1884 i) (rawPin1884 j)) ∧
    bit (sharedProbeStart1884 i j k) (bin 1 (rawPin1884 i) (rawPin1884 k)) =
      bit (sharedProbeEnd1884 i j k) (bin 1 (rawPin1884 i) (rawPin1884 k)) ∧
    ∀ q : Fin 10, q ≠ i →
      bit (sharedProbeStart1884 i j k) (rawPin1884 q) =
        bit (sharedProbeEnd1884 i j k) (rawPin1884 q) := by
  decide +kernel

lemma shared_or_retained1884 {m : Nat} {S : Finset Sig} (i j k : Fin 10)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : adjacent1884 j k = false)
    (run : Live true target m S)
    (support : ∀ c ∈ S, c ∈ initial ∨ c = bin 1 (rawPin1884 i) (rawPin1884 j) ∨
      c = bin 1 (rawPin1884 i) (rawPin1884 k)) : rawPin1884 i ∈ S := by
  classical
  by_contra hmiss
  obtain ⟨hp,hfirst,hsecond,hstable⟩ := sharedProbeSpec1884 i j k hij hik hjk
  obtain ⟨c,hc,hdiff⟩ := live_row_difference run hp
  rcases support c hc with hr | rfl | rfl
  · obtain ⟨q,rfl⟩ := rawPin1884_mem hr
    have hqi : q ≠ i := by
      intro he
      subst q
      exact hmiss hc
    exact hdiff (hstable q hqi)
  · exact hdiff hfirst
  · exact hdiff hsecond

end PEqualNP.Outside.L_meta_1884.SignedFloor.Extended
