import Mathlib.Tactic
namespace PEqualNP.Outside.L_meta_2592.Signed.Extended
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
def target : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
end PEqualNP.Outside.L_meta_2592.Signed.Extended
namespace PEqualNP.Outside.L_meta_2592.Signed.Extended

def firstPairRows (i j : Fin 10) (d : Fin 4) : Row × Row :=
  ([
  (0,0),(0,0),(0,0),(0,0),(64,576),(384,896),(384,896),(64,576),
  (128,640),(96,608),(96,608),(128,640),(128,640),(384,896),(384,896),(128,640),
  (128,640),(192,704),(192,704),(128,640),(128,640),(144,656),(144,656),(128,640),
  (128,640),(68,580),(68,580),(128,640),(128,640),(129,641),(129,641),(128,640),
  (128,640),(136,648),(136,648),(128,640),(128,640),(130,642),(130,642),(128,640),
  (32,160),(544,672),(544,672),(32,160),(0,0),(0,0),(0,0),(0,0),
  (512,640),(544,672),(544,672),(512,640),(512,640),(768,896),(768,896),(512,640),
  (512,640),(96,224),(96,224),(512,640),(512,640),(48,176),(48,176),(512,640),
  (512,640),(516,644),(516,644),(512,640),(512,640),(513,641),(513,641),(512,640),
  (512,640),(520,648),(520,648),(512,640),(512,640),(514,642),(514,642),(512,640),
  (128,160),(768,800),(768,800),(128,160),(256,288),(384,416),(384,416),(256,288),
  (0,0),(0,0),(0,0),(0,0),(128,160),(768,800),(768,800),(128,160),
  (128,160),(192,224),(192,224),(128,160),(128,160),(144,176),(144,176),(128,160),
  (128,160),(260,292),(260,292),(128,160),(128,160),(513,545),(513,545),(128,160),
  (128,160),(136,168),(136,168),(128,160),(128,160),(130,162),(130,162),(128,160),
  (32,288),(544,800),(544,800),(32,288),(32,288),(192,448),(192,448),(32,288),
  (64,320),(544,800),(544,800),(64,320),(0,0),(0,0),(0,0),(0,0),
  (32,288),(192,448),(192,448),(32,288),(32,288),(48,304),(48,304),(32,288),
  (32,288),(36,292),(36,292),(32,288),(32,288),(65,321),(65,321),(32,288),
  (32,288),(520,776),(520,776),(32,288),(32,288),(34,290),(34,290),(32,288),
  (256,320),(544,608),(544,608),(256,320),(512,576),(384,448),(384,448),(512,576),
  (512,576),(544,608),(544,608),(512,576),(512,576),(768,832),(768,832),(512,576),
  (0,0),(0,0),(0,0),(0,0),(512,576),(272,336),(272,336),(512,576),
  (512,576),(516,580),(516,580),(512,576),(512,576),(513,577),(513,577),(512,576),
  (512,576),(520,584),(520,584),(512,576),(512,576),(514,578),(514,578),(512,576),
  (1,17),(544,560),(544,560),(1,17),(512,528),(129,145),(129,145),(512,528),
  (512,528),(544,560),(544,560),(512,528),(512,528),(768,784),(768,784),(512,528),
  (512,528),(65,81),(65,81),(512,528),(0,0),(0,0),(0,0),(0,0),
  (512,528),(516,532),(516,532),(512,528),(512,528),(513,529),(513,529),(512,528),
  (512,528),(520,536),(520,536),(512,528),(512,528),(514,530),(514,530),(512,528),
  (128,132),(520,524),(520,524),(128,132),(8,12),(384,388),(384,388),(8,12),
  (128,132),(40,44),(40,44),(128,132),(128,132),(384,388),(384,388),(128,132),
  (128,132),(192,196),(192,196),(128,132),(128,132),(144,148),(144,148),(128,132),
  (0,0),(0,0),(0,0),(0,0),(128,132),(129,133),(129,133),(128,132),
  (128,132),(520,524),(520,524),(128,132),(128,132),(514,518),(514,518),(128,132),
  (32,33),(544,545),(544,545),(32,33),(32,33),(144,145),(144,145),(32,33),
  (16,17),(544,545),(544,545),(16,17),(32,33),(272,273),(272,273),(32,33),
  (32,33),(96,97),(96,97),(32,33),(32,33),(144,145),(144,145),(32,33),
  (32,33),(36,37),(36,37),(32,33),(0,0),(0,0),(0,0),(0,0),
  (32,33),(40,41),(40,41),(32,33),(32,33),(514,515),(514,515),(32,33),
  (256,264),(768,776),(768,776),(256,264),(256,264),(384,392),(384,392),(256,264),
  (256,264),(48,56),(48,56),(256,264),(16,24),(768,776),(768,776),(16,24),
  (256,264),(80,88),(80,88),(256,264),(256,264),(144,152),(144,152),(256,264),
  (256,264),(516,524),(516,524),(256,264),(256,264),(257,265),(257,265),(256,264),
  (0,0),(0,0),(0,0),(0,0),(256,264),(258,266),(258,266),(256,264),
  (64,66),(516,518),(516,518),(64,66),(64,66),(192,194),(192,194),(64,66),
  (64,66),(96,98),(96,98),(64,66),(64,66),(260,262),(260,262),(64,66),
  (4,6),(192,194),(192,194),(4,6),(64,66),(80,82),(80,82),(64,66),
  (64,66),(516,518),(516,518),(64,66),(64,66),(513,515),(513,515),(64,66),
  (64,66),(72,74),(72,74),(64,66),(0,0),(0,0),(0,0),(0,0)] : List (Row × Row)).getD (40 * i.val + 4 * j.val + d.val) (0,0)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma firstPairChecked : ∀ (i j : Fin 10) (d : Fin 4), i ≠ j →
    let rs := firstPairRows i j d
    bit rs.1 target ≠ bit rs.2 target ∧
    bit rs.1 (bin d.val (pins.getD i.val zero) (pins.getD j.val zero)) =
      bit rs.2 (bin d.val (pins.getD i.val zero) (pins.getD j.val zero)) ∧
    ∀ q : Fin 10, q ≠ i →
      bit rs.1 (pins.getD q.val zero) = bit rs.2 (pins.getD q.val zero) := by
  decide +kernel

lemma pins_as_ofFn : pins = List.ofFn (fun i : Fin 10 => pins.getD i.val zero) := by
  decide +kernel

lemma pin_mem (a : Sig) : a ∈ pins ↔ ∃ i : Fin 10, pins.getD i.val zero = a := by
  conv_lhs => rw [pins_as_ofFn]
  rw [List.mem_ofFn]

lemma first_gate_keeps_left {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat}
    (ha : a ∈ pins) (hb : b ∈ pins) (distinct : a ≠ b) (op : d < 4)
    (raw : ∀ v ∈ U, v ∈ pins) (run : Live true target k (insert (bin d a b) U)) :
    a ∈ U := by
  by_contra na
  obtain ⟨i, rfl⟩ := (pin_mem a).mp ha
  obtain ⟨j, rfl⟩ := (pin_mem b).mp hb
  have ij : i ≠ j := by
    rintro rfl
    exact distinct rfl
  obtain ⟨diff, gateSame, othersSame⟩ := firstPairChecked i j ⟨d, op⟩ ij
  obtain ⟨v, hv, changed⟩ := live_row_difference run diff
  rcases Finset.mem_insert.mp hv with rfl | inU
  · exact changed gateSame
  · obtain ⟨q, eq⟩ := (pin_mem v).mp (raw v inU)
    have qi : q ≠ i := by
      rintro rfl
      exact na (eq.symm ▸ inU)
    exact changed (eq ▸ othersSame q qi)

lemma first_gate_keeps_both {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat}
    (ha : a ∈ pins) (hb : b ∈ pins) (distinct : a ≠ b) (op : d < 4)
    (raw : ∀ v ∈ U, v ∈ pins) (run : Live true target k (insert (bin d a b) U)) :
    a ∈ U ∧ b ∈ U := by
  have hd : allowed true d := Or.inr ⟨rfl, op⟩
  have flipped : flipOp d < 4 := by
    have h := (flip_flip hd).1
    rcases h with h | ⟨_, h⟩ <;> omega
  have tail : Live true target k (insert (bin (flipOp d) b a) U) := by
    rw [← bin_flip hd]
    exact run
  exact ⟨first_gate_keeps_left ha hb distinct op raw run,
    first_gate_keeps_left hb ha (Ne.symm distinct) flipped raw tail⟩

lemma first_gate_keeps_input {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat}
    (ha : a ∈ pins) (hb : b ∈ pins) (distinct : a ≠ b) (op : d < 4)
    (raw : ∀ v ∈ U, v ∈ pins) (run : Live true target k (insert (bin d a b) U)) :
    a ∈ U ∨ b ∈ U :=
  Or.inl (first_gate_keeps_left ha hb distinct op raw run)

end PEqualNP.Outside.L_meta_2592.Signed.Extended


namespace PEqualNP.Outside.L_meta_2592.Signed.Extended

def petAdjacent (i j : Fin 10) : Bool :=
  ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
    (5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any
      (fun e => (e.1 == i && e.2 == j) || (e.1 == j && e.2 == i))

def overlapBase (i j c : Fin 10) : Nat :=
  ([
  0,0,0,0,0,0,0,0,0,0,0,0,0,384,192,144,0,129,136,130,
  0,0,0,0,96,48,100,0,104,50,0,384,0,0,0,272,276,385,0,386,
  0,192,96,0,0,80,68,65,72,0,0,144,48,272,80,0,20,0,0,18,
  0,0,100,276,68,20,0,69,0,0,0,129,0,385,65,0,69,0,137,0,
  0,136,104,0,72,0,0,137,0,138,0,130,50,386,0,18,0,0,138,0,
  0,0,544,768,0,0,516,513,520,514,0,0,0,0,0,0,0,0,0,0,
  544,0,0,0,96,48,36,0,40,34,768,0,0,0,0,276,260,769,0,770,
  0,0,96,0,0,112,68,69,104,0,0,0,48,276,112,0,20,0,0,50,
  516,0,36,260,68,20,0,5,0,0,513,0,0,769,69,0,5,0,521,0,
  520,0,40,0,104,0,0,521,0,522,514,0,34,770,0,50,0,0,522,0,
  0,0,0,768,0,0,772,513,521,770,0,0,0,384,192,144,0,129,136,130,
  0,0,0,0,0,0,0,0,0,0,768,384,0,0,0,272,260,257,0,258,
  0,192,0,0,0,208,69,65,200,0,0,144,0,272,208,0,276,0,0,146,
  772,0,0,260,69,276,0,5,0,0,513,129,0,257,65,0,5,0,9,0,
  521,136,0,0,200,0,0,9,0,138,770,130,0,258,0,146,0,0,138,0,
  0,0,544,0,0,0,548,521,520,546,0,0,0,0,192,208,0,193,136,138,
  544,0,0,0,96,48,36,0,40,34,0,0,0,0,0,0,0,0,0,0,
  0,192,96,0,0,80,68,65,72,0,0,208,48,0,80,0,52,0,0,50,
  548,0,36,0,68,52,0,69,0,0,521,193,0,0,65,0,69,0,9,0,
  520,136,40,0,72,0,0,9,0,10,546,138,34,0,0,50,0,0,10,0,
  0,0,544,768,0,0,516,513,520,514,0,0,0,384,0,400,0,385,138,130,
  544,0,0,0,0,50,548,0,552,34,768,384,0,0,0,272,260,257,0,258,
  0,0,0,0,0,0,0,0,0,0,0,400,50,272,0,0,276,0,0,18,
  516,0,548,260,0,276,0,517,0,0,513,385,0,257,0,0,517,0,521,0,
  520,138,552,0,0,0,0,521,0,10,514,130,34,258,0,18,0,0,10,0,
  0,0,544,768,0,0,516,513,520,514,0,0,0,385,193,0,0,129,136,138,
  544,0,0,0,104,0,548,0,40,546,768,385,0,0,0,0,772,257,0,770,
  0,193,104,0,0,0,69,65,72,0,0,0,0,0,0,0,0,0,0,0,
  516,0,548,772,69,0,0,5,0,0,513,129,0,257,65,0,5,0,9,0,
  520,136,40,0,72,0,0,9,0,10,514,138,546,770,0,0,0,0,10,0,
  0,0,552,770,0,0,0,521,520,514,0,0,0,384,192,144,0,129,136,130,
  552,0,0,0,104,50,0,0,40,34,770,384,0,0,0,400,0,385,0,258,
  0,192,104,0,0,208,0,193,72,0,0,144,50,400,208,0,0,0,0,18,
  0,0,0,0,0,0,0,0,0,0,521,129,0,385,193,0,0,0,9,0,
  520,136,40,0,72,0,0,9,0,10,514,130,34,258,0,18,0,0,10,0,
  0,0,544,770,0,0,548,0,552,514,0,0,0,400,208,144,0,0,138,130,
  544,0,0,0,96,48,36,0,40,34,770,400,0,0,0,272,276,0,0,258,
  0,208,96,0,0,80,100,0,104,0,0,144,48,272,80,0,20,0,0,18,
  548,0,36,276,100,20,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  552,138,40,0,104,0,0,0,0,10,514,130,34,258,0,18,0,0,10,0,
  0,0,548,768,0,0,516,769,0,770,0,0,0,384,208,144,0,385,0,386,
  548,0,0,0,112,48,36,0,0,50,768,384,0,0,0,272,260,257,0,258,
  0,208,112,0,0,80,68,69,0,0,0,144,48,272,80,0,20,0,0,18,
  516,0,36,260,68,20,0,5,0,0,769,385,0,257,69,0,5,0,0,0,
  0,0,0,0,0,0,0,0,0,0,770,386,50,258,0,18,0,0,0,0,
  0,0,548,772,0,0,516,513,521,0,0,0,0,385,192,208,0,129,200,0,
  548,0,0,0,96,112,36,0,104,0,772,385,0,0,0,276,260,257,0,0,
  0,192,96,0,0,80,68,65,72,0,0,208,112,276,80,0,20,0,0,0,
  516,0,36,260,68,20,0,5,0,0,513,129,0,257,65,0,5,0,9,0,
  521,200,104,0,72,0,0,9,0,0,0,0,0,0,0,0,0,0,0,0] : List Nat).getD (100*i.val + 10*j.val + c.val) 0

def overlapRows (i j c : Fin 10) : Row × Row :=
  (Fin.ofNat 1024 (overlapBase i j c),
    Fin.ofNat 1024 (overlapBase i j c +
      ([512,128,32,256,64,16,4,1,8,2] : List Nat).getD i.val 0))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma overlapChecked : ∀ (i j c : Fin 10), i ≠ j → i ≠ c → j ≠ c →
    petAdjacent j c = false →
    let rs := overlapRows i j c
    bit rs.1 target ≠ bit rs.2 target ∧
    bit rs.1 (bin 1 (pins.getD i.val zero) (pins.getD j.val zero)) =
      bit rs.2 (bin 1 (pins.getD i.val zero) (pins.getD j.val zero)) ∧
    bit rs.1 (bin 1 (pins.getD i.val zero) (pins.getD c.val zero)) =
      bit rs.2 (bin 1 (pins.getD i.val zero) (pins.getD c.val zero)) ∧
    ∀ q : Fin 10, q ≠ i →
      bit rs.1 (pins.getD q.val zero) = bit rs.2 (pins.getD q.val zero) := by
  decide +kernel

lemma overlapping_ors_keep_input (i j c : Fin 10) (ij : i ≠ j) (ic : i ≠ c)
    (jc : j ≠ c) (nonedge : petAdjacent j c = false) {k : Nat} {U : Finset Sig}
    (raw : ∀ v ∈ U, v ∈ pins)
    (run : Live true target k (insert (bin 1 (pins.getD i.val zero) (pins.getD j.val zero))
      (insert (bin 1 (pins.getD i.val zero) (pins.getD c.val zero)) U))) :
    pins.getD i.val zero ∈ U := by
  by_contra missing
  obtain ⟨diff, leftSame, rightSame, othersSame⟩ := overlapChecked i j c ij ic jc nonedge
  obtain ⟨v, hv, changed⟩ := live_row_difference run diff
  rcases Finset.mem_insert.mp hv with rfl | inTail
  · exact changed leftSame
  · rcases Finset.mem_insert.mp inTail with rfl | inU
    · exact changed rightSame
    · obtain ⟨q, eq⟩ := (pin_mem v).mp (raw v inU)
      have qi : q ≠ i := by
        rintro rfl
        exact missing (eq.symm ▸ inU)
      exact changed (eq ▸ othersSame q qi)

end PEqualNP.Outside.L_meta_2592.Signed.Extended

namespace PEqualNP.Outside.L_meta_2592.Signed.Extended

def tripleRows (i j c d : Fin 10) : Row × Row :=
  let weights := ([512,128,32,256,64,16,4,1,8,2] : List Nat)
  let base := weights.getD j.val 0 + weights.getD c.val 0 + weights.getD d.val 0
  (Fin.ofNat 1024 base, Fin.ofNat 1024 (base + weights.getD i.val 0))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma tripleChecked : ∀ (i j c d : Fin 10), ([i,j,c,d] : List (Fin 10)).Nodup →
    petAdjacent j c = false → petAdjacent j d = false → petAdjacent c d = false →
    (petAdjacent i j = true ∨ petAdjacent i c = true ∨ petAdjacent i d = true) →
    let rs := tripleRows i j c d
    bit rs.1 target ≠ bit rs.2 target ∧
    (∀ v ∈ [j,c,d],
      bit rs.1 (bin 1 (pins.getD i.val zero) (pins.getD v.val zero)) =
        bit rs.2 (bin 1 (pins.getD i.val zero) (pins.getD v.val zero))) ∧
    ∀ q : Fin 10, q ≠ i →
      bit rs.1 (pins.getD q.val zero) = bit rs.2 (pins.getD q.val zero) := by
  decide +kernel

lemma triple_ors_keep_input (i j c d : Fin 10) (nd : ([i,j,c,d] : List (Fin 10)).Nodup)
    (jc : petAdjacent j c = false) (jd : petAdjacent j d = false) (cd : petAdjacent c d = false)
    (neighbor : petAdjacent i j = true ∨ petAdjacent i c = true ∨ petAdjacent i d = true)
    {k : Nat} {S : Finset Sig}
    (raw : ∀ v ∈ S, v ∈ pins ∨ ∃ w ∈ [j,c,d],
      v = bin 1 (pins.getD i.val zero) (pins.getD w.val zero))
    (run : Live true target k S) : pins.getD i.val zero ∈ S := by
  by_contra missing
  obtain ⟨diff, gatesSame, othersSame⟩ := tripleChecked i j c d nd jc jd cd neighbor
  obtain ⟨v, hv, changed⟩ := live_row_difference run diff
  rcases raw v hv with ordinary | ⟨w, hw, rfl⟩
  · obtain ⟨q, eq⟩ := (pin_mem v).mp ordinary
    have qi : q ≠ i := by
      rintro rfl
      exact missing (eq.symm ▸ hv)
    exact changed (eq ▸ othersSame q qi)
  · exact changed (gatesSame w hw)

end PEqualNP.Outside.L_meta_2592.Signed.Extended
