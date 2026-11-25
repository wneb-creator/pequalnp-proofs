import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031_aux.SemanticCertificate

def initial : List (BitVec 10) :=
  [0, 1, 2, 4, 8, 16, 32, 64, 113, 128, 204, 256, 387, 512, 550, 792, 1023]

def extend (xs : List (BitVec 10)) (v : BitVec 10) : List (BitVec 10) :=
  (xs ++ xs.map (fun u => u &&& v)).eraseDups

def ors (xs : List (BitVec 10)) : List (BitVec 10) :=
  (xs.flatMap (fun a => xs.map (fun b => a ||| b))).eraseDups

def full (xs : List (BitVec 10)) : List (BitVec 10) :=
  xs.filter (fun u => (u &&& 31) == 31)

def finish (xs : List (BitVec 10)) : Bool :=
  (full xs).all (fun u => xs.all (fun a => xs.all (fun b => !((u &&& (a ||| b)) == 31))))

def checkFirst (v : BitVec 10) : Bool :=
  let xs := extend initial v
  (ors xs).all (fun w => finish (extend xs w))


def select (p : BitVec 8) (i : Nat) (v : BitVec 10) : BitVec 10 :=
  if p.getLsbD i then v else 1023

def meet0 (p : BitVec 8) : BitVec 10 :=
  select p 0 113 &&& select p 1 387 &&& select p 2 550 &&&
    select p 3 204 &&& select p 4 792

def meet1 (p : BitVec 8) (v : BitVec 10) : BitVec 10 := meet0 p &&& select p 5 v

def meet2 (p : BitVec 8) (v w : BitVec 10) : BitVec 10 := meet1 p v &&& select p 6 w

def meet3 (p : BitVec 8) (v w z : BitVec 10) : BitVec 10 := meet2 p v w &&& select p 7 z

lemma initial_meet0 : ∀ p : BitVec 8, meet0 p ∈ initial := by
  decide +kernel

lemma mem_extend {xs : List (BitVec 10)} {u : BitVec 10} (hu : u ∈ xs) (v : BitVec 10) :
    u ∈ extend xs v := by
  simp [extend, hu]

lemma and_mem_extend {xs : List (BitVec 10)} {u : BitVec 10} (hu : u ∈ xs) (v : BitVec 10) :
    u &&& v ∈ extend xs v := by
  simp only [extend, List.mem_eraseDups, List.mem_append, List.mem_map]
  exact Or.inr ⟨u, hu, rfl⟩

lemma selected_mem_extend {xs : List (BitVec 10)} {u : BitVec 10} (hu : u ∈ xs)
    (v : BitVec 10) (bit : Bool) :
    u &&& (if bit then v else (1023 : BitVec 10)) ∈ extend xs v := by
  cases bit with
  | false =>
    change u &&& BitVec.allOnes 10 ∈ extend xs v
    rw [BitVec.and_allOnes]
    exact mem_extend hu v
  | true => exact and_mem_extend hu v

lemma meet1_mem (p : BitVec 8) (v : BitVec 10) : meet1 p v ∈ extend initial v :=
  selected_mem_extend (initial_meet0 p) v (p.getLsbD 5)

lemma meet2_mem (p : BitVec 8) (v w : BitVec 10) :
    meet2 p v w ∈ extend (extend initial v) w :=
  selected_mem_extend (meet1_mem p v) w (p.getLsbD 6)

lemma or_mem {xs : List (BitVec 10)} {a b : BitVec 10} (ha : a ∈ xs) (hb : b ∈ xs) :
    a ||| b ∈ ors xs := by
  simp only [ors, List.mem_eraseDups, List.mem_flatMap, List.mem_map]
  exact ⟨a, ha, b, hb, rfl⟩

lemma finish_sound (xs : List (BitVec 10)) (hfinish : finish xs = true)
    {u a b : BitVec 10} (hu : u ∈ xs) (ha : a ∈ xs) (hb : b ∈ xs) :
    u &&& (a ||| b) ≠ (31 : BitVec 10) := by
  intro heq
  have hmask : u &&& (31 : BitVec 10) = 31 := by
    rw [← heq, ← BitVec.and_assoc, BitVec.and_self]
  have hfull : u ∈ full xs := by
    apply List.mem_filter.mpr
    exact ⟨hu, by simpa only [beq_iff_eq] using hmask⟩
  have htest := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hfinish u hfull) a ha) b hb
  rw [heq] at htest
  simp at htest

lemma finish_selected_sound (xs : List (BitVec 10)) (hfinish : finish xs = true)
    {u a b : BitVec 10} (hu : u ∈ xs) (ha : a ∈ xs) (hb : b ∈ xs)
    (hone : (1023 : BitVec 10) ∈ xs) (bit : Bool) :
    u &&& (if bit then a ||| b else (1023 : BitVec 10)) ≠ (31 : BitVec 10) := by
  cases bit with
  | false => simpa only [Bool.false_eq_true, ↓reduceIte, BitVec.or_self] using finish_sound xs hfinish hu hone hone
  | true => exact finish_sound xs hfinish hu ha hb

theorem semantic_soundness
    (hchecks : ∀ v ∈ ors initial, checkFirst v = true) :
    ∀ a b c d e f o : BitVec 8,
      let v := meet0 a ||| meet0 b
      let w := meet1 c v ||| meet1 d v
      let z := meet2 e v w ||| meet2 f v w
      meet3 o v w z ≠ (31 : BitVec 10) := by
  intro a b c d e f o
  let v := meet0 a ||| meet0 b
  let w := meet1 c v ||| meet1 d v
  have hv : v ∈ ors initial := or_mem (initial_meet0 a) (initial_meet0 b)
  have hw : w ∈ ors (extend initial v) := or_mem (meet1_mem c v) (meet1_mem d v)
  have hall : (ors (extend initial v)).all
      (fun w => finish (extend (extend initial v) w)) = true := hchecks v hv
  have hfinish := List.all_eq_true.mp hall w hw
  have hone : (1023 : BitVec 10) ∈ extend (extend initial v) w :=
    mem_extend (mem_extend (by simp [initial]) v) w
  exact finish_selected_sound _ hfinish (meet2_mem o v w) (meet2_mem e v w)
    (meet2_mem f v w) hone (o.getLsbD 7)

end PEqualNP.Outside.L_meta_1031_aux.SemanticCertificate
