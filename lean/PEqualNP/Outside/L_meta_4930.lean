import Mathlib.Data.List.GetD

namespace PEqualNP.Outside.L_meta_4930_aux

def dualGate (g : Bool × Nat × Nat) : Bool × Nat × Nat :=
  (!g.1, g.2.1, g.2.2)

def dualOps (gs : List (Bool × Nat × Nat)) : List (Bool × Nat × Nat) :=
  gs.map dualGate

def complement {w : Nat} (xs : List (BitVec w)) : List (BitVec w) :=
  xs.map (fun x => ~~~x)

def step {w : Nat} (xs : List (BitVec w)) (g : Bool × Nat × Nat) : List (BitVec w) :=
  xs ++ [if g.1 = true then xs.getD g.2.1 0 &&& xs.getD g.2.2 0
    else xs.getD g.2.1 0 ||| xs.getD g.2.2 0]

def run {w : Nat} (xs : List (BitVec w)) (gs : List (Bool × Nat × Nat)) :
    List (BitVec w) := gs.foldl step xs

def valid (n : Nat) : List (Bool × Nat × Nat) → Prop
  | [] => True
  | g :: gs => g.2.1 < g.2.2 ∧ g.2.2 < n ∧ valid (n + 1) gs

def postedValid (n : Nat) (gs : List (Bool × Nat × Nat)) : Prop :=
  ∀ i : Fin gs.length,
    (gs.getD i.val (false, 0, 0)).2.1 < (gs.getD i.val (false, 0, 0)).2.2 ∧
      (gs.getD i.val (false, 0, 0)).2.2 < n + i.val

lemma getD_complement {w : Nat} (xs : List (BitVec w)) (i : Nat)
    (hi : i < xs.length) :
    (complement xs).getD i 0 = ~~~(xs.getD i 0) := by
  simp [complement, hi]

lemma step_dual {w : Nat} (xs : List (BitVec w)) (g : Bool × Nat × Nat)
    (ha : g.2.1 < xs.length) (hb : g.2.2 < xs.length) :
    step (complement xs) (dualGate g) = complement (step xs g) := by
  simp only [step, dualGate, List.map_append, List.map_cons, List.map_nil, complement]
  rw [show (xs.map (fun x => ~~~x)).getD g.2.1 0 = ~~~(xs.getD g.2.1 0) from
    getD_complement xs g.2.1 ha]
  rw [show (xs.map (fun x => ~~~x)).getD g.2.2 0 = ~~~(xs.getD g.2.2 0) from
    getD_complement xs g.2.2 hb]
  rcases g with ⟨b, a, c⟩
  cases b <;> simp [BitVec.not_and, BitVec.not_or]

lemma run_dual {w : Nat} (xs : List (BitVec w)) (gs : List (Bool × Nat × Nat))
    (h : valid xs.length gs) :
    run (complement xs) (dualOps gs) = complement (run xs gs) := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨hab, hb, ht⟩ := h
    have ha : g.2.1 < xs.length := Nat.lt_trans hab hb
    change run (step (complement xs) (dualGate g)) (dualOps gs) =
      complement (run (step xs g) gs)
    rw [step_dual xs g ha hb]
    apply ih
    simpa [step] using ht

lemma valid_iff_postedValid (n : Nat) (gs : List (Bool × Nat × Nat)) :
    valid n gs ↔ postedValid n gs := by
  induction gs generalizing n with
  | nil => simp [valid, postedValid]
  | cons g gs ih =>
    constructor
    · rintro ⟨hab, hb, ht⟩ i
      cases hi : i.val with
      | zero => simpa [hi] using And.intro hab hb
      | succ j =>
        have hj : j < gs.length := by
          simpa only [hi, List.length_cons, Nat.succ_lt_succ_iff] using i.isLt
        have h := (ih (n + 1)).mp ht ⟨j, hj⟩
        simpa [hi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    · intro h
      have hh := h ⟨0, by simp⟩
      refine ⟨by simpa using hh.1, by simpa using hh.2, ?_⟩
      apply (ih (n + 1)).mpr
      intro i
      have hh := h ⟨i.val + 1, by simp⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

lemma valid_dual (n : Nat) (gs : List (Bool × Nat × Nat)) :
    valid n (dualOps gs) ↔ valid n gs := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih => simpa [valid, dualOps, dualGate] using
      and_congr_right (fun _ => and_congr_right (fun _ => ih (n + 1)))

lemma dualOps_length (gs : List (Bool × Nat × Nat)) : (dualOps gs).length = gs.length := by
  simp [dualOps]

lemma complement_involutive {w : Nat} (xs : List (BitVec w)) :
    complement (complement xs) = xs := by
  simp [complement, List.map_map, Function.comp_def, BitVec.not_not]

lemma dualOps_involutive (gs : List (Bool × Nat × Nat)) : dualOps (dualOps gs) = gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rcases g with ⟨b, a, c⟩
    simpa [dualOps, dualGate] using congrArg (List.cons (b, a, c)) ih

lemma mem_complement_iff {w : Nat} (xs : List (BitVec w)) (target : BitVec w) :
    ~~~target ∈ complement xs ↔ target ∈ xs := by
  simp [complement, List.mem_map, BitVec.not_inj]

lemma dual_witness {w : Nat} (xs : List (BitVec w)) (target : BitVec w)
    (k : Nat) (gs : List (Bool × Nat × Nat))
    (hlen : gs.length = k) (hvalid : postedValid xs.length gs)
    (hmem : ~~~target ∈ run (complement xs) gs) :
    (dualOps gs).length = k ∧ postedValid xs.length (dualOps gs) ∧
      target ∈ run xs (dualOps gs) := by
  have hv : valid xs.length gs := (valid_iff_postedValid _ _).mpr hvalid
  have hd : valid xs.length (dualOps gs) := (valid_dual _ _).mpr hv
  refine ⟨(dualOps_length gs).trans hlen, (valid_iff_postedValid _ _).mp hd, ?_⟩
  have he := run_dual xs (dualOps gs) hd
  rw [dualOps_involutive] at he
  rw [he] at hmem
  exact (mem_complement_iff _ _).mp hmem

lemma exists_witness_dual_iff {w : Nat} (xs : List (BitVec w))
    (target : BitVec w) (k : Nat) :
    (∃ gs : List (Bool × Nat × Nat), gs.length = k ∧ postedValid xs.length gs ∧
      target ∈ run xs gs) ↔
    (∃ gs : List (Bool × Nat × Nat), gs.length = k ∧
      postedValid (complement xs).length gs ∧ ~~~target ∈ run (complement xs) gs) := by
  constructor
  · rintro ⟨gs, hlen, hv, hm⟩
    have hvr := (valid_iff_postedValid _ _).mpr hv
    have hvd : postedValid (complement xs).length (dualOps gs) := by
      apply (valid_iff_postedValid _ _).mp
      simpa [complement] using (valid_dual _ _).mpr hvr
    refine ⟨dualOps gs, (dualOps_length gs).trans hlen, hvd, ?_⟩
    rw [run_dual xs gs hvr]
    exact (mem_complement_iff _ _).mpr hm
  · rintro ⟨gs, hlen, hv, hm⟩
    have hv' : postedValid xs.length gs := by simpa [complement] using hv
    exact ⟨dualOps gs, dual_witness xs target k gs hlen hv' hm⟩

end PEqualNP.Outside.L_meta_4930_aux
