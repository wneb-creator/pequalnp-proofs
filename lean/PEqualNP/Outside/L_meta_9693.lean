import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9693.Critical

open PEqualNP.ProofComplexity PEqualNP.Search

abbrev Pigeon := Fin 5
abbrev Hole := Fin 4
abbrev Var := Pigeon × Hole

def pigeonClause (i : Pigeon) : Clause Var :=
  Finset.univ.image fun h : Hole => ((i,h),true)

def pairClause (i j : Pigeon) (h : Hole) : Clause Var :=
  {((i,h),false), ((j,h),false)}

end PEqualNP.Outside.L_meta_9693.Critical
namespace PEqualNP.Outside.L_meta_9693.Critical

open PEqualNP.ProofComplexity PEqualNP.Search

abbrev Collision := Hole × Fin 10
abbrev Label := Pigeon ⊕ Collision

def pairTable : Fin 10 → Pigeon × Pigeon :=
  ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

def leftPigeon (e : Collision) : Pigeon := (pairTable e.2).1

def rightPigeon (e : Collision) : Pigeon := (pairTable e.2).2

def labeledClause : Label → Clause Var
  | .inl p => pigeonClause p
  | .inr e => pairClause (leftPigeon e) (rightPigeon e) e.1

def labeledLine (i : Label) : CPLine Var := clauseCP (labeledClause i)

def slack (a : Var → ℤ) (c : CPLine Var) : ℤ := (∑ v, c.1 v * a v) - c.2

def incompatible (e f : Collision) : Prop :=
  e.1 ≠ f.1 ∨ (leftPigeon e ≠ leftPigeon f ∧ leftPigeon e ≠ rightPigeon f ∧
    rightPigeon e ≠ leftPigeon f ∧ rightPigeon e ≠ rightPigeon f)

def CriticalSlack (a : Var → ℤ) (i : Label) : Prop :=
  (∀ v, a v = 0 ∨ a v = 1) ∧ slack a (labeledLine i) = -1 ∧
    ∀ j, j ≠ i → 0 ≤ slack a (labeledLine j)

private theorem pair_distinct : ∀ e : Collision, leftPigeon e ≠ rightPigeon e := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pair_id : ∀ e f : Collision,
    ((leftPigeon e = leftPigeon f ∧ rightPigeon e = rightPigeon f) ∨
      (leftPigeon e = rightPigeon f ∧ rightPigeon e = leftPigeon f)) → e.2 = f.2 := by
  decide +kernel

private theorem all_pairs : ∀ p q : Pigeon, p ≠ q →
    ∃ k : Fin 10, pairTable k = (p,q) ∨ pairTable k = (q,p) := by
  decide +kernel

theorem label_surjective_on_php (C : Clause Var) (hC : C ∈ PHP 5 4) :
    ∃ i : Label, labeledClause i = C := by
  rcases hC with ⟨p,rfl⟩ | ⟨p,q,h,ne,rfl⟩
  · exact ⟨.inl p,rfl⟩
  · obtain ⟨k,hk | hk⟩ := all_pairs p q ne
    · exact ⟨.inr (h,k), by simp [labeledClause, leftPigeon, rightPigeon, hk, pairClause]⟩
    · exact ⟨.inr (h,k), by simp [labeledClause, leftPigeon, rightPigeon, hk, pairClause, Finset.pair_comm]⟩

private theorem pigeon_normal : ∀ (i : Pigeon) (v : Var),
    (labeledLine (.inl i)).1 v = (if v.1 = i then 1 else 0) ∧
      (labeledLine (.inl i)).2 = 1 := by decide +kernel

private theorem collision_normal : ∀ (e : Collision) (v : Var),
    (labeledLine (.inr e)).1 v =
      -((if v = (leftPigeon e,e.1) then 1 else 0) +
        (if v = (rightPigeon e,e.1) then 1 else 0)) ∧
      (labeledLine (.inr e)).2 = -1 := by
  decide +kernel

def intAssignment (skip : Option Pigeon) (home : Pigeon → Hole) (v : Var) : ℤ :=
  if skip = some v.1 then 0 else if home v.1 = v.2 then 1 else 0

private theorem intAssignment_bits (skip : Option Pigeon) (home : Pigeon → Hole) (v : Var) :
    intAssignment skip home v = 0 ∨ intAssignment skip home v = 1 := by
  unfold intAssignment
  split <;> (try split) <;> simp

theorem pigeonSlack (skip : Option Pigeon) (home : Pigeon → Hole) (p : Pigeon) :
    slack (intAssignment skip home) (labeledLine (.inl p)) =
      if skip = some p then -1 else 0 := by
  unfold slack
  simp only [fun v => (pigeon_normal p v).1, (pigeon_normal p (0,0)).2]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single p]
  · simp only [if_pos rfl, one_mul]
    by_cases h : skip = some p
    · simp [intAssignment, h]
    · simp [intAssignment, h, Finset.sum_ite_eq, eq_comm]
  · intro q _ hq
    simp [hq]
  · simp

theorem collisionSlack (a : Var → ℤ) (e : Collision) :
    slack a (labeledLine (.inr e)) = 1 - a (leftPigeon e,e.1) - a (rightPigeon e,e.1) := by
  unfold slack
  simp only [fun v => (collision_normal e v).1, (collision_normal e (0,0)).2,
    neg_mul, add_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

def missingHome (i : Pigeon) (p : Pigeon) : Hole :=
  Fin.ofNat 4 (p.val - (if i.val < p.val then 1 else 0))

def collidingHome (e : Collision) (p : Pigeon) : Hole :=
  if p = leftPigeon e ∨ p = rightPigeon e then e.1 else
    let t := p.val - (if (leftPigeon e).val < p.val then 1 else 0) -
      (if (rightPigeon e).val < p.val then 1 else 0)
    Fin.ofNat 4 (t + (if e.1.val ≤ t then 1 else 0))

private theorem missingHome_unique : ∀ i p q : Pigeon, p ≠ i → q ≠ i →
    missingHome i p = missingHome i q → p = q := by decide +kernel

private theorem collidingHome_at : ∀ e : Collision, ∀ p : Pigeon,
    collidingHome e p = e.1 ↔ p = leftPigeon e ∨ p = rightPigeon e := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem collidingHome_unique : ∀ e : Collision, ∀ p q : Pigeon, p ≠ q →
    collidingHome e p = collidingHome e q →
      (p = leftPigeon e ∧ q = rightPigeon e) ∨ (p = rightPigeon e ∧ q = leftPigeon e) := by
  decide +kernel

theorem missingSlack (i : Pigeon) (r : Hole ≃ Hole) :
    CriticalSlack (intAssignment (some i) (r ∘ missingHome i)) (.inl i) := by
  refine ⟨intAssignment_bits _ _, by simp [pigeonSlack], ?_⟩
  rintro (p | e) different
  · have hp : p ≠ i := fun eq => different (congrArg Sum.inl eq)
    simp [pigeonSlack, Ne.symm hp]
  · rw [collisionSlack]
    let home := r ∘ missingHome i
    have b1 := intAssignment_bits (some i) home (leftPigeon e,e.1)
    have b2 := intAssignment_bits (some i) home (rightPigeon e,e.1)
    change 0 ≤ 1 - intAssignment (some i) home (leftPigeon e,e.1) -
      intAssignment (some i) home (rightPigeon e,e.1)
    rcases b1 with h1 | h1 <;> rcases b2 with h2 | h2 <;> rw [h1,h2] <;> try omega
    exfalso
    have linfo : leftPigeon e ≠ i ∧ home (leftPigeon e) = e.1 := by
      by_cases hli : i = leftPigeon e
      · simp [intAssignment, hli] at h1
      · refine ⟨Ne.symm hli, ?_⟩
        by_contra hn
        simp [intAssignment, hli, hn] at h1
    have rinfo : rightPigeon e ≠ i ∧ home (rightPigeon e) = e.1 := by
      by_cases hri : i = rightPigeon e
      · simp [intAssignment, hri] at h2
      · refine ⟨Ne.symm hri, ?_⟩
        by_contra hn
        simp [intAssignment, hri, hn] at h2
    exact pair_distinct e (missingHome_unique i _ _ linfo.1 rinfo.1
      (r.injective (linfo.2.trans rinfo.2.symm)))

theorem collidingSlack (e : Collision) (r : Hole ≃ Hole) (fix : r e.1 = e.1) :
    CriticalSlack (intAssignment none (r ∘ collidingHome e)) (.inr e) := by
  let home := r ∘ collidingHome e
  have lhome : home (leftPigeon e) = e.1 := by
    simp [home, (collidingHome_at e _).2 (Or.inl rfl), fix]
  have rhome : home (rightPigeon e) = e.1 := by
    simp [home, (collidingHome_at e _).2 (Or.inr rfl), fix]
  refine ⟨intAssignment_bits _ _, ?_, ?_⟩
  · rw [collisionSlack]
    have leftAt : r (collidingHome e (leftPigeon e)) = e.1 := lhome
    have rightAt : r (collidingHome e (rightPigeon e)) = e.1 := rhome
    simp [intAssignment,leftAt,rightAt]
  · rintro (i | f) different
    · simp [pigeonSlack]
    · rw [collisionSlack]
      change 0 ≤ 1 - intAssignment none home (leftPigeon f,f.1) -
        intAssignment none home (rightPigeon f,f.1)
      have b1 := intAssignment_bits none home (leftPigeon f,f.1)
      have b2 := intAssignment_bits none home (rightPigeon f,f.1)
      rcases b1 with h1 | h1 <;> rcases b2 with h2 | h2 <;> rw [h1,h2] <;> try omega
      exfalso
      have linfo : home (leftPigeon f) = f.1 := by
        by_contra hn
        simp [intAssignment, hn] at h1
      have rinfo : home (rightPigeon f) = f.1 := by
        by_contra hn
        simp [intAssignment, hn] at h2
      have pairs := collidingHome_unique e _ _ (pair_distinct f)
        (r.injective (linfo.trans rinfo.symm))
      have eqPair : f.2 = e.2 := pair_id f e pairs
      have eqHole : f.1 = e.1 := by
        rcases pairs with ⟨h,_⟩ | ⟨h,_⟩
        · rw [h,lhome] at linfo
          exact linfo.symm
        · rw [h,rhome] at linfo
          exact linfo.symm
      exact different (congrArg Sum.inr (Prod.ext eqHole eqPair))

theorem witness_for_label (i : Label) : ∃ a : Var → ℤ, CriticalSlack a i := by
  cases i with
  | inl p => exact ⟨_, missingSlack p (Equiv.refl Hole)⟩
  | inr e => exact ⟨_, collidingSlack e (Equiv.refl Hole) rfl⟩

private theorem safe_missing : ∀ (i : Pigeon) (e : Collision), ∃ p : Pigeon,
    p ≠ i ∧ p ≠ leftPigeon e ∧ p ≠ rightPigeon e := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem safe_collision : ∀ e f : Collision, ∃ p : Pigeon,
    p ≠ leftPigeon e ∧ p ≠ rightPigeon e ∧ p ≠ leftPigeon f ∧ p ≠ rightPigeon f := by
  decide +kernel

theorem witness_pigeon_slack_collision (i : Pigeon) (e : Collision) :
    ∃ a : Var → ℤ, CriticalSlack a (.inl i) ∧ 1 ≤ slack a (labeledLine (.inr e)) := by
  obtain ⟨p, hi, hl, hr⟩ := safe_missing i e
  let r := Equiv.swap (missingHome i p) e.1
  let home := r ∘ missingHome i
  refine ⟨intAssignment (some i) home, missingSlack i r, ?_⟩
  have hhome : home p = e.1 := by simp [home,r]
  have notAt (q : Pigeon) (hne : p ≠ q) : intAssignment (some i) home (q,e.1) = 0 := by
    by_cases hq : q = i
    · simp [intAssignment, hq]
    · have hq' : home q ≠ e.1 := fun eq =>
        hne (missingHome_unique i _ _ hi hq (r.injective (hhome.trans eq.symm)))
      simp [intAssignment,hq']
  rw [collisionSlack, notAt _ hl, notAt _ hr]
  omega

private theorem witness_different_collision_holes (e f : Collision) (holes : e.1 ≠ f.1) :
    ∃ a : Var → ℤ, CriticalSlack a (.inr e) ∧ 1 ≤ slack a (labeledLine (.inr f)) := by
  obtain ⟨p,le,re,lf,rf⟩ := safe_collision e f
  let r := Equiv.swap (collidingHome e p) f.1
  let home := r ∘ collidingHome e
  have away : collidingHome e p ≠ e.1 := fun eq =>
    ((collidingHome_at e p).1 eq).elim le re
  have hfix : r e.1 = e.1 := by
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm away) holes
  have hhome : home p = f.1 := by simp [home,r]
  refine ⟨intAssignment none home, collidingSlack e r hfix, ?_⟩
  have notAt (q : Pigeon) (neq : p ≠ q) : intAssignment none home (q,f.1) = 0 := by
    have hq' : home q ≠ f.1 := by
      intro eq
      exact (collidingHome_unique e _ _ neq (r.injective (hhome.trans eq.symm))).elim
        (fun h => le h.1) (fun h => re h.1)
    simp [intAssignment,hq']
  rw [collisionSlack,notAt _ lf,notAt _ rf]
  omega

theorem witness_incompatible_collisions (e f : Collision) (h : incompatible e f) :
    ∃ a : Var → ℤ, CriticalSlack a (.inr e) ∧ 1 ≤ slack a (labeledLine (.inr f)) := by
  by_cases holes : e.1 ≠ f.1
  · exact witness_different_collision_holes e f holes
  · obtain ⟨ll,lr,rl,rr⟩ := h.resolve_left holes
    have eq : e.1 = f.1 := not_ne_iff.mp holes
    have hL : collidingHome e (leftPigeon f) ≠ f.1 := by
      rw [← eq]
      exact fun he => ((collidingHome_at e _).1 he).elim (Ne.symm ll) (Ne.symm rl)
    have hR : collidingHome e (rightPigeon f) ≠ f.1 := by
      rw [← eq]
      exact fun he => ((collidingHome_at e _).1 he).elim (Ne.symm lr) (Ne.symm rr)
    refine ⟨intAssignment none (collidingHome e), collidingSlack e (Equiv.refl Hole) rfl, ?_⟩
    simp [collisionSlack,intAssignment,hL,hR]

theorem labeledLine_injective : Function.Injective labeledLine := by
  intro i j eq
  by_contra ne
  obtain ⟨a, _, bad, good⟩ := witness_for_label i
  have h := good j (Ne.symm ne)
  rw [← eq, bad] at h
  omega

def asBoolean (a : Var → ℤ) (v : Var) : Bool := decide (a v = 1)

theorem bits_to_boolean (a : Var → ℤ) (bits : ∀ v, a v = 0 ∨ a v = 1) (v : Var) :
    (if asBoolean a v then (1 : ℤ) else 0) = a v := by
  rcases bits v with h | h <;> simp [asBoolean,h]

theorem holds_iff_nonnegative_slack (a : Var → ℤ) (bits : ∀ v, a v = 0 ∨ a v = 1)
    (line : CPLine Var) : line.Holds (asBoolean a) ↔ 0 ≤ slack a line := by
  unfold CPLine.Holds slack
  simp only [bits_to_boolean a bits]
  omega


end PEqualNP.Outside.L_meta_9693.Critical



namespace PEqualNP.Outside.L_meta_9693_aux

open PEqualNP.Search PEqualNP.ProofComplexity

abbrev V := Fin 5 × Fin 4
abbrev Line := CPLine V
abbrev F := PHP 5 4

def lineAt (π : List Line) (i : Fin π.length) : Line := π.get i

def sourceLo (v : V) : Line := (fun u => if u = v then 1 else 0, 0)

def sourceHi (v : V) : Line := (fun u => if u = v then -1 else 0, -1)

def Source (e : Line) : Prop :=
  (∃ C ∈ F, e = clauseCP C) ∨ (∃ v, e = sourceLo v) ∨ (∃ v, e = sourceHi v)

def Local (e : Line) : List Line → Prop
  | [] => Source e
  | [a] => ∀ x : V → Bool, a.Holds x → e.Holds x
  | [a, b] => e = (a.1 + b.1, a.2 + b.2)
  | _ => False

structure Replay (π : List Line) where
  uses : Fin π.length → List (Fin π.length)
  later : ∀ i j, j ∈ uses i → i.val < j.val
  rules : ∀ i, Local (lineAt π i) ((uses i).map (lineAt π))

theorem mulHolds (a : V → Bool) (e : Line) (k : ℕ) (h : e.Holds a) :
    CPLine.Holds a (((k : ℤ) • e.1, (k : ℤ) * e.2) : Line) := by
  unfold CPLine.Holds at *
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem divHolds (a : V → Bool) (e : Line) (d : ℕ) (hd : 0 < d)
    (hdiv : ∀ v, (d : ℤ) ∣ e.1 v) (h : e.Holds a) :
    CPLine.Holds a ((fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ))) : Line) := by
  unfold CPLine.Holds at *
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have hsum : ∑ v, e.1 v * (if a v then 1 else 0) =
      (d : ℤ) * ∑ v, e.1 v / (d : ℤ) * (if a v then 1 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [← mul_assoc, Int.mul_ediv_cancel' (hdiv v)]
  simp only
  have hlead : (-(∑ v, e.1 v / (d : ℤ) * (if a v then 1 else 0))) * d ≤ -e.2 := by
    rw [hsum] at h
    linarith
  have hquot := (Int.le_ediv_iff_mul_le hd').mpr hlead
  linarith

def Replay.push {π : List Line} (r : Replay π) (e : Line)
    (parents : List (Fin π.length)) (rule : Local e (parents.map (lineAt π))) :
    Replay (e :: π) where
  uses := Fin.cases (parents.map Fin.succ) (fun i => (r.uses i).map Fin.succ)
  later := by
    intro i
    refine Fin.cases ?_ ?_ i
    · intro j hj
      change j ∈ parents.map Fin.succ at hj
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hj
      exact Nat.zero_lt_succ k.val
    · intro i j hj
      change j ∈ (r.uses i).map Fin.succ at hj
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
      exact Nat.succ_lt_succ (r.later i k hk)
  rules := by
    intro i
    refine Fin.cases ?_ ?_ i
    · change Local e (((parents.map Fin.succ).map (lineAt (e :: π))))
      rw [List.map_map]
      change Local e (parents.map (lineAt π))
      exact rule
    · intro i
      change Local (lineAt π i) (((r.uses i).map Fin.succ).map (lineAt (e :: π)))
      rw [List.map_map]
      change Local (lineAt π i) ((r.uses i).map (lineAt π))
      exact r.rules i

theorem replay_of_derivation {π : List Line} (h : IsCPDerivation F π) :
    Nonempty (Replay π) := by
  induction h with
  | nil =>
    refine ⟨⟨fun i => Fin.elim0 i, ?_, ?_⟩⟩
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
  | ax C _ hC ih =>
    obtain ⟨r⟩ := ih
    exact ⟨r.push (clauseCP C) [] (Or.inl ⟨C, hC, rfl⟩)⟩
  | boolLo v _ ih =>
    obtain ⟨r⟩ := ih
    exact ⟨r.push (sourceLo v) [] (Or.inr (Or.inl ⟨v, rfl⟩))⟩
  | boolHi v _ ih =>
    obtain ⟨r⟩ := ih
    exact ⟨r.push (sourceHi v) [] (Or.inr (Or.inr ⟨v, rfl⟩))⟩
  | @add π e f _ he hf ih =>
    obtain ⟨r⟩ := ih
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp he
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hf
    refine ⟨r.push (e.1 + f.1, e.2 + f.2) [i, j] ?_⟩
    change (e.1 + f.1, e.2 + f.2) = ((π.get i).1 + (π.get j).1, (π.get i).2 + (π.get j).2)
    rw [hi, hj]
  | @mul π e k _ he ih =>
    obtain ⟨r⟩ := ih
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp he
    refine ⟨r.push (((k : ℤ) • e.1), (k : ℤ) * e.2) [i] ?_⟩
    change ∀ a : V → Bool, (π.get i).Holds a → _
    rw [hi]
    exact fun a => mulHolds a e k
  | @div π e d _ he hd hdiv ih =>
    obtain ⟨r⟩ := ih
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp he
    refine ⟨r.push ((fun v => e.1 v / (d : ℤ)), -((-e.2) / (d : ℤ))) [i] ?_⟩
    change ∀ a : V → Bool, (π.get i).Holds a → _
    rw [hi]
    exact fun a => divHolds a e d hd hdiv

def margin (a : V → Bool) (e : Line) : ℤ :=
  (∑ v, e.1 v * (if a v then 1 else 0)) - e.2

theorem holds_iff_margin (a : V → Bool) (e : Line) : e.Holds a ↔ 0 ≤ margin a e := by
  exact (sub_nonneg).symm

theorem margin_add (a : V → Bool) (e f : Line) :
    margin a (e.1 + f.1, e.2 + f.2) = margin a e + margin a f := by
  simp only [margin, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem boolLoHolds (a : V → Bool) (v : V) : CPLine.Holds a (sourceLo v) := by
  unfold CPLine.Holds sourceLo
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  split_ifs <;> simp

theorem boolHiHolds (a : V → Bool) (v : V) : CPLine.Holds a (sourceHi v) := by
  unfold CPLine.Holds sourceHi
  simp only [ite_mul, neg_one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  split_ifs <;> simp

end PEqualNP.Outside.L_meta_9693_aux


namespace PEqualNP.Outside.L_meta_9693_aux

open scoped BigOperators

structure Graph (I : Type) [Fintype I] where
  rank : I → ℕ
  root : I
  inputs : I → List I
  earlier : ∀ i j, j ∈ inputs i → rank i < rank j
  arity : ∀ i, (inputs i).length ≤ 2
  connected : ∀ i, Relation.ReflTransGen (fun x y => y ∈ inputs x) root i

namespace Graph

variable {I : Type} [Fintype I] [DecidableEq I] (G : Graph I)

def degree (i : I) : ℕ := ∑ j : I, (G.inputs j).count i

def aritySet (n : ℕ) : Finset I := Finset.univ.filter fun i => (G.inputs i).length = n

/-- A singly used premise of a binary addition. -/
def Smooth (a b : I) : Prop :=
  G.degree a = 1 ∧ (G.inputs b).length = 2 ∧ a ∈ G.inputs b

noncomputable def boundary : Finset I := by
  classical
  exact Finset.univ.filter fun a => ¬ ∃ b, G.Smooth a b

theorem mem_boundary (a : I) : a ∈ G.boundary ↔ ¬ ∃ b, G.Smooth a b := by
  classical
  simp [boundary]

theorem reach_rank {a b : I}
    (h : Relation.ReflTransGen (fun x y => y ∈ G.inputs x) a b) :
    G.rank a ≤ G.rank b := by
  induction h with
  | refl => exact le_rfl
  | tail _ edge ih => exact ih.trans (Nat.le_of_lt (G.earlier _ _ edge))

theorem root_degree : G.degree G.root = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply List.count_eq_zero_of_not_mem
  intro h
  exact (Nat.not_lt_of_ge (G.reach_rank (G.connected i))) (G.earlier _ _ h)

theorem member_le_degree {i j : I} (h : j ∈ G.inputs i) : 1 ≤ G.degree j := by
  have present := List.count_pos_iff.mpr h
  exact (show 1 ≤ (G.inputs i).count j by omega).trans
    (Finset.single_le_sum (f := fun k => (G.inputs k).count j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))

theorem nonroot_degree (i : I) (h : i ≠ G.root) : 1 ≤ G.degree i := by
  rcases (G.connected i).cases_tail with eq | ⟨j, _, edge⟩
  · exact (h eq).elim
  · exact G.member_le_degree edge

theorem count_le_degree (i j : I) : (G.inputs i).count j ≤ G.degree j :=
  Finset.single_le_sum (f := fun k => (G.inputs k).count j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem degree_one_consumer {a b c : I} (one : G.degree a = 1)
    (hb : a ∈ G.inputs b) (hc : a ∈ G.inputs c) : b = c := by
  by_contra diff
  have hbcount := List.count_pos_iff.mpr hb
  have hccount := List.count_pos_iff.mpr hc
  have bound : (∑ i ∈ ({b,c} : Finset I), (G.inputs i).count a) ≤ G.degree a :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Finset.sum_pair diff, one] at bound
  omega

theorem smooth_unique {a b c : I} (hb : G.Smooth a b) (hc : G.Smooth a c) : b = c :=
  G.degree_one_consumer hb.1 hb.2.2 hc.2.2

theorem smooth_decreases {a b : I} (h : G.Smooth a b) : G.rank b < G.rank a :=
  G.earlier _ _ h.2.2

private theorem sumCounts (s : List I) : (∑ i : I, s.count i) = s.length := by
  induction s with
  | nil => simp
  | cons a as ih =>
    simp only [List.count_cons, List.length_cons]
    rw [Finset.sum_add_distrib, ih]
    simp [beq_iff_eq]

theorem sum_degree : (∑ i : I, G.degree i) = ∑ i : I, (G.inputs i).length := by
  unfold degree
  rw [Finset.sum_comm]
  simp only [sumCounts]

def surplus : ℕ := ∑ i : I, (G.degree i - 1)

theorem sum_degree_surplus :
    (∑ i : I, G.degree i) + 1 = G.surplus + Fintype.card I := by
  classical
  have each (i : I) : G.degree i = (G.degree i - 1) + (if i = G.root then 0 else 1) := by
    by_cases hi : i = G.root
    · subst i
      simp [G.root_degree]
    · simp only [if_neg hi]
      have h := G.nonroot_degree i hi
      omega
  have total := Finset.sum_congr (s₁ := (Finset.univ : Finset I)) rfl (fun i _ => each i)
  rw [Finset.sum_add_distrib] at total
  have rest : (∑ i : I, if i = G.root then (0 : ℕ) else 1) + 1 = Fintype.card I := by
    let low := ∑ i : I, if i = G.root then (0 : ℕ) else 1
    let high := ∑ i : I, if i = G.root then (1 : ℕ) else 0
    have digit : high = 1 := by simp [high]
    have one (i : I) : (if i = G.root then (0 : ℕ) else 1) +
          (if i = G.root then (1 : ℕ) else 0) = 1 := by
      by_cases h : i = G.root
      · simp only [if_pos h, Nat.zero_add]
      · simp only [if_neg h, Nat.add_zero]
    change low + 1 = _
    calc
      low + 1 = low + high := congrArg (fun k => low + k) digit.symm
      _ = _ := by
        dsimp only [low, high]
        rw [← Finset.sum_add_distrib]
        simp_rw [one]
        simp
  unfold surplus
  rw [total, Nat.add_assoc, rest]

private theorem length_sum :
    (∑ i : I, (G.inputs i).length) = (G.aritySet 1).card + 2 * (G.aritySet 2).card := by
  classical
  have each (i : I) : (G.inputs i).length =
      (if (G.inputs i).length = 1 then 1 else 0) +
        2 * (if (G.inputs i).length = 2 then 1 else 0) := by
    have h := G.arity i
    interval_cases hlen : (G.inputs i).length <;> decide
  have total := Finset.sum_congr (s₁ := (Finset.univ : Finset I)) rfl (fun i _ => each i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at total
  simpa only [aritySet, Finset.card_filter] using total

private theorem cardinal_arities :
    Fintype.card I = (G.aritySet 0).card + (G.aritySet 1).card + (G.aritySet 2).card := by
  classical
  have each (i : I) : (1 : ℕ) =
      (if (G.inputs i).length = 0 then 1 else 0) +
        (if (G.inputs i).length = 1 then 1 else 0) +
        (if (G.inputs i).length = 2 then 1 else 0) := by
    have h := G.arity i
    interval_cases hlen : (G.inputs i).length <;> decide
  have total := Finset.sum_congr (s₁ := (Finset.univ : Finset I)) rfl (fun i _ => each i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at total
  have card : (∑ _ : I, (1 : ℕ)) = Fintype.card I := by simp
  rw [card] at total
  simpa only [aritySet, Finset.card_filter] using total

def shared : Finset I := Finset.univ.filter fun i => 2 ≤ G.degree i

def unaryInputs : Finset I := (G.aritySet 1).biUnion fun i => (G.inputs i).toFinset

theorem shared_le : G.shared.card ≤ G.surplus := by
  calc
    G.shared.card = ∑ _ ∈ G.shared, (1 : ℕ) := by simp
    _ ≤ ∑ i ∈ G.shared, (G.degree i - 1) := by
      apply Finset.sum_le_sum
      intro i hi
      have h : 2 ≤ G.degree i := (Finset.mem_filter.mp hi).2
      omega
    _ ≤ G.surplus := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem unary_le : G.unaryInputs.card ≤ (G.aritySet 1).card := by
  classical
  calc
    G.unaryInputs.card ≤ ∑ i ∈ G.aritySet 1, (G.inputs i).toFinset.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ G.aritySet 1, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro i hi
      have h : (G.inputs i).length = 1 := (Finset.mem_filter.mp hi).2
      obtain ⟨j, eq⟩ := List.length_eq_one_iff.mp h
      simp [eq]
    _ = (G.aritySet 1).card := by simp

theorem boundary_subset : G.boundary ⊆ (insert G.root (G.shared ∪ G.unaryInputs)) := by
  classical
  intro i hi
  rw [Finset.mem_insert, Finset.mem_union]
  by_cases root : i = G.root
  · exact Or.inl root
  right
  have positive := G.nonroot_degree i root
  by_cases many : 2 ≤ G.degree i
  · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, many⟩)
  right
  have one : G.degree i = 1 := by omega
  rcases (G.connected i).cases_tail with eq | ⟨j, _, used⟩
  · exact (root eq).elim
  have notTwo : (G.inputs j).length ≠ 2 := by
    intro two
    exact (G.mem_boundary i).mp hi ⟨j, one, two, used⟩
  have ne : G.inputs j ≠ [] := List.ne_nil_of_mem used
  have oneInput : (G.inputs j).length = 1 := by
    have cap := G.arity j
    have pos : 0 < (G.inputs j).length := List.length_pos_iff.mpr ne
    omega
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _,oneInput⟩,
    List.mem_toFinset.mpr used⟩

theorem boundary_budget :
    2 * (G.aritySet 0).card + G.boundary.card ≤ Fintype.card I + 2 := by
  have laws := G.sum_degree_surplus
  rw [G.sum_degree, G.length_sum, G.cardinal_arities] at laws
  have bound :
      G.boundary.card ≤ 1 + G.surplus + (G.aritySet 1).card := by
    have subset := Finset.card_le_card G.boundary_subset
    have insertion := Finset.card_insert_le (a := G.root) (s := G.shared ∪ G.unaryInputs)
    have union := Finset.card_union_le (s := G.shared) (t := G.unaryInputs)
    have s := G.shared_le
    have u := G.unary_le
    omega
  rw [G.cardinal_arities]
  omega

end Graph

end PEqualNP.Outside.L_meta_9693_aux

namespace PEqualNP.Outside.L_meta_9693_aux

open Relation

variable {π : List Line}

abbrev Reach (r : Replay π) (root : Fin π.length) :=
  { i : Fin π.length // ReflTransGen (fun x y => y ∈ r.uses x) root i }

noncomputable instance reachFintype (r : Replay π) (root : Fin π.length) :
    Fintype (Reach r root) := Fintype.ofFinite _

def trimmedInputs (r : Replay π) (root : Fin π.length) (i : Reach r root) :
    List (Reach r root) :=
  (r.uses i.val).attach.map fun parent => ⟨parent.val, i.property.tail parent.property⟩

theorem trimmedInputs_values (r : Replay π) (root : Fin π.length) (i : Reach r root) :
    (trimmedInputs r root i).map Subtype.val = r.uses i.val := by
  simp [trimmedInputs, List.map_map, Function.comp_def]

theorem trimmedInputs_mem (r : Replay π) (root : Fin π.length) (i j : Reach r root) :
    j ∈ trimmedInputs r root i ↔ j.val ∈ r.uses i.val := by
  constructor
  · intro hj
    have member := List.mem_map_of_mem (f := Subtype.val) hj
    simpa only [trimmedInputs_values] using member
  · intro hj
    refine List.mem_map.mpr ⟨⟨j.val, hj⟩, ?_, ?_⟩
    · simp
    · exact Subtype.ext rfl

theorem trimmedInputs_length (r : Replay π) (root : Fin π.length) (i : Reach r root) :
    (trimmedInputs r root i).length = (r.uses i.val).length := by
  simpa only [List.length_map] using congrArg List.length (trimmedInputs_values r root i)

theorem local_arity {e : Line} {parents : List Line} (h : Local e parents) : parents.length ≤ 2 := by
  rcases parents with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
  · simp
  · simp
  · simp
  · exact False.elim h

theorem trim_connected (r : Replay π) (root : Fin π.length) {i : Fin π.length}
    (h : ReflTransGen (fun x y => y ∈ r.uses x) root i) :
    ReflTransGen (fun x y => y ∈ trimmedInputs r root x)
      (⟨root, ReflTransGen.refl⟩ : Reach r root) ⟨i, h⟩ := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail prior edge ih =>
    refine ih.tail ?_
    exact (trimmedInputs_mem _ _ _ _).mpr edge

def trimGraph (r : Replay π) (root : Fin π.length) : Graph (Reach r root) where
  rank i := i.val.val
  root := ⟨root, ReflTransGen.refl⟩
  inputs := trimmedInputs r root
  earlier := fun i j hj => r.later i.val j.val ((trimmedInputs_mem _ _ _ _).mp hj)
  arity := by
    intro i
    rw [trimmedInputs_length]
    simpa only [List.length_map] using local_arity (r.rules i.val)
  connected := fun i => trim_connected r root i.property

theorem reach_card_le (r : Replay π) (root : Fin π.length) :
    Fintype.card (Reach r root) ≤ π.length := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
    (fun i : Reach r root => i.val) Subtype.val_injective

theorem trimGraph_rules (r : Replay π) (root : Fin π.length) (i : Reach r root) :
    Local (lineAt π i.val) (((trimGraph r root).inputs i).map fun j => lineAt π j.val) := by
  change Local (lineAt π i.val) ((trimmedInputs r root i).map fun j => lineAt π j.val)
  rw [show (trimmedInputs r root i).map (fun j => lineAt π j.val) =
      ((trimmedInputs r root i).map Subtype.val).map (lineAt π) by rw [List.map_map]; rfl,
    trimmedInputs_values]
  exact r.rules i.val

end PEqualNP.Outside.L_meta_9693_aux

namespace PEqualNP.Outside.L_meta_9693_aux.Graph

open scoped Classical

variable {I : Type} [Fintype I] [DecidableEq I] (G : Graph I)

abbrev Path (a b : I) := Relation.ReflTransGen G.Smooth a b

theorem path_rank {a b : I} (h : G.Path a b) : G.rank b ≤ G.rank a := by
  induction h with
  | refl => exact le_rfl
  | tail _ edge ih => exact (Nat.le_of_lt (G.smooth_decreases edge)).trans ih

theorem compare_paths {a b c : I} (hb : G.Path a b) (hc : G.Path a c) :
    G.Path b c ∨ G.Path c b :=
  Relation.ReflTransGen.total_of_right_unique (fun _ _ _ hb hc => G.smooth_unique hb hc) hb hc

theorem boundary_terminal {a b : I} (hb : a ∈ G.boundary) (p : G.Path a b) : a = b := by
  rcases p.cases_head with h | ⟨c, hc, _⟩
  · exact h
  · exact ((G.mem_boundary a).mp hb ⟨c, hc⟩).elim

theorem exists_boundary (a : I) : ∃ b ∈ G.boundary, G.Path a b := by
  classical
  induction a using (measure G.rank).wf.induction with
  | h a ih =>
    by_cases stop : a ∈ G.boundary
    · exact ⟨a, stop, .refl⟩
    · obtain ⟨b, ab⟩ : ∃ b, G.Smooth a b := by
        by_contra! none
        exact stop ((G.mem_boundary a).mpr (fun ⟨b, ab⟩ => none b ab))
      obtain ⟨c, inside, bc⟩ := ih b (G.smooth_decreases ab)
      exact ⟨c, inside, bc.head ab⟩

noncomputable def group (a : I) : I := Classical.choose (G.exists_boundary a)

theorem group_mem (a : I) : G.group a ∈ G.boundary :=
  (Classical.choose_spec (G.exists_boundary a)).1

theorem group_path (a : I) : G.Path a (G.group a) :=
  (Classical.choose_spec (G.exists_boundary a)).2

theorem boundary_path_iff {a b : I} (hb : b ∈ G.boundary) :
    G.Path a b ↔ G.group a = b := by
  constructor
  · intro h
    rcases G.compare_paths (G.group_path a) h with h₁ | h₂
    · exact G.boundary_terminal (G.group_mem a) h₁
    · exact (G.boundary_terminal hb h₂).symm
  · rintro rfl
    exact G.group_path a

theorem root_boundary : G.root ∈ G.boundary := by
  apply (G.mem_boundary G.root).mpr
  rintro ⟨i, hi⟩
  have h := hi.1
  rw [G.root_degree] at h
  omega

noncomputable def chip (a i : I) : ℤ := by
  classical
  exact if G.Path a i then 1 else 0

private theorem path_into_two {a i p q : I} (isSource : G.inputs a = [])
    (shape : G.inputs i = [p,q]) :
    G.Path a i ↔ (G.Path a p ∧ G.Smooth p i) ∨ (G.Path a q ∧ G.Smooth q i) := by
  constructor
  · intro reach
    rcases reach.cases_tail with eq | ⟨b, hb, step⟩
    · subst i
      simp [isSource] at shape
    · have used := step.2.2
      rw [shape] at used
      simp only [List.mem_cons, List.not_mem_nil, or_false] at used
      rcases used with rfl | rfl
      · exact Or.inl ⟨hb, step⟩
      · exact Or.inr ⟨hb, step⟩
  · rintro (⟨reach,step⟩ | ⟨reach,step⟩) <;> exact reach.tail step

private theorem inputs_paths_disjoint {a i p q : I} (shape : G.inputs i = [p,q])
    (hp : G.Path a p ∧ G.Smooth p i) (hq : G.Path a q ∧ G.Smooth q i) : False := by
  have distinct : p ≠ q := by
    rintro rfl
    have count := G.count_le_degree i p
    simp [shape, hp.2.1] at count
  have impossible {x y : I} (xy : x ≠ y) (hx : G.Smooth x i) (hy : G.Smooth y i)
      (path : G.Path x y) : False := by
    rcases path.cases_head with eq | ⟨c, xToC, cToY⟩
    · exact xy eq
    have eq := G.smooth_unique hx xToC
    subst c
    exact (Nat.not_lt_of_ge (G.path_rank cToY)) (G.smooth_decreases hy)
  rcases G.compare_paths hp.1 hq.1 with order | order
  · exact impossible distinct hp.2 hq.2 order
  · exact impossible (Ne.symm distinct) hq.2 hp.2 order

theorem chip_two {a i p q : I} (source : G.inputs a = []) (shape : G.inputs i = [p,q]) :
    G.chip a i = (if G.Smooth p i then G.chip a p else 0) +
      (if G.Smooth q i then G.chip a q else 0) := by
  classical
  have path := G.path_into_two source shape
  by_cases hp : G.Path a p <;> by_cases hq : G.Path a q <;>
    by_cases sp : G.Smooth p i <;> by_cases sq : G.Smooth q i
  all_goals try exact (G.inputs_paths_disjoint shape ⟨hp, sp⟩ ⟨hq, sq⟩).elim
  all_goals simp [chip, path, hp, hq, sp, sq]

theorem parent_not_smooth {p i : I} (hi : p ∈ G.inputs i) (bad : ¬ G.Smooth p i) :
    p ∈ G.boundary := by
  apply (G.mem_boundary p).mpr
  rintro ⟨j, hj⟩
  have eq := G.degree_one_consumer hj.1 hi hj.2.2
  exact bad (eq.symm ▸ hj)

theorem chip_at_terminal {a i : I} (stop : i ∈ G.boundary) :
    G.chip a i = if G.group a = i then 1 else 0 := by
  classical
  simp [chip, G.boundary_path_iff stop]

theorem chip_at_nonbinary {a i : I} (nonbinary : (G.inputs i).length ≠ 2) :
    G.chip a i = if a = i then 1 else 0 := by
  classical
  have paths : G.Path a i ↔ a = i := by
    constructor
    · intro p
      rcases p.cases_tail with eq | ⟨j, _, step⟩
      · exact eq.symm
      · exact (nonbinary step.2.1).elim
    · rintro rfl
      exact .refl
  simp [chip, paths]

structure Margin (w : I → ℤ) : Prop where
  one : ∀ i p, G.inputs i = [p] → 0 ≤ w p → 0 ≤ w i
  two : ∀ i p q, G.inputs i = [p,q] → w i = w p + w q

theorem nonneg_of_sources {w : I → ℤ} (valid : G.Margin w)
    (allSources : ∀ i, G.inputs i = [] → 0 ≤ w i) (i : I) : 0 ≤ w i := by
  let cap := Finset.univ.sup G.rank
  have rankLe (p : I) : G.rank p ≤ cap := Finset.le_sup (Finset.mem_univ p)
  induction i using (measure (fun i => cap - G.rank i)).wf.induction with
  | h i ih =>
    have earlierValid (p : I) (used : p ∈ G.inputs i) : 0 ≤ w p := by
      apply ih p
      change cap - G.rank p < cap - G.rank i
      have lt := G.earlier i p used
      have le := rankLe p
      omega
    cases e : G.inputs i with
    | nil => exact allSources i e
    | cons p tail =>
      have posP := earlierValid p (by simp [e])
      cases tail with
      | nil => exact valid.one i p e posP
      | cons q rest =>
        cases rest with
        | nil =>
          rw [valid.two i p q e]
          exact add_nonneg posP (earlierValid q (by simp [e]))
        | cons s tail =>
          have cap := G.arity i
          simp [e] at cap

/-- Unit slack adjustments along the two paths cancel at their common boundary. -/
theorem compatible_group {w : I → ℤ} (valid : G.Margin w) (badRoot : w G.root < 0)
    {a b : I} (sourceA : G.inputs a = []) (sourceB : G.inputs b = [])
    (badA : w a = -1) (goodB : 1 ≤ w b)
    (others : ∀ i, G.inputs i = [] → i ≠ a → 0 ≤ w i) :
    G.group a ≠ G.group b := by
  classical
  intro same
  have neq : a ≠ b := by rintro rfl; omega
  let d (i : I) := G.chip a i - G.chip b i
  have zeroAt (i : I) (hi : i ∈ G.boundary) : d i = 0 := by
    simp [d, G.chip_at_terminal hi, same]
  let fixed (i : I) := w i + d i
  have fixedValid : G.Margin fixed := by
    constructor
    · intro i p shape inp
      have parentBoundary : p ∈ G.boundary := G.parent_not_smooth (p := p) (i := i)
        (by simp [shape]) (fun h => by
          have impossible := h.2.1
          simp [shape] at impossible)
      have pZero := zeroAt p parentBoundary
      have iZero : d i = 0 := by
        have notA : a ≠ i := by rintro rfl; simp [sourceA] at shape
        have notB : b ≠ i := by rintro rfl; simp [sourceB] at shape
        simp [d, G.chip_at_nonbinary (i := i) (by simp [shape]), notA, notB]
      unfold fixed at *
      rw [pZero, add_zero] at inp
      rw [iZero, add_zero]
      exact valid.one i p shape inp
    · intro i p q shape
      have hA := G.chip_two sourceA shape
      have hB := G.chip_two sourceB shape
      have delta : d i = d p + d q := by
        unfold d
        by_cases hp : G.Smooth p i <;> by_cases hq : G.Smooth q i
        all_goals simp [hp, hq] at hA hB
        all_goals try have pZero := zeroAt p (G.parent_not_smooth (i := i) (by simp [shape]) hp)
        all_goals try have qZero := zeroAt q (G.parent_not_smooth (i := i) (by simp [shape]) hq)
        all_goals dsimp [d] at *
        all_goals omega
      unfold fixed
      rw [valid.two i p q shape, delta]
      omega
  have fixedSource (i : I) (src : G.inputs i = []) : 0 ≤ fixed i := by
    have notBinary : (G.inputs i).length ≠ 2 := by simp [src]
    have ha := G.chip_at_nonbinary (a := a) notBinary
    have hb := G.chip_at_nonbinary (a := b) notBinary
    by_cases ia : i = a
    · subst i
      have ne' := Ne.symm neq
      simp [fixed, d, ha, hb, ne', badA]
    · have good := others i src ia
      by_cases ib : i = b
      · subst i
        simp [fixed, d, ha, hb, neq]
        omega
      · simp [fixed, d, ha, hb, Ne.symm ia, Ne.symm ib, good]
  have contradiction := G.nonneg_of_sources fixedValid fixedSource G.root
  have h := zeroAt G.root G.root_boundary
  dsimp [fixed] at contradiction
  omega

end PEqualNP.Outside.L_meta_9693_aux.Graph


namespace PEqualNP.Outside.L_meta_9693_aux

abbrev CollisionLabel := Fin 4 × Fin 10

def pigeonPair : Fin 10 → Fin 5 × Fin 5 :=
  ![(0,1), (0,2), (0,3), (0,4), (1,2), (1,3), (1,4), (2,3), (2,4), (3,4)]

def pairsIntersect (a b : Fin 10) : Prop :=
  (pigeonPair a).1 = (pigeonPair b).1 ∨ (pigeonPair a).1 = (pigeonPair b).2 ∨
  (pigeonPair a).2 = (pigeonPair b).1 ∨ (pigeonPair a).2 = (pigeonPair b).2

instance (a b : Fin 10) : Decidable (pairsIntersect a b) := by
  unfold pairsIntersect
  infer_instance

private def commonPairs (a b : Fin 10) : Finset (Fin 10) :=
  Finset.univ.filter fun c => pairsIntersect c a ∧ pairsIntersect c b

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem commonPairsBound : ∀ a b : Fin 10, a ≠ b → pairsIntersect a b →
    (commonPairs a b).card ≤ 5 ∧
      ∃ c ∈ commonPairs a b, ∃ d ∈ commonPairs a b, ¬ pairsIntersect c d := by
  decide +kernel

theorem intersectingPairsCard (s : Finset (Fin 10))
    (h : ∀ a ∈ s, ∀ b ∈ s, pairsIntersect a b) : s.card ≤ 4 := by
  by_contra! hc
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (show 1 < s.card by omega)
  have sub : s ⊆ commonPairs a b := by
    intro c hc
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h c hc a ha, h c hc b hb⟩
  obtain ⟨cap, c, hc', d, hd, hcd⟩ := commonPairsBound a b hab (h a ha b hb)
  have same : s = commonPairs a b := Finset.eq_of_subset_of_card_le sub (by omega)
  exact hcd (h c (same.symm ▸ hc') d (same.symm ▸ hd))

private theorem pigeonPairSelf (a : Fin 10) : pairsIntersect a a := Or.inl rfl

theorem count_group_lines {G : Type*} [DecidableEq G]
    (groups : Finset G) (unique : Finset CollisionLabel) (group : CollisionLabel → G)
    (extraAxioms lines : ℕ)
    (hCost : 88 + 2 * extraAxioms + groups.card ≤ lines)
    (hUnique : 40 ≤ unique.card + extraAxioms)
    (hGroup : ∀ c ∈ unique, group c ∈ groups)
    (hPair : ∀ c ∈ unique, ∀ d ∈ unique, group c = group d → c ≠ d →
      c.1 = d.1 ∧ pairsIntersect c.2 d.2)
    (hPigeon : extraAxioms = 0 → ∃ g ∈ groups, ∀ c ∈ unique, group c ≠ g) :
    101 ≤ lines := by
  classical
  by_contra! short
  have globalCap (g : G) : (unique.filter fun c => group c = g).card ≤ 4 := by
    let fiber := unique.filter fun c => group c = g
    have sameHole {a b : CollisionLabel} (ha : a ∈ fiber) (hb : b ∈ fiber) : a.1 = b.1 := by
      by_cases eq : a = b
      · rw [eq]
      · have aIn := Finset.mem_filter.1 ha
        have bIn := Finset.mem_filter.1 hb
        exact (hPair a aIn.1 b bIn.1 (aIn.2.trans bIn.2.symm) eq).1
    have inj : Set.InjOn Prod.snd (fiber : Set CollisionLabel) := by
      intro a ha b hb eq
      exact Prod.ext (sameHole ha hb) eq
    change fiber.card ≤ 4
    rw [← Finset.card_image_of_injOn inj]
    apply intersectingPairsCard
    intro a ha b hb
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hb
    by_cases eq : c = d
    · subst d
      exact pigeonPairSelf c.2
    have cIn := Finset.mem_filter.1 hc
    have dIn := Finset.mem_filter.1 hd
    exact (hPair c cIn.1 d dIn.1 (cIn.2.trans dIn.2.symm) eq).2
  have uniqueCap : unique.card ≤ 4 * groups.card := by
    rw [Finset.card_eq_sum_card_fiberwise hGroup]
    calc
      _ ≤ ∑ _g ∈ groups, (4 : ℕ) := Finset.sum_le_sum fun g _ => globalCap g
      _ = _ := by simp [Nat.mul_comm]
  have extraAtMostOne : extraAxioms ≤ 1 := by omega
  let inHole (h : Fin 4) := (Finset.univ : Finset (Fin 10)).filter fun e => (h,e) ∈ unique
  let holeGroups (h : Fin 4) := (inHole h).image fun e => group (h,e)
  have inHoleMany (h : Fin 4) : 9 ≤ (inHole h).card := by
    let missing := (Finset.univ : Finset CollisionLabel) \ unique
    have missingCard : missing.card ≤ extraAxioms := by
      dsimp [missing]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
      omega
    let missingHere := (Finset.univ : Finset (Fin 10)) \ inHole h
    have hereCap : missingHere.card ≤ missing.card := by
      apply Finset.card_le_card_of_injOn (fun e => (h,e))
      · intro e he
        have hm := (Finset.mem_sdiff.1 he).2
        simp [missing, inHole] at hm ⊢
        exact hm
      · intro a _ b _ eq
        exact congrArg Prod.snd eq
    dsimp [missingHere] at hereCap
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)] at hereCap
    simp only [Finset.card_univ, Fintype.card_fin] at hereCap
    omega
  have holeGroupsMany (h : Fin 4) : 3 ≤ (holeGroups h).card := by
    have bound : (inHole h).card ≤ 4 * (holeGroups h).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := fun e => group (h,e))
        (t := holeGroups h) (fun e he => Finset.mem_image_of_mem _ he)]
      calc
        _ ≤ ∑ _g ∈ holeGroups h, (4 : ℕ) := by
          apply Finset.sum_le_sum
          intro g _
          apply intersectingPairsCard
          intro a ha b hb
          by_cases eq : a = b
          · subst b
            exact pigeonPairSelf a
          have aIn := Finset.mem_filter.1 ha
          have bIn := Finset.mem_filter.1 hb
          exact (hPair (h,a) (Finset.mem_filter.1 aIn.1).2
            (h,b) (Finset.mem_filter.1 bIn.1).2 (aIn.2.trans bIn.2.symm)
            (fun hab => eq (congrArg Prod.snd hab))).2
        _ = _ := by simp [Nat.mul_comm]
    have := inHoleMany h
    omega
  let allCollisionGroups := (Finset.univ : Finset (Fin 4)).biUnion holeGroups
  have independent : ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint holeGroups := by
    intro i _ j _ ne
    apply Finset.disjoint_left.2
    intro g hi hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hi
    obtain ⟨b, hb, eq⟩ := Finset.mem_image.1 hj
    exact ne ((hPair (i,a) (Finset.mem_filter.1 ha).2
      (j,b) (Finset.mem_filter.1 hb).2 eq.symm (fun hab => ne (congrArg Prod.fst hab))).1)
  have allMany : 12 ≤ allCollisionGroups.card := by
    dsimp [allCollisionGroups]
    rw [Finset.card_biUnion independent]
    exact le_trans (show 12 ≤ ∑ _h : Fin 4, (3 : ℕ) by decide) (Finset.sum_le_sum fun h _ => holeGroupsMany h)
  have group_sub : allCollisionGroups ⊆ groups := by
    intro g hg
    obtain ⟨h, _, hm⟩ := Finset.mem_biUnion.1 hg
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hm
    exact hGroup _ (Finset.mem_filter.1 he).2
  have groupsMany := allMany.trans (Finset.card_le_card group_sub)
  have extraZero : extraAxioms = 0 := by omega
  obtain ⟨p, hp, distinct⟩ := hPigeon extraZero
  have pNew : p ∉ allCollisionGroups := by
    intro hm
    obtain ⟨h, _, he⟩ := Finset.mem_biUnion.1 hm
    obtain ⟨e, he, eq⟩ := Finset.mem_image.1 he
    exact distinct (h,e) (Finset.mem_filter.1 he).2 eq
  have insertSub : insert p allCollisionGroups ⊆ groups :=
    Finset.insert_subset_iff.2 ⟨hp, group_sub⟩
  have final := Finset.card_le_card insertSub
  rw [Finset.card_insert_of_notMem pNew] at final
  omega


end PEqualNP.Outside.L_meta_9693_aux

namespace PEqualNP.Outside.L_meta_9693_aux

abbrev SourceLabel := Fin 5 ⊕ CollisionLabel

def uniqueCollisionSources {I : Type*} (sourcesFor : SourceLabel → Finset I) :
    Finset CollisionLabel :=
  Finset.univ.filter fun e => (sourcesFor (.inr e)).card = 1

theorem source_fiber_counts {I : Type*} [DecidableEq I]
    (sources : Finset I) (sourcesFor : SourceLabel → Finset I)
    (present : ∀ l, (sourcesFor l).Nonempty)
    (disjoint : ∀ l l', l ≠ l' → Disjoint (sourcesFor l) (sourcesFor l'))
    (included : ∀ l, sourcesFor l ⊆ sources) :
    45 ≤ sources.card ∧
    40 ≤ (uniqueCollisionSources sourcesFor).card + (sources.card - 45) ∧
    (sources.card = 45 → ∀ l, (sourcesFor l).card = 1) := by
  classical
  let repeated := (Finset.univ : Finset SourceLabel).filter fun l => (sourcesFor l).card ≠ 1
  let used := (Finset.univ : Finset SourceLabel).biUnion sourcesFor
  have usedSub : used ⊆ sources := by
    intro i hi
    obtain ⟨l, _, hm⟩ := Finset.mem_biUnion.1 hi
    exact included l hm
  have hDisjoint : ((Finset.univ : Finset SourceLabel) : Set SourceLabel).PairwiseDisjoint sourcesFor := by
    intro l _ l' _ ne
    exact disjoint l l' ne
  have usedCard : used.card = ∑ l : SourceLabel, (sourcesFor l).card :=
    Finset.card_biUnion hDisjoint
  have repeatedBound : 45 + repeated.card ≤ sources.card := by
    calc
      _ = ∑ l : SourceLabel, (1 + if (sourcesFor l).card ≠ 1 then 1 else 0) := by
        simp [repeated, Finset.sum_add_distrib, Finset.card_filter,
          Fintype.card_sum, Fintype.card_prod]
      _ ≤ ∑ l : SourceLabel, (sourcesFor l).card := by
        apply Finset.sum_le_sum
        intro l _
        have positive := Finset.card_pos.2 (present l)
        split <;> omega
      _ = used.card := usedCard.symm
      _ ≤ sources.card := Finset.card_le_card usedSub
  let omitted := (Finset.univ : Finset CollisionLabel) \ uniqueCollisionSources sourcesFor
  have omittedBound : omitted.card ≤ repeated.card := by
    apply Finset.card_le_card_of_injOn (Sum.inr : CollisionLabel → SourceLabel)
    · intro e he
      have h := (Finset.mem_sdiff.1 he).2
      simpa [uniqueCollisionSources, repeated] using h
    · intro a _ b _ same
      exact Sum.inr.inj same
  have omittedCard : omitted.card = 40 - (uniqueCollisionSources sourcesFor).card := by
    dsimp [omitted]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [Fintype.card_prod]
  refine ⟨by omega, by omega, ?_⟩
  intro count l
  by_contra notOne
  have mem : l ∈ repeated := Finset.mem_filter.2 ⟨Finset.mem_univ _, notOne⟩
  have pos := Finset.card_pos.2 ⟨l, mem⟩
  omega

end PEqualNP.Outside.L_meta_9693_aux

namespace PEqualNP.Outside.L_meta_9693_aux

open PEqualNP.Search

namespace Witness

open PEqualNP.Outside.L_meta_9693.Critical

def contradiction : Line := (0, 1)

theorem margin_at_contradiction (a : V → ℤ) : slack a contradiction = -1 := by
  simp [slack, contradiction]

theorem slack_eq_margin (a : V → ℤ) (bits : ∀ v, a v = 0 ∨ a v = 1) (e : Line) :
    slack a e = margin (asBoolean a) e := by
  simp [slack, margin, bits_to_boolean a bits]

theorem source_slack {l : SourceLabel} {a : V → ℤ} (critical : CriticalSlack a l)
    {e : Line} (src : Source e) (different : e ≠ labeledLine l) : 0 ≤ slack a e := by
  rcases src with ⟨C, hC, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩
  · obtain ⟨k, rfl⟩ := label_surjective_on_php C hC
    exact critical.2.2 k (fun eq => different (by subst k; rfl))
  · exact (holds_iff_nonnegative_slack a critical.1 _).mp (boolLoHolds _ v)
  · exact (holds_iff_nonnegative_slack a critical.1 _).mp (boolHiHolds _ v)

variable {I : Type} [Fintype I] [DecidableEq I] (G : Graph I)

theorem graph_margin (lines : I → Line)
    (rules : ∀ i, Local (lines i) ((G.inputs i).map lines))
    (a : V → ℤ) (bits : ∀ v, a v = 0 ∨ a v = 1) :
    G.Margin (fun i => slack a (lines i)) := by
  constructor
  · intro i p shape positive
    have rule : ∀ x : V → Bool, (lines p).Holds x → (lines i).Holds x := by
      simpa only [shape, List.map_cons, List.map_nil, Local] using rules i
    exact (holds_iff_nonnegative_slack a bits _).mp
      (rule _ ((holds_iff_nonnegative_slack a bits _).mpr positive))
  · intro i p q shape
    have rule : lines i = ((lines p).1 + (lines q).1, (lines p).2 + (lines q).2) := by
      simpa only [shape, List.map_cons, List.map_nil, Local] using rules i
    simpa only [rule, slack_eq_margin a bits] using margin_add (asBoolean a) (lines p) (lines q)

noncomputable def sourceFiber (lines : I → Line) (l : SourceLabel) : Finset I := by
  classical
  exact (G.aritySet 0).filter fun i => lines i = labeledLine l

theorem mem_sourceFiber (lines : I → Line) (l : SourceLabel) (i : I) :
    i ∈ sourceFiber G lines l ↔ G.inputs i = [] ∧ lines i = labeledLine l := by
  classical
  simp [sourceFiber, Graph.aritySet]

theorem sourceFiber_subset (lines : I → Line) (l : SourceLabel) :
    sourceFiber G lines l ⊆ G.aritySet 0 := by
  classical
  exact Finset.filter_subset _ _

theorem sourceFibers_disjoint (lines : I → Line) (l k : SourceLabel) (ne : l ≠ k) :
    Disjoint (sourceFiber G lines l) (sourceFiber G lines k) := by
  apply Finset.disjoint_left.mpr
  intro i hl hk
  exact ne (labeledLine_injective
    (((mem_sourceFiber G lines l i).mp hl).2.symm.trans ((mem_sourceFiber G lines k i).mp hk).2))

theorem sourceFibers_present (lines : I → Line)
    (rules : ∀ i, Local (lines i) ((G.inputs i).map lines))
    (rootLine : lines G.root = contradiction) : ∀ l : SourceLabel,
    (sourceFiber G lines l).Nonempty := by
  classical
  intro l
  obtain ⟨a, critical⟩ := witness_for_label l
  by_contra absent
  have allSrc (i : I) (src : G.inputs i = []) : 0 ≤ slack a (lines i) := by
    have kind : Source (lines i) := by simpa only [src, List.map_nil, Local] using rules i
    apply source_slack critical kind
    intro labelEq
    exact absent ⟨i, (mem_sourceFiber G lines l i).mpr ⟨src, labelEq⟩⟩
  have nonneg := G.nonneg_of_sources (graph_margin G lines rules a critical.1) allSrc G.root
  rw [rootLine, margin_at_contradiction] at nonneg
  omega

theorem group_ne_of_critical_pair (lines : I → Line)
    (rules : ∀ i, Local (lines i) ((G.inputs i).map lines))
    (rootLine : lines G.root = contradiction) {l r : SourceLabel} {i j : I}
    (left : i ∈ sourceFiber G lines l) (right : j ∈ sourceFiber G lines r)
    (once : (sourceFiber G lines l).card = 1)
    (a : V → ℤ) (critical : CriticalSlack a l) (rightSlack : 1 ≤ slack a (labeledLine r)) :
    G.group i ≠ G.group j := by
  have li := (mem_sourceFiber G lines l i).mp left
  have rj := (mem_sourceFiber G lines r j).mp right
  have atRoot : slack a (lines G.root) < 0 := by rw [rootLine, margin_at_contradiction]; decide
  have atI : slack a (lines i) = -1 := by rw [li.2, critical.2.1]
  have atJ : 1 ≤ slack a (lines j) := by simpa only [rj.2] using rightSlack
  apply G.compatible_group (graph_margin G lines rules a critical.1) atRoot li.1 rj.1 atI atJ
  intro k src different
  have raw : Source (lines k) := by simpa only [src, List.map_nil, Local] using rules k
  apply source_slack critical raw
  intro labeled
  have atK := (mem_sourceFiber G lines l k).mpr ⟨src, labeled⟩
  obtain ⟨u, singleton⟩ := Finset.card_eq_one.mp once
  rw [singleton] at left atK
  exact different ((Finset.mem_singleton.mp atK).trans (Finset.mem_singleton.mp left).symm)

end Witness

end PEqualNP.Outside.L_meta_9693_aux

namespace PEqualNP.Outside.L_meta_9693_aux

open PEqualNP.Outside.L_meta_9693.Critical

theorem long_graph {I : Type} [Fintype I] [DecidableEq I]
    (G : Graph I) (lines : I → Line)
    (rules : ∀ i, Local (lines i) ((G.inputs i).map lines))
    (rootLine : lines G.root = Witness.contradiction) : 101 ≤ Fintype.card I := by
  classical
  let fibers := Witness.sourceFiber G lines
  have present := Witness.sourceFibers_present G lines rules rootLine
  let pick (l : SourceLabel) := Classical.choose (present l)
  have picked (l : SourceLabel) : pick l ∈ fibers l := Classical.choose_spec (present l)
  let unique := uniqueCollisionSources fibers
  let grp (c : CollisionLabel) := G.group (pick (.inr c))
  let extra := (G.aritySet 0).card - 45
  obtain ⟨manySrc, enough, once⟩ := source_fiber_counts (G.aritySet 0) fibers present
    (Witness.sourceFibers_disjoint G lines) (Witness.sourceFiber_subset G lines)
  have cost : 88 + 2 * extra + G.boundary.card ≤ Fintype.card I := by
    have budget := G.boundary_budget
    dsimp [extra]
    omega
  apply count_group_lines G.boundary unique grp extra (Fintype.card I) cost enough
  · intro c _
    exact G.group_mem (pick (.inr c))
  · intro c hc d _ same _
    have hcOne : (fibers (.inr c)).card = 1 := (Finset.mem_filter.mp hc).2
    by_contra fails
    have bad : incompatible c d := by
      by_cases hole : c.1 = d.1
      · right
        have noMeet : ¬ pairsIntersect c.2 d.2 := fun h => fails ⟨hole, h⟩
        simpa only [pairsIntersect, pigeonPair, leftPigeon, rightPigeon, pairTable,
          not_or] using noMeet
      · exact Or.inl hole
    obtain ⟨a, critical, other⟩ := witness_incompatible_collisions c d bad
    exact (Witness.group_ne_of_critical_pair G lines rules rootLine
      (picked (.inr c)) (picked (.inr d)) hcOne a critical other) same
  · intro noExtra
    have exactSrc : (G.aritySet 0).card = 45 := by
      dsimp [extra] at noExtra
      omega
    let p : SourceLabel := .inl 0
    refine ⟨G.group (pick p), G.group_mem _, ?_⟩
    intro c _
    obtain ⟨a, critical, other⟩ := witness_pigeon_slack_collision 0 c
    exact (Witness.group_ne_of_critical_pair G lines rules rootLine
      (picked p) (picked (.inr c)) (once exactSrc p) a critical other).symm

end PEqualNP.Outside.L_meta_9693_aux

open PEqualNP.Outside.L_meta_9693_aux in
theorem PEqualNP.Outside.L_meta_9693 : ¬ (∃ π : List (PEqualNP.Search.CPLine (Fin (4 + 1) × Fin 4)), PEqualNP.Search.IsCPRefutation (PEqualNP.ProofComplexity.PHP (4 + 1) 4) π ∧ π.length ≤ 100) := by
  rintro ⟨π, ⟨deriv, refutation⟩, short⟩
  obtain ⟨replay⟩ := replay_of_derivation deriv
  obtain ⟨i, goal⟩ := List.mem_iff_get.mp refutation
  let G := trimGraph replay i
  have lower := long_graph G (fun j => lineAt π j.val)
    (trimGraph_rules replay i) goal
  have upper := reach_card_le replay i
  omega
