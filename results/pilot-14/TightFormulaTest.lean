import LiteralBinaryTest
namespace PEqualNP.Outside.L_meta_670_aux.TightFormula
open LiveCheck

def phase (a : Sig) : Sig := if a.1.getLsbD 63 then neg a else a
lemma phase_neg (a : Sig) : phase (neg a) = phase a := by
  unfold phase neg
  simp only [BitVec.getLsbD_not, BitVec.not_not]
  cases h : a.1.getLsbD 63 <;> simp [h]
lemma phase_sign (a : Sig) : a = phase a ∨ a = neg (phase a) := by
  unfold phase
  split <;> simp [neg, BitVec.not_not]
lemma phase_sep (a : Sig) : sep true (phase a) = sep true a := by
  unfold phase
  split
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [sep, neg, ite_true, BitVec.getLsbD_xor, BitVec.getLsbD_not, hi]
    cases a.1.getLsbD i <;> cases a.2.getLsbD i <;> decide
  · rfl

def ops (a b : Sig) : List Sig :=
  [phase (bin false a b), phase (bin false a (neg b)),
   phase (bin false (neg a) b), phase (bin false (neg a) (neg b))]
lemma op_mem (d : Bool) (a b : Sig) : phase (bin d a b) ∈ ops (phase a) (phase b) := by
  have hand {x y : Sig} (hx : x = phase a ∨ x = neg (phase a))
      (hy : y = phase b ∨ y = neg (phase b)) :
      phase (bin false x y) ∈ ops (phase a) (phase b) := by
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [ops]
  cases d
  · exact hand (phase_sign a) (phase_sign b)
  · rw [← phase_neg (bin true a b)]
    have e : neg (bin true a b) = bin false (neg a) (neg b) := by
      simp [neg, bin, BitVec.not_or]
    rw [e]
    exact hand (by simpa only [phase_neg] using phase_sign (neg a))
      (by simpa only [phase_neg] using phase_sign (neg b))

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))
lemma pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

def steps (v : List Sig) : List (List Sig) :=
  (singles v).flatMap fun (a, r) =>
    (singles r).flatMap fun (b, s) => (ops a b).map fun z => z :: s
lemma step_mem {v r : List Sig} {a b z : Sig}
    (hp : v.Perm (a :: b :: r)) (hz : z ∈ ops a b) :
    ∃ w ∈ steps v, w.Perm (z :: r) := by
  obtain ⟨r₁, h₁, p₁⟩ := pick_one (hp.mem_iff.mpr (by simp : a ∈ a :: b :: r))
  have q₁ : r₁.Perm (b :: r) := List.Perm.cons_inv ((p₁.symm.trans hp))
  obtain ⟨r₂, h₂, p₂⟩ := pick_one (q₁.mem_iff.mpr (by simp : b ∈ b :: r))
  have q₂ : r₂.Perm r := List.Perm.cons_inv (p₂.symm.trans q₁)
  refine ⟨z :: r₂, ?_, q₂.cons z⟩
  exact List.mem_flatMap.mpr ⟨(a, r₁), h₁,
    List.mem_flatMap.mpr ⟨(b, r₂), h₂, List.mem_map.mpr ⟨z, hz, rfl⟩⟩⟩

def test : Nat → List Sig → Bool
  | 0, _ => true
  | n+1, v => decide (v.length ≤ 1) ||
      (steps v).any fun w => (unionSep true w == top) && test n w

lemma cover {k t S} (h : Live k t S) {v : List Sig}
    (hp : v.Perm (S.toList.map phase)) : unionSep true v = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨a, ha, hs⟩ := LiveCheck.live_sep h j hj
  have ht := LiveCheck.sep_weaken t a j hj hs
  have hm : phase a ∈ v := hp.mem_iff.mpr (List.mem_map.mpr ⟨a, Finset.mem_toList.mpr ha, rfl⟩)
  have hu := (LiveCheck.mem_unionSep true v j).mpr ⟨phase a, hm, by simpa only [phase_sep] using ht⟩
  simpa only [top, BitVec.getLsbD_allOnes, hj, decide_true] using hu

lemma tight_test {k t S} (h : Live k t S) (ht : S.card + t = k+1) :
    ∀ n v, v.Perm (S.toList.map phase) → test n v = true := by
  induction h with
  | stop =>
    intro n v hp
    have hl : v.length = 1 := by simpa using hp.length_eq
    cases n <;> simp [test, hl]
  | @unary k t U a ha hf tail ih =>
    have hn : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    have hs := LiveCheck.live_size tail
    rw [Finset.card_insert_of_notMem hn] at hs
    have hu : a ∉ U := by
      intro hm
      rw [Finset.insert_eq_of_mem hm] at ht
      omega
    have ht' : (insert (neg a) U).card + t = k+1 := by
      rw [Finset.card_insert_of_notMem hu] at ht
      rw [Finset.card_insert_of_notMem hn]
      omega
    intro n v hp
    apply ih ht' n v
    have p₁ := (Finset.toList_insert hu).map phase
    have p₂ := (Finset.toList_insert hn).map phase
    simp only [List.map_cons, phase_neg] at p₁ p₂
    exact hp.trans (p₁.trans p₂.symm)
  | @binary k t U a b d ha hb hab hf tail ih =>
    have hn : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have hs := LiveCheck.live_size tail
    rw [Finset.card_insert_of_notMem hn] at hs
    have hu : a ∉ insert b U := by
      intro hm
      rw [Finset.insert_eq_of_mem hm] at ht
      have hc := Finset.card_insert_le b U
      omega
    have hv : b ∉ U := by
      intro hm
      rw [Finset.insert_eq_of_mem hm] at ht
      have hc := Finset.card_insert_le a U
      omega
    have ht' : (insert (bin d a b) U).card + t = k+1 := by
      rw [Finset.card_insert_of_notMem hu, Finset.card_insert_of_notMem hv] at ht
      rw [Finset.card_insert_of_notMem hn]
      omega
    intro n v hp
    cases n with
    | zero => rfl
    | succ n =>
      have p₁ := (Finset.toList_insert hu).map phase
      have p₂ := (Finset.toList_insert hv).map phase
      have p : v.Perm (phase a :: phase b :: U.toList.map phase) := by
        exact hp.trans (p₁.trans (p₂.cons (phase a)))
      obtain ⟨w, hw, hpw⟩ := step_mem p (op_mem d a b)
      have hq : w.Perm ((insert (bin d a b) U).toList.map phase) :=
        hpw.trans ((Finset.toList_insert hn).map phase).symm
      simp only [test, Bool.or_eq_true]
      right
      exact List.any_eq_true.mpr ⟨w, hw, by simp [cover tail hq, ih ht' n w hq]⟩
end PEqualNP.Outside.L_meta_670_aux.TightFormula
