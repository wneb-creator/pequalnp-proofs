import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3451

open PEqualNP.MetaComplexity

def fsSingle {n : ℕ} (i : Fin n) : Fin n → Bool := fun j => decide (j = i)

def fsPositive {n : ℕ} : DMFormula n → Prop
  | .lit _ b => b = true
  | .and a b => fsPositive a ∧ fsPositive b
  | .or a b => fsPositive a ∧ fsPositive b

def fsCleanAt {n : ℕ} (i : Fin n) : DMFormula n → Prop
  | .lit _ _ => True
  | .and a b => fsCleanAt i a ∧ fsCleanAt i b ∧
      (a.eval (fsSingle i) && b.eval (fsSingle i)) = false
  | .or a b => fsCleanAt i a ∧ fsCleanAt i b

def fsEval {n : ℕ} (a : Option (DMFormula n)) (z : Fin n → Bool) : Bool :=
  a.elim false (fun f => f.eval z)

def fsLeaves {n : ℕ} (a : Option (DMFormula n)) : ℕ :=
  a.elim 0 DMFormula.leaves

def fsPos {n : ℕ} (a : Option (DMFormula n)) : Prop :=
  ∀ f ∈ a, fsPositive f

def fsClean {n : ℕ} (i : Fin n) (a : Option (DMFormula n)) : Prop :=
  ∀ f ∈ a, fsCleanAt i f

def fsOr {n : ℕ} : Option (DMFormula n) → Option (DMFormula n) → Option (DMFormula n)
  | none, b => b
  | a, none => a
  | some a, some b => some (.or a b)

def fsAnd {n : ℕ} : Option (DMFormula n) → Option (DMFormula n) → Option (DMFormula n)
  | some a, some b => some (.and a b)
  | _, _ => none

def fsJoin {n : ℕ} (i : Fin n) : Option (DMFormula n) → DMFormula n
  | none => .lit i true
  | some a => .or (.lit i true) a

lemma fsOr_eval {n : ℕ} (a b : Option (DMFormula n)) (z : Fin n → Bool) :
    fsEval (fsOr a b) z = (fsEval a z || fsEval b z) := by
  cases a <;> cases b <;> simp [fsOr, fsEval, DMFormula.eval]

lemma fsAnd_eval {n : ℕ} (a b : Option (DMFormula n)) (z : Fin n → Bool) :
    fsEval (fsAnd a b) z = (fsEval a z && fsEval b z) := by
  cases a <;> cases b <;> simp [fsAnd, fsEval, DMFormula.eval]

lemma fsJoin_eval {n : ℕ} (i : Fin n) (a : Option (DMFormula n)) (z : Fin n → Bool) :
    (fsJoin i a).eval z = (z i || fsEval a z) := by
  cases a <;> simp [fsJoin, fsEval, DMFormula.eval]

lemma fsOr_leaves {n : ℕ} (a b : Option (DMFormula n)) :
    fsLeaves (fsOr a b) = fsLeaves a + fsLeaves b := by
  cases a <;> cases b <;> simp [fsOr, fsLeaves, DMFormula.leaves]

lemma fsAnd_leaves {n : ℕ} (a b : Option (DMFormula n)) :
    fsLeaves (fsAnd a b) ≤ fsLeaves a + fsLeaves b := by
  cases a <;> cases b <;> simp [fsAnd, fsLeaves, DMFormula.leaves]

lemma fsJoin_leaves {n : ℕ} (i : Fin n) (a : Option (DMFormula n)) :
    (fsJoin i a).leaves = fsLeaves a + 1 := by
  cases a <;> simp [fsJoin, fsLeaves, DMFormula.leaves, Nat.add_comm]

lemma fsOr_pos {n : ℕ} (a b : Option (DMFormula n))
    (ha : fsPos a) (hb : fsPos b) : fsPos (fsOr a b) := by
  cases a <;> cases b <;> simp_all [fsOr, fsPos, fsPositive]

lemma fsAnd_pos {n : ℕ} (a b : Option (DMFormula n))
    (ha : fsPos a) (hb : fsPos b) : fsPos (fsAnd a b) := by
  cases a <;> cases b <;> simp_all [fsAnd, fsPos, fsPositive]

lemma fsJoin_pos {n : ℕ} (i : Fin n) (a : Option (DMFormula n))
    (ha : fsPos a) : fsPositive (fsJoin i a) := by
  cases a <;> simp_all [fsJoin, fsPos, fsPositive]

lemma fsOr_clean {n : ℕ} (i : Fin n) (a b : Option (DMFormula n))
    (ha : fsClean i a) (hb : fsClean i b) : fsClean i (fsOr a b) := by
  cases a <;> cases b <;> simp_all [fsOr, fsClean, fsCleanAt]

lemma fsAnd_clean {n : ℕ} (i : Fin n) (a b : Option (DMFormula n))
    (ha : fsClean i a) (hb : fsClean i b)
    (hz : (fsEval a (fsSingle i) && fsEval b (fsSingle i)) = false) :
    fsClean i (fsAnd a b) := by
  cases a <;> cases b <;> simp_all [fsAnd, fsClean, fsCleanAt, fsEval]

lemma fsJoin_clean {n : ℕ} (i j : Fin n) (a : Option (DMFormula n))
    (ha : fsClean j a) : fsCleanAt j (fsJoin i a) := by
  cases a <;> simp_all [fsJoin, fsClean, fsCleanAt]

lemma fsFactor {n : ℕ} (i : Fin n) (f : DMFormula n) (hf : fsPositive f)
    (hi : f.eval (fsSingle i) = true) :
    ∃ a : Option (DMFormula n), fsPos a ∧ fsLeaves a + 1 ≤ f.leaves ∧
      (∀ z, f.eval z = (z i || fsEval a z)) ∧ fsEval a (fsSingle i) = false ∧
      ∀ j, fsCleanAt j f → fsClean j a := by
  induction f with
  | lit j b =>
    have hb : b = true := hf
    subst b
    have hj : j = i := by simpa [DMFormula.eval, fsSingle] using hi
    subst j
    exact ⟨none, by simp [fsPos], by simp [fsLeaves, DMFormula.leaves],
      by simp [DMFormula.eval, fsEval], rfl, by simp [fsClean]⟩
  | or f g ihf ihg =>
    obtain ⟨hf, hg⟩ := hf
    have he : f.eval (fsSingle i) = true ∨ g.eval (fsSingle i) = true :=
      by simpa only [DMFormula.eval, Bool.or_eq_true] using hi
    by_cases hfi : f.eval (fsSingle i) = true
    · obtain ⟨a, hpa, hla, hea, hza, hca⟩ := ihf hf hfi
      by_cases hgi : g.eval (fsSingle i) = true
      · obtain ⟨b, hpb, hlb, heb, hzb, hcb⟩ := ihg hg hgi
        refine ⟨fsOr a b, fsOr_pos a b hpa hpb, ?_, ?_, ?_, ?_⟩
        · rw [fsOr_leaves]; change _ ≤ f.leaves + g.leaves; omega
        · intro z; simp only [DMFormula.eval, hea, heb, fsOr_eval]
          cases z i <;> simp
        · simp [fsOr_eval, hza, hzb]
        · intro j hj; exact fsOr_clean j a b (hca j hj.1) (hcb j hj.2)
      · refine ⟨fsOr a (some g), fsOr_pos _ _ hpa (by simpa [fsPos] using hg),
          ?_, ?_, ?_, ?_⟩
        · rw [fsOr_leaves]; change fsLeaves a + g.leaves + 1 ≤ f.leaves + g.leaves; omega
        · intro z; rw [DMFormula.eval, hea, fsOr_eval]
          change ((z i || fsEval a z) || g.eval z) = (z i || (fsEval a z || g.eval z))
          exact Bool.or_assoc _ _ _
        · have hg0 : g.eval (fsSingle i) = false := Bool.eq_false_iff.mpr hgi
          rw [fsOr_eval, hza]
          simpa only [fsEval, Option.elim_some, Bool.false_or] using hg0
        · intro j hj; exact fsOr_clean j _ _ (hca j hj.1) (by simpa [fsClean] using hj.2)
    · have hgi : g.eval (fsSingle i) = true := he.resolve_left hfi
      obtain ⟨b, hpb, hlb, heb, hzb, hcb⟩ := ihg hg hgi
      refine ⟨fsOr (some f) b, fsOr_pos _ _ (by simpa [fsPos] using hf) hpb,
        ?_, ?_, ?_, ?_⟩
      · rw [fsOr_leaves]; change f.leaves + fsLeaves b + 1 ≤ f.leaves + g.leaves; omega
      · intro z; rw [DMFormula.eval, heb, fsOr_eval]
        change (f.eval z || (z i || fsEval b z)) = (z i || (f.eval z || fsEval b z))
        cases z i <;> simp
      · have hf0 : f.eval (fsSingle i) = false := Bool.eq_false_iff.mpr hfi
        rw [fsOr_eval, hzb]
        simpa only [fsEval, Option.elim_some, Bool.or_false] using hf0
      · intro j hj; exact fsOr_clean j _ _ (by simpa [fsClean] using hj.1) (hcb j hj.2)
  | and f g ihf ihg =>
    obtain ⟨hf, hg⟩ := hf
    have hp : f.eval (fsSingle i) = true ∧ g.eval (fsSingle i) = true :=
      by simpa only [DMFormula.eval, Bool.and_eq_true] using hi
    obtain ⟨hfi, hgi⟩ := hp
    obtain ⟨a, hpa, hla, hea, hza, hca⟩ := ihf hf hfi
    obtain ⟨b, hpb, hlb, heb, hzb, hcb⟩ := ihg hg hgi
    refine ⟨fsAnd a b, fsAnd_pos a b hpa hpb, ?_, ?_, ?_, ?_⟩
    · have hh := fsAnd_leaves a b
      change _ ≤ f.leaves + g.leaves; omega
    · intro z; simp only [DMFormula.eval, hea, heb, fsAnd_eval]
      cases z i <;> simp
    · simp [fsAnd_eval, hza, hzb]
    · intro j hj
      apply fsAnd_clean j a b (hca j hj.1) (hcb j hj.2.1)
      have hz := hj.2.2
      rw [hea, heb] at hz
      cases fsSingle j i <;> simp_all

lemma fsNormalizeAt {n : ℕ} (i : Fin n) (f : DMFormula n) (hf : fsPositive f) :
    ∃ g : DMFormula n, fsPositive g ∧ g.leaves ≤ f.leaves ∧
      (∀ z, g.eval z = f.eval z) ∧ fsCleanAt i g ∧
      ∀ j, fsCleanAt j f → fsCleanAt j g := by
  induction f with
  | lit j b => exact ⟨.lit j b, hf, le_rfl, fun _ => rfl, trivial, fun _ h => h⟩
  | or f g ihf ihg =>
    obtain ⟨a, hpa, hla, hea, hca, hsa⟩ := ihf hf.1
    obtain ⟨b, hpb, hlb, heb, hcb, hsb⟩ := ihg hf.2
    refine ⟨.or a b, ⟨hpa, hpb⟩, Nat.add_le_add hla hlb,
      ?_, ⟨hca, hcb⟩, ?_⟩
    · intro z; simp [DMFormula.eval, hea, heb]
    · intro j hj; exact ⟨hsa j hj.1, hsb j hj.2⟩
  | and f g ihf ihg =>
    obtain ⟨a, hpa, hla, hea, hca, hsa⟩ := ihf hf.1
    obtain ⟨b, hpb, hlb, heb, hcb, hsb⟩ := ihg hf.2
    by_cases hfi : (a.eval (fsSingle i) && b.eval (fsSingle i)) = true
    · have hp : a.eval (fsSingle i) = true ∧ b.eval (fsSingle i) = true :=
        by simpa only [Bool.and_eq_true] using hfi
      obtain ⟨hai, hbi⟩ := hp
      obtain ⟨a', hpa', hla', hea', hza', hca'⟩ := fsFactor i a hpa hai
      obtain ⟨b', hpb', hlb', heb', hzb', hcb'⟩ := fsFactor i b hpb hbi
      refine ⟨fsJoin i (fsAnd a' b'), fsJoin_pos _ _ (fsAnd_pos _ _ hpa' hpb'),
        ?_, ?_, ?_, ?_⟩
      · rw [fsJoin_leaves]
        have hh := fsAnd_leaves a' b'
        change _ ≤ f.leaves + g.leaves; omega
      · intro z
        rw [fsJoin_eval, fsAnd_eval, DMFormula.eval]
        rw [← hea, ← heb, hea', heb']
        cases z i <;> simp
      · apply fsJoin_clean
        exact fsAnd_clean _ _ _ (hca' i hca) (hcb' i hcb) (by simp [hza', hzb'])
      · intro j hj
        apply fsJoin_clean
        apply fsAnd_clean _ _ _ (hca' j (hsa j hj.1)) (hcb' j (hsb j hj.2.1))
        have hz := hj.2.2
        rw [← hea, ← heb, hea', heb'] at hz
        cases hji : fsSingle j i
        · simpa [hji] using hz
        · simp [hji] at hz
    · refine ⟨.and a b, ⟨hpa, hpb⟩, Nat.add_le_add hla hlb, ?_,
        ⟨hca, hcb, Bool.eq_false_iff.mpr hfi⟩, ?_⟩
      · intro z; simp [DMFormula.eval, hea, heb]
      · intro j hj
        exact ⟨hsa j hj.1, hsb j hj.2.1, by simpa [hea, heb] using hj.2.2⟩

lemma fsNormalizeList {n : ℕ} (is : List (Fin n)) (f : DMFormula n) (hf : fsPositive f) :
    ∃ g : DMFormula n, fsPositive g ∧ g.leaves ≤ f.leaves ∧
      (∀ z, g.eval z = f.eval z) ∧ (∀ i ∈ is, fsCleanAt i g) ∧
      ∀ j, fsCleanAt j f → fsCleanAt j g := by
  induction is generalizing f with
  | nil => exact ⟨f, hf, le_rfl, fun _ => rfl, by simp, fun _ h => h⟩
  | cons i is ih =>
    obtain ⟨a, hpa, hla, hea, hca, hsa⟩ := fsNormalizeAt i f hf
    obtain ⟨b, hpb, hlb, heb, hcb, hsb⟩ := ih a hpa
    refine ⟨b, hpb, hlb.trans hla, fun z => (heb z).trans (hea z), ?_, ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hsb _ hca
      · exact hcb j hj
    · intro j hj; exact hsb j (hsa j hj)

lemma fsNormalize {n : ℕ} (f : DMFormula n) (hf : fsPositive f) :
    ∃ g : DMFormula n, fsPositive g ∧ g.leaves ≤ f.leaves ∧
      (∀ z, g.eval z = f.eval z) ∧ ∀ i, fsCleanAt i g := by
  obtain ⟨g, hpg, hlg, heg, hcg, _⟩ := fsNormalizeList (List.finRange n) f hf
  exact ⟨g, hpg, hlg, heg, fun i => hcg i (by simp)⟩

end PEqualNP.Outside.L_meta_3451
