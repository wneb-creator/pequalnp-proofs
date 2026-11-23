import Mathlib
import PEqualNP.Defs

namespace PriorRoutes.Meta971
namespace OrCost

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Arbitrarily many AND gates and both constants are free. -/
inductive Meet {X : Type} (B : Set (Set X)) : Set X → Prop
  | atom {f} : f ∈ B → Meet B f
  | top : Meet B Set.univ
  | bot : Meet B ∅
  | inter {f g} : Meet B f → Meet B g → Meet B (f ∩ g)

/-- One counted instruction adjoins the union of two already available meets. -/
inductive Run {X : Type} : Set (Set X) → ℕ → Set X → Prop
  | done {B f} : Meet B f → Run B 0 f
  | add {B a b k f} : Meet B a → Meet B b → Run (insert (a∪b) B) k f → Run B (k+1) f

theorem mapMeet {X Y : Type} {B : Set (Set X)} {D : Set (Set Y)} (π : Y → X)
    (atoms : ∀ f∈B, Meet D (π ⁻¹' f)) {f} (h : Meet B f) : Meet D (π ⁻¹' f) := by
  induction h with
  | atom hf => exact atoms _ hf
  | top => exact Meet.top
  | bot => exact Meet.bot
  | inter _ _ hi hj => exact hi.inter hj

theorem weaken {X : Type} {B D : Set (Set X)} (hd : B ⊆ D) {f}
    (h : Meet B f) : Meet D f :=
  mapMeet id (fun _ hf => Meet.atom (hd hf)) h

theorem freeMap {X Y : Type} {B : Set (Set X)} {D : Set (Set Y)} (π : Y → X)
    (atoms : ∀ f∈B, Meet D (π ⁻¹' f)) {k f} (h : Run B k f) : Run D k (π ⁻¹' f) := by
  induction h generalizing D with
  | done hf => exact Run.done (mapMeet π atoms hf)
  | @add B a b k f ha hb _ ih =>
    apply Run.add (mapMeet π atoms ha) (mapMeet π atoms hb)
    apply ih
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl|hg
    · exact Meet.atom (Set.mem_insert _ _)
    · exact weaken (Set.subset_insert _ _) (atoms _ hg)

def Good {X Y : Type} (π : Y → X) (p q : X) (f : Set X) : Prop :=
  (p∈f ↔ q∈f) ∨ π ⁻¹' f = ∅

theorem meetGood {X Y : Type} {B : Set (Set X)} {π : Y → X} {p q : X}
    (atoms : ∀ f∈B, Good π p q f) {f} (h : Meet B f) : Good π p q f := by
  induction h with
  | atom h => exact atoms _ h
  | top => exact Or.inl Iff.rfl
  | bot => exact Or.inr rfl
  | inter _ _ ih jh =>
    rcases ih with h|h
    · rcases jh with j|j
      · exact Or.inl (and_congr h j)
      · exact Or.inr (by rw [Set.preimage_inter,j,Set.inter_empty])
    · exact Or.inr (by rw [Set.preimage_inter,h,Set.empty_inter])

/-- A change visible at p,q but absent from all surviving raw inputs forces
one OR to disappear on restriction. -/
theorem paidMap {X Y : Type} {B : Set (Set X)} {D : Set (Set Y)}
    (π : Y → X) (p q : X) (atoms : ∀ f∈B, Meet D (π ⁻¹' f))
    (good : ∀ f∈B, Good π p q f) {k f} (h : Run B k f) (bad : ¬Good π p q f) :
    ∃ j<k, Run D j (π ⁻¹' f) := by
  classical
  induction h generalizing D with
  | done hf => exact (bad (meetGood good hf)).elim
  | @add B a b k f ha hb tail ih =>
    have aa := mapMeet π atoms ha
    have ab := mapMeet π atoms hb
    by_cases gg : Good π p q (a∪b)
    · let D' := insert ((π ⁻¹' a)∪(π ⁻¹' b)) D
      have m : ∀ g∈insert (a∪b) B, Meet D' (π ⁻¹' g) := by
        intro g hg
        rcases Set.mem_insert_iff.mp hg with rfl|hg
        · exact Meet.atom (Set.mem_insert _ _)
        · exact weaken (Set.subset_insert _ _) (atoms _ hg)
      obtain ⟨j,hj,hr⟩ := ih m (fun g hg => (Set.mem_insert_iff.mp hg).elim
        (fun e => e ▸ gg) (good g)) bad
      exact ⟨j+1,by omega,Run.add aa ab hr⟩
    · have bypass : Meet D (π ⁻¹' (a∪b)) := by
        rcases meetGood good ha with h|h
        · rcases meetGood good hb with z|z
          · exact (gg (Or.inl (or_congr h z))).elim
          · simpa [Set.preimage_union,z] using aa
        · simpa [Set.preimage_union,h] using ab
      exact ⟨k,by omega,freeMap π (fun g hg => (Set.mem_insert_iff.mp hg).elim
        (fun e => e ▸ bypass) (atoms g)) tail⟩

abbrev V (n : ℕ) := Fin n
abbrev Sig (n : ℕ) := Set (Finset (V n))
def var {n} (v : V n) : Sig n := {s | v∈s}
def inputs (n : ℕ) : Set (Sig n) := Set.range var
def edge {n} (G : SimpleGraph (V n)) : Sig n :=
  {s | ∃ u v, G.Adj u v ∧ u∈s ∧ v∈s}
def P {n} (G : SimpleGraph (V n)) (t : ℕ) : Prop :=
  ∃ k≤t, Run (inputs n) k (edge G)

def erase {n} (v : V n) (s : Finset (V n)) := s.erase v

theorem prVar {n} (v u : V n) : (erase v) ⁻¹' var u =
    if u=v then ∅ else var u := by
  ext s; by_cases h : u=v <;> simp [h,erase,var]

theorem inputMap {n} (v : V n) (f : Sig n) (hf : f∈inputs n) :
    Meet (inputs n) (erase v ⁻¹' f) := by
  obtain ⟨u,rfl⟩ := hf
  rw [prVar]; split
  · exact Meet.bot
  · exact Meet.atom ⟨u,rfl⟩

theorem inputGood {n} (v : V n) (s : Finset (V n)) (f : Sig n) (hf : f∈inputs n) :
    Good (erase v) (insert v s) s f := by
  obtain ⟨u,rfl⟩ := hf
  by_cases h : u=v
  · exact Or.inr (by simp [prVar,h])
  · exact Or.inl (by simp [var,h])

theorem prEdge {n} (G : SimpleGraph (V n)) (v : V n) :
    erase v ⁻¹' edge G = edge (G.deleteIncidenceSet v) := by
  ext s
  change (∃ i j, G.Adj i j ∧ i∈s.erase v ∧ j∈s.erase v) ↔
    (∃ i j, (G.deleteIncidenceSet v).Adj i j ∧ i∈s ∧ j∈s)
  simp only [SimpleGraph.deleteIncidenceSet_adj,Finset.mem_erase]
  tauto

theorem singleton_no {n} (G : SimpleGraph (V n)) (w : V n) : {w} ∉ edge G := by
  rintro ⟨u,v,ha,hu,hv⟩
  simp only [Finset.mem_singleton] at hu hv
  exact ha.ne (hu.trans hv.symm)

theorem two_yes {n} {G : SimpleGraph (V n)} {v w : V n} (h : G.Adj v w) :
    insert v {w} ∈ edge G :=
  ⟨v,w,h,by simp,by simp⟩

theorem hasSurvivor {n} {G : SimpleGraph (V n)} {v i j : V n}
    (h : G.Adj i j) (hi : i≠v) (hj : j≠v) : erase v ⁻¹' edge G ≠ ∅ := by
  intro he
  have hh : ({i,j} : Finset (V n)) ∈ erase v ⁻¹' edge G :=
    ⟨i,j,h,by simp [erase,hi],by simp [erase,hj]⟩
  rw [he] at hh; exact hh

theorem paidVertex {n} {G : SimpleGraph (V n)} {t} {v w i j : V n}
    (run : P G t) (hw : G.Adj v w) (h : G.Adj i j) (hi : i≠v) (hj : j≠v) :
    ∃ b, P (G.deleteIncidenceSet v) b ∧ b+1≤t := by
  obtain ⟨k,hk,r⟩ := run
  have bad : ¬ Good (erase v) (insert v {w}) {w} (edge G) :=
    fun hbad => hbad.elim (fun z => singleton_no G _ (z.mp (two_yes hw))) (hasSurvivor h hi hj)
  obtain ⟨j,hj,rt⟩ := paidMap (erase v) (insert v {w}) {w} (inputMap v) (inputGood v _) r bad
  rw [prEdge] at rt
  exact ⟨j,⟨j,le_rfl,rt⟩,by omega⟩


/-- Two fixed prefix unions are free after restriction, and a remaining
positive/negative distinction forces a third union to disappear. -/
theorem threePaymentOfProbe {n} {G : SimpleGraph (V n)} {v : V n}
    {g h : Sig n} {k}
    (tail : Run (insert h (insert g (inputs n))) k (edge G))
    (s : Finset (V n))
    (freeg : Meet (inputs n) (erase v ⁻¹' g))
    (freeh : Meet (inputs n) (erase v ⁻¹' h))
    (agreeg : insert v s ∈ g ↔ s ∈ g)
    (agreeh : insert v s ∈ h ↔ s ∈ h)
    (yes : insert v s ∈ edge G) (no : s ∉ edge G)
    (survive : ∃ i j, G.Adj i j ∧ i ≠ v ∧ j ≠ v) :
    ∃ b, P (G.deleteIncidenceSet v) b ∧ b + 3 ≤ k + 2 := by
  obtain ⟨i,j,ij,iv,jv⟩ := survive
  have bad : ¬ Good (erase v) (insert v s) s (edge G) :=
    fun h => h.elim (fun e => no (e.mp yes)) (hasSurvivor ij iv jv)
  have map (z) (hz : z ∈ insert h (insert g (inputs n))) :
      Meet (inputs n) (erase v ⁻¹' z) := by
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact freeh
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact freeg
    exact inputMap v z hz
  have good (z) (hz : z ∈ insert h (insert g (inputs n))) :
      Good (erase v) (insert v s) s z := by
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact Or.inl agreeh
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact Or.inl agreeg
    exact inputGood v s z hz
  obtain ⟨b,hb,run⟩ := paidMap (erase v) (insert v s) s map good tail bad
  rw [prEdge] at run
  exact ⟨b, ⟨b, le_rfl, run⟩, by omega⟩

theorem common_variable_prefix_payment {n} {G : SimpleGraph (V n)}
    {v u r w : V n} {k}
    (huv : u ≠ v) (hrv : r ≠ v)
    (hvw : G.Adj v w) (hur : ¬ G.Adj u r)
    (huw : ¬ G.Adj u w) (hrw : ¬ G.Adj r w)
    (tail : Run (insert (var v ∪ var r) (insert (var v ∪ var u) (inputs n)))
      k (edge G))
    (survive : ∃ i j, G.Adj i j ∧ i ≠ v ∧ j ≠ v) :
    ∃ b, P (G.deleteIncidenceSet v) b ∧ b + 3 ≤ k + 2 := by
  have free (z : V n) (hz : z ≠ v) :
      Meet (inputs n) (erase v ⁻¹' (var v ∪ var z)) := by
    rw [Set.preimage_union, prVar, prVar]
    simpa [hz] using (Meet.atom (show var z ∈ inputs n from ⟨z, rfl⟩))
  have no : ({u, r, w} : Finset (V n)) ∉ edge G := by
    rintro ⟨a,b,hab,ha,hb⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl <;>
      simp_all [SimpleGraph.adj_comm]
  apply threePaymentOfProbe tail {u, r, w} (free u huv) (free r hrv)
  · exact iff_of_true (Or.inr (by simp [var])) (Or.inr (by simp [var]))
  · exact iff_of_true (Or.inr (by simp [var])) (Or.inr (by simp [var]))
  · exact ⟨v,w,hvw,by simp,by simp⟩
  · exact no
  · exact survive

end OrCost
end PriorRoutes.Meta971
