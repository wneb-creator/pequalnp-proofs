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

def Refines {X : Type} (P f g : Set X) : Prop :=
  g ⊆ f ∧ ∀ x ∈ P, (x ∈ g ↔ x ∈ f)

theorem refine_refl {X : Type} (P f : Set X) : Refines P f f :=
  ⟨fun _ h => h, fun _ _ => Iff.rfl⟩

theorem refine_inter {X : Type} {P f g f' g' : Set X}
    (hf : Refines P f f') (hg : Refines P g g') :
    Refines P (f ∩ g) (f' ∩ g') :=
  ⟨fun _ h => ⟨hf.1 h.1, hg.1 h.2⟩,
    fun x hx => and_congr (hf.2 x hx) (hg.2 x hx)⟩

theorem refine_union {X : Type} {P f g f' g' : Set X}
    (hf : Refines P f f') (hg : Refines P g g') :
    Refines P (f ∪ g) (f' ∪ g') :=
  ⟨fun _ h => h.elim (fun h => Or.inl (hf.1 h)) (fun h => Or.inr (hg.1 h)),
    fun x hx => or_congr (hf.2 x hx) (hg.2 x hx)⟩

theorem refineMeet {X : Type} {P : Set X} {B D : Set (Set X)}
    (atoms : ∀ f ∈ B, ∃ g, Meet D g ∧ Refines P f g)
    {f} (h : Meet B f) : ∃ g, Meet D g ∧ Refines P f g := by
  induction h with
  | atom h => exact atoms _ h
  | top => exact ⟨_, Meet.top, refine_refl _ _⟩
  | bot => exact ⟨_, Meet.bot, refine_refl _ _⟩
  | inter _ _ ih jh =>
    obtain ⟨g, hg, hr⟩ := ih
    obtain ⟨g', hg', hr'⟩ := jh
    exact ⟨_, hg.inter hg', refine_inter hr hr'⟩

theorem refineRun {X : Type} {P : Set X} {B : Set (Set X)}
    {k f} (h : Run B k f) : ∀ D : Set (Set X),
    (∀ f ∈ B, ∃ g, Meet D g ∧ Refines P f g) →
    ∃ g, Run D k g ∧ Refines P f g := by
  induction h with
  | done hf =>
    intro D atoms
    obtain ⟨g,hg,hr⟩ := refineMeet atoms hf
    exact ⟨g,Run.done hg,hr⟩
  | @add B a b k f ha hb tail ih =>
    intro D atoms
    obtain ⟨a',ha',hra⟩ := refineMeet atoms ha
    obtain ⟨b',hb',hrb⟩ := refineMeet atoms hb
    obtain ⟨g,hg,hrg⟩ := ih (insert (a' ∪ b') D) (by
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact ⟨a' ∪ b',Meet.atom (Set.mem_insert _ _),refine_union hra hrb⟩
      · obtain ⟨z',hz',hrz⟩ := atoms z hz
        exact ⟨z',weaken (Set.subset_insert _ _) hz',hrz⟩)
    exact ⟨g,Run.add ha' hb' hg,hrg⟩

def Upward {n} (f : Sig n) : Prop :=
  ∀ s t : Finset (V n), s ⊆ t → s ∈ f → t ∈ f

theorem upwardMeet {n} {B : Set (Sig n)}
    (atoms : ∀ f ∈ B, Upward f) {f} (h : Meet B f) : Upward f := by
  induction h with
  | atom h => exact atoms _ h
  | top => intro s t hst hs; trivial
  | bot => intro s t hst hs; exact hs.elim
  | inter _ _ ih jh =>
    intro s t hst hs
    exact ⟨ih s t hst hs.1,jh s t hst hs.2⟩

theorem upwardRun {n} {B : Set (Sig n)} {k f} (h : Run B k f) :
    (∀ f ∈ B, Upward f) → Upward f := by
  induction h with
  | done hf => exact fun atoms => upwardMeet atoms hf
  | @add B a b k f ha hb tail ih =>
    intro atoms
    have ua := upwardMeet atoms ha
    have ub := upwardMeet atoms hb
    apply ih
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · intro s t hst hs
      exact hs.elim (fun h => Or.inl (ua s t hst h)) (fun h => Or.inr (ub s t hst h))
    · exact atoms z hz

def edgePoints {n} (G : SimpleGraph (V n)) : Set (Finset (V n)) :=
  {s | ∃ u v, G.Adj u v ∧ s = {u,v}}

theorem refine_edge_eq {n} {G : SimpleGraph (V n)} {g : Sig n}
    (hr : Refines (edgePoints G) (edge G) g) (hu : Upward g) : g = edge G := by
  apply Set.Subset.antisymm hr.1
  rintro s ⟨u,v,huv,hus,hvs⟩
  have hp : ({u,v} : Finset (V n)) ∈ edgePoints G := ⟨u,v,huv,rfl⟩
  have hg : ({u,v} : Finset (V n)) ∈ g := (hr.2 _ hp).mpr (two_yes huv)
  exact hu _ _ (by intro w hw; simp only [Finset.mem_insert,Finset.mem_singleton] at hw; rcases hw with rfl | rfl <;> assumption) hg

def need {n} (a : Finset (V n)) : Sig n := {s | a ⊆ s}

theorem needMeet {n} (a : Finset (V n)) : Meet (inputs n) (need a) := by
  induction a using Finset.induction_on with
  | empty => simpa [need] using (Meet.top : Meet (inputs n) Set.univ)
  | @insert a s ha ih =>
    have e : need (insert a s) = var a ∩ need s := by
      ext t
      exact Finset.insert_subset_iff
    rw [e]
    exact (Meet.atom (show var a ∈ inputs n from ⟨a,rfl⟩)).inter ih

/-- The first counted OR can be removed if one monomial operand is false on
every positive edge input. This is stated in the actual free-AND Run model. -/
theorem drop_first_dead_operand {n} {G : SimpleGraph (V n)} {A B : Finset (V n)} {k}
    (dead : ∀ u v, G.Adj u v → ¬ A ⊆ {u,v})
    (tail : Run (insert (need A ∪ need B) (inputs n)) k (edge G)) : P G k := by
  obtain ⟨g,run,hr⟩ := refineRun (P := edgePoints G) tail (inputs n) (by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · refine ⟨need B,needMeet B,?_,?_⟩
      · intro s hs; exact Or.inr hs
      · rintro s ⟨u,v,huv,rfl⟩
        change B ⊆ {u,v} ↔ A ⊆ {u,v} ∨ B ⊆ {u,v}
        simp [dead u v huv]
    · exact ⟨z,Meet.atom hz,refine_refl _ _⟩)
  have hu : Upward g := upwardRun run (by
    rintro z ⟨v,rfl⟩ s t hst hs
    exact hst hs)
  rw [refine_edge_eq hr hu] at run
  exact ⟨k,le_rfl,run⟩

end OrCost
end PriorRoutes.Meta971
