import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590

namespace Petersen

abbrev V := Fin 10

def edges : Finset (Sym2 V) := {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0), s(0, 5), s(1, 6), s(2, 7), s(3, 8),
      s(4, 9), s(5, 7), s(6, 8), s(7, 9), s(8, 5), s(9, 6)}

def related (v w : V) : Bool := decide (s(v, w) ∈ edges)

def digit (w i : ℕ) (t : List ℕ) : ℕ :=
  (t[i / 16]?.getD 0 >>> (w * (i % 16))) % (2 ^ w)

def Autom (f : V → V) : Prop := ∀ v w, related (f v) (f w) = related v w

def permWord (i : ℕ) : ℕ := digit 40 i ([126226149157589975746341902316111795087821178652033608920161735958946923079870511985886294867129905945234916616031849721433987644004584800004927027771687814726114274588084853161905303621743120, 2660427616327399435269531481718178401646082027935301662405787220980513690381215809495705737399288358085788155882573235272057163748261904316948553213991739791448677035952218303664639833339474945, 1239776632479440460244602490183314676691547349958322777359778274831490461234906931871140444825865134744593906462442277757210676840076939554254334611650596719953180810767997775417393455447621720, 680685397305202844481730047074739049850684476135515465580967989292822686912974557059058932175023691582793193531654587653421625127084123126121360498644757611592746733010595291706279375578552370, 2359441078723314407906557783535630859696363947135212612127674429424469707800345139931796134771291749332960158557197026408827764011363104189937445598002369409681521431006698551114156449727010595, 1791754269936980387159954496114408964656880037637619497637505127712020123491113231000397111323065666707872711214067982177652391611727069481362886028575371653022816591766911860414686323241216320, 1541088152341823624237729883312090527910832664816948779100557851341024978419659269577389250850737176470168489800182385030007969897233769982389941546953591982700802455662121076718277292290230645, 835185793909363909917313300847005245958202268679457184379754624500360860895227543323517272014935] : List ℕ)

def permV (k : Fin 120) (v : V) : V := ⟨((permWord k.val >>> (4*v.val)) % 16) % 10, by omega⟩

lemma permVgood : ∀ k : Fin 120, Autom (permV k) := by
  unfold Autom
  decide +kernel

lemma permVinj : ∀ k : Fin 120, Function.Injective (permV k) := by
  unfold Function.Injective
  decide +kernel

noncomputable def permEquiv (k : Fin 120) : Equiv.Perm V :=
  Equiv.ofBijective (permV k) (Finite.injective_iff_bijective.mp (permVinj k))

end Petersen

namespace SlotGeometry

abbrev V := Fin 10

def mask (m : ℕ) : Finset V := Finset.univ.filter fun i => m.testBit i.val

def edges : List (V × V) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

def rectangles : List (ℕ × ℕ) := [(1,2),(1,48),(2,68),(4,136),(64,768),(400,552)]

def dirtyEdges : List (V × V) := edges.filter fun e =>
  (e.1 ∈ mask 400 ∧ e.2 ∈ mask 552) ∨ (e.2 ∈ mask 400 ∧ e.1 ∈ mask 552)

def opposite (v : V) : Finset V := rectangles.foldl (fun acc r =>
  acc ∪ (if v ∈ mask r.1 then mask r.2 else ∅) ∪
    (if v ∈ mask r.2 then mask r.1 else ∅)) ∅

lemma dirty_count : dirtyEdges.length = 6 := by decide +kernel

lemma dirty_disjoint : Disjoint (mask 400) (mask 552) := by decide +kernel

lemma dirty_sizes : (mask 400).card = 3 ∧ (mask 552).card = 3 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma needs_three_to_cover : ∀ S : Finset V, S.card ≤ 2 →
    ∃ e ∈ dirtyEdges, e.1 ∉ S ∧ e.2 ∉ S := by decide +kernel

lemma outside_branch_misses : ∀ v : V, v ∉ mask 400 ∪ mask 552 →
    ∃ e ∈ dirtyEdges, e.1 ∉ opposite v ∧ e.2 ∉ opposite v := by decide +kernel

lemma side_occurrences : ∀ v : V,
    ((rectangles.map fun r => (if v ∈ mask r.1 then 1 else 0) +
      (if v ∈ mask r.2 then 1 else 0)).sum : ℕ) = 2 := by decide +kernel

lemma edge_cover_unique : ∀ e ∈ edges,
    (rectangles.filter fun r =>
      (e.1 ∈ mask r.1 ∧ e.2 ∈ mask r.2) ∨
      (e.2 ∈ mask r.1 ∧ e.1 ∈ mask r.2)).length = 1 := by decide +kernel

lemma other_sides_small : ∀ r ∈ rectangles, r ≠ (400,552) →
    (mask r.1).card ≤ 2 ∧ (mask r.2).card ≤ 2 := by decide +kernel

def knownPatterns : List (List (ℕ × ℕ)) := [[(1, 2), (1, 48), (2, 68), (4, 136), (64, 768), (400, 552)],
  [(1, 2), (1, 48), (2, 68), (16, 520), (32, 384), (200, 772)],
  [(1, 16), (1, 34), (2, 68), (16, 520), (32, 384), (200, 772)],
  [(1, 16), (1, 34), (8, 260), (16, 520), (100, 386), (192, 512)],
  [(1, 18), (1, 32), (2, 68), (16, 520), (32, 384), (200, 772)],
  [(1, 18), (1, 32), (32, 384), (72, 256), (84, 522), (128, 516)],
  [(1, 18), (32, 128), (32, 257), (72, 256), (84, 522), (128, 516)],
  [(1, 18), (32, 129), (32, 256), (72, 256), (84, 522), (128, 516)],
  [(1, 34), (8, 16), (8, 260), (16, 513), (100, 386), (192, 512)],
  [(1, 34), (8, 260), (9, 16), (16, 512), (100, 386), (192, 512)],
  [(1, 48), (2, 4), (2, 65), (4, 136), (64, 768), (400, 552)],
  [(1, 48), (2, 5), (2, 64), (4, 136), (64, 768), (400, 552)],
  [(2, 4), (2, 65), (4, 136), (8, 272), (112, 769), (128, 544)],
  [(2, 5), (2, 64), (40, 256), (52, 137), (64, 768), (144, 512)],
  [(2, 5), (40, 256), (52, 137), (64, 256), (64, 514), (144, 512)],
  [(2, 5), (40, 256), (52, 137), (64, 258), (64, 512), (144, 512)],
  [(2, 65), (4, 8), (4, 130), (8, 272), (112, 769), (128, 544)],
  [(2, 65), (4, 10), (4, 128), (8, 272), (112, 769), (128, 544)],
  [(4, 8), (4, 130), (8, 272), (16, 513), (96, 256), (193, 546)],
  [(4, 10), (4, 128), (32, 257), (73, 274), (80, 512), (128, 544)],
  [(4, 10), (32, 128), (32, 257), (73, 274), (80, 512), (128, 516)],
  [(4, 10), (32, 257), (36, 128), (73, 274), (80, 512), (128, 512)],
  [(4, 130), (8, 16), (8, 260), (16, 513), (96, 256), (193, 546)],
  [(4, 130), (8, 20), (8, 256), (16, 513), (96, 256), (193, 546)],
  [(8, 20), (8, 256), (32, 129), (64, 514), (96, 256), (146, 517)],
  [(8, 20), (32, 129), (32, 256), (64, 514), (72, 256), (146, 517)],
  [(8, 20), (32, 129), (40, 256), (64, 256), (64, 514), (146, 517)],
  [(9, 16), (16, 512), (36, 128), (42, 261), (64, 258), (192, 512)],
  [(9, 16), (36, 128), (42, 261), (64, 258), (64, 512), (144, 512)],
  [(9, 16), (36, 128), (42, 261), (64, 258), (80, 512), (128, 512)]]

def cross (r : ℕ × ℕ) (e : V × V) : Bool :=
  decide ((e.1 ∈ mask r.1 ∧ e.2 ∈ mask r.2) ∨
    (e.2 ∈ mask r.1 ∧ e.1 ∈ mask r.2))

def dirtyOf (r : ℕ × ℕ) : List (V × V) := edges.filter (cross r)

def oppositeOf (p : List (ℕ × ℕ)) (v : V) : Finset V := p.foldl (fun acc r =>
  acc ∪ (if v ∈ mask r.1 then mask r.2 else ∅) ∪
    (if v ∈ mask r.2 then mask r.1 else ∅)) ∅

def geometry (p : List (ℕ × ℕ)) : Prop :=
  p.length = 6 ∧
  (∀ v : V, ((p.map fun r => (if v ∈ mask r.1 then 1 else 0) +
      (if v ∈ mask r.2 then 1 else 0)).sum : ℕ) = 2) ∧
  (∀ e ∈ edges, (p.filter fun r => cross r e).length = 1) ∧
  ∃ r ∈ p,
    (mask r.1).card = 3 ∧ (mask r.2).card = 3 ∧
    Disjoint (mask r.1) (mask r.2) ∧ (dirtyOf r).length = 6 ∧
    (∀ S : Finset V, S.card ≤ 2 → ∃ e ∈ dirtyOf r, e.1 ∉ S ∧ e.2 ∉ S) ∧
    (∀ v : V, v ∉ mask r.1 ∪ mask r.2 →
      ∃ e ∈ dirtyOf r, e.1 ∉ oppositeOf p v ∧ e.2 ∉ oppositeOf p v) ∧
    ∀ q ∈ p, q ≠ r → (mask q.1).card ≤ 2 ∧ (mask q.2).card ≤ 2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma all_known_geometry : ∀ p ∈ knownPatterns, geometry p := by
  unfold geometry
  decide +kernel

end SlotGeometry

namespace ExtraGeometry

abbrev V := Fin 10

def mask (m : ℕ) : Finset V := Finset.univ.filter fun i => m.testBit i.val

def edges : List (V × V) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

def cross (r : ℕ × ℕ) (e : V × V) : Bool :=
  decide ((e.1 ∈ mask r.1 ∧ e.2 ∈ mask r.2) ∨
    (e.2 ∈ mask r.1 ∧ e.1 ∈ mask r.2))

def dirtyOf (r : ℕ × ℕ) : List (V × V) := edges.filter (cross r)

def oppositeOf (p : List (ℕ × ℕ)) (v : V) : Finset V := p.foldl (fun acc r =>
  acc ∪ (if v ∈ mask r.1 then mask r.2 else ∅) ∪
    (if v ∈ mask r.2 then mask r.1 else ∅)) ∅

def occurrences (p : List (ℕ × ℕ)) (v : V) : ℕ :=
  (p.map fun r => (if v ∈ mask r.1 then 1 else 0) +
    (if v ∈ mask r.2 then 1 else 0)).sum

def fivePatterns : List (List (ℕ × ℕ)) := [
  [(1, 18), (32, 385), (72, 256), (84, 522), (128, 516)],
  [(1, 34), (8, 260), (16, 521), (100, 386), (192, 512)],
  [(1, 48), (2, 69), (4, 136), (64, 768), (400, 552)],
  [(1, 50), (2, 68), (16, 520), (32, 384), (200, 772)],
  [(2, 5), (40, 256), (52, 137), (64, 770), (144, 512)],
  [(2, 65), (4, 138), (8, 272), (112, 769), (128, 544)],
  [(4, 10), (32, 257), (73, 274), (80, 512), (128, 548)],
  [(4, 130), (8, 276), (16, 513), (96, 256), (193, 546)],
  [(8, 20), (32, 129), (64, 514), (104, 256), (146, 517)],
  [(9, 16), (36, 128), (42, 261), (64, 258), (208, 512)]]

def fourPatterns : List (List (ℕ × ℕ)) := [
  [(1, 2), (8, 256), (116, 907), (128, 512)],
  [(1, 16), (4, 128), (64, 256), (469, 554)],
  [(1, 32), (4, 8), (64, 512), (402, 621)],
  [(2, 4), (16, 512), (32, 256), (201, 822)],
  [(2, 64), (8, 16), (32, 128), (250, 773)]]

def fiveGeometry (p : List (ℕ × ℕ)) : Prop :=
  p.length = 5 ∧ ∃ r ∈ p, ∃ v : V,
    (mask r.1).card = 3 ∧ (mask r.2).card = 3 ∧
    Disjoint (mask r.1) (mask r.2) ∧ (dirtyOf r).length = 6 ∧
    occurrences p v = 1 ∧ (∀ w : V, w ≠ v → occurrences p w = 2) ∧
    v ∉ mask r.1 ∪ mask r.2 ∧
    Disjoint (oppositeOf p v) (mask r.1 ∪ mask r.2) ∧
    (∀ w : V, w ∉ mask r.1 ∪ mask r.2 → w ≠ v →
      ∃ e ∈ dirtyOf r, e.1 ∉ oppositeOf p w ∧ e.2 ∉ oppositeOf p w) ∧
    ∀ q ∈ p, q ≠ r →
      ((mask q.1) ∩ (mask r.1 ∪ mask r.2)).card ≤ 2 ∧
      ((mask q.2) ∩ (mask r.1 ∪ mask r.2)).card ≤ 2

def fourGeometry (p : List (ℕ × ℕ)) : Prop :=
  p.length = 4 ∧ ∃ r ∈ p, ∃ a ∈ [r.1, r.2], ∃ b ∈ [r.1, r.2],
    ((r.1 = a ∧ r.2 = b) ∨ (r.1 = b ∧ r.2 = a)) ∧
    (mask a).card = 4 ∧ (mask b).card = 6 ∧
    Disjoint (mask a) (mask b) ∧ mask a ∪ mask b = Finset.univ ∧
    (dirtyOf r).length = 12 ∧
    (∀ e ∈ edges, ¬(e.1 ∈ mask a ∧ e.2 ∈ mask a)) ∧
    (∀ q ∈ p, q ≠ r → (mask q.1).card = 1 ∧ (mask q.2).card = 1 ∧
      Disjoint (mask q.1 ∪ mask q.2) (mask a)) ∧
    ∀ S : Finset V, (S ∩ mask b).card ≤ 1 →
      (∀ e ∈ dirtyOf r, e.1 ∈ S ∨ e.2 ∈ S) → mask a ⊆ S

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma all_five_geometry : ∀ p ∈ fivePatterns, fiveGeometry p := by
  unfold fiveGeometry
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma all_four_geometry : ∀ p ∈ fourPatterns, fourGeometry p := by
  unfold fourGeometry
  decide +kernel

end ExtraGeometry

end PEqualNP.Outside.L_meta_2590


namespace PEqualNP.Outside.L_meta_2590.FiniteSlots

abbrev V := Fin 10
abbrev H := Fin 15 × Bool
abbrev Slot := ℕ × Bool

def edges : Fin 15 → V × V := ![(0,1),(1,2),(2,3),(3,4),(4,0),
  (0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def endpoint (h : H) : V := if h.2 then (edges h.1).2 else (edges h.1).1
def barH (h : H) : H := (h.1, !h.2)
def bar (s : Slot) : Slot := (s.1, !s.2)
def incident (v : V) : Finset H := Finset.univ.filter fun h => endpoint h = v
def selected (t : H → Slot) (v : V) : Finset Slot := (incident v).image t

def lower (t : H → Slot) (h : H) : Finset V :=
  Finset.univ.filter fun v => ∃ k : H, endpoint k = v ∧ t k = t h

def independent (A : Finset V) : Prop :=
  ∀ e : Fin 15, ¬((edges e).1 ∈ A ∧ (edges e).2 ∈ A)
def touches (v : V) (A : Finset V) : Prop :=
  ∃ h : H, endpoint h = v ∧ endpoint (barH h) ∈ A

def Conditions (t : H → Slot) : Prop :=
  (∀ h, t (barH h) = bar (t h)) ∧
  (∀ h, endpoint h ∉ lower t (barH h)) ∧
  (∀ v, (selected t v).card ≤ 2) ∧
  ∀ v A, independent A → touches v A → (selected t v).card = 2 →
    ∃ h : H, endpoint h = v ∧ Disjoint (lower t h) A

lemma mem_selected {t : H → Slot} {v : V} {s : Slot} :
    s ∈ selected t v ↔ ∃ h : H, endpoint h = v ∧ t h = s := by
  simp only [selected, incident, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]

lemma lower_subset (t : H → Slot) (S : Slot → Finset V) (W : V → Finset Slot)
    (hw : ∀ h, t h ∈ W (endpoint h))
    (hs : ∀ v s, s ∈ W v → v ∈ S s) (h : H) : lower t h ⊆ S (t h) := by
  intro v hv
  obtain ⟨k, hk, he⟩ := (Finset.mem_filter.mp hv).2
  have hvS := hs (endpoint k) (t k) (hw k)
  simpa only [hk, he] using hvS

lemma conditions_of_exits (t : H → Slot) (S : Slot → Finset V) (W : V → Finset Slot)
    (hb : ∀ h, t (barH h) = bar (t h))
    (hw : ∀ h, t h ∈ W (endpoint h))
    (hs : ∀ v s, s ∈ W v → v ∈ S s)
    (ho : ∀ h, endpoint h ∉ S (t (barH h)))
    (hc : ∀ v, (W v).card ≤ 2)
    (he : ∀ v A, independent A → touches v A →
      ∃ s ∈ W v, Disjoint (S s) A) : Conditions t := by
  have hsub (v : V) : selected t v ⊆ W v := by
    intro s hs'
    obtain ⟨h, rfl, rfl⟩ := mem_selected.mp hs'
    exact hw h
  refine ⟨hb, ?_, ?_, ?_⟩
  · intro h hh
    exact ho h (lower_subset t S W hw hs (barH h) hh)
  · intro v
    exact (Finset.card_le_card (hsub v)).trans (hc v)
  · intro v A hA hv htwo
    have hEq : selected t v = W v :=
      Finset.eq_of_subset_of_card_le (hsub v) (by rw [htwo]; exact hc v)
    obtain ⟨s, hsW, hsA⟩ := he v A hA hv
    rw [← hEq] at hsW
    obtain ⟨h, hvh, hsh⟩ := mem_selected.mp hsW
    refine ⟨h, hvh, ?_⟩
    apply hsA.mono_left
    simpa only [hsh] using lower_subset t S W hw hs h

def around : V → Fin 3 → H := ![
  ![(0,false),(4,true),(5,false)], ![(0,true),(1,false),(6,false)],
  ![(1,true),(2,false),(7,false)], ![(2,true),(3,false),(8,false)],
  ![(3,true),(4,false),(9,false)], ![(5,true),(10,false),(14,true)],
  ![(6,true),(12,true),(13,false)], ![(7,true),(10,true),(11,false)],
  ![(8,true),(13,true),(14,false)], ![(9,true),(11,true),(12,false)]]

lemma around_endpoint : ∀ v i, endpoint (around v i) = v := by decide +kernel
lemma around_complete : ∀ v h, endpoint h = v → ∃ i, around v i = h := by decide +kernel

def block : Fin 4 → Fin 3 → Fin 2 := ![![0,0,1], ![0,1,0], ![0,1,1], ![0,0,0]]
def localCode (t : H → Slot) (v : V) : Fin 4 :=
  if t (around v 0) = t (around v 1) then
    if t (around v 0) = t (around v 2) then 3 else 0
  else if t (around v 0) = t (around v 2) then 1 else 2

lemma repeated_at_vertex (t : H → Slot) (v : V) (hc : (selected t v).card ≤ 2) :
    t (around v 0) = t (around v 1) ∨ t (around v 0) = t (around v 2) ∨
      t (around v 1) = t (around v 2) := by
  by_contra hn
  simp only [not_or] at hn
  have hmem (i : Fin 3) : t (around v i) ∈ selected t v :=
    mem_selected.mpr ⟨around v i, around_endpoint v i, rfl⟩
  have hsub : {t (around v 0), t (around v 1), t (around v 2)} ⊆ selected t v := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact hmem 0
    · exact hmem 1
    · exact hmem 2
  have hh := (Finset.card_le_card hsub).trans hc
  simp [hn.1, hn.2.1, hn.2.2] at hh

lemma localCode_exact (t : H → Slot) (v : V) (hc : (selected t v).card ≤ 2)
    (i j : Fin 3) :
    t (around v i) = t (around v j) ↔
      block (localCode t v) i = block (localCode t v) j := by
  have hr := repeated_at_vertex t v hc
  by_cases h01 : t (around v 0) = t (around v 1)
  · by_cases h02 : t (around v 0) = t (around v 2)
    · have h12 := h01.symm.trans h02
      fin_cases i <;> fin_cases j <;> simp [localCode, block, h01, h02, h12]
    · have h12 : t (around v 1) ≠ t (around v 2) := fun h => h02 (h01.trans h)
      fin_cases i <;> fin_cases j <;> simp [localCode, block, h01, h02, h12, Ne.symm h02, Ne.symm h12]
  · by_cases h02 : t (around v 0) = t (around v 2)
    · have h12 : t (around v 1) ≠ t (around v 2) := fun h => h01 (h02.trans h.symm)
      fin_cases i <;> fin_cases j <;> simp [localCode, block, h01, h02, h12, Ne.symm h01, Ne.symm h12]
    · have h12 := hr.resolve_left h01 |>.resolve_left h02
      fin_cases i <;> fin_cases j <;> simp [localCode, block, h01, h02, h12, Ne.symm h01, Ne.symm h02]

def seed (q : V → Fin 4) (h k : H) : Prop :=
  ∃ v : V, ∃ i j : Fin 3, block (q v) i = block (q v) j ∧
    ((h = around v i ∧ k = around v j) ∨
      (h = barH (around v i) ∧ k = barH (around v j)))
def closed (q : V → Fin 4) : H → H → Prop := Relation.ReflTransGen (seed q)

lemma seed_sound (t : H → Slot)
    (hb : ∀ h, t (barH h) = bar (t h))
    (hc : ∀ v, (selected t v).card ≤ 2) {h k : H}
    (hr : seed (localCode t) h k) : t h = t k := by
  obtain ⟨v, i, j, hij, hcases⟩ := hr
  have he := (localCode_exact t v (hc v) i j).mpr hij
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact he
  · rw [hb, hb, he]

lemma closed_sound (t : H → Slot)
    (hb : ∀ h, t (barH h) = bar (t h))
    (hc : ∀ v, (selected t v).card ≤ 2) {h k : H}
    (hr : closed (localCode t) h k) : t h = t k := by
  induction hr with
  | refl => rfl
  | tail _ hseed ih => exact ih.trans (seed_sound t hb hc hseed)

lemma closed_local_exact (t : H → Slot)
    (hb : ∀ h, t (barH h) = bar (t h))
    (hc : ∀ v, (selected t v).card ≤ 2) (v : V) (i j : Fin 3) :
    closed (localCode t) (around v i) (around v j) ↔
      block (localCode t v) i = block (localCode t v) j := by
  constructor
  · intro hr
    exact (localCode_exact t v (hc v) i j).mp (closed_sound t hb hc hr)
  · intro hij
    exact Relation.ReflTransGen.single ⟨v, i, j, hij, Or.inl ⟨rfl, rfl⟩⟩

lemma card_two_of_code_ne_three (t : H → Slot) (v : V)
    (hc : (selected t v).card ≤ 2) (hq : localCode t v ≠ 3) :
    (selected t v).card = 2 := by
  have hblocks : ∀ q : Fin 4, q ≠ 3 → ∃ i j : Fin 3, block q i ≠ block q j := by
    decide +kernel
  obtain ⟨i, j, hij⟩ := hblocks (localCode t v) hq
  have hne : t (around v i) ≠ t (around v j) :=
    fun he => hij ((localCode_exact t v hc i j).mp he)
  have hmem (k : Fin 3) : t (around v k) ∈ selected t v :=
    mem_selected.mpr ⟨around v k, around_endpoint v k, rfl⟩
  have hsub : {t (around v i), t (around v j)} ⊆ selected t v := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact hmem i
    · exact hmem j
  have hh := Finset.card_le_card hsub
  simp [hne] at hh
  omega

def CodeConditions (q : V → Fin 4) : Prop :=
  (∀ v i j, closed q (around v i) (around v j) ↔ block (q v) i = block (q v) j) ∧
  (∀ h k, endpoint k = endpoint h → ¬ closed q k (barH h)) ∧
  ∀ v A, independent A → touches v A → q v ≠ 3 →
    ∃ i : Fin 3, ∀ h : H, closed q h (around v i) → endpoint h ∉ A

lemma code_conditions (t : H → Slot) (ht : Conditions t) :
    CodeConditions (localCode t) := by
  obtain ⟨hb, ho, hc, he⟩ := ht
  refine ⟨closed_local_exact t hb hc, ?_, ?_⟩
  · intro h k hv hrel
    apply ho h
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, k, hv, closed_sound t hb hc hrel⟩
  · intro v A hA hv hq
    obtain ⟨h, hhv, hdis⟩ := he v A hA hv (card_two_of_code_ne_three t v (hc v) hq)
    obtain ⟨i, hi⟩ := around_complete v h hhv
    refine ⟨i, ?_⟩
    intro k hrel hkA
    have hlower : endpoint k ∈ lower t h := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, k, rfl, ?_⟩
      rw [hi] at hrel
      exact closed_sound t hb hc hrel
    exact Finset.disjoint_left.mp hdis hlower hkA

end PEqualNP.Outside.L_meta_2590.FiniteSlots

namespace PEqualNP.Outside.L_meta_2590.FiniteSlots

lemma closed_of_local (q : V → Fin 4) (v : V) (i j : Fin 3)
    (hij : block (q v) i = block (q v) j) :
    closed q (around v i) (around v j) :=
  Relation.ReflTransGen.single ⟨v, i, j, hij, Or.inl ⟨rfl, rfl⟩⟩

lemma closed_of_bar_local (q : V → Fin 4) (v : V) (i j : Fin 3)
    (hij : block (q v) i = block (q v) j) :
    closed q (barH (around v i)) (barH (around v j)) :=
  Relation.ReflTransGen.single ⟨v, i, j, hij, Or.inr ⟨rfl, rfl⟩⟩

lemma reject_local {q : V → Fin 4} (hq : CodeConditions q) (v : V) (i j : Fin 3)
    (hc : closed q (around v i) (around v j))
    (hne : block (q v) i ≠ block (q v) j) : False :=
  hne ((hq.1 v i j).mp hc)

lemma reject_opposite {q : V → Fin 4} (hq : CodeConditions q) (h k : H)
    (hv : endpoint k = endpoint h) (hc : closed q k (barH h)) : False :=
  hq.2.1 h k hv hc

lemma reject_exposure {q : V → Fin 4} (hq : CodeConditions q) (v : V) (A : Finset V)
    (hA : independent A) (hv : touches v A) (htwo : q v ≠ 3)
    (hhit : ∀ i : Fin 3, ∃ h : H, closed q h (around v i) ∧ endpoint h ∈ A) : False := by
  obtain ⟨i, hi⟩ := hq.2.2 v A hA hv htwo
  obtain ⟨h, hc, hm⟩ := hhit i
  exact hi h hc hm

lemma closed_of_code (q : V → Fin 4) (v : V) (c : Fin 4) (i j : Fin 3)
    (hq : q v = c) (hij : block c i = block c j) :
    closed q (around v i) (around v j) :=
  closed_of_local q v i j (by rw [hq]; exact hij)

lemma closed_of_bar_code (q : V → Fin 4) (v : V) (c : Fin 4) (i j : Fin 3)
    (hq : q v = c) (hij : block c i = block c j) :
    closed q (barH (around v i)) (barH (around v j)) :=
  closed_of_bar_local q v i j (by rw [hq]; exact hij)

lemma reject_local_of_code {q : V → Fin 4} (hq : CodeConditions q)
    (v : V) (c : Fin 4) (i j : Fin 3) (hv : q v = c)
    (hc : closed q (around v i) (around v j))
    (hne : block c i ≠ block c j) : False :=
  reject_local hq v i j hc (by rw [hv]; exact hne)

end PEqualNP.Outside.L_meta_2590.FiniteSlots

namespace PEqualNP.Outside.L_meta_2590.SlotTables
open PEqualNP.Outside.L_meta_2590.FiniteSlots

abbrev Step := V × Fin 3 × Fin 3 × Bool

def stepStart (d : Step) : H :=
  if d.2.2.2 then barH (around d.1 d.2.1) else around d.1 d.2.1

def stepEnd (d : Step) : H :=
  if d.2.2.2 then barH (around d.1 d.2.2.1) else around d.1 d.2.2.1

abbrev stepValid (q : V → Fin 4) (d : Step) : Prop :=
  block (q d.1) d.2.1 = block (q d.1) d.2.2.1

lemma step_seed (q : V → Fin 4) (d : Step) (hv : stepValid q d) :
    seed q (stepStart d) (stepEnd d) := by
  rcases d with ⟨v, i, j, s⟩
  cases s
  · exact ⟨v, i, j, hv, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨v, i, j, hv, Or.inr ⟨rfl, rfl⟩⟩

def checkPath (q : V → Fin 4) (h : H) : List Step → H → Bool
  | [], k => decide (h = k)
  | d :: ds, k => decide (h = stepStart d) && decide (stepValid q d) &&
      checkPath q (stepEnd d) ds k

lemma checkPath_closed (q : V → Fin 4) (ds : List Step) (h k : H)
    (hc : checkPath q h ds k = true) : closed q h k := by
  induction ds generalizing h with
  | nil =>
    have he : h = k := by simpa [checkPath] using hc
    subst h
    exact Relation.ReflTransGen.refl
  | cons d ds ih =>
    simp only [checkPath, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with ⟨⟨rfl, hv⟩, ht⟩
    exact (Relation.ReflTransGen.single (step_seed q d hv)).trans (ih _ ht)

lemma seed_symm (q : V → Fin 4) {h k : H} (hs : seed q h k) : seed q k h := by
  obtain ⟨v, i, j, hij, hcases⟩ := hs
  refine ⟨v, j, i, hij.symm, ?_⟩
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

lemma closed_symm (q : V → Fin 4) {h k : H} (hc : closed q h k) : closed q k h := by
  induction hc with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact (Relation.ReflTransGen.single (seed_symm q hs)).trans ih

def codeWords : Fin 45 → ℕ := ![
  0x1a9aa,
  0x8696a,
  0x63f3a,
  0x86969,
  0xa1959,
  0xd8dcd,
  0x86968,
  0x44908,
  0x44508,
  0x44108,
  0x44d08,
  0x3db9c,
  0xa1a59,
  0xa1859,
  0xa1b59,
  0x1a9a6,
  0x1a9a2,
  0x1a9ae,
  0x8696b,
  0x6a6a6,
  0x8f0e7,
  0x12022,
  0x10022,
  0x11022,
  0x13022,
  0xf6673,
  0x6a696,
  0x6a686,
  0x6a6b6,
  0xa8295,
  0x49484,
  0x45484,
  0x41484,
  0x4d484,
  0xa8255,
  0xa8215,
  0xa82d5,
  0x24210,
  0x4210,
  0x14210,
  0x34210,
  0x91441,
  0x11441,
  0x51441,
  0xd1441]

def code (p : Fin 45) (v : V) : Fin 4 :=
  ⟨(Nat.shiftRight (codeWords p) (2 * v.val)) % 4, Nat.mod_lt _ (by decide)⟩

def slotWords : Fin 45 → ℕ := ![
  0xba9889baabbaab76543223ab765410,
  0x89baabba9876baab54322367ab5410,
  0x455445765454325445455445544510,
  0x89baabba9876baab54320167ab5432,
  0x8998abba9876549889320167458932,
  0x765467766776673267760167766776,
  0x89baabba9876baab54320167ab5410,
  0x457689ba549876ab89320189988910,
  0x457689ba329876ab89450189988910,
  0x457689ba329876ab89230189988910,
  0x235467983276548967230167766710,
  0x766745766776676776107667327667,
  0x8998abba9876549889107632458910,
  0x8998abba9876329889104554238910,
  0x677689987654327667105445236710,
  0xba9889baabbaab76541001ab763245,
  0xba9889baabbaab76541001ab763223,
  0x987667988998895432100189543223,
  0x679889987654988932100145893210,
  0x899889baab98765432899876541023,
  0x457667766732766767766776671076,
  0x459889ba76ba547632677667761001,
  0x237689ba54ba325489455445541001,
  0x237689ba54ba325467455445541001,
  0x237667985498325467455445541001,
  0x677667765476766710677632677667,
  0x899889baab98765410899876324501,
  0x899889baab98765410899876322301,
  0x677667988976543210677654322301,
  0x8998abbaab765432abba76541023ba,
  0x457689baab98763267456776100176,
  0x457689ba329876ab67456776100176,
  0x237689ba5498765467236776100176,
  0x235467988976548945234554100154,
  0x8998abbaab765410abba76324501ba,
  0x8998abbaab765410abba76322301ba,
  0x677689988954321089985432230198,
  0x899867ba54ba32ab6745ba1001baab,
  0x459867ba32ba98ab6723ba1001baab,
  0x457689ba32ba54ab8923ba1001baab,
  0x677645983298768945239810019889,
  0x6798abba5432765489670110677667,
  0x457689ba32ba543267450110455445,
  0x457689ba3298543267450110455445,
  0x457689983298543267450110455445]

def slotValue (p : Fin 45) (k : ℕ) : Fin 30 :=
  ⟨(Nat.shiftRight (slotWords p) (4 * k)) % 16,
    (Nat.mod_lt _ (by decide)).trans (by decide : 16 < 30)⟩

def slotData (p : Fin 45) (e : Fin 15) : Fin 30 × Fin 30 :=
  (slotValue p (2 * e.val), slotValue p (2 * e.val + 1))

def slot (i : Fin 45) (h : H) : Fin 30 :=
  if h.2 then (slotData i h.1).2 else (slotData i h.1).1

def repWords : Fin 45 → ℕ := ![
  0x31f192906242420,
  0x216b431c6242420,
  0xbd8438c020,
  0x216b431c6208109,
  0xbd84331c8508109,
  0x837a7b909,
  0x216b431c625a820,
  0x73c438c2b45a820,
  0x73c438c14bad020,
  0x73c438c39d52c20,
  0x1cf10e3052c20,
  0x7192916a,
  0xbd8434a08539820,
  0xbd8439c8e621420,
  0x2f610cc721420,
  0x31f192900118909,
  0x31f19291ac00509,
  0xc7c64a400509,
  0x85ad0c718820,
  0xa5528398a400462,
  0x839d9c862,
  0x9cb19292306b001,
  0x9c98dde8a48c001,
  0x9cb19634a48c001,
  0x272634a48c001,
  0x6b4399ac,
  0xa55283984329001,
  0xa5528399ee10c01,
  0x2954a0e610c01,
  0x837a4a0e610ca4,
  0xa56720814b7b843,
  0x73e720814bad043,
  0xbda72081ee52c43,
  0x1cf9c82052c43,
  0x837a4a08539843,
  0x837a4a23021443,
  0x20de92821443,
  0x77a6354b8c085,
  0x6306379d52c85,
  0x58ddea3052c85,
  0x18c18d52c85,
  0xbd98d005ee9c8e6,
  0x9cb19634017b8e6,
  0xbda72634017b8e6,
  0x272634017b8e6]

def representative (p : Fin 45) (c : Fin 30) : H :=
  let z := (Nat.shiftRight (repWords p) (5 * c.val)) % 32
  (⟨(z / 2) % 15, Nat.mod_lt _ (by decide)⟩, z.testBit 0)

def pathWords : Fin 45 → ℕ := ![
  0x6394400b18a200002cc800006640000000000000000490330004919ac628cae63942570000248800002440000b1a000018d00002c4800006240000b0a000018500002c080000604000000000000000000000000000000000000000000000000000000000000000000000000,
  0x32a00005950048c310004718847184b7230c65b0018a4f002c427800000000000000000024880000244000091a000008d00002c4800006240000b0a000018500002c080000604000000000000000000000000000000000000000000000000000000000000000000000000,
  0x451732f220bd97001864d002c226801610b40030c5a00000000000000001220bc001145e8904e4984a2624c000000000000000000244800002240000b0a00001851145c8bc882f45e24138a612898530004a27002241380000892000004900000000000000000000000000000,
  0x32a00005950048c310004718847184b7230c65b0018a4f002c427800000000000000000024880000244000091a000008d00002c4800006240000b0a0000185000024080000204000000000000000000000000000000000000000000000000000000000000000000000000,
  0x451732f220bd97001864d002c22680000b4a00001a500000000000000001220bc001145e000024880000244000091a000008d0000244800002240000b0a0000185000024080000204000000000000000000000000000000000000000000000000000000000000000000000000,
  0x12012c001049600000000000000001210b40010c5a90056cf8822a67c00208ac009005610c5913c842d89e221291e118908f000000000000000000090a0000085000024080000204000000000000008884a278462413c0011894008884a00002228000011400000000000000,
  0x32a00005950048c310004718847184b7230c65b0018a4f002c427800000000000000000024880000244000091a000008d00002c4800006240000b0a0000185000000000000000000008200004410000000000000000000000000000000000000000000000000000000000,
  0x32a000059500000308000118401610b40030c5a000024e80000274000000000000008904e4984a2624c000000000000000000000000000000000b0a0000185000000000000000000008200004410004a27002241380000892000004900000000000000000000000000000,
  0x12a000049500000308000118401610b40030c5a000024e80000274000000000000008904e4984a2624c000000000000000000000000000000000b0a0000185000000000000000000008200004410004a27002241380000892000004900000000000000000000000000000,
  0x308000118401610b40030c5a000024e8000027400008aa00000558904e4984a2624c000000000000000000000000000000000b0a0000185000000000000000000008200004410004a27002241380000892000004900000000000000000000000000000,
  0x12a000049500000308000118401610b40030c5a000024e8000027400008aa00000558904e4984a2624c000000000000000000000000000000000b0a0000185000000000000000000008200004410004a27002241380000892000004900000000000000000000000000000,
  0x24226b4621931a3000864d00242268000000000000008888a4f8464427c23220bf111145f00042c90022064a2044b1e10a218f000464500222228000090a0000085000000000000000000008200004410044089000214480000000000000000002228000011400000000000000,
  0x451732f220bd97001864d002c22680000b4a00001a500000000000000001220bc001145e00002c880000644000091a000008d0000244800002240000b0a0000185000024080000204000000000000000000000000000000000000000000000000000000000000000000000000,
  0x451732f220bd97001864d002c22680000b4a00001a500000000000000001220bc001145e000000000000000000091a000008d0000244800002240000b0a000018500002408000020400008a200000510000000000000000000000000000000000000000000000000000000000,
  0x451732f220bd97001864d002c22680000b4a00001a500000000000000001220bc001145e000024880000244000091a000008d0000244800002240000b0a000018500002408000020400008a200000510000000000000000000000000000000000000000000000000000000000,
  0x6394400b18a200002cc800006640000000000000000490330004919ac628cae63942570000248800002440000b1a000018d00002c480000624000090a000008500002c080000604000000000000000000000000000000000000000000000000000000000000000000000000,
  0x6394400b18a200002cc800006640000000000000000490330004919ac628cae63942570000248800002440000b1a000018d00002c4800006240000000000000000002c080000604000000000000000000000000000000000000000000000002228000011400000000000000,
  0x6394400b18a200002cc800006640000000000000000490330004919ac628cae63942570000248800002440000b1a000018d00002c480000624000090a000008500002c080000604000000000000000000000000000000000000000000000002228000011400000000000000,
  0x32a00005950048c310004718847184b7230c65b0018a4f002c427800000000000000000024880000244000091a000008d00002c4800006240000b0a0000185000024080000204000008200004410000000000000000000000000000000000000000000000000000000000,
  0x16012c0030496b20a6cd9925266c006494c00b20a600002ce800006740000000000000000002c8800006440000b1a000018d00002c480000624000090a000008500002c080000604000000000000000000000000000000000000000000000000000000000000000000000000,
  0x864d0024226801210b40010c5a90056cf8822a67c00208ac00900560000000000000022044b1e10a218f104548fc802b47c000090a000008500002408000020400000820000441004408900021448214421f102250f00000000000000000000000000000,
  0x94200000a100002cc800006640000000000000000000328000119401620bc003145e0000000000000000000000000000000002c4800006240000000000000089852c184e2860c00138a400898520000226800001340000000000000000002228000011400000000000000,
  0x94200000a100000000000000000000b2000045900000328000119401620bc003145e0000000000000000000000000000000002c4800006240000000000000089852c184e2860c00138a400898520000226800001340000000000000000002228000011400000000000000,
  0x94200000a1000024c800002640000000000000000000328000119401620bc003145e0000000000000000000000000000000002c4800006240000000000000089852c184e2860c00138a400898520000226800001340000000000000000002228000011400000000000000,
  0x94200000a1000024c8000026400000b2000045900000328000119401620bc003145e0000000000000000000000000000000002c4800006240000000000000089852c184e2860c00138a400898520000226800001340000000000000000002228000011400000000000000,
  0x12012c00104961049531c804b98e206494e10b20a78888a4f8464427c0000000000000000042c90022064a221291e118908f00046450022222800000000000000000024080000204000008200004410000000000000000011894008884a00002228000011400000000000000,
  0x16012c0030496b20a6cd9925266c006494c00b20a600002ce800006740000000000000000002c8800006440000b1a000018d000024480000224000090a000008500002c080000604000000000000000000000000000000000000000000000000000000000000000000000000,
  0x16012c0030496b20a6cd9925266c006494c00b20a600002ce800006740000000000000000002c8800006440000b1a000018d000000000000000000090a000008500002c080000604000000000000000000000000000000000892000004900000000000000000000000000000,
  0x16012c0030496b20a6cd9925266c006494c00b20a600002ce800006740000000000000000002c8800006440000b1a000018d000024480000224000090a000008500002c080000604000000000000000000000000000000000892000004900000000000000000000000000000,
  0xb4200001a100000000000000001210b40010c5a90056cf8822a67c00208ac009005600002c8800006440000b1a000018d000024480000224000090a0000085000024080000204000000000000000000000000000000000000000000000000000000000000000000000000,
  0x12a0000495000864d00242268000094a00000a500002ce80000674000000000000000000000000000022044b1e10a218f000000000000000000090a0000085000000000000000000008200004410044089000214480000892000004900000000000000000000000000000,
  0x12a0000495000864d00242268000094a00000a5000024e80000274000000000000000000000000000022044b1e10a218f000000000000000000090a0000085000000000000000000008200004410044089000214480000892000004900000000000000000000000000000,
  0x12a0000495000864d00242268000094a00000a500000000000000000000ba000045d0000000000000022044b1e10a218f000000000000000000090a0000085000000000000000000008200004410044089000214480000892000004900000000000000000000000000000,
  0x12a0000495000864d00242268000094a00000a5000024e8000027400000ba000045d0000000000000022044b1e10a218f000000000000000000090a0000085000000000000000000008200004410044089000214480000892000004900000000000000000000000000000,
  0xb4200001a100000000000000001210b40010c5a90056cf8822a67c00208ac009005600002c880000644000091a000008d000024480000224000090a0000085000024080000204000000000000000000000000000000000000000000000000000000000000000000000000,
  0xb4200001a100000000000000001210b40010c5a90056cf8822a67c00208ac009005600002c88000064400000000000000000024480000224000090a0000085000024080000204000000000000000000226800001340000000000000000000000000000000000000000000,
  0xb4200001a100000000000000001210b40010c5a90056cf8822a67c00208ac009005600002c880000644000091a000008d000024480000224000090a0000085000024080000204000000000000000000226800001340000000000000000000000000000000000000000000,
  0xb4200001a100000000000000000000b200004598888a4f8464427c00008aa000005500042c9002206480000000000000000046450022222800000000000000000000000000000000008200004410000226800001340000000000000000002228000011400000000000000,
  0x308000118400000b200004598888a4f8464427c00008aa000005500042c9002206480000000000000000046450022222800000000000000000000000000000000008200004410000226800001340000000000000000002228000011400000000000000,
  0x94200000a100000000000000000000b200004598888a4f8464427c00008aa000005500042c9002206480000000000000000046450022222800000000000000000000000000000000008200004410000226800001340000000000000000002228000011400000000000000,
  0x94200000a100000308000118400000b200004598888a4f8464427c00008aa000005500042c9002206480000000000000000046450022222800000000000000000000000000000000008200004410000226800001340000000000000000002228000011400000000000000,
  0x12012c0010496000024c800002640000b4a00001a500000000000000000000ba000045d000000000000002221291e118908f0000000000000000000000000000000002408000020400008a200000510000000000000000011894008884a00002228000011400000000000000,
  0x12012c0010496000024c800002640000000000000000000328000119400000ba000045d000000000000002221291e118908f0000000000000000000000000000000002408000020400008a200000510000000000000000011894008884a00002228000011400000000000000,
  0x12012c0010496000024c80000264000094a00000a500000000000000000000ba000045d000000000000002221291e118908f0000000000000000000000000000000002408000020400008a200000510000000000000000011894008884a00002228000011400000000000000,
  0x12012c0010496000024c80000264000094a00000a500000328000119400000ba000045d000000000000002221291e118908f0000000000000000000000000000000002408000020400008a200000510000000000000000011894008884a00002228000011400000000000000]

def unpackStep (z : ℕ) : Step :=
  (⟨(z % 16) % 10, Nat.mod_lt _ (by decide)⟩,
   ⟨((z / 16) % 4) % 3, Nat.mod_lt _ (by decide)⟩,
   ⟨((z / 64) % 4) % 3, Nat.mod_lt _ (by decide)⟩, z.testBit 8)

def unpackPath (z : ℕ) : List Step :=
  List.ofFn fun i : Fin (z % 4) => unpackStep (Nat.shiftRight z (2 + 9 * i.val))

def pathAt (p : Fin 45) (k : ℕ) : List Step :=
  unpackPath ((Nat.shiftRight (pathWords p) (29 * k)) % 536870912)

def pathData (p : Fin 45) (e : Fin 15) : List Step × List Step :=
  (pathAt p (2 * e.val), pathAt p (2 * e.val + 1))

def paths (i : Fin 45) (h : H) : List Step :=
  if h.2 then (pathData i h.1).2 else (pathData i h.1).1

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma seed_table_check : ∀ (r : Fin 45) (v : V) (a b : Fin 3),
    block (code r v) a = block (code r v) b →
      slot r (around v a) = slot r (around v b) ∧
      slot r (barH (around v a)) = slot r (barH (around v b)) := by
  decide +kernel

lemma seed_slots (r : Fin 45) {h k : H} (hs : seed (code r) h k) : slot r h = slot r k := by
  obtain ⟨v, i, j, hij, hcases⟩ := hs
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (seed_table_check r v i j hij).1
  · exact (seed_table_check r v i j hij).2

lemma closed_slots (r : Fin 45) {h k : H} (hc : closed (code r) h k) : slot r h = slot r k := by
  induction hc with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (seed_slots r hs)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_0 : ∀ h : H, checkPath (code 0) h (paths 0 h) (representative 0 (slot 0 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_1 : ∀ h : H, checkPath (code 1) h (paths 1 h) (representative 1 (slot 1 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_2 : ∀ h : H, checkPath (code 2) h (paths 2 h) (representative 2 (slot 2 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_3 : ∀ h : H, checkPath (code 3) h (paths 3 h) (representative 3 (slot 3 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_4 : ∀ h : H, checkPath (code 4) h (paths 4 h) (representative 4 (slot 4 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_5 : ∀ h : H, checkPath (code 5) h (paths 5 h) (representative 5 (slot 5 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_6 : ∀ h : H, checkPath (code 6) h (paths 6 h) (representative 6 (slot 6 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_7 : ∀ h : H, checkPath (code 7) h (paths 7 h) (representative 7 (slot 7 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_8 : ∀ h : H, checkPath (code 8) h (paths 8 h) (representative 8 (slot 8 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_9 : ∀ h : H, checkPath (code 9) h (paths 9 h) (representative 9 (slot 9 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_10 : ∀ h : H, checkPath (code 10) h (paths 10 h) (representative 10 (slot 10 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_11 : ∀ h : H, checkPath (code 11) h (paths 11 h) (representative 11 (slot 11 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_12 : ∀ h : H, checkPath (code 12) h (paths 12 h) (representative 12 (slot 12 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_13 : ∀ h : H, checkPath (code 13) h (paths 13 h) (representative 13 (slot 13 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_14 : ∀ h : H, checkPath (code 14) h (paths 14 h) (representative 14 (slot 14 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_15 : ∀ h : H, checkPath (code 15) h (paths 15 h) (representative 15 (slot 15 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_16 : ∀ h : H, checkPath (code 16) h (paths 16 h) (representative 16 (slot 16 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_17 : ∀ h : H, checkPath (code 17) h (paths 17 h) (representative 17 (slot 17 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_18 : ∀ h : H, checkPath (code 18) h (paths 18 h) (representative 18 (slot 18 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_19 : ∀ h : H, checkPath (code 19) h (paths 19 h) (representative 19 (slot 19 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_20 : ∀ h : H, checkPath (code 20) h (paths 20 h) (representative 20 (slot 20 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_21 : ∀ h : H, checkPath (code 21) h (paths 21 h) (representative 21 (slot 21 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_22 : ∀ h : H, checkPath (code 22) h (paths 22 h) (representative 22 (slot 22 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_23 : ∀ h : H, checkPath (code 23) h (paths 23 h) (representative 23 (slot 23 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_24 : ∀ h : H, checkPath (code 24) h (paths 24 h) (representative 24 (slot 24 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_25 : ∀ h : H, checkPath (code 25) h (paths 25 h) (representative 25 (slot 25 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_26 : ∀ h : H, checkPath (code 26) h (paths 26 h) (representative 26 (slot 26 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_27 : ∀ h : H, checkPath (code 27) h (paths 27 h) (representative 27 (slot 27 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_28 : ∀ h : H, checkPath (code 28) h (paths 28 h) (representative 28 (slot 28 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_29 : ∀ h : H, checkPath (code 29) h (paths 29 h) (representative 29 (slot 29 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_30 : ∀ h : H, checkPath (code 30) h (paths 30 h) (representative 30 (slot 30 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_31 : ∀ h : H, checkPath (code 31) h (paths 31 h) (representative 31 (slot 31 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_32 : ∀ h : H, checkPath (code 32) h (paths 32 h) (representative 32 (slot 32 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_33 : ∀ h : H, checkPath (code 33) h (paths 33 h) (representative 33 (slot 33 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_34 : ∀ h : H, checkPath (code 34) h (paths 34 h) (representative 34 (slot 34 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_35 : ∀ h : H, checkPath (code 35) h (paths 35 h) (representative 35 (slot 35 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_36 : ∀ h : H, checkPath (code 36) h (paths 36 h) (representative 36 (slot 36 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_37 : ∀ h : H, checkPath (code 37) h (paths 37 h) (representative 37 (slot 37 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_38 : ∀ h : H, checkPath (code 38) h (paths 38 h) (representative 38 (slot 38 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_39 : ∀ h : H, checkPath (code 39) h (paths 39 h) (representative 39 (slot 39 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_40 : ∀ h : H, checkPath (code 40) h (paths 40 h) (representative 40 (slot 40 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_41 : ∀ h : H, checkPath (code 41) h (paths 41 h) (representative 41 (slot 41 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_42 : ∀ h : H, checkPath (code 42) h (paths 42 h) (representative 42 (slot 42 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_43 : ∀ h : H, checkPath (code 43) h (paths 43 h) (representative 43 (slot 43 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_44 : ∀ h : H, checkPath (code 44) h (paths 44 h) (representative 44 (slot 44 h)) = true := by
  decide +kernel

lemma paths_checked (i : Fin 45) (h : H) : checkPath (code i) h (paths i h) (representative i (slot i h)) = true := by
  fin_cases i
  · exact paths_0 h
  · exact paths_1 h
  · exact paths_2 h
  · exact paths_3 h
  · exact paths_4 h
  · exact paths_5 h
  · exact paths_6 h
  · exact paths_7 h
  · exact paths_8 h
  · exact paths_9 h
  · exact paths_10 h
  · exact paths_11 h
  · exact paths_12 h
  · exact paths_13 h
  · exact paths_14 h
  · exact paths_15 h
  · exact paths_16 h
  · exact paths_17 h
  · exact paths_18 h
  · exact paths_19 h
  · exact paths_20 h
  · exact paths_21 h
  · exact paths_22 h
  · exact paths_23 h
  · exact paths_24 h
  · exact paths_25 h
  · exact paths_26 h
  · exact paths_27 h
  · exact paths_28 h
  · exact paths_29 h
  · exact paths_30 h
  · exact paths_31 h
  · exact paths_32 h
  · exact paths_33 h
  · exact paths_34 h
  · exact paths_35 h
  · exact paths_36 h
  · exact paths_37 h
  · exact paths_38 h
  · exact paths_39 h
  · exact paths_40 h
  · exact paths_41 h
  · exact paths_42 h
  · exact paths_43 h
  · exact paths_44 h

lemma closed_iff_slot (i : Fin 45) (h k : H) : closed (code i) h k ↔ slot i h = slot i k := by
  constructor
  · exact closed_slots i
  · intro he
    have hh := checkPath_closed (code i) (paths i h) h _ (paths_checked i h)
    have hk := checkPath_closed (code i) (paths i k) k _ (paths_checked i k)
    rw [← he] at hk
    exact hh.trans (closed_symm _ hk)

end PEqualNP.Outside.L_meta_2590.SlotTables

namespace PEqualNP.Outside.L_meta_2590.SlotTree

open FiniteSlots

abbrev Partial := V → Option (Fin 4)

def Agrees (q : V → Fin 4) (p : Partial) : Prop :=
  ∀ v c, p v = some c → q v = c

lemma agrees_update {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (v : V) (c : Fin 4) (hc : q v = c) :
    Agrees q (Function.update p v (some c)) := by
  intro w d hd
  by_cases hw : w = v
  · subst w
    simp only [Function.update_self, Option.some.injEq] at hd
    exact hc.trans hd
  · rw [Function.update_of_ne hw] at hd
    exact ha w d hd

def position (h : H) : Fin 3 :=
  if h.2 then
    (![0,0,0,0,1,0,0,0,0,0,1,1,1,1,2] : Fin 15 → Fin 3) h.1
  else
    (![0,1,1,1,1,2,2,2,2,2,1,2,2,2,2] : Fin 15 → Fin 3) h.1

lemma around_position : ∀ h : H, around (endpoint h) (position h) = h := by
  decide +kernel

lemma barH_barH (h : H) : barH (barH h) = h := by
  rcases h with ⟨e, b⟩
  cases b <;> rfl

def directCheck (p : Partial) (h k : H) : Bool :=
  match p (endpoint h) with
  | none => false
  | some c => decide (endpoint k = endpoint h ∧ block c (position h) = block c (position k))

lemma directCheck_sound {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (h k : H) (sw : Bool) (ht : directCheck p h k = true) :
    closed q (if sw then barH h else h) (if sw then barH k else k) := by
  cases hp : p (endpoint h) with
  | none => simp [directCheck, hp] at ht
  | some c =>
    have hh : endpoint k = endpoint h ∧ block c (position h) = block c (position k) := by
      simpa only [directCheck, hp, decide_eq_true_eq] using ht
    have hk : around (endpoint h) (position k) = k := by
      rw [← hh.1]
      exact around_position k
    have hv := ha (endpoint h) c hp
    cases sw
    · simpa only [Bool.false_eq_true, ↓reduceIte, around_position, hk] using
        closed_of_code q (endpoint h) c (position h) (position k) hv hh.2
    · simpa only [↓reduceIte, around_position, hk] using
        closed_of_bar_code q (endpoint h) c (position h) (position k) hv hh.2

def linkCheck (p : Partial) (h k : H) : Bool :=
  decide (h = k) || directCheck p h k || directCheck p (barH h) (barH k)

lemma linkCheck_sound {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (h k : H) (ht : linkCheck p h k = true) : closed q h k := by
  simp only [linkCheck, Bool.or_eq_true, decide_eq_true_eq] at ht
  rcases ht with (rfl | hd) | hb
  · exact Relation.ReflTransGen.refl
  · exact directCheck_sound ha h k false hd
  · simpa only [↓reduceIte, barH_barH] using directCheck_sound ha (barH h) (barH k) true hb

def half (n : ℕ) : H := (⟨(n / 2) % 15, by omega⟩, decide (n % 2 = 1))
def vertex (n : ℕ) : V := ⟨n % 10, by omega⟩
def localIndex (n : ℕ) : Fin 3 := ⟨n % 3, by omega⟩

def pathCheck (p : Partial) (h : H) (bits : ℕ) : ℕ → H → Bool
  | 0, k => decide (h = k)
  | n + 1, k => linkCheck p h (half (bits % 32)) &&
      pathCheck p (half (bits % 32)) (bits / 32) n k

lemma pathCheck_sound {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (n : ℕ) (h k : H) (bits : ℕ) (ht : pathCheck p h bits n k = true) :
    closed q h k := by
  induction n generalizing h bits with
  | zero =>
    have he : h = k := by simpa only [pathCheck, decide_eq_true_eq] using ht
    subst h
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    simp only [pathCheck, Bool.and_eq_true] at ht
    exact (linkCheck_sound ha _ _ ht.1).trans (ih _ _ ht.2)

def reaches (p : Partial) (h k : H) (bits : ℕ) : Bool := pathCheck p h bits 8 k

lemma reaches_sound {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (h k : H) (bits : ℕ) (ht : reaches p h k bits = true) : closed q h k :=
  pathCheck_sound ha 8 h k bits ht

def rowBits : Fin 15 → ℕ := ![50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]
def row (r : Fin 15) : Finset V := Finset.univ.filter fun v => (rowBits r).testBit v.val

lemma row_independent : ∀ r, independent (row r) := by
  unfold independent
  decide +kernel

lemma mem_row (r : Fin 15) (v : V) : v ∈ row r ↔ (rowBits r).testBit v.val = true := by
  simp [row]

def oppositeCheck (p : Partial) (bits : ℕ) : Bool :=
  let h := half (bits % 32)
  let k := half ((bits / 32) % 32)
  decide (endpoint k = endpoint h) && reaches p k (barH h) (bits / 1024)

lemma oppositeCheck_false {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (hq : CodeConditions q) (bits : ℕ) (ht : oppositeCheck p bits = true) : False := by
  simp only [oppositeCheck, Bool.and_eq_true, decide_eq_true_eq] at ht
  exact reject_opposite hq _ _ ht.1 (reaches_sound ha _ _ _ ht.2)

def localCheck (p : Partial) (bits : ℕ) : Bool :=
  let v := vertex (bits % 16)
  let i := localIndex ((bits / 16) % 4)
  let j := localIndex ((bits / 64) % 4)
  match p v with
  | none => false
  | some c => decide (block c i ≠ block c j) &&
      reaches p (around v i) (around v j) (bits / 256)

lemma localCheck_false {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (hq : CodeConditions q) (bits : ℕ) (ht : localCheck p bits = true) : False := by
  unfold localCheck at ht
  dsimp only at ht
  cases hp : p (vertex (bits % 16)) with
  | none => simp only [hp, Bool.false_eq_true] at ht
  | some c =>
    rw [hp] at ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    exact reject_local_of_code hq _ c _ _ (ha _ _ hp) (reaches_sound ha _ _ _ ht.2) ht.1

def exposureStart (bits : ℕ) (i : Fin 3) : H :=
  half ((bits / (2 ^ (8 + i.val * 45))) % 32)
def exposurePath (bits : ℕ) (i : Fin 3) : ℕ := bits / (2 ^ (13 + i.val * 45))

def exposureCheck (p : Partial) (bits : ℕ) : Bool :=
  let v := vertex (bits % 16)
  let r : Fin 15 := ⟨((bits / 16) % 16) % 15, by omega⟩
  match p v with
  | none => false
  | some c => decide (c ≠ 3) && (decide (∃ h : H, endpoint h = v ∧ (rowBits r).testBit (endpoint (barH h)).val = true) &&
      decide (∀ i : Fin 3,
        (rowBits r).testBit (endpoint (exposureStart bits i)).val = true ∧
        reaches p (exposureStart bits i) (around v i) (exposurePath bits i) = true))

lemma exposureCheck_false {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (hq : CodeConditions q) (bits : ℕ) (ht : exposureCheck p bits = true) : False := by
  unfold exposureCheck at ht
  dsimp only at ht
  cases hp : p (vertex (bits % 16)) with
  | none => simp only [hp, Bool.false_eq_true] at ht
  | some c =>
    rw [hp] at ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    have htouch : touches (vertex (bits % 16)) (row ⟨((bits / 16) % 16) % 15, by omega⟩) := by
      obtain ⟨h, hv, hh⟩ := ht.2.1
      exact ⟨h, hv, (mem_row _ _).mpr hh⟩
    apply reject_exposure hq (vertex (bits % 16)) _ (row_independent _) htouch
    · rw [ha _ _ hp]
      exact ht.1
    · intro i
      exact ⟨exposureStart bits i, reaches_sound ha _ _ _ (ht.2.2 i).2,
        (mem_row _ _).mpr (ht.2.2 i).1⟩

def rejects (p : Partial) (n : ℕ) : Bool :=
  if n % 8 = 1 then oppositeCheck p (n / 8)
  else if n % 8 = 2 then localCheck p (n / 8)
  else if n % 8 = 3 then exposureCheck p (n / 8)
  else false

lemma rejects_false {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (hq : CodeConditions q) (n : ℕ) (ht : rejects p n = true) : False := by
  unfold rejects at ht
  split at ht
  · exact oppositeCheck_false ha hq _ ht
  · split at ht
    · exact localCheck_false ha hq _ ht
    · split at ht
      · exact exposureCheck_false ha hq _ ht
      · cases ht

def good (codes : Fin 45 → V → Fin 4) (p : Partial) (n : ℕ) : Bool :=
  decide (∀ v, p v = some (codes ⟨n % 45, by omega⟩ v))

lemma good_sound (codes : Fin 45 → V → Fin 4) {q : V → Fin 4} {p : Partial}
    (ha : Agrees q p) (n : ℕ) (ht : good codes p n = true) :
    ∃ i, q = codes i := by
  refine ⟨⟨n % 45, by omega⟩, ?_⟩
  apply funext
  intro v
  exact ha v _ ((decide_eq_true_eq.mp ht) v)

def scanFour (f : Fin 4 → List ℕ → Option (List ℕ)) (ns : List ℕ) : Option (List ℕ) :=
  (f 0 ns).bind fun ns0 => (f 1 ns0).bind fun ns1 => (f 2 ns1).bind fun ns2 => f 3 ns2

lemma bind_some_exists {α β : Type} {a : Option α} {f : α → Option β} {b : β}
    (h : a.bind f = some b) : ∃ x, a = some x ∧ f x = some b := by
  cases a with
  | none => cases h
  | some x => exact ⟨x, rfl, h⟩

lemma scanFour_success (f : Fin 4 → List ℕ → Option (List ℕ))
    (ns rest : List ℕ) (ht : scanFour f ns = some rest) (c : Fin 4) :
    ∃ a b, f c a = some b := by
  obtain ⟨ns0, h0, hrest0⟩ := bind_some_exists ht
  obtain ⟨ns1, h1, hrest1⟩ := bind_some_exists hrest0
  obtain ⟨ns2, h2, h3⟩ := bind_some_exists hrest1
  fin_cases c
  · exact ⟨_, _, h0⟩
  · exact ⟨_, _, h1⟩
  · exact ⟨_, _, h2⟩
  · exact ⟨_, _, h3⟩

def check (codes : Fin 45 → V → Fin 4) :
    List V → Partial → List ℕ → Option (List ℕ)
  | _, _, [] => none
  | todo, p, n :: ns =>
    if n % 8 = 0 then
      match todo with
      | [] => none
      | v :: vs => scanFour (fun c => check codes vs (Function.update p v (some c))) ns
    else if n % 8 = 4 then
      if good codes p (n / 8) then some ns else none
    else if rejects p n then some ns else none

lemma check_sound (codes : Fin 45 → V → Fin 4) (todo : List V) (p : Partial)
    (ns rest : List ℕ) (q : V → Fin 4) (ht : check codes todo p ns = some rest)
    (ha : Agrees q p) (hq : CodeConditions q) : ∃ i, q = codes i := by
  induction todo generalizing p ns rest with
  | nil =>
    cases ns with
    | nil => cases ht
    | cons n ns =>
      by_cases h0 : n % 8 = 0
      · simp only [check, if_pos h0] at ht
        cases ht
      · by_cases h4 : n % 8 = 4
        · simp only [check, if_neg h0, if_pos h4] at ht
          by_cases hg : good codes p (n / 8) = true
          · exact good_sound codes ha _ hg
          · simp only [if_neg hg] at ht
            cases ht
        · simp only [check, if_neg h0, if_neg h4] at ht
          by_cases hr : rejects p n = true
          · exact (rejects_false ha hq _ hr).elim
          · simp only [if_neg hr] at ht
            cases ht
  | cons v vs ih =>
    cases ns with
    | nil => cases ht
    | cons n ns =>
      by_cases h0 : n % 8 = 0
      · simp only [check, if_pos h0] at ht
        obtain ⟨a, b, hab⟩ := scanFour_success _ _ _ ht (q v)
        exact ih _ _ _ hab (agrees_update ha v (q v) rfl)
      · by_cases h4 : n % 8 = 4
        · simp only [check, if_neg h0, if_pos h4] at ht
          by_cases hg : good codes p (n / 8) = true
          · exact good_sound codes ha _ hg
          · simp only [if_neg hg] at ht
            cases ht
        · simp only [check, if_neg h0, if_neg h4] at ht
          by_cases hr : rejects p n = true
          · exact (rejects_false ha hq _ hr).elim
          · simp only [if_neg hr] at ht
            cases ht

end PEqualNP.Outside.L_meta_2590.SlotTree


namespace PEqualNP.Outside.L_meta_2590.SlotTree

open FiniteSlots

abbrev code : Fin 45 → V → Fin 4 := SlotTables.code

def order : List V := [6,4,0,1,9,3,2,8,5,7]

def c0 : Nat := 40285217132025004452164840870658545442554899
def c1 : Nat := 34530186113891079769029748219665682433997835
def c2 : Nat := 4648876938730377
def c3 : Nat := 4067767319680633
def c4 : Nat := 34530186112958088927261770659588168495487243
def c5 : Nat := 34530186113024006758473638588465997062166795
def c6 : Nat := 4067767312922233
def c7 : Nat := 581109719901209
def c8 : Nat := 1162219249280553
def c9 : Nat := 46040248151837298530002109249233043495906715
def c10 : Nat := 40285217131900774693342474389311868528428051
def c11 : Nat := 46040248151829692626400739152248122896697499
def c12 : Nat := 51795279170797731404486006749425816615176483
def c13 : Nat := 4067767309391225
def c14 : Nat := 4067767322383737
def c15 : Nat := 2905548137307481
def c16 : Nat := 290554824149249
def c17 : Nat := 1743328977971257
def c18 : Nat := 5229986571581593
def c19 : Nat := 28775155094923777046131687776702302567537539
def c20 : Nat := 34530186112950483023660402003755128655528715
def c21 : Nat := 46040248150975296121846912535639344936221723
def c22 : Nat := 74815403246690904981617960455383509931728307
def c23 : Nat := 3486657682757993
def c24 : Nat := 77111817
def c25 : Nat := 28775155094906029937728513533841213760383491
def c26 : Nat := 51795279170790125500884636652440896015960611
def c27 : Nat := 51795279170790125500884636652440896016658979
def c28 : Nat := 51795279170790125500884661224080462949354531
def c29 : Nat := 581109622563865
def c30 : Nat := 28775155094923777046131712636572245652675459
def c31 : Nat := 80570434264713276411932965248756244158691395
def c32 : Nat := 80570434265537249302081314359729101242185795
def c33 : Nat := 83447949775113152913663093301513426284775979
def c34 : Nat := 2905548063726937
def c35 : Nat := 46040248151837298530002105718410935636660251
def c36 : Nat := 51795279169852064056715747615909276023203235
def c37 : Nat := 51795279170797731404486006749425816614492451
def c38 : Nat := 5811096214722217
def c39 : Nat := 1162219347666473
def c40 : Nat := 51795279170790125500884635499519391409081379
def c41 : Nat := 74815403246581887029998329628378249825164211
def c42 : Nat := 83447949775113152913663050715475349869365803
def c43 : Nat := 4648876951673737
def c44 : Nat := 5811096370493097
def c45 : Nat := 46040248150909378290635044606761516369542171
def c46 : Nat := 3486657693014377
def c47 : Nat := 89514505
def c48 : Nat := 51795279170797731404486030816662225282343075
def c49 : Nat := 1162220099579945
def c50 : Nat := 3486657683634793
def c51 : Nat := 2926412297
def c52 : Nat := 46040248151829692626400763435657313678359323
def c53 : Nat := 46040248151000649133851477844245219379582619
def c54 : Nat := 80570434265613308338094984488928058994139331
def c55 : Nat := 40285217131999651440160275562052670999194387
def c56 : Nat := 74815403246657946066012023680698428170023475
def c57 : Nat := 74815403246690904981617957356906966301642803
def c58 : Nat := 34530186113049359770478203897071871505548043
def c59 : Nat := 34530186113891079769029748219665682434677771
def c60 : Nat := 46040248150876419375029111362898542465455771
def c61 : Nat := 83447949775138505925667658610119300728177451
def c62 : Nat := 34530186153188248376130350184069586883795339
def c63 : Nat := 69060372227677230781924475537483532468433483
def c64 : Nat := 1162219252830249
def c65 : Nat := 28775155094906029937728516920548133542324995
def c66 : Nat := 69060372227715260299931310674140605382347851
def c67 : Nat := 74815403245562695947414833477805276599747635
def c68 : Nat := 74815403246592028234800155751820599602512947
def c69 : Nat := 28775155094074451143978795046459376456984835
def c70 : Nat := 28775155094786870781307059970100523658406147
def c71 : Nat := 34530186113891079769029745409419514954728331
def c72 : Nat := 34530186113891079769029772142786903025992587
def c73 : Nat := 40285216283393774828176441731842948339034387
def c74 : Nat := 40285217132843906739912276343449475334027283
def c75 : Nat := 74815403245570301851016202565983880667274163
def c76 : Nat := 1743329644982841
def c77 : Nat := 1743332530202681
def c78 : Nat := 1961020394512962
def c79 : Nat := 5229983705274265
def c80 : Nat := 5229986575653017
def c81 : Nat := 290554826893825
def c82 : Nat := 40285217131933733608948407633174842432514835
def c83 : Nat := 40285217132851512643513642909612288073991443
def c84 : Nat := 46040247301558123125716988830041640087681819
def c85 : Nat := 83447949775138505925667615807908442198983467
def c86 : Nat := 1743328882119225
def c87 : Nat := 290555046750738
def c88 : Nat := 435833132552730
def c89 : Nat := 28775155142161509013036450099584039073686915
def c90 : Nat := 34530186113883473865428378122680761835465995
def c91 : Nat := 3486657690344041
def c92 : Nat := 4648876942212233
def c93 : Nat := 28775155094049098131974231395178164885921155
def c94 : Nat := 28775155094819829696912994871288160434789763
def c95 : Nat := 28775155094906029937728516920548133571244547
def c96 : Nat := 28775155094923777046131709682210890098337411
def c97 : Nat := 34530186113883473865428402550205140692983179
def c98 : Nat := 34530186145559527063931375127856322698228363
def c99 : Nat := 40284279733468293337354821317351610650412179
def c100 : Nat := 40285217131933733608948638505706139953621267
def c101 : Nat := 46040247200384393420301336744261498848763291
def c102 : Nat := 46040248151000649133851477844245219373047195
def c103 : Nat := 46040248185110591484817993744765992120450203
def c104 : Nat := 51795279169950940803533549509226018873222563
def c105 : Nat := 51795279170797731404486003939179649135222947
def c106 : Nat := 69060372227677230781924463575922922172396107
def c107 : Nat := 83447949775138505925645470203417577723994283
def c108 : Nat := 1162219346964521
def c109 : Nat := 1743331745220665
def c110 : Nat := 3486661939222889
def c111 : Nat := 290555205863681
def c112 : Nat := 290556841994753
def c113 : Nat := 290557664323841
def c114 : Nat := 3705266697
def c115 : Nat := 843541513
def c116 : Nat := 69060372227715260299931323500392344133520459
def c117 : Nat := 1162222083900969
def c118 : Nat := 28775155094819829696912994871288160463809923
def c119 : Nat := 28775155094906029937728513533841213760287235
def c120 : Nat := 28775155142161509013040230601255238231943555
def c121 : Nat := 34530185190136340274315788137397102847373963
def c122 : Nat := 34530186113883473865428378122680761836160267
def c123 : Nat := 46040248151829692626400737278750677910518555
def c124 : Nat := 46040248151829692626400739152248122897387675
def c125 : Nat := 51795279169885022972321680859772249927290531
def c126 : Nat := 83447949775113152913663073053329501628237099
def c127 : Nat := 1162222951278121
def c128 : Nat := 1525412012632634
def c129 : Nat := 1525413258727994
def c130 : Nat := 1743328878536761
def c131 : Nat := 1743329730941497
def c132 : Nat := 2905548061004889
def c133 : Nat := 3486654819424617
def c134 : Nat := 91450377
def c135 : Nat := 28775155123828746032535796495138717302730243
def c136 : Nat := 28775155124447359525450449478330764637510019
def c137 : Nat := 40285217131933733608949423212905212988844691
def c138 : Nat := 40285217132025004452164840870658545465013267
def c139 : Nat := 40285217132843906739912300338628289963976979
def c140 : Nat := 83447949775138505925667658610119300721615019
def c141 : Nat := 3486661091768937
def c142 : Nat := 4648879796173961
def c143 : Nat := 145284155335178
def c144 : Nat := 928975881
def c145 : Nat := 28774285300896136944925761770190280016512515
def c146 : Nat := 28775095158152050790232613418359330829265283
def c147 : Nat := 28775155094049098131974026679553503132653955
def c148 : Nat := 28775155094906029937729287504458775150234755
def c149 : Nat := 34530185291700506364602533349037762930629003
def c150 : Nat := 34530186113883473865428376249183316849286539
def c151 : Nat := 34530186113891079769029979092196980030873355
def c152 : Nat := 46040248150909378290635252420862721753709339
def c153 : Nat := 46040248151837298530002133028239076011347995
def c154 : Nat := 51795279170790125500881969656770364220598947
def c155 : Nat := 69060372194654932645980596048549799617835339
def c156 : Nat := 69060372227715260299920788680143999047048139
def c157 : Nat := 74815402097755783464762239598600392232481331
def c158 : Nat := 74815403246592028234800155751820599574999603
def c159 : Nat := 80570434265641196651299789146806090538877635
def c160 : Nat := 83447949775138505925667636992841089351012523
def c161 : Nat := 1162220187111465
def c162 : Nat := 1743328699369529
def c163 : Nat := 1743332523993145
def c164 : Nat := 4648874074938249
def c165 : Nat := 4648880559823753
def c166 : Nat := 290554913122561
def c167 : Nat := 581109623459353
def c168 : Nat := 28775155124447359525447150537560520220744067
def c169 : Nat := 40285217131900774693342728392330852224402067
def c170 : Nat := 46040248151837298530002109249233043495230875
def c171 : Nat := 80570434264705670508331596737038392394589635
def c172 : Nat := 80570434265567672916486792730056150574245315
def c173 : Nat := 80570434265641196651300029170651830905692739
def c174 : Nat := 1452793099586090
def c175 : Nat := 2106521481776170
def c176 : Nat := 2905548140770393
def c177 : Nat := 5229986568066969
def c178 : Nat := 581109719166489
def c179 : Nat := 28775155094049098131974026895726285246437763
def c180 : Nat := 28775155094074451143979565774485206134188419
def c181 : Nat := 28775155094074451143979566206830770361755907
def c182 : Nat := 28775155094786870781307059970100523665629443
def c183 : Nat := 28775155094923777046131478809679592577229955
def c184 : Nat := 28775155143023511421191645155853074760975875
def c185 : Nat := 34530185190136340274315787416821162468094603
def c186 : Nat := 34530186113049359770478203897071871528370827
def c187 : Nat := 34530186113883473865429382821714432762439435
def c188 : Nat := 40285217131933733608948662356769766507768467
def c189 : Nat := 40285217132025004452164840870658545465005203
def c190 : Nat := 40285217132025004452164840870658568515962003
def c191 : Nat := 40285217148146984785867462398893617582916755
def c192 : Nat := 46040248150909378290636046639664207795420187
def c193 : Nat := 51795278255054543703214456484616401292322339
def c194 : Nat := 51795279169925587791528984200620144429862563
def c195 : Nat := 74815403246657946066011994425315248770450739
def c196 : Nat := 74815403246690904981617928605926945167580595
def c197 : Nat := 74815403246690904981617957356906966301730867
def c198 : Nat := 80570433287407904961177683194352062775362883
def c199 : Nat := 80570434171419262837535954192359134717878467
def c200 : Nat := 80570434264705670508331355848501523601498307
def c201 : Nat := 80570434265567672916486792730056150546056515
def c202 : Nat := 1452793813680682
def c203 : Nat := 1743328977302073
def c204 : Nat := 1961243936569922
def c205 : Nat := 2106522195870762
def c206 : Nat := 2899346682420569
def c207 : Nat := 5229986578339737
def c208 : Nat := 290554913982977
def c209 : Nat := 3712000521
def c210 : Nat := 28775155094786870781307059970100523665636867
def c211 : Nat := 28775155123828746032535796495138716587236867
def c212 : Nat := 34530186113883473865429382821714432665372427
def c213 : Nat := 34530186113891079769029772142786903048240907
def c214 : Nat := 46040248151829692626401738374904646844076443
def c215 : Nat := 51795279180880624278701343408930594680149539
def c216 : Nat := 80570434216593259627270421066306217944627651
def c217 : Nat := 83447949775138505925667658610119300722373291
def c218 : Nat := 1598051181466682
def c219 : Nat := 1598051689966650
def c220 : Nat := 2033882434315330
def c221 : Nat := 3486661054437993
def c222 : Nat := 726388258905090
def c223 : Nat := 28775154273212375568589759961623925150615043
def c224 : Nat := 28775155001944140820591334825606041636444547
def c225 : Nat := 28775155094074451144771137900542234751691139
def c226 : Nat := 28775155094786870781307059970100530406737411
def c227 : Nat := 28775155094819829696912994871288160463783427
def c228 : Nat := 28775155094906029937728516920548133548887171
def c229 : Nat := 28775155094906029937729287504458775144344707
def c230 : Nat := 28775155094923777046131712636572245681616003
def c231 : Nat := 28775155094923777046132482716079728989234051
def c232 : Nat := 34530186113024006758473638588465997077983883
def c233 : Nat := 34530186113883473865428402550205140708042123
def c234 : Nat := 34530186145904328027193450714817257703293323
def c235 : Nat := 34530186153188248376104857071990096435173771
def c236 : Nat := 34530186154116168615471922867383128167688843
def c237 : Nat := 40285216182349345483984045266009438311605395
def c238 : Nat := 40285216217290866628674961209440505872094355
def c239 : Nat := 40285216284240565429128923039279154748129939
def c240 : Nat := 40285217132843906739913289833509618791130643
def c241 : Nat := 40285217132851512643513669931210052319505939
def c242 : Nat := 46040247201309778358467943486778151810156315
def c243 : Nat := 46040247329464183439142024012527639923621019
def c244 : Nat := 46040248150975296121846912535639344930413595
def c245 : Nat := 46040248151837298530002316342758308575209883
def c246 : Nat := 46040248177481870172619190041511350122645275
def c247 : Nat := 46040248185896534856934176088070524837973787
def c248 : Nat := 51795279170797731404486030816662225304726179
def c249 : Nat := 63305341208721868509841473512310111948705851
def c250 : Nat := 63305341208721868509841489220865612217488315
def c251 : Nat := 63305341208721868509841490806132681051410491
def c252 : Nat := 63305341208739615618244683135449873379578043
def c253 : Nat := 63305341208739615618244683135449873379674299
def c254 : Nat := 63305341208739615618244686522156793161787707
def c255 : Nat := 69060372194654932645979087666933803672351051
def c256 : Nat := 69060372227263976686250070590867786085648587
def c257 : Nat := 69060372227677230781924473808101275558502475
def c258 : Nat := 69060372227715260299920578776372566557005003
def c259 : Nat := 69060372227715260299931323500392344105352267
def c260 : Nat := 69060372227715260299931323500392344111291339
def c261 : Nat := 74815402105141115861691904091720185112968371
def c262 : Nat := 74815403218990204065430659508248204609913907
def c263 : Nat := 74815403246592028234800155751820599580986419
def c264 : Nat := 74815403246690904981587740725423101572625971
def c265 : Nat := 80570434265641196651300029170651830905776707
def c266 : Nat := 80570434265641196651300032125013186460072771
def c267 : Nat := 1162219071604265
def c268 : Nat := 1525387728892474
def c269 : Nat := 1525414694556218
def c270 : Nat := 1525415203056186
def c271 : Nat := 1525427511407162
def c272 : Nat := 1598041874017338
def c273 : Nat := 1598057272224826
def c274 : Nat := 3486661843245417
def c275 : Nat := 3970842583258745
def c276 : Nat := 3977830113949305
def c277 : Nat := 4648876948937865
def c278 : Nat := 28775155094049098131738584111526908560153475
def c279 : Nat := 34530186113891079769029772142786903048221579
def c280 : Nat := 40285216310975316587943040964173755299621523
def c281 : Nat := 40285217131933733608949422420271678571637395
def c282 : Nat := 40285217132851512643514659209918599010368787
def c283 : Nat := 46040248150876419375030112675225293512053915
def c284 : Nat := 46040248151000649133851477844245219401619227
def c285 : Nat := 46040248151829692626398071436001650722036123
def c286 : Nat := 46040248151837298530003109480695884070543387
def c287 : Nat := 69060372194720850477192465850925073170647755
def c288 : Nat := 74815403246592028234800155751820599580966067
def c289 : Nat := 74815403246657946066012025554195873155319091
def c290 : Nat := 80570434265567672916486792730056150552698307
def c291 : Nat := 80570434265641196651300032125013186439197251
def c292 : Nat := 83447949775138505925667658610119300706630315
def c293 : Nat := 1162240498152474
def c294 : Nat := 1888605581149234
def c295 : Nat := 2815610797383001
def c296 : Nat := 3967117014283897
def c297 : Nat := 3980742130554489
def c298 : Nat := 28774313642026812873498420143046895667719683
def c299 : Nat := 28775058989071023752877985006948543014902147
def c300 : Nat := 28775155094074451144771164489794434747099907
def c301 : Nat := 28775155094786870781307059970100530406795779
def c302 : Nat := 28775155094819829696912994871288190077363843
def c303 : Nat := 28775155094906029915527376633152324956118147
def c304 : Nat := 28775155094906029937728516920548140974136451
def c305 : Nat := 28775155094906029938517506934781067900783747
def c306 : Nat := 28775155094923777046131709682210890098253443
def c307 : Nat := 34529248372612352376515627677710068760130187
def c308 : Nat := 34530185198801999777475964326028565966324363
def c309 : Nat := 34530186112950483023660656439119676579070347
def c310 : Nat := 34530186112950483023660656655292458692854155
def c311 : Nat := 34530186113024006758473638588466012532491531
def c312 : Nat := 34530186113049359770478203897071871521370763
def c313 : Nat := 34530186113049359770478203897071894302765707
def c314 : Nat := 34530186113883473863503173805537697503504139
def c315 : Nat := 34530186113883473865426472055203270580735755
def c316 : Nat := 34530186113883473865428402550205140708069131
def c317 : Nat := 34530186145559527063931374407280381531400459
def c318 : Nat := 34530186145559527063931375127856321910700683
def c319 : Nat := 34530186145919539834396189467635218141757835
def c320 : Nat := 34530227344112763664300793289103049280805259
def c321 : Nat := 40285217131900774693342728608503634338185875
def c322 : Nat := 40285217132843906739913289833509618784509459
def c323 : Nat := 40285217132851512643513876592389753096826387
def c324 : Nat := 40285217149652953698963449646500342537585299
def c325 : Nat := 40285217156587002482212061550207002803923603
def c326 : Nat := 40285217157038286095868262700415553493326995
def c327 : Nat := 40285217157038286095893324043391567896183827
def c328 : Nat := 46039406012733176141646659226458406191987867
def c329 : Nat := 46040247200376787516700968680179269676123035
def c330 : Nat := 46040248150909378290636045558800297226501275
def c331 : Nat := 46040248151837298530002133028239076033481115
def c332 : Nat := 51794341574086949064400080071760223411312163
def c333 : Nat := 51795278295414003513280318036927915516962595
def c334 : Nat := 51795279169885022972321175447807667900746787
def c335 : Nat := 51795279169885022972577834221477225747156003
def c336 : Nat := 51795279169950940803533549509226018895521315
def c337 : Nat := 51795279170790125500884908237512824967049891
def c338 : Nat := 51795279188509345590899705110903408040578851
def c339 : Nat := 51795279189629948721476582017484899054259747
def c340 : Nat := 69060372194720850477190955811984414352820939
def c341 : Nat := 69060372227715260299931323500392344105325771
def c342 : Nat := 74815403141240122151031907341187667213485875
def c343 : Nat := 74815403218990204065432339242822822748030003
def c344 : Nat := 74815403219056121896644209045198096300842803
def c345 : Nat := 74815403245562695947414275103509076696171571
def c346 : Nat := 74815403246657946066012023680698428170076723
def c347 : Nat := 74815403246690904981587950629194534062667827
def c348 : Nat := 74815409928510177700221037643315672874026035
def c349 : Nat := 80570434264705670508330428827554225658601923
def c350 : Nat := 80570434264705670508330429043727007772385731
def c351 : Nat := 83447949765993674495621190738962218761004843
def c352 : Nat := 83447949775113152913663093301513426278986283

set_option maxRecDepth 32000 in
set_option maxHeartbeats 8000000 in
def treeData : List ℕ := [
  0,
  0,
  0,
  0,
  0,
  c26,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  c315,
  c29,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  c315,
  c29,
  c26,
  0,
  c26,
  c76,
  0,
  0,
  c24,
  c20,
  0,
  c11,
  c245,
  c264,
  c11,
  c24,
  0,
  c122,
  c20,
  c152,
  c20,
  0,
  c122,
  c20,
  c84,
  c20,
  0,
  c24,
  c20,
  0,
  c294,
  0,
  c119,
  290556748466689,
  c14,
  290556748466689,
  c264,
  c294,
  c24,
  c76,
  0,
  c26,
  0,
  c233,
  0,
  c242,
  c58,
  c189,
  c58,
  c316,
  c233,
  0,
  c233,
  0,
  c242,
  c6,
  c138,
  c6,
  c316,
  c233,
  c26,
  0,
  c26,
  c76,
  0,
  c29,
  0,
  c8,
  c6,
  c0,
  c8,
  0,
  c8,
  c6,
  c84,
  c8,
  c29,
  c76,
  0,
  c150,
  c69,
  c97,
  c69,
  0,
  0,
  0,
  0,
  c16,
  0,
  c11,
  0,
  0,
  c111,
  c210,
  c131,
  c111,
  c49,
  0,
  c182,
  c210,
  c247,
  c182,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  0,
  c11,
  0,
  0,
  180,
  c86,
  c131,
  c86,
  c49,
  0,
  c108,
  c86,
  c247,
  c108,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  c16,
  0,
  c90,
  c10,
  c0,
  c90,
  c40,
  c40,
  c37,
  0,
  0,
  c16,
  0,
  c11,
  0,
  0,
  c111,
  c144,
  c136,
  c111,
  c49,
  0,
  c182,
  c144,
  34530218951327728683122963588519954038815371,
  c144,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  0,
  c11,
  0,
  0,
  c252,
  c128,
  c128,
  c136,
  c49,
  0,
  c108,
  c299,
  46040283062851163875824760733867151773236379,
  c108,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  c16,
  0,
  c90,
  c10,
  c0,
  c90,
  0,
  c90,
  0,
  c224,
  c15,
  0,
  c85,
  4648874290158473,
  c61,
  4648874290158473,
  c15,
  c21,
  c90,
  0,
  c16,
  c10,
  c0,
  c16,
  c37,
  c70,
  0,
  0,
  0,
  c154,
  c100,
  c73,
  c154,
  0,
  c242,
  0,
  c124,
  0,
  0,
  c191,
  5229987708377241,
  c131,
  c131,
  c127,
  c137,
  c127,
  c196,
  c124,
  c45,
  c45,
  c40,
  c40,
  c37,
  0,
  0,
  0,
  c11,
  c35,
  c347,
  c35,
  c6,
  c73,
  c6,
  0,
  c242,
  c6,
  c138,
  c6,
  0,
  46040248150975296121846912535639344930408219,
  c6,
  c21,
  c6,
  0,
  0,
  c91,
  c15,
  c347,
  c15,
  c6,
  c73,
  c6,
  c37,
  c70,
  0,
  c150,
  0,
  c26,
  c76,
  0,
  0,
  c24,
  c20,
  0,
  c11,
  c245,
  c264,
  c11,
  c24,
  0,
  c4,
  c20,
  c152,
  c4,
  0,
  c4,
  c20,
  c84,
  c4,
  0,
  c24,
  c20,
  0,
  c294,
  c15,
  c264,
  c15,
  c24,
  c76,
  c97,
  0,
  c26,
  c76,
  0,
  c29,
  0,
  c8,
  c6,
  c0,
  c8,
  0,
  c8,
  c6,
  c84,
  c8,
  c29,
  c76,
  0,
  0,
  0,
  c27,
  0,
  0,
  c130,
  c318,
  34530218580725005103999182333106617655051019,
  c130,
  0,
  c317,
  c318,
  c0,
  c317,
  c125,
  c125,
  c63,
  c27,
  0,
  c27,
  c77,
  c63,
  c77,
  0,
  c27,
  0,
  0,
  0,
  0,
  0,
  c74,
  76,
  c257,
  c74,
  0,
  c74,
  68,
  c257,
  c74,
  0,
  c74,
  60,
  c257,
  c74,
  0,
  c74,
  84,
  c257,
  c74,
  c35,
  c57,
  c35,
  c87,
  c87,
  c58,
  0,
  c88,
  c58,
  c189,
  c88,
  c125,
  c125,
  c63,
  c27,
  0,
  c27,
  c77,
  c63,
  c77,
  0,
  c150,
  0,
  c255,
  0,
  0,
  c143,
  c98,
  0,
  46040248151829692627425924015788847018367387,
  c286,
  c57,
  c286,
  c143,
  0,
  c4,
  c98,
  c330,
  c4,
  0,
  c4,
  c98,
  c243,
  c4,
  0,
  c143,
  c98,
  0,
  c221,
  0,
  3977919630235001,
  0,
  2905553035711577,
  c177,
  c126,
  2905553035711577,
  c14,
  c14,
  c57,
  c221,
  c143,
  c155,
  0,
  0,
  c143,
  c98,
  c3,
  c3,
  0,
  c4,
  c98,
  c330,
  c4,
  0,
  c4,
  c98,
  c243,
  c4,
  0,
  c143,
  c98,
  c3,
  c3,
  c97,
  0,
  c255,
  0,
  0,
  0,
  c285,
  c35,
  c57,
  c35,
  c87,
  c87,
  0,
  c285,
  c35,
  c57,
  c35,
  0,
  c88,
  c10,
  c0,
  c88,
  0,
  c88,
  0,
  c221,
  0,
  c13,
  0,
  c132,
  5229988497184665,
  c126,
  c132,
  3970831009420665,
  c13,
  c57,
  c221,
  c243,
  c88,
  0,
  0,
  c91,
  0,
  c175,
  0,
  c74,
  c83,
  c126,
  c74,
  c174,
  0,
  c167,
  c83,
  1670689995108938,
  c167,
  c57,
  c91,
  c87,
  c87,
  0,
  c91,
  0,
  c13,
  0,
  c132,
  c177,
  c126,
  c132,
  c14,
  c13,
  c57,
  c91,
  c155,
  0,
  0,
  0,
  c285,
  c35,
  c57,
  c35,
  c6,
  c3,
  c3,
  0,
  c88,
  c6,
  c0,
  c6,
  0,
  c88,
  c6,
  c243,
  c6,
  0,
  0,
  c91,
  0,
  c175,
  0,
  c74,
  c178,
  1452774282496554,
  c178,
  c174,
  0,
  c167,
  c178,
  44,
  c167,
  c57,
  c91,
  c6,
  c3,
  c3,
  0,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c150,
  0,
  c27,
  c77,
  c155,
  c77,
  c97,
  0,
  c27,
  c77,
  c155,
  c77,
  0,
  0,
  0,
  0,
  0,
  c130,
  0,
  0,
  0,
  c81,
  308,
  c112,
  c81,
  c19,
  0,
  c218,
  c250,
  c269,
  c187,
  c19,
  0,
  0,
  c81,
  316,
  c112,
  c81,
  c19,
  0,
  c218,
  c250,
  c269,
  c187,
  c19,
  0,
  0,
  c81,
  300,
  c112,
  c81,
  c19,
  0,
  c218,
  c250,
  c269,
  c187,
  c19,
  0,
  0,
  c81,
  324,
  c112,
  c81,
  c19,
  0,
  c218,
  c250,
  c269,
  c187,
  c19,
  0,
  c123,
  0,
  0,
  c211,
  c162,
  c112,
  c112,
  c19,
  0,
  c108,
  c162,
  c314,
  c108,
  c19,
  0,
  0,
  c211,
  c162,
  c112,
  c112,
  c19,
  0,
  c324,
  c162,
  c314,
  c162,
  c19,
  c123,
  c130,
  0,
  c90,
  c10,
  c0,
  c90,
  c28,
  c28,
  80677897,
  0,
  0,
  c130,
  0,
  c56,
  0,
  0,
  c81,
  c144,
  c168,
  c81,
  c19,
  0,
  c187,
  c144,
  c319,
  c144,
  c19,
  0,
  0,
  c81,
  c144,
  c168,
  c81,
  c19,
  0,
  c187,
  c144,
  c141,
  c144,
  c19,
  c56,
  0,
  c123,
  0,
  0,
  c211,
  c234,
  c168,
  c168,
  c19,
  0,
  c108,
  c234,
  c319,
  c108,
  c19,
  0,
  0,
  c211,
  c234,
  c168,
  c168,
  c19,
  0,
  c324,
  c234,
  c141,
  c141,
  c19,
  c123,
  c130,
  0,
  c90,
  c10,
  c0,
  c90,
  c194,
  c194,
  80677897,
  c80,
  0,
  0,
  0,
  c232,
  c312,
  c55,
  c232,
  0,
  c232,
  c312,
  0,
  0,
  0,
  c211,
  c305,
  c112,
  c112,
  c306,
  0,
  c92,
  34530186113883473865428402550205156911164683,
  34530186113883473865428402550205156911605515,
  c92,
  c306,
  0,
  0,
  2905551140167001,
  c305,
  c112,
  c112,
  28775155142161509013036450099584038343384451,
  c14,
  c14,
  c196,
  c196,
  c232,
  c28,
  c28,
  2581692937,
  0,
  0,
  51795279169925587791528984200620137732747811,
  c6,
  c55,
  c6,
  0,
  c287,
  c6,
  c138,
  c6,
  c194,
  c194,
  2581692937,
  c80,
  0,
  c93,
  0,
  0,
  0,
  c4,
  0,
  c195,
  0,
  c42,
  c96,
  c33,
  c96,
  0,
  0,
  c47,
  c180,
  c113,
  c113,
  c50,
  0,
  c212,
  c180,
  c181,
  c181,
  c50,
  c195,
  0,
  c123,
  0,
  c42,
  c96,
  c33,
  c96,
  0,
  0,
  c135,
  c162,
  c113,
  c113,
  c50,
  0,
  51795279170790125500884661224080457005388451,
  c162,
  c181,
  c162,
  c50,
  c123,
  c4,
  0,
  c4,
  0,
  c195,
  0,
  c42,
  c89,
  c33,
  c89,
  0,
  0,
  c47,
  c180,
  c113,
  c113,
  c50,
  0,
  c212,
  c180,
  c181,
  c181,
  c50,
  c195,
  0,
  c262,
  0,
  c42,
  c89,
  c14,
  c14,
  0,
  0,
  c135,
  c180,
  c113,
  c113,
  c50,
  0,
  c164,
  c180,
  c181,
  c164,
  c50,
  c262,
  c4,
  c28,
  c28,
  c166,
  0,
  0,
  c4,
  0,
  c56,
  0,
  c42,
  c96,
  c33,
  c96,
  0,
  0,
  c47,
  c114,
  284,
  c47,
  c50,
  0,
  c212,
  c114,
  c141,
  c114,
  c50,
  c56,
  0,
  c123,
  0,
  c42,
  c96,
  c33,
  c96,
  0,
  0,
  c273,
  c268,
  c254,
  c135,
  c50,
  0,
  83447948986429120174466931391070220908694699,
  c298,
  c141,
  c141,
  c50,
  c123,
  c4,
  0,
  c4,
  0,
  c56,
  0,
  c42,
  c89,
  c33,
  c89,
  0,
  0,
  c47,
  c114,
  276,
  c47,
  c50,
  0,
  c212,
  c114,
  c141,
  c114,
  c50,
  c56,
  0,
  c56,
  0,
  c42,
  3980750176597625,
  c14,
  c14,
  0,
  0,
  c273,
  c268,
  c254,
  c135,
  c50,
  0,
  c164,
  c298,
  c141,
  c141,
  c50,
  c56,
  c4,
  0,
  c4,
  0,
  c56,
  0,
  c42,
  c96,
  c33,
  c96,
  0,
  0,
  c47,
  c114,
  236,
  c47,
  c50,
  c266,
  c50,
  c56,
  0,
  c52,
  0,
  c42,
  c96,
  c33,
  c96,
  0,
  0,
  c273,
  c268,
  c254,
  c135,
  c50,
  c266,
  c50,
  c52,
  c4,
  0,
  c4,
  0,
  c56,
  0,
  c42,
  c89,
  c33,
  c89,
  0,
  0,
  c47,
  c114,
  292,
  c47,
  c50,
  c266,
  c50,
  c56,
  0,
  c56,
  0,
  c42,
  3980750176597625,
  c14,
  c14,
  0,
  0,
  c273,
  c268,
  c254,
  c135,
  c50,
  c266,
  c50,
  c56,
  c4,
  c166,
  c97,
  c93,
  0,
  c94,
  0,
  0,
  c104,
  0,
  c122,
  0,
  c195,
  0,
  c38,
  c120,
  c352,
  c38,
  0,
  c38,
  c348,
  c217,
  c38,
  c195,
  0,
  c262,
  0,
  c38,
  c120,
  c14,
  c14,
  0,
  c38,
  c348,
  c217,
  c38,
  c262,
  c122,
  c28,
  c28,
  c166,
  0,
  c104,
  0,
  c122,
  0,
  c56,
  0,
  c95,
  c120,
  0,
  581113285321753,
  c114,
  28775155094819829696912994871318514437793155,
  c114,
  c120,
  0,
  c95,
  c230,
  c61,
  c95,
  c56,
  0,
  c56,
  0,
  c95,
  c120,
  c14,
  c14,
  0,
  c95,
  c230,
  c61,
  c95,
  c56,
  c122,
  0,
  c122,
  0,
  c56,
  0,
  c95,
  c17,
  0,
  c212,
  c114,
  c302,
  c114,
  c17,
  0,
  c95,
  c230,
  c61,
  c95,
  c56,
  0,
  c52,
  0,
  c95,
  c17,
  0,
  c117,
  28775155094819829696912994871288190076923395,
  c302,
  c117,
  c17,
  0,
  c95,
  c230,
  c61,
  c95,
  c52,
  c122,
  c104,
  c166,
  0,
  0,
  c104,
  0,
  c340,
  69060372194746203489195520400014348416928459,
  0,
  0,
  c38,
  c54,
  0,
  c92,
  c325,
  c176,
  c176,
  c38,
  0,
  c38,
  c280,
  c14,
  c14,
  c196,
  c196,
  c340,
  c28,
  c28,
  0,
  c48,
  0,
  0,
  c91,
  c206,
  c57,
  c206,
  c238,
  c189,
  0,
  c91,
  c206,
  c57,
  c206,
  c338,
  c48,
  0,
  c104,
  0,
  c287,
  c6,
  c138,
  c6,
  0,
  c287,
  c6,
  0,
  c52,
  0,
  69060372227677230781924475537483532446902859,
  c17,
  0,
  c117,
  581112503845913,
  46040283062851163901775462530677257418407067,
  581112503845913,
  c17,
  c196,
  c52,
  c6,
  c104,
  0,
  c48,
  0,
  0,
  c91,
  c206,
  c57,
  c206,
  c6,
  c138,
  c6,
  c28,
  c48,
  c94,
  0,
  c150,
  c80,
  c97,
  c80,
  0,
  0,
  0,
  c106,
  80677897,
  c63,
  80677897,
  c80,
  0,
  c106,
  2581692937,
  c63,
  2581692937,
  c80,
  0,
  c93,
  c69,
  c97,
  c69,
  0,
  c94,
  c70,
  0,
  c106,
  0,
  0,
  0,
  c11,
  c35,
  c57,
  c35,
  c87,
  c87,
  0,
  c11,
  c35,
  c57,
  c35,
  0,
  c88,
  c238,
  c189,
  c88,
  0,
  c88,
  0,
  c221,
  c15,
  c57,
  c15,
  c21,
  c88,
  0,
  0,
  c91,
  c15,
  c57,
  c15,
  c87,
  c87,
  0,
  c91,
  c15,
  c57,
  c15,
  c63,
  0,
  0,
  0,
  c11,
  c35,
  c57,
  c35,
  c6,
  c3,
  c3,
  0,
  c88,
  c6,
  c138,
  c6,
  0,
  c88,
  c6,
  c21,
  c6,
  0,
  0,
  c91,
  c15,
  c57,
  c15,
  c6,
  c3,
  c3,
  c70,
  0,
  c150,
  c80,
  c97,
  c80,
  0,
  0,
  0,
  c71,
  0,
  c26,
  0,
  c105,
  0,
  0,
  c209,
  c310,
  46040248150876419375242181200897865020674075,
  c209,
  c20,
  c152,
  c20,
  0,
  0,
  0,
  c119,
  0,
  260,
  252,
  244,
  268,
  c173,
  c119,
  c204,
  c204,
  c153,
  c20,
  c84,
  c20,
  c105,
  c157,
  c26,
  c72,
  0,
  c26,
  c75,
  c157,
  c26,
  0,
  0,
  0,
  0,
  c16,
  c1,
  0,
  c11,
  0,
  c25,
  c183,
  c33,
  c25,
  0,
  c25,
  c134,
  0,
  c278,
  c86,
  34530227344112763638170488659729348634433931,
  c86,
  c134,
  c11,
  c16,
  0,
  0,
  c115,
  0,
  c175,
  0,
  340,
  c83,
  c126,
  c83,
  c174,
  c25,
  0,
  c25,
  c134,
  c236,
  c134,
  c115,
  c1,
  c0,
  c1,
  c40,
  c40,
  0,
  c105,
  0,
  0,
  c115,
  0,
  c175,
  0,
  348,
  c83,
  c126,
  c83,
  c174,
  c25,
  c197,
  c115,
  c1,
  c0,
  c1,
  0,
  0,
  c147,
  c179,
  c197,
  c147,
  c1,
  c21,
  c1,
  c105,
  0,
  0,
  c16,
  c1,
  0,
  c11,
  0,
  c25,
  c183,
  c33,
  c25,
  0,
  c25,
  c134,
  0,
  c278,
  28775155094049098131738586201197135660063107,
  c110,
  c110,
  c134,
  c11,
  c16,
  0,
  0,
  c115,
  0,
  c175,
  0,
  332,
  c83,
  c126,
  c83,
  c174,
  c25,
  0,
  c25,
  c134,
  c236,
  c134,
  c115,
  c1,
  c0,
  c1,
  0,
  0,
  c147,
  c179,
  c32,
  c147,
  c1,
  c21,
  c1,
  0,
  c16,
  c1,
  c0,
  c16,
  0,
  c105,
  0,
  0,
  c115,
  0,
  c175,
  0,
  356,
  c83,
  c126,
  c83,
  c174,
  c25,
  c197,
  c115,
  c1,
  c0,
  c1,
  c40,
  c105,
  c69,
  0,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c2,
  0,
  c7,
  0,
  c25,
  c186,
  c137,
  c25,
  0,
  c25,
  c51,
  0,
  c249,
  c129,
  c129,
  c149,
  c51,
  c7,
  c45,
  c2,
  c40,
  c40,
  c75,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c2,
  0,
  c7,
  0,
  c25,
  c186,
  c137,
  c25,
  0,
  c25,
  c51,
  0,
  108,
  c46,
  c110,
  c46,
  c51,
  c7,
  c45,
  c2,
  0,
  c5,
  0,
  c62,
  c31,
  c32,
  c62,
  c21,
  c5,
  0,
  c2,
  c82,
  c55,
  c2,
  c75,
  c69,
  0,
  0,
  0,
  0,
  c16,
  c1,
  0,
  c11,
  0,
  0,
  188,
  c86,
  c131,
  c86,
  c49,
  c265,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  c16,
  0,
  0,
  c115,
  0,
  c228,
  c127,
  c301,
  c127,
  0,
  c228,
  c30,
  c236,
  c30,
  c115,
  c1,
  c0,
  c1,
  c40,
  c40,
  c37,
  0,
  0,
  c16,
  c1,
  0,
  c11,
  0,
  0,
  c252,
  c128,
  c128,
  c136,
  c49,
  c265,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  c16,
  0,
  0,
  c115,
  0,
  c228,
  c127,
  c301,
  c127,
  0,
  c228,
  c30,
  c236,
  c30,
  c115,
  c1,
  c0,
  c1,
  0,
  0,
  c224,
  c15,
  c32,
  c15,
  c1,
  c21,
  c1,
  0,
  c16,
  c1,
  c0,
  c16,
  c37,
  c70,
  0,
  0,
  0,
  c154,
  c100,
  c73,
  c154,
  0,
  c2,
  0,
  c7,
  0,
  0,
  c191,
  40285217132851512643513646440434395933228691,
  c131,
  c131,
  c127,
  c137,
  c127,
  0,
  c85,
  c99,
  c61,
  c99,
  c7,
  c45,
  c2,
  c40,
  c40,
  c37,
  0,
  0,
  c261,
  c100,
  c73,
  c261,
  0,
  c2,
  0,
  c7,
  0,
  0,
  c191,
  c46,
  46040248151837298530239371703854659976358299,
  c46,
  c127,
  c137,
  c127,
  0,
  c85,
  c99,
  c61,
  c99,
  c7,
  c45,
  c2,
  0,
  c244,
  0,
  c346,
  c15,
  c32,
  c15,
  c21,
  c21,
  0,
  c2,
  c100,
  c73,
  c2,
  c37,
  c70,
  0,
  c71,
  0,
  c26,
  c37,
  c157,
  c37,
  c72,
  0,
  c26,
  c37,
  c157,
  c37,
  0,
  0,
  c71,
  0,
  c27,
  0,
  51795279169852064056715241483368753617381155,
  0,
  c60,
  c20,
  0,
  c246,
  c9,
  c197,
  c9,
  c20,
  c334,
  c334,
  c67,
  c27,
  c72,
  0,
  c27,
  c75,
  c67,
  c27,
  0,
  0,
  0,
  0,
  c151,
  c1,
  c3,
  c3,
  0,
  c101,
  c1,
  c0,
  c1,
  0,
  c102,
  c1,
  0,
  c235,
  c31,
  c32,
  c235,
  c1,
  0,
  c151,
  c1,
  c3,
  c3,
  0,
  0,
  c151,
  c1,
  c239,
  c1,
  0,
  c101,
  c1,
  c0,
  c1,
  0,
  c102,
  c1,
  0,
  c274,
  c31,
  c197,
  c274,
  c1,
  0,
  c151,
  c1,
  c239,
  c1,
  0,
  0,
  c151,
  c1,
  0,
  c123,
  c170,
  0,
  40285217131999651440160275562052670993378067,
  c134,
  0,
  34530227343511897253662307923419911315085579,
  c177,
  c110,
  c110,
  c134,
  c123,
  c1,
  0,
  c101,
  c1,
  c0,
  c1,
  0,
  c102,
  c1,
  0,
  c235,
  c31,
  c32,
  c235,
  c1,
  0,
  c151,
  c1,
  c0,
  c1,
  0,
  0,
  c151,
  c1,
  c3,
  c3,
  0,
  c101,
  c1,
  c0,
  c1,
  0,
  c102,
  c1,
  0,
  c274,
  c31,
  c197,
  c274,
  c1,
  0,
  c151,
  c1,
  c3,
  c3,
  0,
  0,
  0,
  c4,
  c59,
  c3,
  c3,
  0,
  c4,
  c59,
  0,
  c246,
  c9,
  c34,
  c34,
  c4,
  0,
  c4,
  c59,
  0,
  c52,
  c31,
  c34,
  c34,
  c4,
  0,
  c4,
  c59,
  c3,
  c3,
  0,
  74815403245562695947414274166760354203109171,
  0,
  c4,
  c59,
  0,
  c246,
  c9,
  c34,
  c34,
  c4,
  c345,
  c345,
  c67,
  c67,
  0,
  0,
  0,
  c5,
  c188,
  c3,
  c3,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  0,
  c47,
  c149,
  c313,
  c47,
  c51,
  0,
  c249,
  c129,
  c129,
  c149,
  c51,
  c7,
  0,
  c7,
  c9,
  0,
  0,
  c279,
  c39,
  c213,
  c39,
  c51,
  0,
  c164,
  c39,
  c320,
  c39,
  c51,
  c7,
  c2,
  0,
  c5,
  0,
  c62,
  c31,
  c32,
  c62,
  0,
  c62,
  c31,
  c32,
  c62,
  c5,
  0,
  c2,
  c188,
  c3,
  c3,
  c75,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  0,
  c47,
  c46,
  c213,
  c47,
  c51,
  0,
  36,
  c46,
  c110,
  c46,
  c51,
  c7,
  0,
  c7,
  c9,
  0,
  0,
  c279,
  c241,
  c213,
  c279,
  c51,
  0,
  c164,
  c241,
  c110,
  c110,
  c51,
  c7,
  c2,
  0,
  c5,
  0,
  c62,
  c31,
  c32,
  c62,
  0,
  c62,
  c31,
  c32,
  c62,
  c5,
  0,
  c2,
  c82,
  c55,
  c2,
  c75,
  0,
  0,
  0,
  0,
  c64,
  c35,
  c34,
  c64,
  c169,
  c3,
  c3,
  0,
  c2,
  c10,
  c0,
  c2,
  0,
  c102,
  0,
  0,
  c13,
  4648879689653385,
  c173,
  c13,
  c31,
  c34,
  c34,
  0,
  c52,
  c31,
  c34,
  c34,
  c102,
  0,
  c2,
  c169,
  c3,
  c3,
  c75,
  c67,
  c75,
  0,
  0,
  0,
  c36,
  0,
  c60,
  c1,
  c0,
  c1,
  0,
  c53,
  c1,
  0,
  c52,
  c31,
  c32,
  c52,
  c1,
  c36,
  c12,
  0,
  c36,
  0,
  c60,
  c1,
  c0,
  c1,
  0,
  c53,
  c1,
  0,
  c52,
  c31,
  c32,
  c52,
  c1,
  c36,
  c12,
  0,
  0,
  c36,
  0,
  c60,
  c59,
  0,
  c246,
  c9,
  0,
  c65,
  290557992716545,
  c61,
  290557992716545,
  c9,
  c59,
  0,
  c53,
  c59,
  0,
  c52,
  c31,
  c32,
  c52,
  c59,
  c36,
  c12,
  c67,
  c12,
  0,
  0,
  c36,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  c85,
  c99,
  c61,
  c99,
  c7,
  0,
  c7,
  c9,
  0,
  c85,
  c190,
  c61,
  c190,
  c7,
  c2,
  0,
  c53,
  0,
  c193,
  c31,
  c32,
  c193,
  0,
  c52,
  c31,
  c32,
  c52,
  c53,
  c36,
  c12,
  0,
  c36,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  c85,
  c99,
  c61,
  c99,
  c7,
  0,
  c7,
  c9,
  0,
  c85,
  c190,
  c61,
  c190,
  c7,
  c2,
  0,
  c53,
  0,
  c193,
  c31,
  c32,
  c193,
  0,
  c52,
  c31,
  c32,
  c52,
  c53,
  c36,
  c12,
  0,
  0,
  c36,
  0,
  c2,
  c10,
  c0,
  c2,
  0,
  c53,
  0,
  c193,
  c31,
  c32,
  c193,
  0,
  c52,
  c31,
  c32,
  c52,
  c53,
  c36,
  c12,
  c67,
  c12,
  0,
  c71,
  0,
  c27,
  c12,
  c67,
  c12,
  c72,
  0,
  c27,
  c12,
  c67,
  c12,
  0,
  0,
  c71,
  0,
  0,
  c333,
  0,
  c185,
  c121,
  0,
  c297,
  c349,
  80570434138802612893662684670901663300657603,
  c297,
  c185,
  c28,
  c28,
  c23,
  c67,
  c23,
  c72,
  0,
  0,
  c333,
  0,
  c2,
  c10,
  c0,
  c2,
  c28,
  c28,
  c23,
  c67,
  c23,
  0,
  c93,
  0,
  0,
  0,
  c4,
  c59,
  0,
  c223,
  0,
  c42,
  4648880478460809,
  c33,
  4648880478460809,
  c34,
  c34,
  c4,
  0,
  c4,
  c59,
  0,
  c223,
  c350,
  c34,
  c34,
  c4,
  c28,
  c28,
  0,
  c48,
  0,
  c4,
  c59,
  0,
  c223,
  c350,
  c34,
  c34,
  c4,
  0,
  c4,
  c59,
  0,
  c223,
  c31,
  c34,
  c34,
  c4,
  c48,
  c67,
  c67,
  0,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c2,
  0,
  c7,
  0,
  c42,
  c89,
  c137,
  c89,
  0,
  0,
  c47,
  28775155094906029938517504340707021685435139,
  c113,
  c113,
  c51,
  0,
  c249,
  c129,
  c129,
  c149,
  c51,
  c7,
  0,
  c7,
  0,
  c42,
  c89,
  c14,
  c14,
  0,
  0,
  c135,
  28775155094906029938517506934780407050841219,
  c113,
  c113,
  c51,
  0,
  c164,
  c325,
  c320,
  c164,
  c51,
  c7,
  c2,
  c28,
  c28,
  c75,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c2,
  0,
  c7,
  0,
  c42,
  c89,
  c137,
  c89,
  0,
  0,
  c47,
  c46,
  c213,
  c47,
  c51,
  0,
  100,
  c46,
  c110,
  c46,
  c51,
  c7,
  0,
  c7,
  0,
  c42,
  c89,
  c14,
  c14,
  0,
  0,
  c135,
  c241,
  c213,
  c135,
  c51,
  0,
  c164,
  c241,
  c110,
  c110,
  c51,
  c7,
  c2,
  0,
  c5,
  0,
  c62,
  c31,
  c32,
  c62,
  0,
  c62,
  c31,
  c32,
  c62,
  c5,
  0,
  c2,
  c82,
  c55,
  c2,
  c75,
  c93,
  0,
  c94,
  0,
  0,
  c104,
  0,
  0,
  c209,
  0,
  c38,
  c120,
  c352,
  c38,
  c118,
  c209,
  c59,
  0,
  c227,
  0,
  c38,
  c120,
  c14,
  c14,
  c118,
  c118,
  c59,
  c28,
  c28,
  0,
  c48,
  0,
  0,
  c209,
  0,
  c65,
  c120,
  83447949775113152913663093301513426278992555,
  c120,
  c118,
  c209,
  c59,
  0,
  c227,
  0,
  c65,
  c120,
  c14,
  c14,
  c118,
  c118,
  c59,
  0,
  0,
  c227,
  c153,
  c118,
  c118,
  c59,
  0,
  c227,
  c31,
  c118,
  c118,
  c59,
  c48,
  c67,
  c67,
  0,
  0,
  c104,
  0,
  c2,
  0,
  c7,
  0,
  c38,
  c281,
  c137,
  c38,
  0,
  c38,
  c275,
  c217,
  c275,
  c7,
  0,
  c7,
  0,
  c38,
  c280,
  c14,
  c14,
  0,
  c38,
  40285217132025004452164840870682172606034963,
  c217,
  c38,
  c7,
  c2,
  c28,
  c28,
  c75,
  0,
  c104,
  0,
  c2,
  0,
  c7,
  0,
  0,
  c191,
  c46,
  c207,
  c46,
  c281,
  c137,
  c281,
  0,
  c85,
  c99,
  c61,
  c99,
  c7,
  0,
  c7,
  0,
  83447949739413576710035654814928352465077035,
  c280,
  c14,
  c14,
  0,
  c85,
  c190,
  c61,
  c190,
  c7,
  c2,
  0,
  0,
  c267,
  c153,
  c32,
  c267,
  0,
  c336,
  c31,
  c32,
  c336,
  0,
  c52,
  c31,
  c32,
  c52,
  0,
  c267,
  c153,
  c32,
  c267,
  c104,
  c75,
  c94,
  0,
  c71,
  0,
  0,
  c104,
  0,
  c4,
  c121,
  0,
  c297,
  c349,
  c34,
  c34,
  c4,
  c28,
  c28,
  c23,
  c67,
  c23,
  c72,
  0,
  0,
  c104,
  0,
  c2,
  c10,
  c0,
  c2,
  c28,
  c28,
  c23,
  c67,
  c23,
  0,
  0,
  c71,
  0,
  0,
  0,
  c24,
  c121,
  c3,
  c24,
  0,
  c185,
  c121,
  c152,
  c185,
  0,
  c185,
  c121,
  c84,
  c185,
  0,
  c24,
  c121,
  c3,
  c24,
  c23,
  c157,
  c23,
  c72,
  0,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  0,
  c8,
  0,
  0,
  c119,
  c19,
  c173,
  c119,
  c204,
  c204,
  0,
  c119,
  c208,
  0,
  c218,
  c129,
  c129,
  92,
  c208,
  c84,
  c8,
  c29,
  c23,
  c157,
  c23,
  0,
  c93,
  c69,
  0,
  0,
  0,
  c5,
  c188,
  c3,
  c3,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  c25,
  c51,
  0,
  c249,
  c129,
  c129,
  c149,
  c51,
  c7,
  c45,
  c2,
  0,
  c5,
  0,
  c62,
  c31,
  c32,
  c62,
  c21,
  c5,
  0,
  c2,
  c188,
  c3,
  c3,
  c75,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  c25,
  c51,
  0,
  116,
  c46,
  c110,
  c46,
  c51,
  c7,
  c45,
  c2,
  0,
  c5,
  0,
  c62,
  c31,
  c32,
  c62,
  c21,
  c5,
  0,
  c2,
  c82,
  c55,
  c2,
  c75,
  c69,
  0,
  c94,
  c70,
  0,
  0,
  0,
  0,
  c64,
  c35,
  0,
  c38,
  0,
  c74,
  581110472830489,
  c176,
  581110472830489,
  5891845567436457,
  c38,
  c64,
  c100,
  c3,
  c3,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  c38,
  c275,
  c217,
  c275,
  c7,
  c45,
  c2,
  0,
  c244,
  0,
  0,
  3970839051851129,
  c277,
  c173,
  3970839051851129,
  c15,
  c32,
  c15,
  c21,
  c21,
  0,
  c2,
  c100,
  c3,
  c3,
  c75,
  0,
  0,
  c261,
  c100,
  c73,
  c261,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  c85,
  c99,
  c61,
  c99,
  c7,
  c45,
  c2,
  0,
  c244,
  0,
  c346,
  c15,
  c32,
  c15,
  c21,
  c21,
  0,
  c2,
  c100,
  c73,
  c2,
  c75,
  c70,
  0,
  c71,
  0,
  0,
  0,
  c24,
  c121,
  c3,
  c24,
  0,
  c4,
  c121,
  c152,
  c4,
  0,
  c4,
  c121,
  c84,
  c4,
  0,
  c24,
  c121,
  c3,
  c24,
  c23,
  c157,
  c23,
  c72,
  0,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  0,
  c8,
  0,
  0,
  c13,
  c277,
  c173,
  c13,
  c15,
  c34,
  c15,
  c84,
  c8,
  c29,
  c23,
  c157,
  c23,
  0,
  0,
  0,
  0,
  c26,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  0,
  c8,
  51795279170797731404485476693764073670736547,
  c21,
  c8,
  c29,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  0,
  c8,
  0,
  c296,
  80570433295604533742253414504429745707945539,
  80570434265567672916486792730056150552677955,
  c296,
  c21,
  c8,
  c29,
  c26,
  0,
  c26,
  0,
  c105,
  0,
  0,
  c309,
  c310,
  c339,
  c309,
  c20,
  c152,
  c20,
  0,
  0,
  c203,
  c153,
  c339,
  c203,
  c20,
  c84,
  c20,
  c105,
  c158,
  c26,
  0,
  c26,
  c41,
  0,
  0,
  c24,
  c58,
  c55,
  c24,
  0,
  c263,
  c58,
  c45,
  c58,
  0,
  0,
  c311,
  c153,
  c22,
  c311,
  c58,
  c21,
  c58,
  0,
  c24,
  c58,
  c55,
  c24,
  c26,
  0,
  c26,
  c41,
  c158,
  c26,
  0,
  0,
  0,
  0,
  c16,
  0,
  c11,
  0,
  c13,
  c237,
  c33,
  c13,
  0,
  c13,
  c184,
  c292,
  c13,
  c11,
  0,
  c11,
  0,
  c25,
  c183,
  c33,
  c25,
  0,
  c25,
  c183,
  0,
  c278,
  c86,
  5229987765647513,
  c86,
  c25,
  c11,
  c16,
  0,
  0,
  c145,
  c198,
  c201,
  c145,
  c10,
  c0,
  c45,
  c40,
  c40,
  0,
  c105,
  0,
  0,
  c145,
  c198,
  c201,
  c145,
  c10,
  c0,
  c45,
  0,
  0,
  c203,
  c179,
  0,
  c25,
  c184,
  83447949775138505925667658610119300706609835,
  c25,
  c203,
  0,
  c203,
  c179,
  0,
  c13,
  c184,
  c292,
  c13,
  c203,
  c21,
  c21,
  c105,
  0,
  0,
  c16,
  0,
  c11,
  0,
  c13,
  c237,
  c33,
  c13,
  0,
  c13,
  c184,
  c44,
  c13,
  c11,
  0,
  c11,
  0,
  c25,
  c183,
  c33,
  c25,
  0,
  c25,
  c183,
  c44,
  c44,
  c11,
  c16,
  0,
  0,
  c145,
  c198,
  c201,
  c145,
  c10,
  c0,
  c45,
  0,
  0,
  c147,
  c179,
  0,
  c25,
  c184,
  c44,
  c44,
  c147,
  0,
  c147,
  c179,
  0,
  c13,
  c184,
  c44,
  c13,
  c147,
  c21,
  c21,
  0,
  c16,
  c10,
  c0,
  c16,
  0,
  c105,
  0,
  0,
  c145,
  c198,
  c201,
  c145,
  c10,
  c0,
  c45,
  c40,
  c105,
  c69,
  0,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c5,
  0,
  c124,
  c171,
  c22,
  c124,
  c45,
  c5,
  c40,
  c40,
  c41,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c5,
  0,
  c124,
  c171,
  c22,
  c124,
  c45,
  c5,
  0,
  c5,
  0,
  c344,
  0,
  c25,
  290557737879809,
  c33,
  290557737879809,
  c22,
  c22,
  c21,
  c5,
  0,
  c5,
  c82,
  c55,
  c5,
  c41,
  c69,
  0,
  0,
  0,
  0,
  c16,
  0,
  c11,
  0,
  0,
  c111,
  c210,
  c131,
  c111,
  c49,
  0,
  c182,
  c210,
  c247,
  c182,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  0,
  c11,
  0,
  0,
  172,
  c86,
  c131,
  c86,
  c49,
  0,
  c108,
  c86,
  c247,
  c108,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  c16,
  0,
  0,
  c226,
  c198,
  c201,
  c226,
  c10,
  c0,
  c45,
  c40,
  c40,
  c37,
  0,
  0,
  c16,
  0,
  c11,
  0,
  0,
  c111,
  c304,
  c136,
  c111,
  c49,
  0,
  c182,
  c210,
  c165,
  c165,
  c49,
  0,
  c107,
  c30,
  c44,
  c44,
  c11,
  0,
  c11,
  0,
  0,
  c252,
  c128,
  c128,
  c136,
  c49,
  0,
  c108,
  c299,
  c165,
  c108,
  c49,
  0,
  c107,
  c276,
  c44,
  c276,
  c11,
  c16,
  0,
  0,
  c226,
  c198,
  c201,
  c226,
  c10,
  c0,
  c45,
  0,
  0,
  c224,
  c15,
  c290,
  c15,
  0,
  c224,
  c15,
  c290,
  c15,
  c21,
  c21,
  0,
  c16,
  c10,
  c0,
  c16,
  c37,
  c70,
  0,
  0,
  0,
  c154,
  c100,
  c73,
  c154,
  0,
  0,
  3486655034120553,
  c171,
  c22,
  3486655034120553,
  0,
  c124,
  c171,
  c22,
  c124,
  c45,
  c45,
  c40,
  c40,
  c37,
  0,
  0,
  c288,
  c100,
  c73,
  c288,
  0,
  c263,
  0,
  c124,
  c171,
  c22,
  c124,
  c45,
  c45,
  0,
  0,
  46040248178511202460029643914656874506818715,
  c15,
  c22,
  c15,
  0,
  c344,
  c15,
  c22,
  c15,
  c21,
  c21,
  0,
  c263,
  c100,
  c73,
  c263,
  c37,
  c70,
  0,
  0,
  c26,
  c37,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  0,
  c8,
  0,
  c296,
  c15,
  c290,
  c15,
  c21,
  c8,
  c29,
  c37,
  0,
  c26,
  c37,
  c158,
  c37,
  0,
  c26,
  c37,
  0,
  0,
  c24,
  c58,
  c73,
  c24,
  0,
  c5,
  c58,
  c45,
  c5,
  0,
  c5,
  c58,
  c21,
  c5,
  0,
  c24,
  c58,
  c73,
  c24,
  c37,
  0,
  c26,
  c37,
  c158,
  c37,
  0,
  0,
  0,
  c27,
  0,
  0,
  c130,
  c321,
  c239,
  c130,
  0,
  c329,
  c10,
  c0,
  c329,
  c43,
  c43,
  0,
  0,
  c130,
  0,
  0,
  0,
  c81,
  c303,
  c168,
  c81,
  c19,
  0,
  40285217132843906739912276343449475334709267,
  c326,
  c142,
  c142,
  c19,
  c170,
  0,
  0,
  c81,
  c303,
  2905551204212057,
  c81,
  c19,
  c44,
  c44,
  c170,
  c259,
  c130,
  0,
  c60,
  c10,
  c0,
  c60,
  c125,
  c125,
  c27,
  0,
  c27,
  0,
  c342,
  0,
  c283,
  c20,
  c192,
  c20,
  c43,
  c43,
  c68,
  c27,
  0,
  c27,
  c41,
  0,
  0,
  c288,
  c58,
  c55,
  c58,
  0,
  c60,
  c58,
  0,
  0,
  0,
  c219,
  c253,
  c270,
  c139,
  c54,
  0,
  c92,
  52,
  c142,
  c92,
  c54,
  c9,
  c22,
  c9,
  c58,
  c125,
  c125,
  c27,
  0,
  c27,
  c41,
  c68,
  c27,
  0,
  0,
  0,
  0,
  c258,
  c169,
  c3,
  c3,
  0,
  c101,
  c10,
  c0,
  c101,
  0,
  c102,
  0,
  c18,
  0,
  c13,
  3967131513149049,
  c33,
  c13,
  0,
  c13,
  c216,
  c292,
  c13,
  c18,
  0,
  c18,
  0,
  c42,
  c103,
  c33,
  c103,
  0,
  0,
  581109441217561,
  c39,
  c328,
  581109441217561,
  c216,
  c291,
  c216,
  c18,
  c102,
  0,
  c258,
  c169,
  c3,
  c3,
  0,
  0,
  0,
  c161,
  c35,
  c295,
  c161,
  c321,
  c239,
  0,
  c161,
  c35,
  c295,
  c161,
  0,
  c283,
  c10,
  c0,
  c192,
  c43,
  c43,
  0,
  0,
  c341,
  0,
  0,
  c13,
  c237,
  0,
  c132,
  c326,
  c142,
  c132,
  c13,
  c170,
  0,
  c13,
  c237,
  c44,
  c13,
  c170,
  c259,
  c259,
  0,
  c101,
  c10,
  c0,
  c101,
  0,
  c102,
  0,
  c79,
  0,
  c13,
  80570434265613308338095008988510031890371907,
  c33,
  c13,
  0,
  c13,
  c216,
  c44,
  c13,
  c79,
  0,
  c79,
  0,
  c42,
  c103,
  c33,
  c103,
  0,
  83447949767015400879405121298714409793423915,
  c216,
  c44,
  c44,
  c79,
  c102,
  0,
  c341,
  c10,
  c0,
  c259,
  0,
  0,
  0,
  c161,
  c35,
  c295,
  c161,
  c169,
  c3,
  c3,
  0,
  c283,
  c10,
  c0,
  c192,
  c43,
  c43,
  0,
  0,
  0,
  c4,
  0,
  c289,
  c170,
  0,
  0,
  c47,
  581113291007001,
  c307,
  c47,
  c133,
  69060372235813012334189239874728763344499275,
  c133,
  c170,
  c3,
  c3,
  0,
  c4,
  0,
  c289,
  c9,
  c172,
  c9,
  0,
  c343,
  c9,
  c172,
  c9,
  c4,
  0,
  c4,
  0,
  c18,
  0,
  c42,
  c308,
  c33,
  c308,
  0,
  0,
  c47,
  34530186112958088927262776943888908159113611,
  c307,
  c47,
  c133,
  c291,
  c133,
  c18,
  0,
  c18,
  0,
  c42,
  c103,
  c33,
  c103,
  0,
  0,
  c284,
  c39,
  c328,
  c39,
  c133,
  c291,
  c133,
  c18,
  c4,
  0,
  c4,
  0,
  c18,
  c171,
  c172,
  c18,
  c3,
  c3,
  0,
  c342,
  0,
  c4,
  0,
  1162222946641449,
  c9,
  c172,
  1162222946641449,
  c192,
  c4,
  c43,
  c43,
  c68,
  c68,
  0,
  0,
  0,
  c5,
  c188,
  c3,
  c3,
  0,
  c5,
  0,
  0,
  0,
  c47,
  c149,
  c313,
  c47,
  c54,
  0,
  c240,
  c149,
  c214,
  c149,
  c54,
  c9,
  c22,
  c9,
  0,
  0,
  0,
  c139,
  c39,
  c214,
  c39,
  c54,
  0,
  c92,
  c39,
  c214,
  c39,
  c54,
  c9,
  c22,
  c9,
  c5,
  0,
  c5,
  0,
  c18,
  0,
  c42,
  c186,
  c33,
  c186,
  c22,
  c18,
  0,
  c18,
  0,
  c42,
  c103,
  c33,
  c103,
  c22,
  c18,
  c5,
  0,
  c5,
  c188,
  c3,
  c3,
  c41,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c5,
  0,
  0,
  0,
  c47,
  c46,
  34530186113049359770478203897071894303136779,
  c47,
  c54,
  0,
  c240,
  c46,
  c142,
  c46,
  c54,
  c9,
  c22,
  c9,
  0,
  0,
  0,
  c219,
  c253,
  c270,
  c139,
  c54,
  0,
  c92,
  28,
  c142,
  c92,
  c54,
  c9,
  c22,
  c9,
  c5,
  0,
  c5,
  0,
  c79,
  0,
  c42,
  c186,
  c33,
  c186,
  c22,
  c79,
  0,
  c79,
  0,
  c42,
  c103,
  c33,
  c103,
  c22,
  c79,
  c5,
  0,
  c5,
  c82,
  c55,
  c5,
  c41,
  0,
  0,
  0,
  c258,
  c169,
  c3,
  c3,
  0,
  c101,
  c10,
  c0,
  c101,
  0,
  c102,
  0,
  c18,
  0,
  c13,
  3967131513149049,
  c33,
  c13,
  c22,
  c18,
  0,
  c18,
  0,
  c42,
  c103,
  c33,
  c103,
  c22,
  c18,
  c102,
  0,
  c258,
  c169,
  c3,
  c3,
  c41,
  c68,
  c41,
  0,
  0,
  0,
  c36,
  0,
  c60,
  c10,
  c0,
  c60,
  0,
  c53,
  0,
  c18,
  0,
  0,
  c111,
  28775155094906029937728516920548140973765123,
  c163,
  c111,
  c17,
  0,
  c272,
  c271,
  c251,
  c215,
  c17,
  0,
  c85,
  c30,
  c61,
  c30,
  c18,
  0,
  c18,
  0,
  0,
  c284,
  c39,
  c163,
  c39,
  c17,
  0,
  c117,
  c39,
  132,
  c39,
  c17,
  0,
  c85,
  c30,
  c61,
  c30,
  c18,
  c53,
  c36,
  c12,
  0,
  c36,
  0,
  c60,
  c10,
  c0,
  c60,
  0,
  c53,
  0,
  c79,
  0,
  0,
  c111,
  c304,
  c136,
  c111,
  c17,
  0,
  c332,
  63305341208113396221732444880399746894598203,
  c165,
  c165,
  c17,
  0,
  c85,
  c30,
  c44,
  c44,
  c79,
  0,
  c79,
  0,
  0,
  c284,
  c327,
  c136,
  c136,
  c17,
  0,
  c117,
  c327,
  c165,
  c117,
  c17,
  0,
  c85,
  c30,
  c44,
  c44,
  c79,
  c53,
  c36,
  c12,
  0,
  0,
  c36,
  0,
  c60,
  0,
  c289,
  c9,
  c172,
  c9,
  0,
  c343,
  c9,
  c172,
  c9,
  c60,
  0,
  c53,
  0,
  c18,
  0,
  c65,
  c17,
  0,
  c272,
  c271,
  c251,
  c215,
  c17,
  0,
  c65,
  c337,
  c61,
  c65,
  c18,
  0,
  c18,
  0,
  c65,
  c17,
  0,
  c117,
  c39,
  124,
  c39,
  c17,
  0,
  c65,
  c337,
  c61,
  c65,
  c18,
  c53,
  c36,
  c12,
  c68,
  c12,
  0,
  0,
  c36,
  0,
  c60,
  0,
  0,
  0,
  c191,
  c282,
  c163,
  c163,
  c54,
  0,
  c240,
  c282,
  c214,
  c282,
  c54,
  c9,
  c22,
  c9,
  0,
  0,
  0,
  c139,
  c39,
  c163,
  c39,
  c54,
  0,
  c92,
  c39,
  c214,
  c39,
  c54,
  c9,
  c22,
  c9,
  c60,
  0,
  c53,
  0,
  c18,
  0,
  0,
  51795279170790125501140076499849708274102947,
  c215,
  c163,
  c163,
  c17,
  0,
  c272,
  c271,
  c251,
  c215,
  c17,
  c22,
  c18,
  0,
  c18,
  0,
  0,
  c139,
  c39,
  c163,
  c39,
  c17,
  0,
  c117,
  c39,
  4,
  c39,
  c17,
  c22,
  c18,
  c53,
  c36,
  c12,
  0,
  c36,
  0,
  c60,
  0,
  0,
  0,
  c191,
  c46,
  40285217131933733609986487563456523874298131,
  c46,
  c54,
  0,
  c240,
  c46,
  c142,
  c46,
  c54,
  c9,
  c22,
  c9,
  0,
  0,
  0,
  c219,
  c253,
  c270,
  c139,
  c54,
  0,
  c92,
  12,
  c142,
  c92,
  c54,
  c9,
  c22,
  c9,
  c60,
  0,
  c53,
  0,
  c79,
  0,
  0,
  51795279169885022972321930827565967499300643,
  c46,
  c335,
  c46,
  c17,
  0,
  c332,
  c46,
  c165,
  c46,
  c17,
  c22,
  c79,
  0,
  c79,
  0,
  0,
  c139,
  c331,
  c335,
  c139,
  c17,
  0,
  c117,
  c331,
  c165,
  c117,
  c17,
  c22,
  c79,
  c53,
  c36,
  c12,
  0,
  0,
  c36,
  0,
  c60,
  c10,
  c0,
  c60,
  0,
  c53,
  0,
  c18,
  0,
  c65,
  c17,
  0,
  c272,
  c271,
  c251,
  c215,
  c17,
  c22,
  c18,
  0,
  c18,
  0,
  c65,
  c17,
  0,
  c117,
  c39,
  140,
  c39,
  c17,
  c22,
  c18,
  c53,
  c36,
  c12,
  c68,
  c12,
  0,
  0,
  c27,
  c12,
  0,
  c36,
  0,
  c101,
  c10,
  c0,
  c101,
  c125,
  c36,
  c12,
  0,
  c27,
  c12,
  c68,
  c12,
  0,
  c27,
  c12,
  0,
  c36,
  0,
  c5,
  c58,
  0,
  0,
  0,
  c219,
  c253,
  c270,
  c139,
  c54,
  0,
  c92,
  148,
  c142,
  c92,
  c54,
  c9,
  c22,
  c9,
  c5,
  c125,
  c36,
  c12,
  0,
  c27,
  c12,
  c68,
  c12,
  0,
  0,
  0,
  c156,
  0,
  c48,
  0,
  0,
  0,
  c148,
  c19,
  c159,
  c19,
  c78,
  c78,
  0,
  c148,
  c222,
  0,
  581110559313433,
  c83,
  5229988613101465,
  581110559313433,
  c222,
  c10,
  c0,
  0,
  0,
  c148,
  c19,
  c159,
  c19,
  c78,
  c78,
  0,
  c148,
  c222,
  c14,
  c14,
  c194,
  c48,
  c260,
  0,
  c48,
  0,
  0,
  0,
  c148,
  c19,
  c159,
  c19,
  c78,
  c78,
  0,
  c148,
  c222,
  c44,
  c44,
  c10,
  c0,
  0,
  0,
  c148,
  c19,
  c159,
  c19,
  c78,
  c78,
  0,
  c148,
  c222,
  c14,
  c14,
  c28,
  c48,
  0,
  c66,
  c23,
  c68,
  c23,
  0,
  c66,
  c41,
  c116,
  c41,
  0,
  c156,
  c23,
  c68,
  c23,
  0,
  c93,
  0,
  c66,
  0,
  c48,
  0,
  c4,
  0,
  c225,
  c200,
  c199,
  c225,
  0,
  c225,
  c200,
  c199,
  c225,
  c4,
  0,
  c4,
  0,
  c109,
  0,
  c229,
  c231,
  c248,
  c231,
  0,
  c229,
  c133,
  c300,
  c133,
  c109,
  0,
  c109,
  0,
  c229,
  c231,
  c248,
  c231,
  0,
  c229,
  c133,
  c300,
  c133,
  c109,
  c4,
  c48,
  c68,
  c68,
  0,
  c66,
  c41,
  c116,
  c41,
  c93,
  0,
  c94,
  0,
  c66,
  0,
  c48,
  0,
  0,
  c146,
  c200,
  c199,
  c146,
  0,
  c146,
  c200,
  c199,
  c146,
  0,
  c146,
  c200,
  c199,
  c146,
  0,
  c146,
  c200,
  c199,
  c146,
  0,
  0,
  c109,
  c153,
  0,
  c205,
  0,
  c160,
  c256,
  220,
  c160,
  c202,
  c65,
  c109,
  0,
  c109,
  0,
  c65,
  c17,
  c248,
  c17,
  0,
  c205,
  0,
  c160,
  c256,
  212,
  c160,
  c202,
  c65,
  c109,
  0,
  c109,
  0,
  c65,
  c17,
  c248,
  c17,
  0,
  c205,
  0,
  c160,
  c256,
  156,
  c160,
  c202,
  c65,
  c109,
  0,
  c109,
  c153,
  0,
  c205,
  0,
  c160,
  c256,
  228,
  c160,
  c202,
  c65,
  c109,
  c48,
  c68,
  c68,
  0,
  c66,
  c41,
  c116,
  c41,
  c94,
  0,
  0,
  c156,
  0,
  c48,
  0,
  0,
  0,
  0,
  c167,
  c83,
  c207,
  c167,
  c220,
  c159,
  c220,
  c78,
  c78,
  0,
  c175,
  0,
  c322,
  c83,
  c126,
  c83,
  c174,
  0,
  c167,
  c83,
  c207,
  c167,
  c10,
  c0,
  0,
  0,
  c13,
  c220,
  c159,
  c13,
  c78,
  c78,
  0,
  c13,
  0,
  c132,
  1670689536887370,
  c126,
  c132,
  c14,
  c13,
  c194,
  c48,
  c260,
  0,
  c48,
  0,
  0,
  0,
  c38,
  c220,
  c159,
  c38,
  c78,
  c78,
  0,
  c38,
  0,
  c322,
  1016942465451026,
  c176,
  c176,
  c44,
  c38,
  c10,
  c0,
  0,
  0,
  c13,
  c220,
  c159,
  c13,
  c78,
  c78,
  0,
  c13,
  0,
  c132,
  204,
  c176,
  c132,
  c14,
  c13,
  c28,
  c48,
  0,
  c66,
  c23,
  c68,
  c23,
  0,
  c66,
  c41,
  c116,
  c41,
  0,
  c156,
  c23,
  c68,
  c23,
  0,
  0,
  0,
  c156,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  c43,
  c29,
  c260,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  c43,
  c29,
  0,
  c66,
  c23,
  c158,
  c23,
  0,
  c66,
  c41,
  c116,
  c41,
  0,
  c156,
  c23,
  c158,
  c23,
  0,
  c93,
  c69,
  0,
  c66,
  c41,
  c116,
  c41,
  c69,
  0,
  c94,
  c70,
  0,
  c66,
  c41,
  c116,
  c41,
  c70,
  0,
  0,
  c156,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  c43,
  c29,
  c260,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  c43,
  c29,
  0,
  c66,
  c23,
  c158,
  c23,
  0,
  c66,
  c41,
  c116,
  c41,
  0,
  c156,
  c23,
  c158,
  c23,
  0,
  0,
  0,
  c71,
  0,
  c26,
  c76,
  0,
  0,
  c24,
  c20,
  0,
  c293,
  c245,
  0,
  c119,
  c208,
  3977827287274873,
  c208,
  c293,
  c24,
  0,
  c122,
  c20,
  c152,
  c20,
  0,
  c122,
  c20,
  c84,
  c20,
  0,
  c24,
  c20,
  0,
  0,
  c119,
  28775155094923777046131478809679592605463683,
  c173,
  c119,
  c204,
  c204,
  0,
  c119,
  c208,
  c14,
  c208,
  c24,
  c76,
  c72,
  0,
  c26,
  c76,
  0,
  c29,
  0,
  c8,
  c6,
  c0,
  c8,
  0,
  c8,
  c6,
  c84,
  c8,
  c29,
  c76,
  0,
  c150,
  c69,
  c97,
  c69,
  0,
  0,
  0,
  0,
  c16,
  c1,
  0,
  c11,
  0,
  0,
  196,
  c86,
  c131,
  c86,
  c49,
  c265,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  c16,
  0,
  c90,
  c1,
  c0,
  c1,
  c40,
  c40,
  c37,
  0,
  0,
  c16,
  c1,
  0,
  c11,
  0,
  0,
  c252,
  c128,
  c128,
  c136,
  c49,
  c265,
  c49,
  0,
  c107,
  c276,
  c44,
  c276,
  c11,
  c16,
  0,
  c90,
  c1,
  c0,
  c1,
  0,
  c90,
  c1,
  c21,
  c1,
  0,
  c16,
  c1,
  c0,
  c16,
  c37,
  c70,
  0,
  0,
  0,
  c154,
  c100,
  c73,
  c154,
  0,
  c2,
  0,
  c7,
  c171,
  c172,
  c7,
  c45,
  c2,
  c40,
  c40,
  c37,
  0,
  0,
  0,
  c64,
  c35,
  0,
  5728516812781225,
  0,
  c74,
  c178,
  2905553124914265,
  c178,
  c44,
  c44,
  c64,
  c6,
  c73,
  c6,
  0,
  c2,
  c6,
  c138,
  c6,
  0,
  c244,
  c6,
  c21,
  c6,
  0,
  c2,
  c6,
  c73,
  c6,
  c37,
  c70,
  0,
  c71,
  0,
  c26,
  c76,
  0,
  0,
  c24,
  c20,
  0,
  c293,
  c245,
  c34,
  c34,
  c24,
  0,
  c4,
  c20,
  c152,
  c4,
  0,
  c4,
  c20,
  c84,
  c4,
  0,
  c24,
  c20,
  0,
  0,
  0,
  c219,
  c128,
  c128,
  164,
  c277,
  c173,
  c277,
  c15,
  c34,
  c15,
  c24,
  c76,
  c72,
  0,
  c26,
  c76,
  0,
  c29,
  0,
  c8,
  c6,
  c0,
  c8,
  0,
  c8,
  c6,
  c84,
  c8,
  c29,
  c76,
  0,
  0,
  c71,
  0,
  c27,
  c77,
  c63,
  c77,
  c72,
  0,
  c27,
  c77,
  c63,
  c77,
  0,
  c150,
  0,
  c255,
  0,
  0,
  c143,
  c98,
  0,
  c161,
  c286,
  c34,
  c161,
  c143,
  0,
  c4,
  c98,
  c192,
  c4,
  c43,
  c43,
  c155,
  0,
  0,
  c143,
  c98,
  c3,
  c3,
  0,
  c4,
  c98,
  c192,
  c4,
  c43,
  c43,
  c97,
  0,
  c255,
  0,
  0,
  0,
  c64,
  c35,
  c34,
  c64,
  c87,
  c87,
  0,
  c64,
  c35,
  c34,
  c64,
  0,
  c2,
  c10,
  c0,
  c2,
  c43,
  c43,
  c155,
  0,
  0,
  0,
  c64,
  c35,
  c34,
  c64,
  c6,
  c3,
  c3,
  0,
  c2,
  c6,
  c0,
  c6,
  c43,
  c43,
  0,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c71,
  0,
  c27,
  c77,
  c155,
  c77,
  c72,
  0,
  c27,
  c77,
  c155,
  c77,
  0,
  0,
  c71,
  c80,
  c72,
  c80,
  0,
  c93,
  0,
  c66,
  c166,
  c116,
  c166,
  c97,
  c93,
  0,
  c94,
  0,
  c66,
  c166,
  c116,
  c166,
  0,
  c66,
  0,
  c48,
  0,
  c2,
  c238,
  c189,
  c2,
  c338,
  c48,
  c116,
  0,
  c48,
  0,
  c2,
  c6,
  c138,
  c6,
  c28,
  c48,
  c94,
  0,
  c71,
  c80,
  c72,
  c80,
  0,
  0,
  c71,
  c80,
  c72,
  c80,
  0,
  c93,
  c69,
  c97,
  c69,
  0,
  c94,
  c70,
  0,
  c106,
  0,
  0,
  0,
  c64,
  c35,
  0,
  c205,
  0,
  c74,
  c323,
  c351,
  c74,
  c202,
  0,
  1016942286236690,
  c323,
  c207,
  c207,
  c64,
  c87,
  c87,
  0,
  c64,
  c35,
  0,
  c205,
  0,
  1452773636260394,
  c177,
  c351,
  c177,
  c202,
  0,
  20,
  c177,
  c207,
  c177,
  c64,
  0,
  c2,
  c238,
  c189,
  c2,
  c43,
  c43,
  c63,
  0,
  0,
  0,
  c64,
  c35,
  0,
  c38,
  0,
  c74,
  c178,
  c176,
  c178,
  c44,
  c38,
  c64,
  c6,
  c3,
  c3,
  0,
  c2,
  c6,
  c138,
  c6,
  c43,
  c43,
  c70,
  0,
  c71,
  c80,
  c72,
  c80
]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
lemma tree_checked : check code order (fun _ => none) treeData = some [] := by
  decide +kernel

lemma classified (q : V → Fin 4) (hq : CodeConditions q) : ∃ i, q = SlotTables.code i := by
  exact check_sound code order (fun _ => none) treeData [] q tree_checked
    (by intro v c h; cases h) hq

lemma conditions_classified (t : H → Slot) (ht : Conditions t) :
    ∃ i, localCode t = SlotTables.code i :=
  classified (localCode t) (code_conditions t ht)

end PEqualNP.Outside.L_meta_2590.SlotTree

namespace PEqualNP.Outside.L_meta_2590.FiniteSlots

def joined (f : H → Fin 30) (a b h k : H) : Prop :=
  (f h = f a ∨ f h = f b) ∧ (f k = f a ∨ f k = f b)
def mergeRel (f : H → Fin 30) (a b h k : H) : Prop :=
  f h = f k ∨ joined f a b h k ∨ joined f (barH a) (barH b) h k

lemma joined_sound (t : H → Slot) (f : H → Fin 30)
    (hf : ∀ h k, f h = f k → t h = t k) (a b h k : H)
    (hab : t a = t b) (hr : joined f a b h k) : t h = t k := by
  obtain ⟨hh, hk⟩ := hr
  rcases hh with hh | hh <;> rcases hk with hk | hk
  · exact (hf h a hh).trans (hf k a hk).symm
  · exact (hf h a hh).trans (hab.trans (hf k b hk).symm)
  · exact (hf h b hh).trans (hab.symm.trans (hf k a hk).symm)
  · exact (hf h b hh).trans (hf k b hk).symm

lemma mergeRel_sound (t : H → Slot) (f : H → Fin 30)
    (hf : ∀ h k, f h = f k → t h = t k)
    (hb : ∀ h, t (barH h) = bar (t h)) (a b h k : H)
    (hab : t a = t b) (hr : mergeRel f a b h k) : t h = t k := by
  rcases hr with hr | hr | hr
  · exact hf h k hr
  · exact joined_sound t f hf a b h k hab hr
  · apply joined_sound t f hf (barH a) (barH b) h k ?_ hr
    rw [hb, hb, hab]

def mergeRows : Fin 15 → Finset V := ![{1,4,5}, {0,2,6}, {3,5,6}, {2,4,5,6},
  {1,3,7}, {0,3,6,7}, {4,6,7}, {2,4,8}, {0,7,8}, {1,4,7,8},
  {0,3,9}, {2,5,9}, {1,3,5,9}, {1,8,9}, {0,2,8,9}]
lemma mergeRows_independent : ∀ r, independent (mergeRows r) := by
  unfold independent
  decide +kernel

def mergeHalf (n : ℕ) : H := (⟨(n / 2) % 15, Nat.mod_lt _ (by decide)⟩, n.testBit 0)
def mergeVertex (z : ℕ) : V := ⟨(z / 3) % 10, Nat.mod_lt _ (by decide)⟩
def mergeFirst (z : ℕ) : ℕ := (z / 30) % 30
def mergeSecond (z : ℕ) : ℕ := (z / 900) % 30
def mergeThird (z : ℕ) : ℕ := (z / 27000) % 30
def mergeRow (z : ℕ) : Fin 15 := ⟨(z / 810000) % 15, Nat.mod_lt _ (by decide)⟩
def mergeWitness (z : ℕ) : Fin 3 → H :=
  ![mergeHalf (mergeFirst z), mergeHalf (mergeSecond z), mergeHalf (mergeThird z)]

def MergeCheck (q : V → Fin 4) (f : H → Fin 30) (a b : H) (z : ℕ) : Prop :=
  let v := mergeVertex z
  if z % 3 = 0 then
    let i : Fin 3 := ⟨mergeFirst z % 3, Nat.mod_lt _ (by decide)⟩
    let j : Fin 3 := ⟨mergeSecond z % 3, Nat.mod_lt _ (by decide)⟩
    block (q v) i ≠ block (q v) j ∧ mergeRel f a b (around v i) (around v j)
  else if z % 3 = 1 then
    let h := mergeHalf (mergeFirst z)
    let k := mergeHalf (mergeSecond z)
    endpoint k = endpoint h ∧ mergeRel f a b k (barH h)
  else
    q v ≠ 3 ∧ touches v (mergeRows (mergeRow z)) ∧
      ∀ i : Fin 3, endpoint (mergeWitness z i) ∈ mergeRows (mergeRow z) ∧
        mergeRel f a b (mergeWitness z i) (around v i)

lemma mergeCheck_false (t : H → Slot) (ht : Conditions t) (q : V → Fin 4)
    (hq : localCode t = q) (f : H → Fin 30)
    (hf : ∀ h k, f h = f k → t h = t k) (a b : H) (hab : t a = t b)
    (z : ℕ) (hz : MergeCheck q f a b z) : False := by
  have hs := mergeRel_sound t f hf ht.1 a b
  unfold MergeCheck at hz
  dsimp only at hz
  split_ifs at hz with hzero hone
  · apply hz.1
    rw [← hq]
    exact (localCode_exact t _ (ht.2.2.1 _) _ _).mp (hs _ _ hab hz.2)
  · apply ht.2.1 (mergeHalf (mergeFirst z))
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, mergeHalf (mergeSecond z), hz.1, hs _ _ hab hz.2⟩
  · obtain ⟨hn, htouch, hhits⟩ := hz
    have hc : (selected t (mergeVertex z)).card = 2 :=
      card_two_of_code_ne_three t _ (ht.2.2.1 _) (by rw [hq]; exact hn)
    obtain ⟨h, hv, hdis⟩ := ht.2.2.2 _ _ (mergeRows_independent _) htouch hc
    obtain ⟨i, hi⟩ := around_complete _ h hv
    obtain ⟨hmem, hrel⟩ := hhits i
    have hEq := hs _ _ hab hrel
    rw [hi] at hEq
    have hlower : endpoint (mergeWitness z i) ∈ lower t h := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, mergeWitness z i, rfl, hEq⟩
    exact Finset.disjoint_left.mp hdis hlower hmem

def canonicalLabel (f : H → Fin 30) (h : H) : Finset V :=
  Finset.univ.filter fun v => ∃ k : H, endpoint k = v ∧ f k = f h

lemma lower_eq_canonicalLabel (t : H → Slot) (f : H → Fin 30)
    (he : ∀ h k, t h = t k ↔ f h = f k) (h : H) :
    lower t h = canonicalLabel f h := by
  ext v
  simp only [lower, canonicalLabel, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, heq⟩
    exact ⟨k, hk, (he k h).mp heq⟩
  · rintro ⟨k, hk, heq⟩
    exact ⟨k, hk, (he k h).mpr heq⟩

end PEqualNP.Outside.L_meta_2590.FiniteSlots

namespace PEqualNP.Outside.L_meta_2590.NonlocalMerge
open PEqualNP.Outside.L_meta_2590.FiniteSlots
open PEqualNP.Outside.L_meta_2590.SlotTables

def repData : Fin 45 → ℕ := ![
  0x31f192906242420,
  0x216b431c6242420,
  0xbd8438c020,
  0x216b431c6208109,
  0xbd84331c8508109,
  0x837a7b909,
  0x216b431c625a820,
  0x73c438c2b45a820,
  0x73c438c14bad020,
  0x73c438c39d52c20,
  0x1cf10e3052c20,
  0x7192916a,
  0xbd8434a08539820,
  0xbd8439c8e621420,
  0x2f610cc721420,
  0x31f192900118909,
  0x31f19291ac00509,
  0xc7c64a400509,
  0x85ad0c718820,
  0xa5528398a400462,
  0x839d9c862,
  0x9cb19292306b001,
  0x9c98dde8a48c001,
  0x9cb19634a48c001,
  0x272634a48c001,
  0x6b4399ac,
  0xa55283984329001,
  0xa5528399ee10c01,
  0x2954a0e610c01,
  0x837a4a0e610ca4,
  0xa56720814b7b843,
  0x73e720814bad043,
  0xbda72081ee52c43,
  0x1cf9c82052c43,
  0x837a4a08539843,
  0x837a4a23021443,
  0x20de92821443,
  0x77a6354b8c085,
  0x6306379d52c85,
  0x58ddea3052c85,
  0x18c18d52c85,
  0xbd98d005ee9c8e6,
  0x9cb19634017b8e6,
  0xbda72634017b8e6,
  0x272634017b8e6]

def certData : Fin 45 → ℕ := ![
  0x15cd00072300039c00039c00072300573100038d000399235e4a2d9ad900039900038d2d9ad9235e4a000e894fb2f970185500596b000396000e6b00038a7018554fb2f900039600596b00038a000e6b0007450003930003906a427046cd9041a2ba1d688246a3603a20a400039000039346cd906a42701d688241a2ba3a20a446a360001d116fab5962e24dad094e4675b83dcddeb51f9f000727000387000384001fa562e24d6fab594675b8ad094eb51f9f3dcdde000387000727001fa5000384000001,
  0xe890007200003990003990007200048a900039f00038d50a2092faa3100038d00039f2faa3150a2090015cd00038a0003966a1fba9e1dc4856400767a2600039600038a9e1dc46a1fba767a268564000007451d688241a2ba00479b000393001cf3000390767a446a1e5241a2ba1d688200039300479b000390001cf36a1e52767a44001d11ad4bb73dcdde9664496faa8d756fe916abc1000727000387000384001fa53dcddead4bb76faa8d96644916abc1756fe9000387000727001fa5000384000001,
  0x4fed00000000000000000000000000039f00071d00000000000000000000000000071d00039f000745000000000000000000000000536f3991b38900039c00071100000000000000000000000091b389536f3900071100039c003a21000000000000000000000000324cce900e180003870003841adaee620504000000000000000000000000900e18324cce0003840003876205041adaee000001,
  0xe890007200003990003990007200048a900039f00038d50a2092faa3100038d00039f2faa3150a2090015cd00038a000396213d1f9e1dc42810631b475700039600038a9e1dc4213d1f1b47572810630007451d68823dcdde00479b0003932f8a8d16abc10007270003873dcdde1d688200039300479b16abc12f8a8d0003870007270000014d91ce41a2ba2f800d72a49f001cf3000390767a44287d5f000384001fa541a2ba4d91ce72a49f2f800d000390001cf3287d5f767a44001fa5000384001d11,
  0x4fed00039600071d00071d00039600074500039f0053171b475728106300531700039f2810631b47570015cd9ce15c1e6caa00039c00038a0015af00038d1e6caa9ce15c00038a00039c00038d0015af000e89b88a2b4431ad000387000393442fcd508bfb620381442faf4431adb88a2b000393000387508bfb442fcd442faf620381000001ae655a085bec287d5f72c50c001cf3000390085be043489a000384001fa5085becae655a72c50c287d5f000390001cf343489a085be0001fa5000384001d11,
  0x100000000000000000000000000071a00039c00000000000000000000000000039c00071a005e7500000000000000000000000000070e000399239d926e003000000000000000000000000000039900070e6e0030239d920032dd0000000000000000000000000003840003901e702858202026822c3a4e4c0000000000000000000000000003900003845820201e70283a4e4c26822c001d11,
  0xe890007200003990003990007200048a900039f00038d50a2092faa3100038d00039f2faa3150a2090015cd00038a0003962d98d5531a01281009767a2600039600038a531a012d98d5767a262810090007451d6882420fb600479b0003932f8a8d16cee99e1cb629c3f9420fb61d688200039300479b16cee92f8a8d29c3f99e1cb60024554d91ce3dcdde2f800d16abcd001cf30003900007270003870007080023293dcdde4d91ce16abcd2f800d000390001cf3000387000727002329000708000001,
  0x32dd00039f00070e00070e00039f0007457656fe1f7ee200071a0007111f7ee27656fe00071100071a003a21004b97000399531a012d98d500072000646f000399004b972d98d5531a0100646f0007200048a904a19e421a4229c3f99df286b16ca1048f7700479b000393421a4204a19e9df28629c3f9048f77b16ca100039300479b0024557dbc433fef03000387000390b521971adaf13fefb71adb690007080023293fef037dbc430003900003871adaf1b521971adb693fefb7002329000708000001,
  0x32dd00039f00070e00070e00039f0007457656fe1f7ee200071a0007111f7ee27656fe00071100071a003a21421a4204a19e6270f529c3f900072000646f04a19e421a4229c3f96270f500646f000720002455004b97000399531a012d98d50844af77eab700039300479b000399004b972d98d5531a0177eab70844af00479b0003930048a97afc3062406e000387000390b52197624b540023290007083fefb77b11fc62406e7afc30000390000387624b54b521970007080023297b11fc3fefb7000001,
  0x32dd00039f00070e00070e00039f0007457656fe1f7ee200071a0007111f7ee27656fe00071100071a003a217adf260c0c0e6270f5316db100072000646f0c0c0e7adf26316db16270f500646f0007200065b9004b97000399531a0129c3f9048f7777eab700071700673f000399004b9729c3f9531a0177eab7048f7700673f0007170024553a4d983fef030003870003903a513a78212cb522e17849220023290007083fef033a4d9800039000038778212c3a513a784922b522e1000708002329000001,
  0x32dd00000000000000039f00070e00000000000000070e00039f0007450000000000007656fe1f7ee200071a0007110000000000001f7ee27656fe00071100071a003a21000000000000004b97000399531a0129c3f900072000646f000000000000000399004b9729c3f9531a0100646f0007200024550000000000003a4d9862406e0003870003903a513a624b5400232900070800000000000062406e3a4d98000390000387624b543a513a000708002329000001,
  0x100000000000000000000000000072300039600000000000000000000000000039600072300573100000000000000000000000000038d00038a1b89907bed0800000000000000000000000000038a00038d7bed081b8990000e89000000000000000000000000000393000708231aa691e2d826c4f81add4600000000000000000000000000070800039391e2d8231aa61add4626c4f8002455,
  0x4fed00039600071d00071d00039600074500039f005317900cb3287d5f00531700039f287d5f900cb3001d119ce15c1e6caa00039c00038a43489a085be01e6caa9ce15c00038a00039c085be043489a000e899ca5a40858682810631b4757001cf300039000038d0015af0858689ca5a41b4757281063000390001cf30015af00038d0015cdb88a2b91b3f8000387000393001fa500038496a37c89ddd6970d12442fcd91b3f8b88a2b000393000387000384001fa589ddd696a37c442fcd970d12000001,
  0x4fed00039600071d00071d00039600074500039f005317900cb32cbf3700531700039f2cbf37900cb30041659ca5a40858682810631b475700401b0007140858689ca5a41b475728106300071400401b0015cd9ce15c1e6caa00039c00038a9cd34c087f0800038d0015af1e6caa9ce15c00038a00039c087f089cd34c0015af00038d000e89231ce09de254000387000393b889b39c3bfc000384001fa51add28442faf9de254231ce00003930003879c3bfcb889b3001fa5000384442faf1add28000001,
  0x4fed00000000000000039600071d00000000000000071d00039600074500000000000000039f0053171b475728106300000000000000531700039f2810631b47570015cd0000000000009ce15c1e6caa00039c00038a0015af00038d0000000000001e6caa9ce15c00038a00039c00038d0015af000e89000000000000231ce091b3f8000387000393001fa50003841add2889ddd600000000000091b3f8231ce0000393000387000384001fa589ddd61add28000001,
  0x15cd00072300039c00039c00072300573100038d000399900e3f2d9ad900039900038d2d9ad9900e3f000e894fb2f96fab5900596b0003962d99710883d96fab594fb2f900039600596b0883d92d9971000001954aa67018552801f0ae4fe8000e6b00038a000387000727701855954aa6ae4fe82801f000038a000e6b000727000387000745000393000390235e4446cd9026c9a81ada94001fa5000384b41670265cac00039000039346cd90235e441ada9426c9a8000384001fa5265cacb41670001d11,
  0x15cd00072300039c00039c00072300573100038d0003994870f46e5f1c00039900038d6e5f1c4870f4000e894fb2f9745a2d00596b0003962d9971435524745a2d4fb2f900039600596b4355242d9971002b9962e24d6fab592801f002e6b8000e6b00038a00070b002a4f6fab5962e24d02e6b82801f000038a000e6b002a4f00070b0000010003930003902fb92862036026c87cb520ad46a3602a9d58001fa50003840003900003936203602fb928b520ad26c87c2a9d5846a360000384001fa5001d11,
  0x15cd00000000000000072300039c00000000000000039c00072300573100000000000000038d000399235e4a6e5f1c00000000000000039900038d6e5f1c235e4a000e890000000000004fb2f96fab5900596b000396000e6b00038a0000000000006fab594fb2f900039600596b00038a000e6b000001000000000000000393000390235e4462036026c87c1ada94001fa5000384000000000000000390000393620360235e441ada9426c87c000384001fa5001d11,
  0xe890000000000000007200003990000000000000003990007200048a900000000000000039f00038d50a2092faa3100000000000000038d00039f2faa3150a2090015cd00000000000000038a000396213d1f531a012810091b475700000000000000039600038a531a01213d1f1b47572810090007450000000000001d68823dcdde00479b000393001cf30003900007270003870000000000003dcdde1d688200039300479b000390001cf3000387000727000001,
  0x48a900039f00039300039300039f001d11531ad948737000039c000390487370531ad900039000039c0015cd004b970003991ada9426c9a80015af00038d000399004b9726c9a81ada9400038d0015af000e89900dbe7abd9c0003840003966203d89c682a7abce862037e7abd9c900dbe0003960003849c682a6203d862037e7abce800000116b653729059265cacae51e070185598ffde000e6b00038a00038700072772905916b653ae51e0265cac98ffde70185500038a000e6b000727000387000745,
  0x10000000000000000000000000007200007170000000000000000000000000007170007200065b900000000000000000000000000039f00071424d2bc6ea77000000000000000000000000000071400039f6ea77024d2bc00416500000000000000000000000000038a0003871da78b588d3d26f9d58557eb00000000000000000000000000038700038a588d3d1da78b8557eb26f9d5000745,
  0x416500072300569b00569b00072300573100071400071d6203602fb92800071d0007142fb928620360000e8951c959b4fd8500039c0060eb000717000711b4fd8551c9590060eb00039c000711000717003a21996a6411c5be00596b0003962a9d584355247464b911d7e511c5be996a6400039600596b4355242a9d5811d7e57464b9002b999673e83393c275a2801adbfc00038400038a75a1541adaee00070b002a4f3393c29673e81adbfc75a28000038a0003841adaee75a154002a4f00070b000001,
  0x416500072300569b00569b000723002b991720d6b8371e00071a005cefb8371e1720d6005cef00071a005e7500071400071d922cac2a9d5862036030262400071d0007142a9d58922cac302624620360000e8951c959b4fd8511d7e57464b900039c0060eb000717000711b4fd8551c9597464b911d7e50060eb00039c000711000717003a219673e83393c2002a4f00070b75a2801adc1a00038400038a75a1541adaee3393c29673e800070b002a4f1adc1a75a28000038a0003841adaee75a154000001,
  0x416500072300569b00569b00072300573111c5be996a6400039600596b996a6411c5be00596b000396002b9900071400071d922cac2fb9286203602a9d5800071d0007142fb928922cac2a9d58620360000e8951c959b4fd8516c985b70cdd00039c0060eb000717000711b4fd8551c959b70cdd16c9850060eb00039c000711000717003a219673e83393c296747e1adbfc002a4f00070b00038400038a75a1541adaee3393c29673e81adbfc96747e00070b002a4f00038a0003841adaee75a154000001,
  0x416500000000000000072300569b00000000000000569b000723002b9900000000000000071400071d6203602a9d5800000000000000071d0007142a9d58620360000e8900000000000051c959b4fd8500039c0060eb000717000711000000000000b4fd8551c9590060eb00039c000711000717003a210000000000009673e83393c2002a4f00070b00038400038a75a1541adaee0000000000003393c29673e800070b002a4f00038a0003841adaee75a154000001,
  0x10000000000000000000000000003930003990000000000000000000000000003990003930048a900000000000000000000000000038d00039000aff14dbeef00000000000000000000000000039000038d4dbeef00aff10015cd00000000000000000000000000070b0003962107af4685571b431f28138d00000000000000000000000000039600070b4685572107af28138d1b431f002b99,
  0x48a900039f00039300039300039f001d111d695a48737000039c0003904873701d695a00039000039c0015cd004b97000399508cac265cac4872bc170114000399004b97265cac508cac1701144872bc000745482d9b16b9d71ada9426c9a80015af00038d00038a000e6b16b9d7482d9b26c9a81ada9400038d0015af000e6b00038a000e89900dbe7abd9c0003840003966203d89c682a0007270003879c680c62037e7abd9c900dbe0003960003849c682a6203d800038700072762037e9c680c000001,
  0x48a900039f00039300039300039f001d11782d830883f700039c0003900883f7782d8300039000039c0015cd004b97000399508cac2b0b804872bc759f9b000399004b972b0b80508cac759f9b4872bc0032dd482d9b16b6531ada94265cac0015af00038d00070e00319316b653482d9b265cac1ada9400038d0015af00319300070e000745900dbe7abd9c0003840003966203d89c682a7abce86204aa0007270003877abd9c900dbe0003960003849c682a6203d86204aa7abce8000387000727000001,
  0x48a900000000000000039f00039300000000000000039300039f001d11000000000000531ad90883f700039c0003900000000000000883f7531ad900039000039c0015cd000000000000004b970003991ada94265cac0015af00038d000000000000000399004b97265cac1ada9400038d0015af000745000000000000900dbe7abd9c0003840003966203d89c682a0007270003870000000000007abd9c900dbe0003960003849c682a6203d8000387000727000001,
  0x100071a00071700071700071a005e7500039f0003847844cc1e702800038400039f1e70287844cc001d11970d12a7f29400039c0060eb001cf3000390a7f294970d120060eb00039c000390001cf30015cd000387000399b6e44b1d9cff3a20982a7b5c29b6431d56af0003990003871d9cffb6e44b2a7b5c3a20981d56af29b64300074589ddd696a37caf025f33834b1e26542a7ee00015af00038d00038a000e6b96a37c89ddd633834baf025f2a7ee01e265400038d0015af000e6b00038a000e89,
  0x48a900039f00531700531700039f0041657b11fcac8980000396000714ac89807b11fc00071400039600000100479b0003939c3a76231aa600072000070800039300479b231aa69c3a76000708000720002455004b97000399b30b4037a1f862406e7afc3037b4162b07fc000399004b9737a1f8b30b407afc3062406e2b07fc37b4160032dd283d9f4d5553b44ea728369700038700038d1add46267fd400070e0031934d5553283d9f283697b44ea700038d000387267fd41add4600319300070e000745,
  0x32dd00039f00531700531700039f0041657afc3062406e00039600071462406e7afc300007140003960000012b07fc37b4169c3a76231aa600072000070837b4162b07fc231aa69c3a76000708000720002455004b970003999c91d03a1ac84687377b11fc00039300479b000399004b973a1ac89c91d07b11fc46873700479b0003930048a900319300070eb44ea728369700038700038d1add46267fd44d5553283d9f00070e003193283697b44ea700038d000387267fd41add46283d9f4d5553000745,
  0x4fed00039f00531700531700039f0041657b159eac8980000396000714ac89807b159e000714000396000001004f1b00071d9c91d037a1f862406e7afc3000071d004f1b37a1f89c91d07afc3062406e0032dd9de0563a965e9c3a76231aa600072000070800039300479b3a965e9de056231aa69c3a7600070800072000479b000393002455b45cb74d58d7b44ea728369700038700038d00070e0031931add46267fd44d58d7b45cb7283697b44ea700038d00038700319300070e267fd41add46000745,
  0x32dd00000000000000039f00531700000000000000531700039f0041650000000000007afc3062406e00039600071400000000000062406e7afc3000071400039600000100000000000000479b0003939c3a76231aa600072000070800000000000000039300479b231aa69c3a7600070800072000245500000000000000319300070eb44ea728369700038700038d1add46267fd400000000000000070e003193283697b44ea700038d000387267fd41add46000745,
  0x100071a00071700071700071a005e7500039f0003847844cc1e702800038400039f1e70287844cc001d1196a37c89ddd600039c0060eb2a7ee01e265489ddd696a37c0060eb00039c1e26542a7ee0000e89970d12407a9533ecc372228b001cf300039000038d0015af407a95970d1272228b33ecc3000390001cf30015af00038d0015cd000387000399b6e44b1d9cff3a20982a7b5c000e6b00038a29b6431d56af0003990003871d9cffb6e44b2a7b5c3a209800038a000e6b1d56af29b643000745,
  0x100071a00071700071700071a005e7500039f0003847844cc1e702800038400039f1e70287844cc001d119b2ceea7f29400039c0060eb7821a41e4d00a7f2949b2cee0060eb00039c1e4d007821a4003a2196a37c89ddd633834b72228b001cf30003900007110038d789ddd696a37c72228b33834b000390001cf30038d7000711000e89000387000399b6e44b1d9cff3a20982a7b5cb6c1231d79d7000e6b00038a0003990003871d9cffb6e44b2a7b5c3a20981d79d7b6c12300038a000e6b000745,
  0x100000000000000071a00071700000000000000071700071a005e7500000000000000039f0003847844cc1e702800000000000000038400039f1e70287844cc001d1100000000000096a37c89ddd600039c0060eb001cf300039000000000000089ddd696a37c0060eb00039c000390001cf3000e89000000000000000387000399b6e44b1d9cff3a20982a7b5c000e6b00038a0000000000000003990003871d9cffb6e44b2a7b5c3a209800038a000e6b000745,
  0x1784580532dae532dae784580005e7500072300070b00071a005cef00070b000723005cef00071a002b9900070800039900071700673f91e2d82a7a3000039900070800673f0007172a7a3091e2d800245578212c3a513a00039c0060eb5da27d449a535d90509b2d483a513a78212c0060eb00039c449a535da27d9b2d485d9050003a2100038a000390633f743e27c026d72540122b26c4f896a5200007110038d700039000038a3e27c0633f7440122b26d72596a52026c4f80038d7000711000e89,
  0x178212c3a513a3a513a78212c003a2100072300070b00071a005cef00070b000723005cef00071a002b99784922b751dd00072000646f622aa53123ddb751dd78492200646f0007203123dd622aa50065b90007080003995d90502fd54891e2d82a7a3000071700673f0003990007082fd5485d90502a7a3091e2d800673f00071700245500038a0003900007110038d726d72540122b6342f89c8cde26c4f896a52000039000038a0038d700071140122b26d7259c8cde6342f896a52026c4f8000e89,
  0x100072300070b00070b000723002b99784580532dae00071a005cef532dae784580005cef00071a005e7578212c3a513a5da27d3123dd00039c0060eb3a513a78212c3123dd5da27d0060eb00039c003a2100070800039991e2d82a7a3061af002fd54800071700673f0003990007082a7a3091e2d82fd54861af0000673f00071700245500038a00039026d72540122b633f743e27c00007110038d726c4f896a52000039000038a40122b26d7253e27c0633f740038d700071196a52026c4f8000e89,
  0x100000000000078212c3a513a0000000000003a513a78212c003a2100000000000000072300070b00071a005cef00000000000000070b000723005cef00071a002b9900000000000000070800039900071700673f91e2d82a7a3000000000000000039900070800673f0007172a7a3091e2d800245500000000000000038a0003900007110038d726d72540122b26c4f896a52000000000000000039000038a0038d700071140122b26d72596a52026c4f8000e89,
  0x4fed00039600596b00596b000396002b999de254231ce000039c00070b231ce09de25400070b00039c000001004f1b00071d440c872107af00039300070e00071d004f1b2107af440c8700070e0003930032dd00039f005317837eb72ca69b9c3bfcb86d9376e4ca836c9000531700039f2ca69b837eb7b86d939c3bfc836c9076e4ca00416526a8d8898250267ea858202000038d00038426822c76744400401b00071489825026a8d8582020267ea800038400038d76744426822c00071400401b0015cd,
  0x416500072300569b00569b000723005731837eb72ca69b00039600596b2ca69b837eb700596b000396002b999c3bfc3a983e9e4bea231ce000039c00070b3a983e9c3bfc231ce09e4bea00070b00039c000001004f1b00071d481910857be8440c872107af00039300070e00071d004f1b857be84819102107af440c8700070e0003930032dd00401b00071426a8d88985d4267ea858202000038d00038426822c76744400071400401b8985d426a8d8582020267ea800038400038d76744426822c0015cd,
  0x4fed00039f00531700531700039f00416585249746eecf00039600596b46eecf85249700596b000396002b999de2543a983e9c3bfc231ce000039c00070b3a983e9de254231ce09c3bfc00070b00039c000001004f1b00071d481910836c90440c872107af00039300070e00071d004f1b836c904819102107af440c8700070e0003930032dd768ce089825000401b000714267ea858202000038d00038426822c767444898250768ce000071400401b582020267ea800038400038d76744426822c0015cd,
  0x416500000000000000039600596b00000000000000596b000396002b990000000000009c3bfc231ce000039c00070b000000000000231ce09c3bfc00070b00039c000001000000000000004f1b00071d440c872107af00039300070e00000000000000071d004f1b2107af440c8700070e0003930032dd00000000000000401b000714267ea858202000038d00038426822c76744400000000000000071400401b582020267ea800038400038d76744426822c0015cd]

def mergeRep (p : Fin 45) (a : Fin 30) : H :=
  mergeHalf ((Nat.shiftRight (repData p) (5 * a.val)) % 32)

def certificate (p : Fin 45) (a b : Fin 30) : ℕ :=
  (Nat.shiftRight (certData p) (24 * (a.val * (23 - a.val) / 2 + b.val - a.val - 1))) % 16777216

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_0 : ∀ h, slot 0 (mergeRep 0 (slot 0 h)) = slot 0 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_1 : ∀ h, slot 1 (mergeRep 1 (slot 1 h)) = slot 1 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_2 : ∀ h, slot 2 (mergeRep 2 (slot 2 h)) = slot 2 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_3 : ∀ h, slot 3 (mergeRep 3 (slot 3 h)) = slot 3 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_4 : ∀ h, slot 4 (mergeRep 4 (slot 4 h)) = slot 4 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_5 : ∀ h, slot 5 (mergeRep 5 (slot 5 h)) = slot 5 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_6 : ∀ h, slot 6 (mergeRep 6 (slot 6 h)) = slot 6 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_7 : ∀ h, slot 7 (mergeRep 7 (slot 7 h)) = slot 7 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_8 : ∀ h, slot 8 (mergeRep 8 (slot 8 h)) = slot 8 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_9 : ∀ h, slot 9 (mergeRep 9 (slot 9 h)) = slot 9 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_10 : ∀ h, slot 10 (mergeRep 10 (slot 10 h)) = slot 10 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_11 : ∀ h, slot 11 (mergeRep 11 (slot 11 h)) = slot 11 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_12 : ∀ h, slot 12 (mergeRep 12 (slot 12 h)) = slot 12 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_13 : ∀ h, slot 13 (mergeRep 13 (slot 13 h)) = slot 13 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_14 : ∀ h, slot 14 (mergeRep 14 (slot 14 h)) = slot 14 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_15 : ∀ h, slot 15 (mergeRep 15 (slot 15 h)) = slot 15 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_16 : ∀ h, slot 16 (mergeRep 16 (slot 16 h)) = slot 16 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_17 : ∀ h, slot 17 (mergeRep 17 (slot 17 h)) = slot 17 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_18 : ∀ h, slot 18 (mergeRep 18 (slot 18 h)) = slot 18 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_19 : ∀ h, slot 19 (mergeRep 19 (slot 19 h)) = slot 19 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_20 : ∀ h, slot 20 (mergeRep 20 (slot 20 h)) = slot 20 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_21 : ∀ h, slot 21 (mergeRep 21 (slot 21 h)) = slot 21 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_22 : ∀ h, slot 22 (mergeRep 22 (slot 22 h)) = slot 22 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_23 : ∀ h, slot 23 (mergeRep 23 (slot 23 h)) = slot 23 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_24 : ∀ h, slot 24 (mergeRep 24 (slot 24 h)) = slot 24 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_25 : ∀ h, slot 25 (mergeRep 25 (slot 25 h)) = slot 25 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_26 : ∀ h, slot 26 (mergeRep 26 (slot 26 h)) = slot 26 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_27 : ∀ h, slot 27 (mergeRep 27 (slot 27 h)) = slot 27 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_28 : ∀ h, slot 28 (mergeRep 28 (slot 28 h)) = slot 28 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_29 : ∀ h, slot 29 (mergeRep 29 (slot 29 h)) = slot 29 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_30 : ∀ h, slot 30 (mergeRep 30 (slot 30 h)) = slot 30 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_31 : ∀ h, slot 31 (mergeRep 31 (slot 31 h)) = slot 31 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_32 : ∀ h, slot 32 (mergeRep 32 (slot 32 h)) = slot 32 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_33 : ∀ h, slot 33 (mergeRep 33 (slot 33 h)) = slot 33 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_34 : ∀ h, slot 34 (mergeRep 34 (slot 34 h)) = slot 34 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_35 : ∀ h, slot 35 (mergeRep 35 (slot 35 h)) = slot 35 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_36 : ∀ h, slot 36 (mergeRep 36 (slot 36 h)) = slot 36 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_37 : ∀ h, slot 37 (mergeRep 37 (slot 37 h)) = slot 37 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_38 : ∀ h, slot 38 (mergeRep 38 (slot 38 h)) = slot 38 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_39 : ∀ h, slot 39 (mergeRep 39 (slot 39 h)) = slot 39 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_40 : ∀ h, slot 40 (mergeRep 40 (slot 40 h)) = slot 40 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_41 : ∀ h, slot 41 (mergeRep 41 (slot 41 h)) = slot 41 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_42 : ∀ h, slot 42 (mergeRep 42 (slot 42 h)) = slot 42 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_43 : ∀ h, slot 43 (mergeRep 43 (slot 43 h)) = slot 43 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_44 : ∀ h, slot 44 (mergeRep 44 (slot 44 h)) = slot 44 h := by
  decide +kernel

lemma rep_slot : ∀ p h, slot p (mergeRep p (slot p h)) = slot p h := by
  intro p
  fin_cases p
  · exact rep_slot_0
  · exact rep_slot_1
  · exact rep_slot_2
  · exact rep_slot_3
  · exact rep_slot_4
  · exact rep_slot_5
  · exact rep_slot_6
  · exact rep_slot_7
  · exact rep_slot_8
  · exact rep_slot_9
  · exact rep_slot_10
  · exact rep_slot_11
  · exact rep_slot_12
  · exact rep_slot_13
  · exact rep_slot_14
  · exact rep_slot_15
  · exact rep_slot_16
  · exact rep_slot_17
  · exact rep_slot_18
  · exact rep_slot_19
  · exact rep_slot_20
  · exact rep_slot_21
  · exact rep_slot_22
  · exact rep_slot_23
  · exact rep_slot_24
  · exact rep_slot_25
  · exact rep_slot_26
  · exact rep_slot_27
  · exact rep_slot_28
  · exact rep_slot_29
  · exact rep_slot_30
  · exact rep_slot_31
  · exact rep_slot_32
  · exact rep_slot_33
  · exact rep_slot_34
  · exact rep_slot_35
  · exact rep_slot_36
  · exact rep_slot_37
  · exact rep_slot_38
  · exact rep_slot_39
  · exact rep_slot_40
  · exact rep_slot_41
  · exact rep_slot_42
  · exact rep_slot_43
  · exact rep_slot_44

def ChecksFor (p : Fin 45) : Prop := ∀ a b : Fin 30, a < b →
  slot p (mergeRep p a) = a → slot p (mergeRep p b) = b →
  MergeCheck (code p) (slot p) (mergeRep p a) (mergeRep p b) (certificate p a b)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_0 : ChecksFor 0 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_1 : ChecksFor 1 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_2 : ChecksFor 2 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_3 : ChecksFor 3 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_4 : ChecksFor 4 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_5 : ChecksFor 5 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_6 : ChecksFor 6 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_7 : ChecksFor 7 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_8 : ChecksFor 8 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_9 : ChecksFor 9 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_10 : ChecksFor 10 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_11 : ChecksFor 11 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_12 : ChecksFor 12 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_13 : ChecksFor 13 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_14 : ChecksFor 14 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_15 : ChecksFor 15 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_16 : ChecksFor 16 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_17 : ChecksFor 17 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_18 : ChecksFor 18 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_19 : ChecksFor 19 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_20 : ChecksFor 20 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_21 : ChecksFor 21 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_22 : ChecksFor 22 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_23 : ChecksFor 23 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_24 : ChecksFor 24 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_25 : ChecksFor 25 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_26 : ChecksFor 26 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_27 : ChecksFor 27 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_28 : ChecksFor 28 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_29 : ChecksFor 29 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_30 : ChecksFor 30 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_31 : ChecksFor 31 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_32 : ChecksFor 32 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_33 : ChecksFor 33 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_34 : ChecksFor 34 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_35 : ChecksFor 35 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_36 : ChecksFor 36 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_37 : ChecksFor 37 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_38 : ChecksFor 38 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_39 : ChecksFor 39 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_40 : ChecksFor 40 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_41 : ChecksFor 41 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_42 : ChecksFor 42 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_43 : ChecksFor 43 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_44 : ChecksFor 44 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

lemma all_checks : ∀ p, ChecksFor p := by
  intro p
  fin_cases p
  · exact checks_0
  · exact checks_1
  · exact checks_2
  · exact checks_3
  · exact checks_4
  · exact checks_5
  · exact checks_6
  · exact checks_7
  · exact checks_8
  · exact checks_9
  · exact checks_10
  · exact checks_11
  · exact checks_12
  · exact checks_13
  · exact checks_14
  · exact checks_15
  · exact checks_16
  · exact checks_17
  · exact checks_18
  · exact checks_19
  · exact checks_20
  · exact checks_21
  · exact checks_22
  · exact checks_23
  · exact checks_24
  · exact checks_25
  · exact checks_26
  · exact checks_27
  · exact checks_28
  · exact checks_29
  · exact checks_30
  · exact checks_31
  · exact checks_32
  · exact checks_33
  · exact checks_34
  · exact checks_35
  · exact checks_36
  · exact checks_37
  · exact checks_38
  · exact checks_39
  · exact checks_40
  · exact checks_41
  · exact checks_42
  · exact checks_43
  · exact checks_44

lemma actual_eq_iff_slot (t : H → Slot) (ht : Conditions t) (p : Fin 45)
    (hclosed : ∀ h k, closed (code p) h k ↔ slot p h = slot p k)
    (hq : localCode t = code p) (h k : H) : t h = t k ↔ slot p h = slot p k := by
  have hf (a b : H) (hab : slot p a = slot p b) : t a = t b := by
    apply closed_sound t ht.1 ht.2.2.1
    rw [hq]
    exact (hclosed a b).mpr hab
  constructor
  · intro heq
    by_contra hne
    have hrep (a : H) : t (mergeRep p (slot p a)) = t a := hf _ _ (rep_slot p a)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact mergeCheck_false t ht (code p) hq (slot p) hf _ _
        ((hrep h).trans (heq.trans (hrep k).symm)) _
        (all_checks p (slot p h) (slot p k) hlt (rep_slot p h) (rep_slot p k))
    · exact mergeCheck_false t ht (code p) hq (slot p) hf _ _
        ((hrep k).trans (heq.symm.trans (hrep h).symm)) _
        (all_checks p (slot p k) (slot p h) hgt (rep_slot p k) (rep_slot p h))
  · exact hf h k

def classLabel (p : Fin 45) (h : H) : Finset V := canonicalLabel (slot p) h

lemma lower_eq_label (t : H → Slot) (ht : Conditions t) (p : Fin 45)
    (hclosed : ∀ h k, closed (code p) h k ↔ slot p h = slot p k)
    (hq : localCode t = code p) (h : H) : lower t h = classLabel p h :=
  lower_eq_canonicalLabel t (slot p) (actual_eq_iff_slot t ht p hclosed hq) h

end PEqualNP.Outside.L_meta_2590.NonlocalMerge

namespace PEqualNP.Outside.L_meta_2590.SlotLabels

open FiniteSlots

def maskWord : Fin 45 → ℕ := ![717044977533379493273861595016988673, 1002367299225542016166459398851397633, 604611505078938005145601, 1002367299225542016166459383819026433, 664857864774063428997499861655896065, 654588766363988812382209, 1002367299225542016166459381671544833, 669969200334374568157590724444964865, 669969200334374568014601539387672577, 669969200334374568013475640554571777, 638932419142126625212399110145, 733611447441494013673473, 664857864774055164856154820456777729, 664857864774053983989815887280506881, 634057869695725068654175356929, 717044977533379493270483848052916225, 717044977533379493269357949219815425, 683827378781680577540385718273, 955931948876897827307185555457, 706315584149176803395142971679576066, 970678337718248364052482, 664797490394374026405337395353359362, 664797175957744552022702309626614786, 664797173481866834635183194650973186, 634000294561628441787813073922, 912885697341100285558786, 706315584149176803388387511037395970, 706315584149176803386135713371194370, 673595031880547336003680011266, 708993494785160617563682203657838596, 706315265959903517084148165983086596, 669969187950159723684434691707906052, 664776891091624895910667643955193860, 678546488588751167977026496516, 708993494785160617550171282373478404, 708993494785160617545667687041075204, 676148886475716226165948680196, 671289762982573626245841535656546312, 671289762953559406718079587292565512, 671290082332113543151137181845704712, 640191805832142861178167644168, 664857706273911327560303846415679497, 664797173481866834774783650540044297, 664776891091605996218193770084057097, 634077061351313571196295987209]

def mask (i : Fin 45) (s : Fin 30) : ℕ := (maskWord i / (2 ^ (10 * s.val))) % 1024

def maskSet (m : ℕ) : Finset V := Finset.univ.filter fun v => m.testBit v.val

def label (i : Fin 45) (s : Fin 30) : Finset V :=
  Finset.univ.filter fun v => ∃ h : H, endpoint h = v ∧ SlotTables.slot i h = s

abbrev LabelMatches (i : Fin 45) : Prop := ∀ (s : Fin 30) (v : V),
    (∃ h : H, endpoint h = v ∧ SlotTables.slot i h = s) ↔
      (mask i s).testBit v.val = true

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma labels_checked0 : ∀ j : Fin 9, LabelMatches ⟨0 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma labels_checked1 : ∀ j : Fin 9, LabelMatches ⟨9 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma labels_checked2 : ∀ j : Fin 9, LabelMatches ⟨18 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma labels_checked3 : ∀ j : Fin 9, LabelMatches ⟨27 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma labels_checked4 : ∀ j : Fin 9, LabelMatches ⟨36 + j.val, by omega⟩ := by
  decide +kernel

lemma labels_checked (i : Fin 45) : LabelMatches i := by
  fin_cases i
  · exact labels_checked0 0
  · exact labels_checked0 1
  · exact labels_checked0 2
  · exact labels_checked0 3
  · exact labels_checked0 4
  · exact labels_checked0 5
  · exact labels_checked0 6
  · exact labels_checked0 7
  · exact labels_checked0 8
  · exact labels_checked1 0
  · exact labels_checked1 1
  · exact labels_checked1 2
  · exact labels_checked1 3
  · exact labels_checked1 4
  · exact labels_checked1 5
  · exact labels_checked1 6
  · exact labels_checked1 7
  · exact labels_checked1 8
  · exact labels_checked2 0
  · exact labels_checked2 1
  · exact labels_checked2 2
  · exact labels_checked2 3
  · exact labels_checked2 4
  · exact labels_checked2 5
  · exact labels_checked2 6
  · exact labels_checked2 7
  · exact labels_checked2 8
  · exact labels_checked3 0
  · exact labels_checked3 1
  · exact labels_checked3 2
  · exact labels_checked3 3
  · exact labels_checked3 4
  · exact labels_checked3 5
  · exact labels_checked3 6
  · exact labels_checked3 7
  · exact labels_checked3 8
  · exact labels_checked4 0
  · exact labels_checked4 1
  · exact labels_checked4 2
  · exact labels_checked4 3
  · exact labels_checked4 4
  · exact labels_checked4 5
  · exact labels_checked4 6
  · exact labels_checked4 7
  · exact labels_checked4 8

lemma label_eq_mask (i : Fin 45) (s : Fin 30) : label i s = maskSet (mask i s) := by
  ext v
  simp only [label, maskSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact labels_checked i s v

end PEqualNP.Outside.L_meta_2590.SlotLabels

namespace PEqualNP.Outside.L_meta_2590.SlotLabels

def patternKind : Fin 45 → Fin 3 := ![0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 1, 1, 0, 2, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1]
def patternIndex : Fin 45 → Fin 30 := ![0, 1, 0, 2, 3, 1, 4, 5, 6, 7, 0, 2, 8, 9, 1, 10, 11, 2, 3, 12, 3, 13, 14, 15, 4, 4, 16, 17, 5, 18, 19, 20, 21, 6, 22, 23, 7, 24, 25, 26, 8, 27, 28, 29, 9]

def pattern (i : Fin 45) : List (ℕ × ℕ) :=
  if patternKind i = 0 then SlotGeometry.knownPatterns[(patternIndex i).val]?.getD []
  else if patternKind i = 1 then ExtraGeometry.fivePatterns[(patternIndex i).val]?.getD []
  else ExtraGeometry.fourPatterns[(patternIndex i).val]?.getD []

def patternMask (p : List (ℕ × ℕ)) (s : Fin 30) : ℕ :=
  let r := p[s.val / 2]?.getD (0, 0)
  if s.val % 2 = 0 then r.1 else r.2

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma masks_match_catalogue : ∀ (i : Fin 45) (s : Fin 30),
    mask i s = patternMask (pattern i) s := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma pattern_known : ∀ i : Fin 45,
    pattern i ∈ SlotGeometry.knownPatterns ∨ pattern i ∈ ExtraGeometry.fivePatterns ∨
      pattern i ∈ ExtraGeometry.fourPatterns := by decide +kernel

end PEqualNP.Outside.L_meta_2590.SlotLabels

namespace PEqualNP.Outside.L_meta_2590.SlotOrbits

open FiniteSlots

def word : Fin 45 → ℕ := ![105043959308623874, 104969483439309342, 1016437415936, 105043376338371210, 58393590189269218, 596667025024, 104819952128796798, 85978298829530330, 28557403578642670, 85977711937907906, 186024800087141, 725516043896, 58393586762330342, 20112277620452554, 78272031943793, 105043375186701410, 104819948213824694, 334977050895389, 335267972259841, 85978427682988230, 723247694432, 58170165482775806, 58168577991586042, 19706175202210034, 77108366715049, 593246998148, 85977843561065694, 28557821711281386, 186027585070177, 104936499226878074, 47515898312942722, 47515894890442886, 641515830438946, 35490131143697, 104935623047196814, 104786962864991258, 334555003284485, 104861733572600838, 104861730154540134, 104818782273334450, 334262958842905, 39179399506970226, 38879166909584042, 9160243775196690, 2925682675233]

def canonical (i : Fin 45) : Fin 45 :=
  if word i % 4 = 0 then 2 else if word i % 4 = 1 then 18 else 0

def vertexPerm (i : Fin 45) : Fin 120 := ⟨((word i / 4) % 128) % 120, by omega⟩

def rename (i : Fin 45) (s : Fin 30) : Fin 30 :=
  if s.val < 2 * (4 + word i % 4) then
    ⟨((word i / 512) / (2 ^ (4 * s.val))) % 16, by omega⟩
  else s

def flip (s : Fin 30) : Fin 30 := ⟨2 * (s.val / 2) + (1 - s.val % 2), by omega⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma rename_injective : ∀ i : Fin 45, Function.Injective (rename i) := by
  unfold Function.Injective
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma rename_flip : ∀ (i : Fin 45) (s : Fin 30), rename i (flip s) = flip (rename i s) := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma masks_permuted : ∀ (i : Fin 45) (s : Fin 30) (v : V),
    (SlotLabels.mask i s).testBit v.val =
      (SlotLabels.mask (canonical i) (rename i s)).testBit (Petersen.permV (vertexPerm i) v).val := by
  decide +kernel

lemma maskSet_image (i : Fin 45) (s : Fin 30) :
    (SlotLabels.maskSet (SlotLabels.mask i s)).image (Petersen.permEquiv (vertexPerm i)) =
      SlotLabels.maskSet (SlotLabels.mask (canonical i) (rename i s)) := by
  ext u
  obtain ⟨v, rfl⟩ := (Petersen.permEquiv (vertexPerm i)).surjective u
  have hh : Petersen.permEquiv (vertexPerm i) v ∈
      (SlotLabels.maskSet (SlotLabels.mask i s)).image (Petersen.permEquiv (vertexPerm i)) ↔
      v ∈ SlotLabels.maskSet (SlotLabels.mask i s) := by simp
  rw [hh]
  simpa [SlotLabels.maskSet, Petersen.permEquiv] using
    congrArg (· = true) (masks_permuted i s v)

end PEqualNP.Outside.L_meta_2590.SlotOrbits

namespace PEqualNP.Outside.L_meta_2590.FiniteSlots

lemma classified_selected (t : H → Slot) (ht : Conditions t) :
    ∃ i : Fin 45, localCode t = SlotTables.code i ∧
      (∀ h k, t h = t k ↔ SlotTables.slot i h = SlotTables.slot i k) ∧
      ∀ h, lower t h = SlotLabels.label i (SlotTables.slot i h) := by
  obtain ⟨i, hi⟩ := SlotTree.conditions_classified t ht
  refine ⟨i, hi, ?_, ?_⟩
  · exact NonlocalMerge.actual_eq_iff_slot t ht i (SlotTables.closed_iff_slot i) hi
  · intro h
    exact NonlocalMerge.lower_eq_label t ht i (SlotTables.closed_iff_slot i) hi h

end PEqualNP.Outside.L_meta_2590.FiniteSlots


namespace PEqualNP.Outside.L_meta_2590.TopFormFinite

abbrev V := Fin 10
abbrev I := Fin 15
def ends : I → V × V := ![(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def neighbors : V → Finset V := ![{1,4,5},{0,2,6},{1,3,7},{2,4,8},{0,3,9},{0,7,8},{1,8,9},{2,5,9},{3,5,6},{4,6,7}]
abbrev adjacent (U : Finset I) (u v : V) : Prop :=
  v ∈ neighbors u ∧ ∀ i ∈ U,
    ¬ ((u = (ends i).1 ∧ v = (ends i).2) ∨
       (u = (ends i).2 ∧ v = (ends i).1))

abbrev independent (X : Finset V) : Prop :=
  ∀ i : I, ¬ ((ends i).1 ∈ X ∧ (ends i).2 ∈ X)

abbrev badRow (U : Finset I) (X : Finset V) : Prop :=
  independent X ∧
  (∀ v : V, v ∉ X → ∃ i ∈ U, (ends i).1 ≠ v ∧ (ends i).2 ≠ v) ∧
  ∀ v : V, ∃ i ∈ U,
    (¬ adjacent U v (ends i).1 ∨ (ends i).1 ∈ X) ∧
    (¬ adjacent U v (ends i).2 ∨ (ends i).2 ∈ X)

def rows : I → Finset V := ![{0,2,6},{0,3,9},{0,7,8},{1,3,7},{1,4,5},{1,8,9},{2,4,8},{2,5,9},{3,5,6},{4,6,7},{0,2,8,9},{0,3,6,7},{1,3,5,9},{1,4,7,8},{2,4,5,6}]

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma triples0 : ∀ b c : I, (0 : I) < b → b < c →
    ∃ r : I, badRow {0,b,c} (rows r) := by decide +kernel

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma triples1 : ∀ b c : I, (1 : I) < b → b < c →
    ∃ r : I, badRow {1,b,c} (rows r) := by decide +kernel

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma triples2 : ∀ b c : I, (2 : I) < b → b < c →
    ∃ r : I, badRow {2,b,c} (rows r) := by decide +kernel

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma triples3 : ∀ b c : I, (3 : I) < b → b < c →
    ∃ r : I, badRow {3,b,c} (rows r) := by decide +kernel

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma triples4 : ∀ b c : I, (4 : I) < b → b < c →
    ∃ r : I, badRow {4,b,c} (rows r) := by decide +kernel

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma triples5 : ∀ b c : I, (5 : I) < b → b < c →
    ∃ r : I, badRow {5,b,c} (rows r) := by decide +kernel

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma triples6 : ∀ b c : I, (6 : I) < b → b < c →
    ∃ r : I, badRow {6,b,c} (rows r) := by decide +kernel

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma triples7 : ∀ b c : I, (7 : I) < b → b < c →
    ∃ r : I, badRow {7,b,c} (rows r) := by decide +kernel

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma triples8 : ∀ b c : I, (8 : I) < b → b < c →
    ∃ r : I, badRow {8,b,c} (rows r) := by decide +kernel

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma triples9 : ∀ b c : I, (9 : I) < b → b < c →
    ∃ r : I, badRow {9,b,c} (rows r) := by decide +kernel

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma triples10 : ∀ b c : I, (10 : I) < b → b < c →
    ∃ r : I, badRow {10,b,c} (rows r) := by decide +kernel

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma triples11 : ∀ b c : I, (11 : I) < b → b < c →
    ∃ r : I, badRow {11,b,c} (rows r) := by decide +kernel

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma triples12 : ∀ b c : I, (12 : I) < b → b < c →
    ∃ r : I, badRow {12,b,c} (rows r) := by decide +kernel

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma triples13 : ∀ b c : I, (13 : I) < b → b < c →
    ∃ r : I, badRow {13,b,c} (rows r) := by decide +kernel

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma triples14 : ∀ b c : I, (14 : I) < b → b < c →
    ∃ r : I, badRow {14,b,c} (rows r) := by decide +kernel

lemma sorted_triples : ∀ a b c : I, a < b → b < c →
    ∃ r : I, badRow {a,b,c} (rows r) := by
  intro a
  fin_cases a
  · exact triples0
  · exact triples1
  · exact triples2
  · exact triples3
  · exact triples4
  · exact triples5
  · exact triples6
  · exact triples7
  · exact triples8
  · exact triples9
  · exact triples10
  · exact triples11
  · exact triples12
  · exact triples13
  · exact triples14

def Covers (U : Finset I) (S : Finset V) : Prop :=
  ∀ i ∈ U, (ends i).1 ∈ S ∨ (ends i).2 ∈ S

def Condition (U : Finset I) : Prop :=
  ∃ t : V, ∀ i ∈ U, ∃ w : V,
    (w = (ends i).1 ∨ w = (ends i).2) ∧ adjacent U t w ∧
    ∀ X : Finset V, w ∈ X → independent X →
      ∃ S : Finset V,
        (S.card ≤ 1 ∨ ∃ z : V, ∀ y ∈ S, adjacent U y z) ∧
        Covers U S ∧ Disjoint S X

lemma neighbors_symm : ∀ u v : V, v ∈ neighbors u ↔ u ∈ neighbors v := by
  decide +kernel

lemma adjacent_symm {U : Finset I} {u v : V} (h : adjacent U u v) :
    adjacent U v u := by
  refine ⟨(neighbors_symm u v).mp h.1, ?_⟩
  intro i hi hp
  apply h.2 i hi
  rcases hp with ⟨hva, hub⟩ | ⟨hvb, hua⟩
  · exact Or.inr ⟨hub, hva⟩
  · exact Or.inl ⟨hua, hvb⟩

lemma adjacent_mono {T U : Finset I} (hTU : T ⊆ U) {u v : V}
    (h : adjacent U u v) : adjacent T u v := by
  exact ⟨h.1, fun i hi => h.2 i (hTU hi)⟩

lemma condition_mono {T U : Finset I} (hTU : T ⊆ U) (h : Condition U) :
    Condition T := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t, ?_⟩
  intro i hi
  obtain ⟨w, hw, hadj, hall⟩ := ht i (hTU hi)
  refine ⟨w, hw, adjacent_mono hTU hadj, ?_⟩
  intro X hwX hX
  obtain ⟨S, hshape, hcover, hdis⟩ := hall X hwX hX
  refine ⟨S, ?_, fun j hj => hcover j (hTU hj), hdis⟩
  rcases hshape with hsmall | ⟨z, hz⟩
  · exact Or.inl hsmall
  · exact Or.inr ⟨z, fun y hy => adjacent_mono hTU (hz y hy)⟩

lemma badRow_not_shape {U : Finset I} {X S : Finset V}
    (hbad : badRow U X)
    (hshape : S.card ≤ 1 ∨ ∃ z : V, ∀ y ∈ S, adjacent U y z)
    (hcover : Covers U S) (hdis : Disjoint S X) : False := by
  have hout {v : V} (hv : v ∈ S) : v ∉ X := by
    intro hx
    exact Finset.disjoint_left.mp hdis hv hx
  rcases hshape with hsmall | ⟨z, hz⟩
  · obtain ⟨i, hi, _, _⟩ := hbad.2.2 0
    have hSne : S.Nonempty := by
      rcases hcover i hi with hl | hr
      · exact ⟨_, hl⟩
      · exact ⟨_, hr⟩
    obtain ⟨v, hv⟩ := hSne
    obtain ⟨j, hj, hjl, hjr⟩ := hbad.2.1 v (hout hv)
    rcases hcover j hj with hl | hr
    · exact hjl (Finset.card_le_one.mp hsmall _ hl _ hv)
    · exact hjr (Finset.card_le_one.mp hsmall _ hr _ hv)
  · obtain ⟨i, hi, hl, hr⟩ := hbad.2.2 z
    rcases hcover i hi with hleft | hright
    · rcases hl with hnadj | hx
      · exact hnadj (adjacent_symm (hz _ hleft))
      · exact hout hleft hx
    · rcases hr with hnadj | hx
      · exact hnadj (adjacent_symm (hz _ hright))
      · exact hout hright hx

lemma badRow_not_condition {U : Finset I} {X : Finset V}
    (hbad : badRow U X) : ¬ Condition U := by
  rintro ⟨t, ht⟩
  obtain ⟨i, hi, hl, hr⟩ := hbad.2.2 t
  obtain ⟨w, hw, hadj, hall⟩ := ht i hi
  have hwX : w ∈ X := by
    rcases hw with rfl | rfl
    · exact hl.resolve_left (fun hn => hn hadj)
    · exact hr.resolve_left (fun hn => hn hadj)
  obtain ⟨S, hshape, hcover, hdis⟩ := hall X hwX hbad.1
  exact badRow_not_shape hbad hshape hcover hdis

lemma all_triples_of_sorted
    (hsorted : ∀ a b c : I, a < b → b < c →
      ∃ r : I, badRow {a,b,c} (rows r)) :
    ∀ a b c : I, a ≠ b → a ≠ c → b ≠ c →
      ∃ r : I, badRow {a,b,c} (rows r) := by
  intro a b c hab hac hbc
  rcases lt_or_gt_of_ne hab with hab | hba
  · rcases lt_or_gt_of_ne hbc with hbc | hcb
    · exact hsorted a b c hab hbc
    · rcases lt_or_gt_of_ne hac with hac | hca
      · have hp : ({a,c,b} : Finset I) = {a,b,c} :=
          congrArg (fun s : Finset I => insert a s) (Finset.pair_comm c b)
        exact hp ▸ hsorted a c b hac hcb
      · have hp : ({c,a,b} : Finset I) = {a,b,c} :=
          (Finset.insert_comm c a {b}).trans
            (congrArg (fun s : Finset I => insert a s) (Finset.pair_comm c b))
        exact hp ▸ hsorted c a b hca hab
  · rcases lt_or_gt_of_ne hac with hac | hca
    · have hp : ({b,a,c} : Finset I) = {a,b,c} := Finset.insert_comm b a {c}
      exact hp ▸ hsorted b a c hba hac
    · rcases lt_or_gt_of_ne hbc with hbc | hcb
      · have hp : ({b,c,a} : Finset I) = {a,b,c} :=
          (congrArg (fun s : Finset I => insert b s) (Finset.pair_comm c a)).trans
            (Finset.insert_comm b a {c})
        exact hp ▸ hsorted b c a hbc hca
      · have hp : ({c,b,a} : Finset I) = {a,b,c} :=
          (Finset.insert_comm c b {a}).trans
            ((congrArg (fun s : Finset I => insert b s) (Finset.pair_comm c a)).trans
              (Finset.insert_comm b a {c}))
        exact hp ▸ hsorted c b a hcb hba

lemma card_le_two_of_triples
    (htriples : ∀ a b c : I, a ≠ b → a ≠ c → b ≠ c →
      ∃ r : I, badRow {a,b,c} (rows r))
    {U : Finset I} (hU : Condition U) : U.card ≤ 2 := by
  by_contra hn
  have hlarge : 2 < U.card := Nat.lt_of_not_ge hn
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hlarge
  obtain ⟨r, hr⟩ := htriples a b c hab hac hbc
  apply badRow_not_condition hr
  apply condition_mono (U := U) _ hU
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc

lemma condition_card_le_two {U : Finset I} (h : Condition U) : U.card ≤ 2 :=
  card_le_two_of_triples (all_triples_of_sorted sorted_triples) h


def edge (i : I) : Sym2 V := s((ends i).1, (ends i).2)

def edgeSet : Finset (Sym2 V) := Finset.univ.image edge

def indices (U : Finset (Sym2 V)) : Finset I :=
  Finset.univ.filter fun i => edge i ∈ U

lemma mem_indices {U : Finset (Sym2 V)} {i : I} :
    i ∈ indices U ↔ edge i ∈ U := by
  simp only [indices, Finset.mem_filter, Finset.mem_univ, true_and]

lemma image_indices_eq {U : Finset (Sym2 V)} (hU : U ⊆ edgeSet) :
    (indices U).image edge = U := by
  ext e
  constructor
  · intro he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    exact mem_indices.mp hi
  · intro he
    obtain ⟨i, _, hie⟩ := Finset.mem_image.mp (hU he)
    exact Finset.mem_image.mpr ⟨i, mem_indices.mpr (hie.symm ▸ he), hie⟩

set_option synthInstance.maxSize 10000 in
lemma neighbor_ends : ∀ u v : V, v ∈ neighbors u ↔
    ∃ i : I, (u = (ends i).1 ∧ v = (ends i).2) ∨
      (u = (ends i).2 ∧ v = (ends i).1) := by
  decide +kernel

lemma adjacent_indices_iff (G : SimpleGraph V)
    (hG : ∀ u v : V, G.Adj u v ↔ v ∈ neighbors u)
    (U : Finset (Sym2 V)) (u v : V) :
    adjacent (indices U) u v ↔ (G.deleteEdges ↑U).Adj u v := by
  rw [SimpleGraph.deleteEdges_adj]
  change adjacent (indices U) u v ↔ G.Adj u v ∧ s(u,v) ∉ U
  constructor
  · intro h
    refine ⟨(hG u v).mpr h.1, ?_⟩
    intro huv
    obtain ⟨i, hi⟩ := (neighbor_ends u v).mp h.1
    have heq : s(u,v) = edge i := Sym2.eq_iff.mpr hi
    exact h.2 i (mem_indices.mpr (heq ▸ huv)) hi
  · rintro ⟨hGuv, huv⟩
    refine ⟨(hG u v).mp hGuv, ?_⟩
    intro i hi hp
    have heq : s(u,v) = edge i := Sym2.eq_iff.mpr hp
    exact huv (heq.symm ▸ mem_indices.mp hi)

def GraphIndependent (G : SimpleGraph V) (X : Finset V) : Prop :=
  ∀ u ∈ X, ∀ v ∈ X, ¬ G.Adj u v

lemma graphIndependent_of_independent (G : SimpleGraph V)
    (hG : ∀ u v : V, G.Adj u v ↔ v ∈ neighbors u)
    {X : Finset V} (hX : independent X) : GraphIndependent G X := by
  intro u hu v hv hadj
  obtain ⟨i, hi⟩ := (neighbor_ends u v).mp ((hG u v).mp hadj)
  rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hX i ⟨hu, hv⟩
  · exact hX i ⟨hv, hu⟩

def GraphCondition (G : SimpleGraph V) (U : Finset (Sym2 V)) : Prop :=
  ∃ t : V, ∀ u v : V, s(u,v) ∈ U → ∃ w : V,
    (w = u ∨ w = v) ∧ (G.deleteEdges ↑U).Adj t w ∧
    ∀ X : Finset V, w ∈ X → GraphIndependent G X →
      ∃ S : Finset V,
        (S.card ≤ 1 ∨ ∃ z : V, ∀ y ∈ S, (G.deleteEdges ↑U).Adj y z) ∧
        (∀ p q : V, s(p,q) ∈ U → p ∈ S ∨ q ∈ S) ∧ Disjoint S X

lemma condition_of_graphCondition (G : SimpleGraph V)
    (hG : ∀ u v : V, G.Adj u v ↔ v ∈ neighbors u)
    {U : Finset (Sym2 V)} (hU : GraphCondition G U) : Condition (indices U) := by
  obtain ⟨t, ht⟩ := hU
  refine ⟨t, ?_⟩
  intro i hi
  obtain ⟨w, hw, hadj, hall⟩ := ht (ends i).1 (ends i).2 (mem_indices.mp hi)
  refine ⟨w, hw, (adjacent_indices_iff G hG U t w).mpr hadj, ?_⟩
  intro X hwX hX
  obtain ⟨S, hshape, hcover, hdis⟩ :=
    hall X hwX (graphIndependent_of_independent G hG hX)
  refine ⟨S, ?_, ?_, hdis⟩
  · rcases hshape with hsmall | ⟨z, hz⟩
    · exact Or.inl hsmall
    · exact Or.inr ⟨z, fun y hy => (adjacent_indices_iff G hG U y z).mpr (hz y hy)⟩
  · intro j hj
    exact hcover (ends j).1 (ends j).2 (mem_indices.mp hj)

lemma graph_card_le_two
    (hbound : ∀ U : Finset I, Condition U → U.card ≤ 2)
    (G : SimpleGraph V) (hG : ∀ u v : V, G.Adj u v ↔ v ∈ neighbors u)
    {U : Finset (Sym2 V)} (hU : U ⊆ edgeSet) (hcond : GraphCondition G U) :
    U.card ≤ 2 := by
  calc
    U.card = ((indices U).image edge).card := congrArg Finset.card (image_indices_eq hU).symm
    _ ≤ (indices U).card := Finset.card_image_le
    _ ≤ 2 := hbound _ (condition_of_graphCondition G hG hcond)

lemma mem_edgeSet_iff (u v : V) : s(u,v) ∈ edgeSet ↔ v ∈ neighbors u := by
  simp only [edgeSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact (neighbor_ends u v).mpr ⟨i, Sym2.eq_iff.mp hi.symm⟩
  · intro h
    obtain ⟨i, hi⟩ := (neighbor_ends u v).mp h
    exact ⟨i, (Sym2.eq_iff.mpr hi).symm⟩

lemma edgeSet_eq_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ u v : V, G.Adj u v ↔ v ∈ neighbors u) : edgeSet = G.edgeFinset := by
  apply Finset.ext
  intro e
  refine Sym2.inductionOn e ?_
  intro u v
  rw [mem_edgeSet_iff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, hG]

lemma graph_card_le_two_of_subset
    (hbound : ∀ U : Finset I, Condition U → U.card ≤ 2)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ u v : V, G.Adj u v ↔ v ∈ neighbors u)
    {U : Finset (Sym2 V)} (hU : U ⊆ G.edgeFinset) (hcond : GraphCondition G U) :
    U.card ≤ 2 := by
  apply graph_card_le_two hbound G hG _ hcond
  rwa [edgeSet_eq_edgeFinset G hG]

def BooleanCondition (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset (Sym2 V)) : Prop :=
  ∃ t : V, ∀ u v : V, s(u,v) ∈ U → ∃ w : V,
    (w = u ∨ w = v) ∧ (G.deleteEdges ↑U).Adj t w ∧
    ∀ x : V → Bool, x w = true →
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = false →
      ∃ S : Finset V,
        (S.card ≤ 1 ∨ ∃ z : V, ∀ y ∈ S, (G.deleteEdges ↑U).Adj y z) ∧
        (∀ p q : V, s(p,q) ∈ U → p ∈ S ∨ q ∈ S) ∧ ∀ y ∈ S, x y = false

lemma graphFun_mask_false (G : SimpleGraph V) [DecidableRel G.Adj]
    {X : Finset V} (hX : GraphIndependent G X) :
    PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (fun v => decide (v ∈ X)) = false := by
  have hnone : ¬ ∃ u v : V, G.Adj u v ∧ u ∈ X ∧ v ∈ X := by
    rintro ⟨u, v, hadj, hu, hv⟩
    exact hX u hu v hv hadj
  simp [PEqualNP.MetaComplexity.NestedCover.graphFun, hnone]

lemma graphCondition_of_boolean (G : SimpleGraph V) [DecidableRel G.Adj]
    {U : Finset (Sym2 V)} (h : BooleanCondition G U) : GraphCondition G U := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t, ?_⟩
  intro u v huv
  obtain ⟨w, hw, hadj, hall⟩ := ht u v huv
  refine ⟨w, hw, hadj, ?_⟩
  intro X hwX hX
  obtain ⟨S, hshape, hcover, hout⟩ :=
    hall (fun v => decide (v ∈ X)) (by simpa using hwX) (graphFun_mask_false G hX)
  refine ⟨S, hshape, hcover, Finset.disjoint_left.mpr ?_⟩
  intro y hyS hyX
  have hf := hout y hyS
  simp [hyX] at hf

lemma Boolean_card_le_two
    (hbound : ∀ U : Finset I, Condition U → U.card ≤ 2)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ u v : V, G.Adj u v ↔ v ∈ neighbors u)
    {U : Finset (Sym2 V)} (hU : U ⊆ G.edgeFinset) (hfinish : BooleanCondition G U) :
    U.card ≤ 2 :=
  graph_card_le_two_of_subset hbound G hG hU (graphCondition_of_boolean G hfinish)

lemma graph_condition_card_le_two
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ u v : V, G.Adj u v ↔ v ∈ neighbors u)
    {U : Finset (Sym2 V)} (hU : U ⊆ G.edgeFinset) (hcond : GraphCondition G U) :
    U.card ≤ 2 :=
  graph_card_le_two_of_subset (fun _ h => condition_card_le_two h) G hG hU hcond

lemma finish_condition_card_le_two
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ u v : V, G.Adj u v ↔ v ∈ neighbors u)
    {U : Finset (Sym2 V)} (hU : U ⊆ G.edgeFinset) (hfinish : BooleanCondition G U) :
    U.card ≤ 2 :=
  Boolean_card_le_two (fun _ h => condition_card_le_two h) G hG hU hfinish

end PEqualNP.Outside.L_meta_2590.TopFormFinite

namespace PEqualNP.Outside.L_meta_2590.SlotGateIds
open FiniteSlots

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma slot_bar : ∀ (p : Fin 45) (h : H),
    SlotTables.slot p (barH h) = SlotOrbits.flip (SlotTables.slot p h) := by
  decide +kernel

lemma same_gate_cases {e f : Slot} (h : e.1 = f.1) : e = f ∨ e = bar f := by
  rcases e with ⟨j, s⟩
  rcases f with ⟨k, t⟩
  dsimp only at h
  subst k
  cases s <;> cases t <;> simp [bar]

lemma signed_gate_injective {α : Type} (f : α × Bool → Slot)
    (hf : Function.Injective f) (hb : ∀ a b, f (a, !b) = bar (f (a, b))) :
    Function.Injective (fun a => (f (a, false)).1) := by
  intro a b h
  rcases same_gate_cases h with he | he
  · exact congrArg Prod.fst (hf he)
  · have he' : f (a, false) = f (b, true) := he.trans (hb b false).symm
    exact congrArg Prod.fst (hf he')

lemma gate_eq_iff (t : H → Slot) (p : Fin 45)
    (hb : ∀ h, t (barH h) = bar (t h))
    (heq : ∀ h k, t h = t k ↔ SlotTables.slot p h = SlotTables.slot p k)
    (h k : H) :
    (t h).1 = (t k).1 ↔ SlotTables.slot p h = SlotTables.slot p k ∨
      SlotTables.slot p h = SlotOrbits.flip (SlotTables.slot p k) := by
  constructor
  · intro hg
    rcases same_gate_cases hg with he | he
    · exact Or.inl ((heq h k).mp he)
    · right
      rw [← slot_bar p k]
      apply (heq h (barH k)).mp
      rw [hb k]
      exact he
  · rintro (hsame | hopp)
    · exact congrArg Prod.fst ((heq h k).mpr hsame)
    · have hc : SlotTables.slot p h = SlotTables.slot p (barH k) := by
        rw [slot_bar p k]
        exact hopp
      have ha := (heq h (barH k)).mpr hc
      rw [hb k] at ha
      simpa only [bar] using congrArg (fun e : Slot => e.1) ha

lemma paired_iff_div_two : ∀ a b : Fin 30,
    (a = b ∨ a = SlotOrbits.flip b) ↔ a.val / 2 = b.val / 2 := by
  decide +kernel

lemma gate_id_eq_iff (t : H → Slot) (p : Fin 45)
    (hb : ∀ h, t (barH h) = bar (t h))
    (heq : ∀ h k, t h = t k ↔ SlotTables.slot p h = SlotTables.slot p k)
    (h k : H) : (t h).1 = (t k).1 ↔
      (SlotTables.slot p h).val / 2 = (SlotTables.slot p k).val / 2 :=
  (gate_eq_iff t p hb heq h k).trans (paired_iff_div_two _ _)

lemma mem_lower_iff_selected (t : H → Slot) (v : V) (h : H) :
    v ∈ lower t h ↔ t h ∈ selected t v := by
  rw [mem_selected]
  simp only [lower, Finset.mem_filter, Finset.mem_univ, true_and]

lemma selected_subset_W (t : H → Slot) (W : V → Finset Slot)
    (hw : ∀ h, t h ∈ W (endpoint h)) (v : V) : selected t v ⊆ W v := by
  intro s hs
  obtain ⟨h, rfl, rfl⟩ := mem_selected.mp hs
  exact hw h

end PEqualNP.Outside.L_meta_2590.SlotGateIds

namespace PEqualNP.Outside.L_meta_2590.TopFormFinite

def missedEdges (S : Finset V) : Finset I :=
  Finset.univ.filter fun i => (ends i).1 ∉ S ∧ (ends i).2 ∉ S

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma small_cover_misses : ∀ S : Finset V,
    (S.card ≤ 5 → 2 ≤ (missedEdges S).card) ∧
    (S.card ≤ 4 → 3 ≤ (missedEdges S).card) := by
  decide +kernel

lemma edge_injective : Function.Injective edge := by
  unfold Function.Injective
  decide +kernel

lemma missed_card_le_removed
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ u v : V, G.Adj u v ↔ v ∈ neighbors u)
    (U : Finset (Sym2 V)) (S : Finset V)
    (hcover : ∀ u v : V, (G.deleteEdges ↑U).Adj u v → u ∈ S ∨ v ∈ S) :
    (missedEdges S).card ≤ U.card := by
  have hsub : (missedEdges S).image edge ⊆ U := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    have hout := (Finset.mem_filter.mp hi).2
    by_contra hnot
    have hadj : G.Adj (ends i).1 (ends i).2 :=
      (hG _ _).mpr ((neighbor_ends _ _).mpr ⟨i, Or.inl ⟨rfl, rfl⟩⟩)
    have hdeleted : (G.deleteEdges ↑U).Adj (ends i).1 (ends i).2 := by
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨hadj, ?_⟩
      change edge i ∉ U
      exact hnot
    rcases hcover _ _ hdeleted with hleft | hright
    · exact hout.1 hleft
    · exact hout.2 hright
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ edge_injective] at hcard
  exact hcard

lemma cover_after_delete_le_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ u v : V, G.Adj u v ↔ v ∈ neighbors u)
    {U : Finset (Sym2 V)} {S : Finset V} (hU : U.card ≤ 1)
    (hcover : ∀ u v : V, (G.deleteEdges ↑U).Adj u v → u ∈ S ∨ v ∈ S) :
    6 ≤ S.card := by
  have hmiss := missed_card_le_removed G hG U S hcover
  by_contra hsmall
  have hS : S.card ≤ 5 := by omega
  have htwo := (small_cover_misses S).1 hS
  omega

lemma cover_after_delete_le_two
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ u v : V, G.Adj u v ↔ v ∈ neighbors u)
    {U : Finset (Sym2 V)} {S : Finset V} (hU : U.card ≤ 2)
    (hcover : ∀ u v : V, (G.deleteEdges ↑U).Adj u v → u ∈ S ∨ v ∈ S) :
    5 ≤ S.card := by
  have hmiss := missed_card_le_removed G hG U S hcover
  by_contra hsmall
  have hS : S.card ≤ 4 := by omega
  have hthree := (small_cover_misses S).2 hS
  omega

end PEqualNP.Outside.L_meta_2590.TopFormFinite
