import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_2592_aux.FewNots

def Point := Fin 10 → Bool

def Below (x y : Point) : Prop := ∀ i, x i = true → y i = true

def Increasing (g : Point → Bool) : Prop :=
  ∀ x y, Below x y → g x = true → g y = true

def edges : List (Fin 10 × Fin 10) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
   (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
   (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]

def graph (x : Point) : Bool := edges.any fun e => x e.1 && x e.2

def edgePoint (e : Fin 10 × Fin 10) : Point :=
  fun i => decide (i = e.1 ∨ i = e.2)

def maskPoint (a : ℕ) : Point := fun i => a.testBit i.val

def maximalIndependent : List ℕ :=
  [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]

lemma edgePoint_below (e : Fin 10 × Fin 10) (x : Point)
    (hu : x e.1 = true) (hv : x e.2 = true) : Below (edgePoint e) x := by
  intro i hi
  simp only [edgePoint, decide_eq_true_eq] at hi
  rcases hi with rfl | rfl
  · exact hu
  · exact hv

lemma graph_true_witness (x : Point) (hx : graph x = true) :
    ∃ e ∈ edges, Below (edgePoint e) x := by
  obtain ⟨e, he, h⟩ := List.any_eq_true.mp hx
  have hb : x e.1 = true ∧ x e.2 = true := by
    simpa only [Bool.and_eq_true] using h
  exact ⟨e, he, edgePoint_below e x hb.1 hb.2⟩

lemma edgePoint_true (e : Fin 10 × Fin 10) (he : e ∈ edges) :
    graph (edgePoint e) = true := by
  apply List.any_eq_true.mpr
  exact ⟨e, he, by simp [edgePoint]⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 0 in
lemma independent_boundaries :
    (∀ a ∈ maximalIndependent, graph (maskPoint a) = false) ∧
    (∀ x : Point, graph x = false →
      ∃ a ∈ maximalIndependent, Below x (maskPoint a)) := by
  have negative : maximalIndependent.all (fun a => !(graph (maskPoint a))) = true := by
    decide +kernel
  have cover : ∀ x : Point, graph x = false →
      maximalIndependent.any (fun a =>
        (List.ofFn (fun i : Fin 10 => !x i || maskPoint a i)).all id) = true := by
    intro x
    have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := by
      funext i
      fin_cases i <;> rfl
    rw [hx]
    generalize x 0 = a, x 1 = b, x 2 = c, x 3 = d, x 4 = e,
      x 5 = f, x 6 = g, x 7 = h, x 8 = i, x 9 = j
    revert a b c d e f g h i j
    decide +kernel
  constructor
  · intro a ha
    have hn := List.all_eq_true.mp negative a ha
    simpa using hn
  · intro x hx
    obtain ⟨a, ha, hab⟩ := List.any_eq_true.mp (cover x hx)
    refine ⟨a, ha, ?_⟩
    intro i hi
    have hb := List.all_eq_true.mp hab _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
    simpa [hi] using hb

lemma lower_of_edges (g : Point → Bool) (hg : Increasing g)
    (hle : ∀ x, g x = true → graph x = true)
    (hedge : ∀ e ∈ edges, g (edgePoint e) = true) : g = graph := by
  funext x
  by_cases h : graph x = true
  · obtain ⟨e, he, hex⟩ := graph_true_witness x h
    rw [hg _ _ hex (hedge e he), h]
  · have hzero : graph x = false := by
      cases hx : graph x
      · rfl
      · exact False.elim (h hx)
    have gzero : g x = false := by
      cases hx : g x
      · rfl
      · exact False.elim (h (hle x hx))
    rw [hzero, gzero]

lemma upper_of_independent (g : Point → Bool) (hg : Increasing g)
    (hge : ∀ x, graph x = true → g x = true)
    (hmax : ∀ a ∈ maximalIndependent, g (maskPoint a) = false) : g = graph := by
  funext x
  by_cases h : graph x = true
  · rw [hge x h, h]
  · have hzero : graph x = false := by
      cases hx : graph x
      · rfl
      · exact False.elim (h hx)
    obtain ⟨a, ha, hxa⟩ := independent_boundaries.2 x hzero
    have gzero : g x = false := by
      cases hx : g x
      · rfl
      · have := hg _ _ hxa hx
        rw [hmax a ha] at this
        cases this
    rw [hzero, gzero]

lemma essential_cut_witnesses (h lo hi : Point → Bool)
    (hlo : Increasing lo) (hhi : Increasing hi)
    (low : ∀ x, lo x = true → graph x = true)
    (high : ∀ x, graph x = true → hi x = true)
    (cut : ∀ x, graph x = if h x then lo x else hi x)
    (hlo_ne : lo ≠ graph) (hhi_ne : hi ≠ graph) :
    (∃ e ∈ edges, h (edgePoint e) = false) ∧
    (∃ a ∈ maximalIndependent, h (maskPoint a) = true) := by
  constructor
  · by_contra hn
    apply hlo_ne
    apply lower_of_edges lo hlo low
    intro e he
    have hh : h (edgePoint e) = true := by
      cases hh : h (edgePoint e)
      · exact False.elim (hn ⟨e, he, hh⟩)
      · rfl
    have hc := cut (edgePoint e)
    simpa [hh, edgePoint_true e he] using hc.symm
  · by_contra hn
    apply hhi_ne
    apply upper_of_independent hi hhi high
    intro a ha
    have hh : h (maskPoint a) = false := by
      cases hh : h (maskPoint a)
      · rfl
      · exact False.elim (hn ⟨a, ha, hh⟩)
    have hc := cut (maskPoint a)
    simpa [hh, independent_boundaries.1 a ha] using hc.symm

end PEqualNP.Outside.L_meta_2592_aux.FewNots
