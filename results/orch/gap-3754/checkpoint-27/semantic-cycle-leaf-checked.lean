import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3754.CycleChecks
open PEqualNP.TopForm

lemma no_four_walk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (v : Fin n) (c : G.Walk v v) (hc : c.IsCycle) :
    c.length ≠ 4 := by
  intro hlen
  have h02 : c.getVert 0 ≠ c.getVert 2 := by
    intro h
    have he := hc.getVert_injOn' (by simp [hlen]) (by simp [hlen]) h
    omega
  have h13 : c.getVert 1 ≠ c.getVert 3 := by
    intro h
    have he := hc.getVert_injOn' (by simp [hlen]) (by simp [hlen]) h
    omega
  have h01 : G.Adj (c.getVert 0) (c.getVert 1) := c.adj_getVert_succ (by omega)
  have h21 : G.Adj (c.getVert 2) (c.getVert 1) := (c.adj_getVert_succ (i:=1) (by omega)).symm
  have h23 : G.Adj (c.getVert 2) (c.getVert 3) := c.adj_getVert_succ (by omega)
  have h03 : G.Adj (c.getVert 0) (c.getVert 3) := by
    have hh := (c.adj_getVert_succ (i:=3) (by omega)).symm
    simpa [←hlen] using hh
  have hbound := hG (c.getVert 0) (c.getVert 2) h02
  have hbig : 1 < (Finset.univ.filter fun w =>
      G.Adj (c.getVert 0) w ∧ G.Adj (c.getVert 2) w).card :=
    Finset.one_lt_card.mpr ⟨c.getVert 1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h01,h21⟩,
      c.getVert 3,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h03,h23⟩,h13⟩
  omega

end PEqualNP.Outside.L_meta_3754.CycleChecks

namespace PEqualNP.Outside.L_meta_3754.CycleExamples
open PEqualNP.EdgeOwnership PEqualNP.TopForm

def cycleEdges (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).map fun i => (i,(i+1)%n)

def cycle (n : ℕ) : SimpleGraph (Fin n) := edgeGraph n (cycleEdges n)

instance (n : ℕ) : DecidableRel (cycle n).Adj := by
  unfold cycle
  infer_instance

set_option maxRecDepth 100000 in
lemma cycle8_no_four : NoFourCycle (cycle 8) := by decide +kernel

set_option maxRecDepth 100000 in
lemma cycle10_no_four : NoFourCycle (cycle 10) := by decide +kernel

lemma cycle8_no_four_walk (v : Fin 8) (c : (cycle 8).Walk v v) (hc : c.IsCycle) :
    c.length≠4 := CycleChecks.no_four_walk (cycle 8) cycle8_no_four v c hc

lemma cycle10_no_four_walk (v : Fin 10) (c : (cycle 10).Walk v v) (hc : c.IsCycle) :
    c.length≠4 := CycleChecks.no_four_walk (cycle 10) cycle10_no_four v c hc

end PEqualNP.Outside.L_meta_3754.CycleExamples
namespace PEqualNP.Outside.L_meta_3754.CycleExamples
open PEqualNP.EdgeOwnership PEqualNP.TopForm

def cycleLeaf7 : SimpleGraph (Fin 7) :=
  edgeGraph 7 [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),(0,6)]

instance : DecidableRel cycleLeaf7.Adj := by
  unfold cycleLeaf7
  infer_instance

set_option maxRecDepth 100000 in
lemma cycleLeaf7_no_four : NoFourCycle cycleLeaf7 := by decide +kernel

lemma cycleLeaf7_no_four_walk (v : Fin 7) (c : cycleLeaf7.Walk v v) (hc : c.IsCycle) :
    c.length≠4 := CycleChecks.no_four_walk cycleLeaf7 cycleLeaf7_no_four v c hc

lemma cycleLeaf7_edges : cycleLeaf7.edgeFinset.card=7 := by decide +kernel

end PEqualNP.Outside.L_meta_3754.CycleExamples
