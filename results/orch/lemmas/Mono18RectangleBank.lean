import Mono18RectangleSamples
import RectangleRunIndexed

namespace PEqualNP.Outside.L_meta_2373.Mono18Rectangle

open Live1024 RectangleRun

def targetCost (m : Nat) : Int :=
  rect (fun r : Fin (rowCount (matrixWeight m)) =>
    fun c : Fin (colCount (matrixWeight m)) => weight (matrixWeight m) r.val c.val)
    Finset.univ Finset.univ

lemma run_exclusion_of_records (m : Nat) (labels : List (Sig × Nat)) {k : Nat}
    (valid : ∀ a ∈ labels, checkRecord (matrixWeight m) a.2 = true)
    (covered : ∀ a ∈ labels, supportCheck m a.2 a.1 = true)
    (positive : ∀ r : Fin (rowCount (matrixWeight m)),
      bit (positiveSample m r.val) graph = true)
    (negative : ∀ c : Fin (colCount (matrixWeight m)),
      bit (negativeSample m c.val) graph = false)
    (gap : (labels.map (fun a => recordCap (matrixWeight m) a.2)).sum < targetCost m)
    (cap : k + 1 ≤ labels.length)
    (trace : Run false (observe graph) k (labels.map (fun a => observe a.1))) : False := by
  have lower := run_length_le trace
  simp only [List.length_map] at lower
  have tight : labels.length = k + 1 := Nat.le_antisymm lower cap
  have bound := tight_run_indexed
    (fun r : Fin (rowCount (matrixWeight m)) => positiveSample m r.val)
    (fun c : Fin (colCount (matrixWeight m)) => negativeSample m c.val)
    (fun r c => weight (matrixWeight m) r.val c.val)
    (fun a : Sig × Nat => observe a.1)
    (fun a => recordCap (matrixWeight m) a.2) labels trace tight
    (fun a ha => bounds_of_support m a.2 a.1 (valid a ha) (covered a ha))
  have full := bound Finset.univ Finset.univ (fun r _ => positive r) (fun c _ => negative c)
  exact (not_le_of_gt gap) full

end PEqualNP.Outside.L_meta_2373.Mono18Rectangle
