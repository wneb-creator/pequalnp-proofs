import PEqualNP.Library.LRAT.Cube
import PEqualNP.Library.LRAT.PromiseGen

/-!
# The representing lower bound from unsatisfiable cubes

`lower_of_cubes` for circuits that represent a bipartite graph. The encoding and the cubes are the
root's (`PEqualNP.Defs.LratEncoding`); `g` and the rows may be given as `gMask n m M` and
`repRows n m` or by any terms that unfold to them.
-/

namespace PEqualNP.Library.LRAT.Promise

open PEqualNP.Represents PEqualNP.Defs.LratEncoding

theorem rep_lower_of_cubes {n m : ℕ} (A : Fin n → Fin m → Bool) (s : ℕ) (hs : 0 < s) (g : ℕ → Bool)
    (hg : ∀ (u : Fin n) (v : Fin m), g (repRow n u v) = A u v)
    (hU : ∀ k < enc2CubeCount (n + m) s,
      ¬ FormulaSat (enc2 (n + m) s g (repRows n m) ++ enc2Cube (n + m) s k)) :
    ¬ RepSizeAtMost A s := by
  refine rep_lower A s g hg fun h => ?_
  obtain ⟨k, hk, hk'⟩ := Cube.enc2_cover (n + m) s hs g (repRows n m) h
  exact hU k hk hk'

theorem rep_lower_mask_of_cubes (n m M s : ℕ) (hs : 0 < s)
    (hU : ∀ k < enc2CubeCount (n + m) s,
      ¬ FormulaSat (enc2 (n + m) s (gMask n m M) (repRows n m) ++ enc2Cube (n + m) s k)) :
    ¬ RepSizeAtMost (fun (u : Fin n) (v : Fin m) => M.testBit (m * u + v)) s :=
  rep_lower_of_cubes (n := n) (m := m) (fun u v => M.testBit (m * u + v)) s hs (gMask n m M)
    (fun u v => gMask_row (n := n) (m := m) M u v) hU

end PEqualNP.Library.LRAT.Promise
