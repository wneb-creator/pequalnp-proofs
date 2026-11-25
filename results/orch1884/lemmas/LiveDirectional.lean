import Binary17

namespace PEqualNP.Outside.L_meta_1884.LiveDirectional

open PEqualNP.Outside.L_meta_2592.Binary17.Extended

lemma binary_increase {d : Nat} (hd : allowed false d) (a b : Sig) (r s : Row)
    (hr : bit r (bin d a b) = false) (hs : bit s (bin d a b) = true) :
    (bit r a = false ∧ bit s a = true) ∨ (bit r b = false ∧ bit s b = true) := by
  have hlt : d < 2 := by simpa [allowed] using hd
  have hd' : d = 0 ∨ d = 1 := by omega
  rcases hd' with rfl | rfl
  all_goals
    cases hra : bit r a <;> cases hrb : bit r b <;>
      cases hsa : bit s a <;> cases hsb : bit s b <;>
      simp_all [bin, bit]

theorem live_row_increase {T k S} (h : Live false T k S) {r s : Row}
    (hr : bit r T = false) (hs : bit s T = true) :
    ∃ a ∈ S, bit r a = false ∧ bit s a = true := by
  induction h using Live.ind with
  | stop hp => exact ⟨_, by simp, hr, hs⟩
  | @binary k U a b d hd ha hb hab hf tail ih =>
    obtain ⟨v, hv, hvr, hvs⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rcases binary_increase hd a b r s hvr hvs with ha | hb
      · exact ⟨a, by simp, ha⟩
      · exact ⟨b, by simp, hb⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu), hvr, hvs⟩

theorem increasing_root_required {T k S} (h : Live false T k S)
    (roots : List Sig) (a : Sig) (sub : ∀ v ∈ S, v ∈ roots) (r s : Row)
    (hr : bit r T = false) (hs : bit s T = true)
    (isolated : ∀ v ∈ roots, bit r v = false → bit s v = true → v = a) : a ∈ S := by
  obtain ⟨v, hv, hvr, hvs⟩ := live_row_increase h hr hs
  exact isolated v (sub v hv) hvr hvs ▸ hv

end PEqualNP.Outside.L_meta_1884.LiveDirectional
