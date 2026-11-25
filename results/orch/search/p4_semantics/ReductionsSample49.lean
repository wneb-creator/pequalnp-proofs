import ReductionsIR

namespace PEqualNP.Outside.Pilot64Bridge

open PEqualNP.Library.LRAT
open PEqualNP.Outside.Pilot64KernelControl

set_option maxRecDepth 100000
set_option maxHeartbeats 0

example (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) : True := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc0 : ClauseSat (assignment c) [2] := by
    simp [ClauseSat, litVal, assignment_1]
  have hc1 : ClauseSat (assignment c) [6,8,10,12] := by
    have hb := c.a0.isLt
    simp [ClauseSat, litVal, assignment_3, assignment_4, assignment_5, assignment_6, v3, v4, v5, v6]
    omega
  have hc2 : ClauseSat (assignment c) [7,9] := by
    simp [ClauseSat, litVal, assignment_3, assignment_4, v3, v4]
    all_goals omega
  have hc3 : ClauseSat (assignment c) [23,7] := by
    cases ha0 : v3 c <;> cases ha1 : v4 c <;> simp [ClauseSat, litVal, assignment_3, assignment_11, v11, ha0, ha1]
  have hc5 : ClauseSat (assignment c) [22,6,8] := by
    cases ha0 : v3 c <;> cases ha1 : v4 c <;> simp [ClauseSat, litVal, assignment_3, assignment_4, assignment_11, v11, ha0, ha1]
  have hc6 : ClauseSat (assignment c) [22,11] := by
    simp [ClauseSat, litVal, assignment_5, assignment_11, v3, v4, v5, v11]
    all_goals omega
  have hc7 : ClauseSat (assignment c) [25,22] := by
    cases ha0 : v5 c <;> cases ha1 : v11 c <;> simp [ClauseSat, litVal, assignment_11, assignment_12, v12, ha0, ha1]
  have hc9 : ClauseSat (assignment c) [24,23,10] := by
    cases ha0 : v5 c <;> cases ha1 : v11 c <;> simp [ClauseSat, litVal, assignment_5, assignment_11, assignment_12, v12, ha0, ha1]
  have hc27 : ClauseSat (assignment c) [7,15] := by
    simp [ClauseSat, litVal, assignment_3, assignment_7, v3, v7]
    all_goals omega
  have hc28 : ClauseSat (assignment c) [9,28] := by
    simp [ClauseSat, litVal, assignment_4, assignment_14, v4, v7, v8, v14]
    all_goals omega
  have hc31 : ClauseSat (assignment c) [36,38,40,42,44] := by
    have hb := c.a1.isLt
    simp [ClauseSat, litVal, assignment_18, assignment_19, assignment_20, assignment_21, assignment_22, v18, v19, v20, v21, v22]
    omega
  have hc70 : ClauseSat (assignment c) [74,76,78,80,82,84] := by
    have hb := c.a2.isLt
    simp [ClauseSat, litVal, assignment_37, assignment_38, assignment_39, assignment_40, assignment_41, assignment_42, v37, v38, v39, v40, v41, v42]
    omega
  have hc118 : ClauseSat (assignment c) [120,122,124,126,128,130,132] := by
    have hb := c.a3.isLt
    simp [ClauseSat, litVal, assignment_60, assignment_61, assignment_62, assignment_63, assignment_64, assignment_65, assignment_66, v60, v61, v62, v63, v64, v65, v66]
    omega
  have hc175 : ClauseSat (assignment c) [174,176,178,180,182,184,186,188] := by
    have hb := c.a4.isLt
    simp [ClauseSat, litVal, assignment_87, assignment_88, assignment_89, assignment_90, assignment_91, assignment_92, assignment_93, assignment_94, v87, v88, v89, v90, v91, v92, v93, v94]
    omega
  have hc241 : ClauseSat (assignment c) [5,235] := by
    cases ha0 : v2 c <;> simp [ClauseSat, litVal, assignment_2, assignment_117, v117, ha0]
  have hc243 : ClauseSat (assignment c) [4,235] := by
    cases ha0 : v2 c <;> simp [ClauseSat, litVal, assignment_2, assignment_117, v117, ha0]
  have hc244 : ClauseSat (assignment c) [37,237] := by
    by_cases hs : c.a1.val = 0
    · simp [ClauseSat, litVal, assignment_18, assignment_118, v118, v18, hs]
    · simp [ClauseSat, litVal, assignment_18, assignment_118, v18, hs]
  have hc248 : ClauseSat (assignment c) [45,237,234] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_117, assignment_118, v118, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_117, assignment_118, v22, hs]
  have hc249 : ClauseSat (assignment c) [45,236,235] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_117, assignment_118, v118, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_117, assignment_118, v22, hs]
  have hc256 : ClauseSat (assignment c) [35,241,236] := by
    cases ha0 : v17 c <;> cases ha1 : v118 c <;> cases ha2 : v119 c <;> simp [ClauseSat, litVal, assignment_17, assignment_118, assignment_120, v120, ha0, ha1, ha2]
  have hc258 : ClauseSat (assignment c) [35,240,237,239] := by
    cases ha0 : v17 c <;> cases ha1 : v118 c <;> cases ha2 : v119 c <;> simp [ClauseSat, litVal, assignment_17, assignment_118, assignment_119, assignment_120, v120, ha0, ha1, ha2]
  have hc259 : ClauseSat (assignment c) [34,240,237] := by
    cases ha0 : v17 c <;> cases ha1 : v118 c <;> cases ha2 : v119 c <;> simp [ClauseSat, litVal, assignment_17, assignment_118, assignment_120, v120, ha0, ha1, ha2]
  have hc261 : ClauseSat (assignment c) [34,241,236,238] := by
    cases ha0 : v17 c <;> cases ha1 : v118 c <;> cases ha2 : v119 c <;> simp [ClauseSat, litVal, assignment_17, assignment_118, assignment_119, assignment_120, v120, ha0, ha1, ha2]
  have hc340 : ClauseSat (assignment c) [259] := by
    have hh := hr ⟨0, by decide⟩
    have ht : target ⟨0, by decide⟩ = false := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_129, output] using hh
  have hc341 : ClauseSat (assignment c) [7,260] := by
    by_cases hs : c.a0.val = 0
    · simp [ClauseSat, litVal, assignment_3, assignment_130, v130, v3, hs]
    · simp [ClauseSat, litVal, assignment_3, assignment_130, v3, hs]
  have hc451 : ClauseSat (assignment c) [289] := by
    have hh := hr ⟨1, by decide⟩
    have ht : target ⟨1, by decide⟩ = false := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_144, output] using hh
  have hc562 : ClauseSat (assignment c) [319] := by
    have hh := hr ⟨2, by decide⟩
    have ht : target ⟨2, by decide⟩ = false := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_159, output] using hh
  have hc673 : ClauseSat (assignment c) [348] := by
    have hh := hr ⟨3, by decide⟩
    have ht : target ⟨3, by decide⟩ = true := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_174, output] using hh
  have hc784 : ClauseSat (assignment c) [379] := by
    have hh := hr ⟨4, by decide⟩
    have ht : target ⟨4, by decide⟩ = false := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_189, output] using hh
  have hc895 : ClauseSat (assignment c) [408] := by
    have hh := hr ⟨5, by decide⟩
    have ht : target ⟨5, by decide⟩ = true := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_204, output] using hh
  have hc1006 : ClauseSat (assignment c) [439] := by
    have hh := hr ⟨6, by decide⟩
    have ht : target ⟨6, by decide⟩ = false := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_219, output] using hh
  have hc1117 : ClauseSat (assignment c) [468] := by
    have hh := hr ⟨7, by decide⟩
    have ht : target ⟨7, by decide⟩ = true := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_234, output] using hh
  have hc1228 : ClauseSat (assignment c) [499] := by
    have hh := hr ⟨8, by decide⟩
    have ht : target ⟨8, by decide⟩ = false := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_249, output] using hh
  have hc1339 : ClauseSat (assignment c) [529] := by
    have hh := hr ⟨9, by decide⟩
    have ht : target ⟨9, by decide⟩ = false := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_264, output] using hh
  have hc1450 : ClauseSat (assignment c) [558] := by
    have hh := hr ⟨10, by decide⟩
    have ht : target ⟨10, by decide⟩ = true := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_279, output] using hh
  have hc1561 : ClauseSat (assignment c) [588] := by
    have hh := hr ⟨11, by decide⟩
    have ht : target ⟨11, by decide⟩ = true := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_294, output] using hh
  have hc1672 : ClauseSat (assignment c) [619] := by
    have hh := hr ⟨12, by decide⟩
    have ht : target ⟨12, by decide⟩ = false := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_309, output] using hh
  have hc1783 : ClauseSat (assignment c) [648] := by
    have hh := hr ⟨13, by decide⟩
    have ht : target ⟨13, by decide⟩ = true := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_324, output] using hh
  have hc1894 : ClauseSat (assignment c) [678] := by
    have hh := hr ⟨14, by decide⟩
    have ht : target ⟨14, by decide⟩ = true := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_339, output] using hh
  have hc1895 : ClauseSat (assignment c) [5,680] := by
    cases ha0 : v2 c <;> simp [ClauseSat, litVal, assignment_2, assignment_340, v340, ha0]
  have hc1896 : ClauseSat (assignment c) [4,680] := by
    cases ha0 : v2 c <;> simp [ClauseSat, litVal, assignment_2, assignment_340, v340, ha0]
  have hc1994 : ClauseSat (assignment c) [704] := by
    have hh := hr ⟨15, by decide⟩
    have ht : target ⟨15, by decide⟩ = true := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_352, output] using hh
  have hc2115 : ClauseSat (assignment c) [740,707,739] := by
    cases ha0 : v353 c <;> cases ha1 : v369 c <;> simp [ClauseSat, litVal, assignment_353, assignment_369, assignment_370, v370, ha0, ha1]
  have hc2125 : ClauseSat (assignment c) [5,749,745] := by
    cases ha0 : v2 c <;> cases ha1 : v372 c <;> cases ha2 : v373 c <;> simp [ClauseSat, litVal, assignment_2, assignment_372, assignment_374, v374, ha0, ha1, ha2]
  have hc2126 : ClauseSat (assignment c) [5,748,744] := by
    cases ha0 : v2 c <;> cases ha1 : v372 c <;> cases ha2 : v373 c <;> simp [ClauseSat, litVal, assignment_2, assignment_372, assignment_374, v374, ha0, ha1, ha2]
  have hc2127 : ClauseSat (assignment c) [4,749,747] := by
    cases ha0 : v2 c <;> cases ha1 : v372 c <;> cases ha2 : v373 c <;> simp [ClauseSat, litVal, assignment_2, assignment_373, assignment_374, v374, ha0, ha1, ha2]
  have hc2128 : ClauseSat (assignment c) [4,748,746] := by
    cases ha0 : v2 c <;> cases ha1 : v372 c <;> cases ha2 : v373 c <;> simp [ClauseSat, litVal, assignment_2, assignment_373, assignment_374, v374, ha0, ha1, ha2]
  have hc2265 : ClauseSat (assignment c) [805] := by
    simpa [ClauseSat, litVal, assignment_402, derivativeLeft] using hl
  have hc2536 : ClauseSat (assignment c) [905] := by
    simpa [ClauseSat, litVal, assignment_452, derivativeRight] using hd
  trivial

end PEqualNP.Outside.Pilot64Bridge
