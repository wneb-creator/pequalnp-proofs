import PEqualNP.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Polynomial.Resultant.Basic

namespace PEqualNP.Outside.L_gct_231_aux

noncomputable def polynomialOfCoeffs {R : Type*} [Semiring R] : List R → Polynomial R
  | [] => 0
  | a :: cs => Polynomial.C a + Polynomial.X * polynomialOfCoeffs cs

theorem polynomialOfCoeffs_coeff {R : Type*} [Semiring R] (cs : List R) (n : ℕ) :
    (polynomialOfCoeffs cs).coeff n = (cs[n]?).getD 0 := by
  induction cs generalizing n with
  | nil => simp [polynomialOfCoeffs]
  | cons a cs ih =>
    cases n <;> simp [polynomialOfCoeffs, Polynomial.coeff_X_mul, ih]

theorem polynomialOfCoeffs_map {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (cs : List R) :
    (polynomialOfCoeffs cs).map f = polynomialOfCoeffs (cs.map f) := by
  induction cs with
  | nil => simp [polynomialOfCoeffs]
  | cons a cs ih =>
    simp [polynomialOfCoeffs, Polynomial.map_add, Polynomial.map_mul, ih]

theorem polynomialOfCoeffs_eval {R : Type*} [CommSemiring R]
    (cs : List R) (z : R) :
    (polynomialOfCoeffs cs).eval z = cs.foldr (fun a v => a + z*v) 0 := by
  induction cs with
  | nil => simp [polynomialOfCoeffs]
  | cons a cs ih => simp [polynomialOfCoeffs, ih]

theorem polynomialOfCoeffs_degree_le {R : Type*} [Semiring R] (cs : List R) :
    (polynomialOfCoeffs cs).natDegree ≤ cs.length - 1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [polynomialOfCoeffs_coeff]
  have hlen : cs.length ≤ n := by omega
  have hz : cs[n]? = none := by simp only [List.getElem?_eq_none_iff]; exact hlen
  simp [hz]

theorem polynomialOfCoeffs_degree_eq {R : Type*} [Semiring R]
    (cs : List R) (n : ℕ) (hlen : cs.length = n + 1)
    (hlast : (cs[n]?).getD 0 ≠ 0) :
    (polynomialOfCoeffs cs).natDegree = n := by
  apply le_antisymm
  · simpa [hlen] using polynomialOfCoeffs_degree_le cs
  · apply Polynomial.le_natDegree_of_ne_zero
    simpa [polynomialOfCoeffs_coeff] using hlast

end PEqualNP.Outside.L_gct_231_aux

namespace PEqualNP.Outside.L_gct_231.trace
open PEqualNP.Outside.L_gct_231_aux

noncomputable def case2CofactorLeft : Polynomial (ℤ) := polynomialOfCoeffs ([567002529792, -10073660719104, 42678213279744, 152371420397568, -1359067682848768, 1123343828107264, 9770903451582464, -21913158068674560, -18855473919455232, 112673564432310272, -61856563016427520, -285875542802354176, 444301158301289472, 348786211407216640, -1287481020019996672, 83791561946866688, 2443920984047352320, -1161884919701942272, -3522355534198141696, 2334680495548560384, 4183406015983618560, -2568987699042079744, -4170211890288527360, 1330009013057276416, 3208563686326317824, 653937308649333760, -1354506268248111104, -1914220257439588352, -590012849004447232, 1690981156076082944, 1566376977751266432, -612696540074092288, -1307387264818277888, -197706283083905280, 520737817244340896, 320894417690460416, 6997929669710688, -111174570452081024, -110163567206321408, -29924724787167232, 42787758703178944, 38258701528660768, 984757934198440, -12038470878765808, -4804495544975020, 947427943352592, 1137298974630624, 191671121042988, -76970263268474, -34213828436096, -1863974810151, 1292042680092, 235722237716, -1805903584, -2377543112] : List (ℤ))

noncomputable def case2CofactorRight : Polynomial (ℤ) := polynomialOfCoeffs ([-1017099740774400, 233523495053557760, -966635141580455936, -12599864265165242368, 47592234513776771072, 274269676855272407040, -937030822754508079104, -3246863937442460729344, 10601983831242954768384, 25297871917359865135104, -82133235006067753156608, -144886885351880963325952, 482648840405741265616896, 651809974039751452262400, -2291234664597034950262784, -2395575522675195731312640, 9115498662659383867015168, 7355090693682244017029120, -30979057935428540547874816, -19138309526315999749521408, 90755798705449040380919808, 42899295948184476459040768, -230243599088282612857778176, -85349513122274078961176576, 507264045184196954783535104, 158817057042533808122404864, -971921763696326130470858752, -293909322472348331112433664, 1617562700236806202341249024, 553187899823926021810356224, -2324156334489339003718115328, -1015431844232774516252623872, 2840406266772651398214937600, 1700592996677566661617142784, -2859921269656963992090545152, -2466877867262094237686756864, 2200004385300186351853128704, 2994421001074653676904466432, -985781654723175969084826368, -2949663311470483345254498304, -333946994407266636029055488, 2248603214458528017654275840, 1225614004914792229819510528, -1175945937757528228098195456, -1414208247643293266238062592, 207140814457419439045675264, 1038719403698342387877588992, 323823111236900794144718720, -486437910053271548527713408, -406987867969752131165071616, 82990565693533461437560128, 258279722234569603082600960, 79027187115109322128021504, -95462530634822826672088064, -83406911582790849146056592, 9713956255720571094483760, 42505651196341869637878480, 11887034372278917858974336, -13178352061056996898230480, -8732657282769218299910760, 2034969512726718054821264, 3376871404702912857475968, 249812743103490025386880, -865202433542520218120292, -255009101611082947386932, 145551312425713511931596, 82313892871204825318316, -12493362464286090753486, -16565755672036172099396, -833104763185341220048, 2226126464002506944967, 452116178126219056654, -185442598096408364716, -71193659975367893783, 6739957927110273194, 6192764800791088082, 283179930622381764, -302507267146280273, -42760118528981785, 6337101562596176, 1546727280035924, -5083517617920, -13131007671600] : List (ℤ))

noncomputable def case2ModLeft : Polynomial (ZMod 11) := polynomialOfCoeffs ([6, 7, 9, 9, 9, 5, 4, 5, 7, 6, 0, 10, 7, 2, 9, 2, 5, 10, 0, 5, 4, 0, 9, 7, 10, 7, 6, 10, 10, 7, 4, 10, 8, 8, 2, 0, 5, 2, 1, 0, 4, 1, 6, 7, 7, 9, 3, 4, 7, 10, 8, 10, 9, 10, 1] : List (ZMod 11))

noncomputable def case2ModRight : Polynomial (ZMod 11) := polynomialOfCoeffs ([3, 7, 5, 5, 1, 6, 10, 6, 8, 1, 8, 6, 8, 8, 4, 0, 3, 2, 9, 10, 7, 1, 6, 10, 6, 4, 5, 10, 6, 1, 9, 3, 1, 6, 2, 4, 3, 3, 10, 7, 0, 7, 1, 9, 1, 5, 6, 1, 7, 1, 9, 6, 5, 3, 9, 0, 0, 6, 7, 1, 7, 2, 7, 2, 8, 4, 4, 1, 3, 9, 0, 6, 7, 5, 10, 2, 4, 0, 3, 9, 8, 6, 6] : List (ZMod 11))

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem case2_cofactor_degree_bounds :
    case2CofactorLeft.natDegree ≤ 54 ∧ case2CofactorRight.natDegree ≤ 82 := by
  constructor
  · unfold case2CofactorLeft
    exact polynomialOfCoeffs_degree_le _
  · unfold case2CofactorRight
    exact polynomialOfCoeffs_degree_le _

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem case2_left_map :
    case2CofactorLeft.map (Int.castRingHom (ZMod 11)) = case2ModLeft := by
  unfold case2CofactorLeft case2ModLeft
  rw [polynomialOfCoeffs_map]
  congr 1
  decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem case2_right_map :
    case2CofactorRight.map (Int.castRingHom (ZMod 11)) = case2ModRight := by
  unfold case2CofactorRight case2ModRight
  rw [polynomialOfCoeffs_map]
  congr 1
  decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem case2_modular_degrees :
    (case2CofactorLeft.map (Int.castRingHom (ZMod 11))).natDegree = 54 ∧
    (case2CofactorRight.map (Int.castRingHom (ZMod 11))).natDegree = 82 := by
  rw [case2_left_map, case2_right_map]
  constructor
  · unfold case2ModLeft
    apply polynomialOfCoeffs_degree_eq _ 54 (by rfl)
    decide
  · unfold case2ModRight
    apply polynomialOfCoeffs_degree_eq _ 82 (by rfl)
    decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
theorem case2_modular_coprime :
    IsCoprime (case2CofactorLeft.map (Int.castRingHom (ZMod 11)))
      (case2CofactorRight.map (Int.castRingHom (ZMod 11))) := by
  rw [case2_left_map, case2_right_map]
  refine ⟨polynomialOfCoeffs ([7, 1, 0, 2, 4, 1, 6, 0, 0, 9, 0, 2, 4, 4, 9, 1, 7, 8, 2, 4, 3, 4, 1, 7, 6, 3, 5, 1, 8, 7, 8, 6, 1, 0, 7, 8, 9, 9, 6, 9, 9, 5, 9, 4, 3, 6, 5, 9, 10, 9, 5, 10, 2, 3, 0, 6, 5, 8, 5, 1, 4, 10, 4, 1, 9, 4, 8, 4, 4, 9, 1, 0, 10, 5, 2, 8, 5, 10, 1, 10, 6, 10] : List (ZMod 11)), polynomialOfCoeffs ([1, 5, 0, 6, 3, 6, 6, 5, 2, 10, 9, 9, 5, 1, 1, 5, 0, 7, 1, 4, 6, 9, 3, 0, 0, 8, 10, 9, 0, 7, 1, 2, 6, 2, 7, 2, 8, 5, 1, 10, 8, 4, 10, 1, 5, 5, 5, 1, 7, 2, 2, 5, 6, 2] : List (ZMod 11)), ?_⟩
  have hp : (11 : Polynomial (ZMod 11)) = 0 := by
    have h : (11 : ZMod 11) = 0 := by norm_num
    simpa using congrArg (fun x : ZMod 11 => Polynomial.C x) h
  have hh : polynomialOfCoeffs ([4, 7, 10, 12, 17, 16, 25, 28, 31, 38, 37, 54, 56, 56, 61, 65, 70, 89, 78, 74, 90, 87, 92, 109, 90, 107, 109, 118, 145, 131, 132, 154, 147, 162, 149, 146, 157, 179, 173, 192, 200, 183, 206, 198, 210, 229, 210, 225, 242, 237, 241, 246, 256, 261, 253, 240, 250, 251, 257, 276, 258, 255, 273, 265, 273, 271, 259, 273, 263, 271, 265, 254, 273, 261, 250, 281, 236, 265, 263, 275, 277, 269, 249, 277, 257, 245, 243, 233, 240, 254, 237, 243, 219, 217, 206, 182, 193, 181, 187, 185, 193, 179, 160, 158, 150, 153, 155, 128, 154, 131, 125, 116, 110, 114, 104, 94, 90, 96, 84, 82, 82, 84, 77, 67, 74, 67, 61, 50, 51, 43, 45, 34, 33, 22, 14, 2] : List (ZMod 11)) * (11 : Polynomial (ZMod 11)) = 0 := by rw [hp, mul_zero]
  unfold case2ModLeft case2ModRight
  simp only [polynomialOfCoeffs, map_ofNat, map_neg] at hh ⊢
  linear_combination hh

end PEqualNP.Outside.L_gct_231.trace
