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

noncomputable def case3CofactorLeft : Polynomial (ℤ) := polynomialOfCoeffs ([47550862240, -183525744624, -5013793690488, 42346742286632, -3022833765064, -1183595873081286, 4176214468163509, 6695479284701032, -72372499980606228, 100708969004970541, 421736716976252656, -1543673334931282226, 48631055147094256, 7987711169335291172, -11348938299449267740, -15992824083696154900, 55073962508736130464, -13560915570302665860, -116548545030258664048, 140045477462823550920, 51964586211031439808, -267825904425947230624, 354618608664092650784, -84493140312368351568, -992345049463315880384, 1590038778616802815552, 1029427844167094858112, -4222999431010708681088, 645211116929886695296, 6433532745825515351296, -4033810442675025531776, -5692011366574525568128, 7136210250271641158144, 455217967532437338752, -7137592488182896733184, 8239067052894874399488, 3047250537832124000256, -17222473578834368480256, 2932277067948596329728, 23210399144366337554944, -7036121560333493703680, -24501535812687417265920, 7079834590206681958400, 21360201860950247888384, -3995633785944362680320, -15491112637246482473984, 490201782476646179840, 9173908249718343363584, 1433403723166500323328, -4257991191086175314944, -1612866069069696782336, 1429584755751132628992, 993373449384270381056, -275185717802355277824, -409027834869129494528, -14623355630208864256, 114790827876308762624, 29723964375007551488, -20624268009657270272, -10065282921384427520, 1842120282414874624, 1758722121379676160, 45770099512246272, -149275821986086912, -22133886853840896, 3565497563480064, 984685970718720, 56700252979200] : List (ℤ))

noncomputable def case3CofactorRight : Polynomial (ℤ) := polynomialOfCoeffs ([-47706827568120, 693055324263792, 641949452118980, -79304389977959180, 668980249688114299, -1754820234175086830, -7958636176014289089, 78269048327610356752, -226504686267265253994, -96508910938571756094, 2592584788215396335168, -6802124891710115363756, 554668061719776272384, 30292421094163696828472, -38156482811513472826184, -44911537882945444651112, -170763787991622345136752, 1472765430732214012604800, -1264654334844478333653312, -10326334311728717933521152, 31119046286063608016204560, -1351676074664430524750912, -150914603649916557311591200, 249826528817656825833795296, 209620658538992422690219456, -1151893669510597820242666688, 810333309530682074526832064, 2321745655812258890886512896, -4707644151429700346681833088, -569744114878619219087333376, 10939841949074945918764427072, -9535699250958392163404014720, -11592220237101321355687742848, 28031664237244269254419931520, -7267732836379024718124611584, -39292159365803097610343324928, 51203402526563197088191275264, 14608506680868075422166467584, -100657268767857344444960365312, 64823294297913122010465708544, 115020525871624196630913573376, -183267808757106003297372152320, -63147641380165122517672219648, 293167033119091372795568538624, -46621336518856941790698962944, -347641441945765941462179813376, 168174836774204737244842389504, 332417484349368279553746716672, -249834541180997558103105617920, -269033212687490346942494289920, 266593673978055072460928401408, 192531257826148349982998945792, -227711082530573913381214031872, -127968387819754561585416519680, 161608973052197057548087525376, 82749578964600276038823157760, -95976163071694246518636150784, -52927551100134547336257470464, 46687609021282358019195158528, 32452385166011972953781338112, -17236844880024416062775525376, -17889488859907128468659175424, 3560011285926007512386125824, 8209733058804684727046406144, 745025391398835593211314176, -2838570259994018388993015808, -1056908778220378890765860864, 597802067894390165475622912, 474647637305484819769327616, -4333806433017652822540288, -100921085048457104862609408, -38066326890240511041470464, -2302230687875996123922432, 7783666141509681414930432, 6595979221598436601364480, 953850625272514438234112, -1285767545544987577942016, -512654833164421755305984, 67240006407993606275072, 52364226249540837048320, -4734025589644574326784, -4892117926583373660160, -233612262330364592128, 198644580405930360832, 35661331342395703296, 1695226359636295680] : List (ℤ))

noncomputable def case3ModLeft : Polynomial (ZMod 11) := polynomialOfCoeffs ([2, 9, 0, 3, 8, 6, 2, 1, 4, 6, 0, 10, 1, 9, 8, 4, 10, 2, 0, 5, 5, 3, 5, 7, 3, 9, 0, 3, 9, 0, 7, 8, 8, 6, 7, 10, 0, 6, 8, 7, 0, 5, 9, 0, 7, 1, 10, 0, 2, 4, 5, 3, 3, 6, 7, 8, 6, 4, 5, 8, 8, 4, 9, 5, 9, 3, 6, 6] : List (ZMod 11))

noncomputable def case3ModRight : Polynomial (ZMod 11) := polynomialOfCoeffs ([5, 6, 5, 10, 1, 7, 6, 8, 8, 3, 5, 3, 6, 2, 5, 4, 8, 7, 3, 4, 5, 5, 3, 3, 7, 4, 6, 0, 6, 2, 2, 4, 9, 4, 7, 9, 2, 1, 6, 9, 8, 3, 10, 1, 5, 10, 2, 10, 9, 8, 2, 4, 1, 6, 8, 5, 7, 7, 4, 5, 10, 9, 1, 3, 5, 10, 5, 2, 2, 10, 1, 3, 2, 10, 3, 6, 7, 9, 6, 2, 1, 3, 8, 9, 0, 7] : List (ZMod 11))

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem case3_cofactor_degree_bounds :
    case3CofactorLeft.natDegree ≤ 67 ∧ case3CofactorRight.natDegree ≤ 85 := by
  constructor
  · unfold case3CofactorLeft
    exact polynomialOfCoeffs_degree_le _
  · unfold case3CofactorRight
    exact polynomialOfCoeffs_degree_le _

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem case3_left_map :
    case3CofactorLeft.map (Int.castRingHom (ZMod 11)) = case3ModLeft := by
  unfold case3CofactorLeft case3ModLeft
  rw [polynomialOfCoeffs_map]
  congr 1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem case3_right_map :
    case3CofactorRight.map (Int.castRingHom (ZMod 11)) = case3ModRight := by
  unfold case3CofactorRight case3ModRight
  rw [polynomialOfCoeffs_map]
  congr 1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem case3_modular_degrees :
    (case3CofactorLeft.map (Int.castRingHom (ZMod 11))).natDegree = 67 ∧
    (case3CofactorRight.map (Int.castRingHom (ZMod 11))).natDegree = 85 := by
  rw [case3_left_map, case3_right_map]
  constructor
  · unfold case3ModLeft
    apply polynomialOfCoeffs_degree_eq _ 67 (by rfl)
    decide
  · unfold case3ModRight
    apply polynomialOfCoeffs_degree_eq _ 85 (by rfl)
    decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
theorem case3_modular_coprime :
    IsCoprime (case3CofactorLeft.map (Int.castRingHom (ZMod 11)))
      (case3CofactorRight.map (Int.castRingHom (ZMod 11))) := by
  rw [case3_left_map, case3_right_map]
  refine ⟨polynomialOfCoeffs ([3, 1, 5, 6, 5, 10, 1, 3, 2, 0, 2, 5, 4, 2, 6, 4, 4, 9, 0, 7, 8, 10, 4, 2, 8, 1, 4, 1, 4, 10, 2, 1, 0, 10, 0, 5, 10, 7, 4, 8, 8, 2, 10, 9, 2, 9, 5, 8, 5, 6, 8, 8, 4, 4, 2, 5, 3, 8, 10, 8, 2, 6, 3, 7, 2, 10, 7, 4, 8, 2, 3, 6, 9, 2, 10, 1, 7, 10, 7, 8, 10, 1, 7, 2, 10] : List (ZMod 11)), polynomialOfCoeffs ([10, 2, 8, 8, 0, 2, 1, 9, 9, 9, 10, 3, 0, 4, 3, 9, 0, 7, 6, 7, 9, 2, 1, 9, 6, 3, 6, 5, 5, 9, 4, 3, 7, 4, 0, 4, 9, 1, 10, 2, 0, 7, 10, 0, 3, 9, 8, 10, 2, 9, 0, 10, 5, 2, 6, 2, 7, 10, 3, 1, 9, 10, 5, 2, 8, 7, 4] : List (ZMod 11)), ?_⟩
  have hp : (11 : Polynomial (ZMod 11)) = 0 := by
    have h : (11 : ZMod 11) = 0 := by decide
    simpa only [map_ofNat, Polynomial.C_0] using congrArg (Polynomial.C : ZMod 11 → Polynomial (ZMod 11)) h
  have hh : polynomialOfCoeffs ([5, 9, 11, 24, 19, 28, 31, 30, 44, 44, 51, 49, 50, 54, 58, 68, 81, 74, 87, 79, 90, 93, 91, 96, 105, 121, 115, 115, 122, 113, 135, 125, 135, 147, 151, 161, 150, 165, 157, 168, 178, 179, 197, 187, 205, 197, 197, 222, 223, 252, 226, 236, 257, 238, 263, 254, 272, 266, 287, 288, 270, 299, 303, 317, 314, 305, 320, 336, 336, 303, 334, 331, 318, 325, 331, 331, 318, 349, 333, 333, 347, 347, 325, 350, 342, 345, 331, 309, 324, 318, 307, 314, 313, 329, 276, 302, 318, 281, 278, 286, 288, 271, 287, 267, 258, 274, 249, 258, 222, 245, 225, 237, 224, 202, 216, 198, 183, 182, 193, 165, 172, 176, 163, 153, 149, 147, 143, 126, 122, 125, 133, 106, 109, 106, 113, 89, 90, 89, 92, 88, 72, 66, 66, 61, 51, 35, 41, 30, 23, 16, 11, 8] : List (ZMod 11)) * (11 : Polynomial (ZMod 11)) = 0 := by rw [hp, mul_zero]
  unfold case3ModLeft case3ModRight
  simp only [polynomialOfCoeffs, map_ofNat, Polynomial.C_0, Polynomial.C_1] at hh ⊢
  linear_combination hh

end PEqualNP.Outside.L_gct_231.trace

#print axioms PEqualNP.Outside.L_gct_231.trace.case3_modular_coprime
