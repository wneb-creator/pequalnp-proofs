import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1398_aux

def idx (x : Fin 5 → Bool) : Nat :=
  (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) + (if x 3 then 8 else 0) + (if x 4 then 16 else 0)

def toFun (s : Nat) : (Fin 5 → Bool) → Bool := fun x => s.testBit (idx x)

def pt (i : Nat) : Fin 5 → Bool := fun j => i.testBit j.val

def C5 : (Fin 5 → Bool) → Bool := fun z : Fin 5 → Bool => (z 0 && z 1) || (z 1 && z 2) || (z 2 && z 3) || (z 3 && z 4) || (z 4 && z 0)

def c5 : Nat := 4293589192

def S0 : List Nat := [2863311530,3435973836,4042322160,4278255360,4294901760]
def S1 : List Nat := [2863311530,3435973836,4042322160,4278255360,4294901760,2290649224,2694881440,2852170240,2863267840,3233857728,3422604288,3435921408,4008636142,4026593280,4042260480,4210752250,4244438268,4278190080,4289396650,4291624908,4293984240,4294945450,4294954188,4294963440,4294967040]
def S2 : List Nat := [2863311530,3435973836,4042322160,4278255360,4294901760,2290649224,2694881440,2852170240,2863267840,3233857728,3422604288,3435921408,4008636142,4026593280,4042260480,4210752250,4244438268,4278190080,4289396650,4291624908,4293984240,4294945450,4294954188,4294963440,4294967040,2147516416,2155872256,2155905152,2281701376,2281736192,2290124928,2290614272,2290647168,2290649088,2684354560,2684395520,2692784256,2694840320,2694873216,2694881280,2818615296,2829582336,2829625512,2852126720,2852161536,2852167680,2861039616,2861083272,2862612480,2862656160,2863302792,2863308960,2863311360,3221225472,3221274624,3229663360,3233808384,3233841280,3233857536,3355494400,3368550400,3368601800,3422552064,3422586880,3422601216,3431464960,3431517320,3435134976,3435187392,3435956360,3435970752,3435973632,3758153728,3772776448,3772834016,3938511552,3941253312,3941264106,3969969312,3974930592,3974950124,3992977408,3993038336,4004170752,4004179626,4006390272,4006407884,4007718624,4008574976,4008618666,4008627404,4008632544,4008635904,4026531840,4026572800,4026580992,4037017600,4037079200,4039114752,4039176384,4042301600,4042309824,4042321920,4169726088,4177037448,4177066232,4194304000,4194368000,4205506560,4205509290,4207475400,4210076160,4210096880,4210688000,4210731690,4210739400,4210749680,4210752000,4227858432,4227922944,4238933160,4241289216,4241292492,4243639296,4243651824,4244373504,4244416680,4244425932,4244435184,4244438016,4277075694,4277862138,4277993212,4278120174,4278123258,4278123772,4278124286,4278233600,4278242304,4278251520,4287137928,4287168392,4288716960,4288741280,4289331200,4289374890,4289383560,4289392800,4289396480,4290822336,4290838464,4291559424,4291603080,4291611852,4291621056,4291624704,4293591018,4293722092,4293848814,4293853098,4293853132,4293853166,4293918720,4293962400,4293971136,4293980400,4293984000,4294508536,4294638330,4294639530,4294639600,4294639610,4294769916,4294770636,4294770672,4294770684,4294901758,4294936712,4294942880,4294945280,4294951104,4294953984,4294961898,4294962412,4294962858,4294962892,4294962926,4294963200,4294965496,4294965930,4294966000,4294966010,4294966476,4294966512,4294966524,4294967038,4294967176,4294967200,4294967210,4294967232,4294967244,4294967278,4294967280,4294967290,4294967292]

def T : ℕ → Set ((Fin 5 → Bool) → Bool)
  | 0 => {f | ∃ s ∈ S0, f = toFun s}
  | 1 => {f | ∃ s ∈ S1, f = toFun s}
  | 2 => {f | ∃ s ∈ S2, f = toFun s}
  | 3 => {f | f ≠ C5}
  | (_ + 4) => Set.univ

theorem pts : ∀ i : Fin 32, C5 (pt i.val) = c5.testBit i.val ∧ idx (pt i.val) = i.val := by decide

theorem key (m : Nat) (h : toFun m = C5) : m % 2 ^ 32 = c5 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow]
  by_cases hi : i < 32
  · obtain ⟨h1, h2⟩ := pts ⟨i, hi⟩
    have h3 := congrFun h (pt i)
    simp only [toFun] at h3
    rw [h2] at h3
    simp [hi, h3, h1]
  · have : c5 < 2 ^ i := lt_of_lt_of_le (by decide : c5 < 2 ^ 32) (Nat.pow_le_pow_right (by norm_num) (by omega))
    simp [hi, Nat.testBit_eq_false_of_lt this]

theorem ne_of (m : Nat) (h : m % 2 ^ 32 ≠ c5) : toFun m ≠ C5 := fun h' => h (key m h')

theorem and_eq (a b : Nat) : (fun y => toFun a y && toFun b y) = toFun (a &&& b) := by
  funext y; simp [toFun, Nat.testBit_and]

theorem or_eq (a b : Nat) : (fun y => toFun a y || toFun b y) = toFun (a ||| b) := by
  funext y; simp [toFun, Nat.testBit_or]

theorem proj : ∀ i : Fin 5, ∃ s ∈ S0, (fun x : Fin 5 → Bool => x i) = toFun s := by
  intro i
  refine ⟨S0.get ⟨i.val, by simp [S0]⟩, List.get_mem _ _, ?_⟩
  funext x
  revert x
  fin_cases i <;> decide

theorem sub01 : S0.all (fun s => S1.contains s) = true := by decide +kernel
theorem sub12 : S1.all (fun s => S2.contains s) = true := by decide +kernel
theorem sub23 : S2.all (fun s => s % 2 ^ 32 != c5) = true := by decide +kernel
theorem cl0 : S0.all (fun a => S0.all (fun b => S1.contains (a &&& b) && S1.contains (a ||| b))) = true := by decide +kernel
theorem cl1 : S1.all (fun a => S1.all (fun b => S2.contains (a &&& b) && S2.contains (a ||| b))) = true := by decide +kernel
theorem cl2 : S2.all (fun a => S2.all (fun b => (a &&& b) % 2 ^ 32 != c5 && (a ||| b) % 2 ^ 32 != c5)) = true := by decide +kernel

end PEqualNP.Outside.L_meta_1398_aux

open PEqualNP.Outside.L_meta_1398_aux in
theorem PEqualNP.Outside.L_meta_1398 : ¬ (∀ T : ℕ → Set ((Fin 5 → Bool) → Bool), (∀ i : Fin 5, (fun x : Fin 5 → Bool => x i) ∈ T 0) → (∀ (k : ℕ) (f : (Fin 5 → Bool) → Bool), f ∈ T k → f ∈ T (k + 1)) → (∀ (k : ℕ) (f g : (Fin 5 → Bool) → Bool), f ∈ T k → g ∈ T k → (fun y : Fin 5 → Bool => f y && g y) ∈ T (k + 1) ∧ (fun y : Fin 5 → Bool => f y || g y) ∈ T (k + 1)) → (fun z : Fin 5 → Bool => (z 0 && z 1) || (z 1 && z 2) || (z 2 && z 3) || (z 3 && z 4) || (z 4 && z 0)) ∈ T 3) := by
  intro h
  have hT := h T proj ?_ ?_
  · exact hT rfl
  · intro k f hf
    rcases k with _ | _ | _ | _ | k
    · obtain ⟨s, hs, rfl⟩ := hf
      have sub01 := sub01
      simp only [List.all_eq_true, List.contains_iff_mem] at sub01
      exact ⟨s, sub01 s hs, rfl⟩
    · obtain ⟨s, hs, rfl⟩ := hf
      have sub12 := sub12
      simp only [List.all_eq_true, List.contains_iff_mem] at sub12
      exact ⟨s, sub12 s hs, rfl⟩
    · obtain ⟨s, hs, rfl⟩ := hf
      have sub23 := sub23
      simp only [List.all_eq_true, bne_iff_ne, ne_eq] at sub23
      exact ne_of s (sub23 s hs)
    · trivial
    · trivial
  · intro k f g hf hg
    rcases k with _ | _ | _ | k
    · obtain ⟨a, ha, rfl⟩ := hf
      obtain ⟨b, hb, rfl⟩ := hg
      have cl0 := cl0
      simp only [List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem] at cl0
      rw [and_eq, or_eq]
      exact ⟨⟨_, (cl0 a ha b hb).1, rfl⟩, ⟨_, (cl0 a ha b hb).2, rfl⟩⟩
    · obtain ⟨a, ha, rfl⟩ := hf
      obtain ⟨b, hb, rfl⟩ := hg
      have cl1 := cl1
      simp only [List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem] at cl1
      rw [and_eq, or_eq]
      exact ⟨⟨_, (cl1 a ha b hb).1, rfl⟩, ⟨_, (cl1 a ha b hb).2, rfl⟩⟩
    · obtain ⟨a, ha, rfl⟩ := hf
      obtain ⟨b, hb, rfl⟩ := hg
      have cl2 := cl2
      simp only [List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at cl2
      rw [and_eq, or_eq]
      exact ⟨ne_of _ (cl2 a ha b hb).1, ne_of _ (cl2 a ha b hb).2⟩
    · exact ⟨trivial, trivial⟩
