import Mathlib

namespace PEqualNP.Outside.L_meta_3678_aux
namespace TarjanLower

abbrev Sig := BitVec 11

def initial : List Sig := [0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]
def small : List Sig := [40, 80, 136, 272, 9, 11, 15, 17, 19, 23]
def large : List Sig := [559, 599, 1167, 1303]
def special : List Sig := [519, 1031]
def base : List Sig := initial ++ small

abbrev Sub (a b : Sig) : Prop := a ||| b = b
abbrev Makes (xs : List Sig) (v : Sig) : Prop :=
  ∃ a ∈ xs, ∃ b ∈ xs, v = a ||| b
abbrev Useful (v : Sig) : Prop := ∃ t ∈ large, Sub v t ∧ v ≠ t
abbrev Exclusive (t v : Sig) : Prop :=
  Sub v t ∧ ∀ u ∈ large, u ≠ t → ¬ Sub v u

def candidates (xs : List Sig) : List Sig :=
  ((xs.flatMap fun a => xs.map fun b => a ||| b).filter
    fun v => decide (v ∉ base ∧ Useful v)).eraseDups

def submasks (t : Sig) : List Sig :=
  if t = 559 then [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559]
  else if t = 599 then [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 512, 513, 514, 515, 516, 517, 518, 519, 528, 529, 530, 531, 532, 533, 534, 535, 576, 577, 578, 579, 580, 581, 582, 583, 592, 593, 594, 595, 596, 597, 598, 599]
  else if t = 1167 then [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167]
  else if t = 1303 then [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 256, 257, 258, 259, 260, 261, 262, 263, 272, 273, 274, 275, 276, 277, 278, 279, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1296, 1297, 1298, 1299, 1300, 1301, 1302, 1303]
  else []


abbrev Keep (v : Sig) : Prop := v ∉ base ∧ Useful v

def helpers (xs : List Sig) : List Sig := xs.filter fun v => decide (Keep v)

def Built : List Sig → List Sig → Prop
  | _, [] => True
  | env, v :: vs => Makes env v ∧ Built (v :: env) vs

lemma sub_refl (a : Sig) : Sub a a := BitVec.or_self

lemma sub_left (a b : Sig) : Sub a (a ||| b) := by
  change a ||| (a ||| b) = a ||| b
  rw [← BitVec.or_assoc, BitVec.or_self]

lemma sub_right (a b : Sig) : Sub b (a ||| b) := by
  rw [BitVec.or_comm a b]
  exact sub_left b a

lemma sub_trans {a b c : Sig} (hab : Sub a b) (hbc : Sub b c) : Sub a c := by
  change a ||| c = c
  calc
    a ||| c = a ||| (b ||| c) := by rw [hbc]
    _ = (a ||| b) ||| c := (BitVec.or_assoc _ _ _).symm
    _ = b ||| c := by rw [hab]
    _ = c := hbc

lemma sub_antisymm {a b : Sig} (hab : Sub a b) (hba : Sub b a) : a = b := by
  exact hba.symm.trans ((BitVec.or_comm _ _).trans hab)

lemma useful_down {a b : Sig} (hab : Sub a b) (hb : Useful b) : Useful a := by
  rcases hb with ⟨t, ht, hbt, hne⟩
  refine ⟨t, ht, sub_trans hab hbt, ?_⟩
  intro hat
  subst a
  exact hne (sub_antisymm hbt hab)

lemma makes_mono {xs ys : List Sig} {v : Sig} (h : xs ⊆ ys) (hv : Makes xs v) :
    Makes ys v := by
  rcases hv with ⟨a, ha, b, hb, he⟩
  exact ⟨a, h ha, b, h hb, he⟩

lemma makes_helpers {env : List Sig} {v : Sig} (hv : Makes env v)
    (hu : Useful v) : Makes (helpers env ++ base) v := by
  rcases hv with ⟨a, ha, b, hb, rfl⟩
  have keep_mem (x : Sig) (hx : x ∈ env) (hsub : Sub x (a ||| b)) :
      x ∈ helpers env ++ base := by
    by_cases hbase : x ∈ base
    · exact List.mem_append_right _ hbase
    · apply List.mem_append_left
      exact List.mem_filter.mpr ⟨hx, by simpa using And.intro hbase (useful_down hsub hu)⟩
  exact ⟨a, keep_mem a ha (sub_left a b), b, keep_mem b hb (sub_right a b), rfl⟩

lemma built_helpers {env xs : List Sig} (h : Built env xs) :
    Built (helpers env ++ base) (helpers xs) := by
  induction xs generalizing env with
  | nil => trivial
  | cons v vs ih =>
    obtain ⟨hv, hvs⟩ := h
    by_cases hk : Keep v
    · have hkeep : decide (Keep v) = true := by simp [hk]
      simp only [helpers, List.filter_cons, hkeep, Bool.true_eq, ↓reduceIte]
      refine ⟨makes_helpers hv hk.2, ?_⟩
      simpa only [helpers, List.filter_cons, hkeep, Bool.true_eq, ↓reduceIte,
        List.cons_append] using ih hvs
    · have hkeep : decide (Keep v) = false := by simp [hk]
      simpa only [helpers, List.filter_cons, hkeep, Bool.false_eq_true, ↓reduceIte]
        using ih hvs

end TarjanLower
end PEqualNP.Outside.L_meta_3678_aux
