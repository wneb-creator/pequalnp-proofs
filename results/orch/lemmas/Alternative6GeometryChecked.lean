import Mathlib

namespace PEqualNP.Outside.L_meta_1477.Alternative6

def planeEdges : List (ℕ × ℕ) :=
  [(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)]

def planePairs : List (Fin 42 × Fin 42) :=
  [(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)]

def localPairs : List (Fin 19 × Fin 19) :=
  [(0, 6), (1, 6), (1, 7), (2, 7), (5, 7), (2, 8), (3, 8), (3, 9), (4, 10), (0, 11), (1, 12), (0, 13), (2, 13), (4, 13), (1, 14), (3, 14), (4, 14), (2, 15), (5, 16), (4, 17), (5, 17), (0, 18), (3, 18), (5, 18)]

def coreInput (x : Fin 42 → Bool) : Fin 19 → Bool :=
  ![x 0, x 1, x 2, x 3, x 8, x 15, x 21, x 22, x 23, x 24 || x 31, x 25 || x 34, x 26 || x 38, x 27 || x 39, x 28, x 29, x 30 || x 40, x 32 || x 35, x 36, x 41]

def remainingStars : List (Fin 42 × (Fin 5 → Fin 42)) :=
  [(4, ![21, 24, 25, 30, 32]),
   (5, ![22, 25, 26, 31, 33]),
   (6, ![23, 26, 27, 32, 34]),
   (7, ![24, 27, 28, 33, 35]),
   (9, ![26, 29, 30, 35, 37]),
   (10, ![27, 30, 31, 36, 38]),
   (11, ![28, 31, 32, 37, 39]),
   (12, ![29, 32, 33, 38, 40]),
   (13, ![30, 33, 34, 39, 41]),
   (14, ![21, 31, 34, 35, 40]),
   (16, ![21, 23, 33, 36, 37]),
   (17, ![22, 24, 34, 37, 38]),
   (18, ![23, 25, 35, 38, 39]),
   (19, ![24, 26, 36, 39, 40]),
   (20, ![25, 27, 37, 40, 41])]

def edgeValue {n : ℕ} (es : List (Fin n × Fin n)) (x : Fin n → Bool) : Bool :=
  es.any (fun e => x e.1 && x e.2)

def starValue {n : ℕ} (s : Fin n × (Fin 5 → Fin n)) (x : Fin n → Bool) : Bool :=
  x s.1 && ((((x (s.2 0) || x (s.2 1)) || x (s.2 2)) || x (s.2 3)) || x (s.2 4))

def starsValue {n : ℕ} (s : List (Fin n × (Fin 5 → Fin n))) (x : Fin n → Bool) : Bool :=
  s.any (fun a => starValue a x)

lemma planePairs_map : planePairs.map (fun e => (e.1.val, e.2.val)) = planeEdges := by
  decide

lemma localPairs_length : localPairs.length = 24 := by decide

lemma localPairs_nodup : localPairs.Nodup := by decide

lemma remainingStars_length : remainingStars.length = 15 := by decide

lemma edgeValue_iff {n : ℕ} (es : List (Fin n × Fin n)) (x : Fin n → Bool) :
    edgeValue es x = true ↔ ∃ u v : Fin n, (u, v) ∈ es ∧ x u = true ∧ x v = true := by
  simp only [edgeValue, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨u, v⟩, he, hu, hv⟩
    exact ⟨u, v, he, hu, hv⟩
  · rintro ⟨u, v, he, hu, hv⟩
    exact ⟨(u, v), he, hu, hv⟩

lemma planeValue_iff (x : Fin 42 → Bool) :
    edgeValue planePairs x = true ↔
      ∃ u v : Fin 42, (u.val, v.val) ∈ planeEdges ∧ x u = true ∧ x v = true := by
  rw [edgeValue_iff]
  constructor
  · rintro ⟨u, v, he, hu, hv⟩
    refine ⟨u, v, ?_, hu, hv⟩
    rw [← planePairs_map]
    exact List.mem_map.mpr ⟨(u, v), he, rfl⟩
  · rintro ⟨u, v, he, hu, hv⟩
    rw [← planePairs_map] at he
    obtain ⟨⟨a, b⟩, hab, heq⟩ := List.mem_map.mp he
    have hau : a = u := Fin.ext (congrArg Prod.fst heq)
    have hbv : b = v := Fin.ext (congrArg Prod.snd heq)
    subst a
    subst b
    exact ⟨u, v, hab, hu, hv⟩

lemma and_or_dist (a b c : Bool) : (a && (b || c)) = ((a && b) || (a && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma plane_decomposition (x : Fin 42 → Bool) :
    edgeValue planePairs x =
      (edgeValue localPairs (coreInput x) || starsValue remainingStars x) := by
  simp [edgeValue, planePairs, localPairs, coreInput, starsValue, remainingStars, starValue,
    and_or_dist]
  ac_rfl

end PEqualNP.Outside.L_meta_1477.Alternative6
