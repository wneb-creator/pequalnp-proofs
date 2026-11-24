import Mathlib

namespace PEqualNP.Outside.L_meta_1477.Complement12

def planeEdges : List (ℕ × ℕ) :=
  [(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)]

def planePairs : List (Fin 42 × Fin 42) :=
  [(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)]

def localPairs : List (Fin 33 × Fin 33) :=
  [(0, 14), (0, 17), (0, 18), (0, 23), (0, 25), (1, 15), (1, 18), (1, 19), (1, 24), (1, 26), (2, 16), (2, 19), (2, 20), (2, 25), (2, 27), (3, 17), (3, 20), (3, 21), (3, 26), (3, 28), (4, 19), (4, 22), (4, 23), (4, 28), (4, 30), (5, 21), (5, 24), (5, 25), (5, 30), (5, 32), (6, 12), (6, 22), (6, 25), (6, 26), (6, 31), (7, 13), (7, 23), (7, 26), (7, 27), (7, 32), (8, 12), (8, 14), (8, 24), (8, 27), (8, 28), (9, 13), (9, 15), (9, 25), (9, 28), (9, 29), (10, 14), (10, 16), (10, 26), (10, 29), (10, 30), (11, 16), (11, 18), (11, 28), (11, 31), (11, 32)]

def inputMap : Fin 33 → Fin 42 :=
  ![6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41]

def coreInput (x : Fin 42 → Bool) : Fin 33 → Bool :=
  fun i => x (inputMap i)

def remainingStars : List (Fin 42 × (Fin 5 → Fin 42)) :=
  [(0, ![21, 26, 28, 38, 41]),
   (1, ![21, 22, 27, 29, 39]),
   (2, ![22, 23, 28, 30, 40]),
   (3, ![23, 24, 29, 31, 41]),
   (4, ![21, 24, 25, 30, 32]),
   (5, ![22, 25, 26, 31, 33]),
   (10, ![27, 30, 31, 36, 38]),
   (12, ![29, 32, 33, 38, 40]),
   (19, ![24, 26, 36, 39, 40])]

def edgeValue {n : ℕ} (es : List (Fin n × Fin n)) (x : Fin n → Bool) : Bool :=
  es.any (fun e => x e.1 && x e.2)

def starValue {n : ℕ} (s : Fin n × (Fin 5 → Fin n)) (x : Fin n → Bool) : Bool :=
  x s.1 && ((((x (s.2 0) || x (s.2 1)) || x (s.2 2)) || x (s.2 3)) || x (s.2 4))

def starsValue {n : ℕ} (s : List (Fin n × (Fin 5 → Fin n))) (x : Fin n → Bool) : Bool :=
  s.any (fun a => starValue a x)

lemma planePairs_map : planePairs.map (fun e => (e.1.val, e.2.val)) = planeEdges := by
  decide

lemma localPairs_length : localPairs.length = 60 := by decide

lemma localPairs_nodup : localPairs.Nodup := by decide

lemma remainingStars_length : remainingStars.length = 9 := by decide

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
  simp [edgeValue, planePairs, localPairs, coreInput, inputMap, starsValue, remainingStars, starValue,
    and_or_dist]
  ac_rfl

end PEqualNP.Outside.L_meta_1477.Complement12
