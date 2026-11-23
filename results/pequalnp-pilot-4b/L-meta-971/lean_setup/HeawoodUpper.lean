import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
namespace HeawoodUpperAudit

def gates : List Gate :=
  [⟨.or, [7, 8]⟩,
   ⟨.or, [10, 14]⟩,
   ⟨.and, [0, 15]⟩,
   ⟨.or, [7, 9]⟩,
   ⟨.or, [13, 17]⟩,
   ⟨.and, [1, 18]⟩,
   ⟨.or, [8, 12]⟩,
   ⟨.or, [13, 20]⟩,
   ⟨.and, [2, 21]⟩,
   ⟨.or, [7, 11]⟩,
   ⟨.or, [12, 23]⟩,
   ⟨.and, [3, 24]⟩,
   ⟨.or, [10, 11]⟩,
   ⟨.or, [13, 26]⟩,
   ⟨.and, [4, 27]⟩,
   ⟨.or, [9, 10]⟩,
   ⟨.or, [12, 29]⟩,
   ⟨.and, [5, 30]⟩,
   ⟨.or, [8, 9]⟩,
   ⟨.or, [11, 32]⟩,
   ⟨.and, [6, 33]⟩,
   ⟨.or, [16, 19]⟩,
   ⟨.or, [35, 22]⟩,
   ⟨.or, [36, 25]⟩,
   ⟨.or, [37, 28]⟩,
   ⟨.or, [38, 31]⟩,
   ⟨.or, [39, 34]⟩]

def circuit : Circuit := ⟨gates, 40⟩

def target (x : Fin 14 → Bool) : Bool :=
  (x 0 && (x 7 || x 8 || x 10)) ||
  (x 1 && (x 7 || x 9 || x 13)) ||
  (x 2 && (x 8 || x 12 || x 13)) ||
  (x 3 && (x 7 || x 11 || x 12)) ||
  (x 4 && (x 10 || x 11 || x 13)) ||
  (x 5 && (x 9 || x 10 || x 12)) ||
  (x 6 && (x 8 || x 9 || x 11))

theorem size_eq : circuit.size = 27 := by decide

theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  simp [PEqualNP.MetaComplexity.Monotone2, circuit, gates]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 500000 in
theorem eval_eq (x : Fin 14 → Bool) : circuit.eval (List.ofFn x) = target x := by
  simp [circuit, gates, Circuit.eval, Circuit.wires, GateOp.eval,
    List.ofFn_succ, List.getD, target, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]


def edgePairs : List (Fin 14 × Fin 14) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

def edgeNat : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

theorem pair_map : edgePairs.map (fun e => (e.1.val, e.2.val)) = edgeNat := by decide

private theorem bool_and_or (a b c : Bool) :
    (a && (b || c)) = ((a && b) || (a && c)) := by cases a <;> rfl

def targetDNF (x : Fin 14 → Bool) : Bool :=
  (x 0 && x 7) ||
  (x 0 && x 8) ||
  (x 0 && x 10) ||
  (x 1 && x 7) ||
  (x 1 && x 9) ||
  (x 1 && x 13) ||
  (x 2 && x 8) ||
  (x 2 && x 12) ||
  (x 2 && x 13) ||
  (x 3 && x 7) ||
  (x 3 && x 11) ||
  (x 3 && x 12) ||
  (x 4 && x 10) ||
  (x 4 && x 11) ||
  (x 4 && x 13) ||
  (x 5 && x 9) ||
  (x 5 && x 10) ||
  (x 5 && x 12) ||
  (x 6 && x 8) ||
  (x 6 && x 9) ||
  (x 6 && x 11)

theorem target_dnf (x : Fin 14 → Bool) : target x = targetDNF x := by
  simp only [target, targetDNF, bool_and_or, Bool.or_assoc]

theorem target_pairs (x : Fin 14 → Bool) : target x = true ↔
    ∃ e ∈ edgePairs, x e.1 = true ∧ x e.2 = true := by
  rw [target_dnf]
  simp [targetDNF, edgePairs, Bool.or_eq_true, Bool.and_eq_true, or_assoc]

theorem computes (x : Fin 14 → Bool) : circuit.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 14, (u.val, v.val) ∈ edgeNat ∧ x u = true ∧ x v = true := by
  rw [eval_eq, target_pairs]
  constructor
  · rintro ⟨e, he, hu, hv⟩
    refine ⟨e.1, e.2, ?_, hu, hv⟩
    rw [← pair_map]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    rw [← pair_map] at huv
    obtain ⟨e, he, hval⟩ := List.mem_map.mp huv
    have hpair : e = (u, v) := by
      apply Prod.ext
      · exact Fin.ext (congrArg Prod.fst hval)
      · exact Fin.ext (congrArg Prod.snd hval)
    subst e
    exact ⟨(u, v), he, hu, hv⟩

end HeawoodUpperAudit
