import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17870_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev val (C : Circuit) (x : Fin 24 → Bool) (i : ℕ) := PEqualNP.BlindGate.wireValue C 24 x i

def add (C : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op, [a,b]⟩], 24 + C.size⟩

theorem add_size (C : Circuit) (op : GateOp) (a b : ℕ) :
    (add C op a b).size = C.size + 1 := by simp [add, Circuit.size]

theorem add_head (C : Circuit) (op : GateOp) (a b : ℕ) (h : 0 < C.size) :
    (add C op a b).gates.head? = C.gates.head? := by
  cases e : C.gates with
  | nil => simp [Circuit.size,e] at h
  | cons g gs => simp [add,e]

theorem add_mono {C : Circuit} (h : Monotone2 C) {op : GateOp}
    (hok : op = .and ∨ op = .or) (a b : ℕ) : Monotone2 (add C op a b) := by
  intro g hg
  change g ∈ C.gates ++ [⟨op,[a,b]⟩] at hg
  rcases List.mem_append.mp hg with old | new
  · exact h g old
  · obtain rfl := List.mem_singleton.mp new
    exact ⟨hok, by simp⟩

theorem wires_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun z g => z ++ [g.op.eval (g.inputs.map fun i => z.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons,ih]; simp; omega

theorem size_wires (C : Circuit) (x : Fin 24 → Bool) :
    (C.wires (List.ofFn x)).length = 24 + C.size := by
  simpa [Circuit.wires,Circuit.size] using wires_len C.gates (List.ofFn x)

theorem wires_add (C : Circuit) (op : GateOp) (a b : ℕ) (x : Fin 24 → Bool) :
    (add C op a b).wires (List.ofFn x) =
      C.wires (List.ofFn x) ++ [op.eval [val C x a, val C x b]] := by
  simp [add,Circuit.wires,List.foldl_append,val,PEqualNP.BlindGate.wireValue]

theorem old (C : Circuit) (op : GateOp) (a b i : ℕ) (x : Fin 24 → Bool)
    (hi : i < 24 + C.size) : val (add C op a b) x i = val C x i := by
  unfold val PEqualNP.BlindGate.wireValue
  rw [wires_add, List.getD_append _ _ _ _ (by simpa only [size_wires] using hi)]

theorem lastVal (C : Circuit) (op : GateOp) (a b : ℕ) (x : Fin 24 → Bool) :
    (add C op a b).eval (List.ofFn x) = op.eval [val C x a, val C x b] := by
  unfold Circuit.eval
  rw [wires_add]
  change (_ ++ [_]).getD (24 + C.size) false = _
  rw [← size_wires C x]
  simp

theorem build (C : Circuit) (cm : Monotone2 C) (cp : 0 < C.size) (p : List (ℕ × ℕ)) :
    p ≠ [] → (∀ q ∈ p, q.1 < 24 + C.size ∧ q.2 < 24 + C.size) →
    ∃ D : Circuit, Monotone2 D ∧ D.gates.head? = C.gates.head? ∧ C.size ≤ D.size ∧
      D.size + 1 ≤ C.size + 2 * p.length ∧ D.output < 24 + D.size ∧
      ∀ x : Fin 24 → Bool, (∀ i < 24 + C.size, val D x i = val C x i) ∧
        D.eval (List.ofFn x) = p.any fun q => val C x q.1 && val C x q.2 := by
  induction p with
  | nil => intro hn; exact (hn rfl).elim
  | cons q qs ih =>
    intro _ bounds
    rcases qs with _ | ⟨r,rs⟩
    · refine ⟨add C .and q.1 q.2, add_mono cm (Or.inl rfl) _ _, add_head _ _ _ _ cp, ?_, ?_, ?_, ?_⟩
      · rw [add_size]; omega
      · simp [add_size]
      · change 24 + C.size < 24 + (add C .and q.1 q.2).size
        rw [add_size]; omega
      · intro x
        refine ⟨fun i hi => old _ _ _ _ i x hi, ?_⟩
        rw [lastVal]; simp [GateOp.eval]
    · obtain ⟨D,dm,dh,ds,dk,do',dv⟩ := ih (by simp) (fun a ha => bounds a (by simp [ha]))
      let A := add D .and q.1 q.2
      let E := add A .or A.output D.output
      have aSize : A.size = D.size + 1 := add_size _ _ _ _
      have eSize : E.size = A.size + 1 := add_size _ _ _ _
      have dpos : 0 < D.size := by omega
      have apos : 0 < A.size := by omega
      have am : Monotone2 A := add_mono dm (Or.inl rfl) _ _
      have pr := bounds q (by simp)
      refine ⟨E,add_mono am (Or.inr rfl) _ _, ?_, by omega, ?_, ?_, ?_⟩
      · exact (add_head A _ _ _ apos).trans ((add_head D _ _ _ dpos).trans dh)
      · simp only [List.length_cons] at dk ⊢
        omega
      · change 24 + A.size < 24 + E.size
        omega
      · intro x
        obtain ⟨keep, hv⟩ := dv x
        constructor
        · intro i hi
          exact (old A _ _ _ i x (by omega)).trans ((old D _ _ _ i x (by omega)).trans (keep i hi))
        · change (add A .or A.output D.output).eval _ = _
          rw [lastVal]
          change (val A x A.output || (val A x D.output || false)) = _
          rw [old D _ _ _ D.output x do', Bool.or_false]
          change (A.eval (List.ofFn x) || D.eval (List.ofFn x)) = _
          rw [hv]
          change ((add D .and q.1 q.2).eval _ || _) = _
          rw [lastVal, keep _ pr.1, keep _ pr.2]
          simp [GateOp.eval]

end PEqualNP.Outside.L_meta_17870_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_17870_aux in
theorem PEqualNP.Outside.L_meta_17870 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (ℕ × ℕ)), PEqualNP.MetaComplexity.Monotone2 x1 → x1.gates ≠ [] → x2 ≠ [] → (∀ x6 ∈ x2, x6.1 < (24 : ℕ) + x1.size ∧ x6.2 < (24 : ℕ) + x1.size) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 ∧ x7.gates.head? = x1.gates.head? ∧ x1.size ≤ x7.size ∧ x7.size + (1 : ℕ) ≤ x1.size + (2 : ℕ) * x2.length ∧ x7.output < (24 : ℕ) + x7.size ∧ ∀ (x8 : Fin (24 : ℕ) → Bool), (∀ x9 < (24 : ℕ) + x1.size, PEqualNP.BlindGate.wireValue x7 (24 : ℕ) x8 x9 = PEqualNP.BlindGate.wireValue x1 (24 : ℕ) x8 x9) ∧ x7.eval (List.ofFn x8) = x2.any fun (x9 : ℕ × ℕ) => PEqualNP.BlindGate.wireValue x1 (24 : ℕ) x8 x9.1 && PEqualNP.BlindGate.wireValue x1 (24 : ℕ) x8 x9.2) := by
  intro C p cm cn pn h
  exact build C cm (List.length_pos_iff.mpr cn) p pn h
