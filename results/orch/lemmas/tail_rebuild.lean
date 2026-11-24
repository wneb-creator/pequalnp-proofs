import PEqualNP.Outside.L_meta_3451

namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

def taTerm {m : ℕ} (t : Fin m ⊕ (Fin m × Fin m)) (x : Fin m → Bool) : Bool :=
  match t with
  | .inl i => x i
  | .inr (i, j) => x i && x j

def taTermCost {m : ℕ} (t : Fin m ⊕ (Fin m × Fin m)) : ℕ :=
  match t with
  | .inl _ => 0
  | .inr _ => 1

lemma taTermBld {m : ℕ} (t : Fin m ⊕ (Fin m × Fin m)) :
    CleanUpper.Bld m (fun _ => true) (taTerm t) (taTermCost t) := by
  cases t with
  | inl i => exact CleanUpper.bld_var _ i
  | inr p =>
    obtain ⟨i, j⟩ := p
    exact CleanUpper.bld_and (by intros; rfl)
      (CleanUpper.bld_var _ i) (CleanUpper.bld_var _ j)

lemma taAttach {m : ℕ} (ts : List (Fin m ⊕ (Fin m × Fin m))) :
    ∀ (F : (Fin m → Bool) → Bool) (s : ℕ),
      CleanUpper.Bld m (fun _ => true) F s →
      CleanUpper.Bld m (fun _ => true)
        (fun x => F x || ts.any (fun t => taTerm t x))
        (s + (ts.map taTermCost).sum + ts.length) := by
  induction ts with
  | nil =>
    intro F s h
    simpa using h
  | cons t ts ih =>
    intro F s h
    have h' := ih (fun x => F x || taTerm t x) (s + taTermCost t + 1)
      (CleanUpper.bld_or h (taTermBld t))
    have hc : s + taTermCost t + 1 + (ts.map taTermCost).sum + ts.length =
        s + ((t :: ts).map taTermCost).sum + (t :: ts).length := by simp; omega
    rw [hc] at h'
    apply CleanUpper.bld_congr h'
    intro x
    simp [Bool.or_assoc]

lemma taFactoredBld {m : ℕ} (u v : Fin m) (vs : List (Fin m))
    (ts : List (Fin m ⊕ (Fin m × Fin m))) :
    CleanUpper.Bld m (fun _ => true)
      (fun x => (v :: vs).any (fun w => x u && x w) || ts.any (fun t => taTerm t x))
      (vs.length + 1 + (ts.map taTermCost).sum + ts.length) := by
  have h := CleanUpper.bld_and (by intros; rfl) (CleanUpper.bld_var (fun _ => true) u)
    (CleanUpper.bld_anyList (fun _ => true) vs v)
  have h' := taAttach ts _ (vs.length + 1) (by simpa using h)
  apply CleanUpper.bld_congr h'
  intro x
  cases x u <;> simp

lemma taAppend (n : ℕ) (P : Circuit) (hm : Monotone2 P) (hr : ReadsBack n P)
    (F : (Fin (n + P.size) → Bool) → Bool) (s : ℕ)
    (hb : CleanUpper.Bld (n + P.size) (fun _ => true) F s) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size ≤ P.size + s ∧
      ∀ z : Fin n → Bool, circuitFun n D z =
        F (fun i => (P.wires (List.ofFn z)).getD i false) := by
  obtain ⟨gs, out, hok, hn, hlen, _, hread, _, hev⟩ := hb (n + P.size) le_rfl
  let D : Circuit := ⟨P.gates ++ gs, out⟩
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ P.gates ++ gs at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hm g hg
    · refine ⟨?_, (hok g hg).2⟩
      rcases (hok g hg).1 with hand | hor | hnot
      · exact Or.inl hand
      · exact Or.inr hor
      · exact (hn g hg hnot).elim
  · change CleanUpper.Reads n (P.gates ++ gs)
    exact CleanUpper.reads_append n P.gates gs hr hread
  · simp only [D, Circuit.size, List.length_append]
    omega
  · intro z
    have hw : (P.wires (List.ofFn z)).length = n + P.size := by
      change (P.gates.foldl decStep (List.ofFn z)).length = _
      simp [lcLength, Circuit.size]
    have he := hev (P.wires (List.ofFn z)) hw
    change ((P.gates ++ gs).foldl decStep (List.ofFn z)).getD out false = _
    rw [List.foldl_append]
    exact he

lemma taFactorCircuit (n : ℕ) (P : Circuit) (hm : Monotone2 P) (hr : ReadsBack n P)
    (u v : Fin (n + P.size)) (vs : List (Fin (n + P.size)))
    (ts : List (Fin (n + P.size) ⊕ (Fin (n + P.size) × Fin (n + P.size)))) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧
      D.size ≤ P.size + vs.length + 1 + (ts.map taTermCost).sum + ts.length ∧
      ∀ z : Fin n → Bool,
        let x : Fin (n + P.size) → Bool := fun i => (P.wires (List.ofFn z)).getD i false
        circuitFun n D z =
          ((v :: vs).any (fun w => x u && x w) || ts.any (fun t => taTerm t x)) := by
  obtain ⟨D, hdm, hdr, hds, hdf⟩ := taAppend n P hm hr _ _ (taFactoredBld u v vs ts)
  refine ⟨D, hdm, hdr, ?_, hdf⟩
  omega

end PEqualNP.Outside.L_meta_3451
