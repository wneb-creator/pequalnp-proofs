import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2602_aux

open PEqualNP.CircuitLowerBounds

def activeStep (n : ℕ) (C : Circuit) (base : ℕ → Bool) (a w : ℕ) : Prop :=
  ∃ (j b : ℕ) (g : Gate), w = n + j ∧ C.gates[j]? = some g ∧
    (g.inputs = [a, b] ∨ g.inputs = [b, a]) ∧
    (g.op = .or ∨ base b = true)

lemma trace_carries (n : ℕ) (C : Circuit) (base d : ℕ → Bool)
    (ops : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = .and ∨ g.op = .or)
    (rec : ∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a, b] →
      (g.op = .and → d (n + j) = (base a && d b || d a && base b)) ∧
      (g.op = .or → d (n + j) = (d a || d b)))
    {start finish : ℕ} (init : d start = true)
    (path : Relation.ReflTransGen (activeStep n C base) start finish) :
    d finish = true := by
  induction path with
  | refl => exact init
  | tail _ step ih =>
    obtain ⟨j, b, g, rfl, hg, inputs, pass⟩ := step
    rcases inputs with e | e
    · obtain ⟨ha, ho⟩ := rec _ _ _ _ hg e
      rcases ops j g hg with h | h
      · rcases pass with bad | side
        · rw [h] at bad
          contradiction
        · simp [ha h, ih, side]
      · simp [ho h, ih]
    · obtain ⟨ha, ho⟩ := rec _ _ _ _ hg e
      rcases ops j g hg with h | h
      · rcases pass with bad | side
        · rw [h] at bad
          contradiction
        · simp [ha h, ih, side]
      · simp [ho h, ih]

lemma false_trace_no_path (n : ℕ) (C : Circuit) (base d : ℕ → Bool)
    (ops : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = .and ∨ g.op = .or)
    (rec : ∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a, b] →
      (g.op = .and → d (n + j) = (base a && d b || d a && base b)) ∧
      (g.op = .or → d (n + j) = (d a || d b)))
    {start finish : ℕ} (init : d start = true) (final : d finish = false) :
    ¬ Relation.ReflTransGen (activeStep n C base) start finish := by
  intro path
  have ht := trace_carries n C base d ops rec init path
  exact Bool.noConfusion (ht.symm.trans final)

lemma true_trace_reachable (n : ℕ) (C : Circuit) (base d : ℕ → Bool)
    (wf : ∀ j (g : Gate), C.gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a < n + j ∧ b < n + j)
    (rec : ∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a, b] →
      (g.op = .and → d (n + j) = (base a && d b || d a && base b)) ∧
      (g.op = .or → d (n + j) = (d a || d b)))
    (start : ℕ) (init : ∀ k < n, d k = decide (k = start))
    (i : ℕ) (hi : i < n + C.gates.length) (truth : d i = true) :
    Relation.ReflTransGen (activeStep n C base) start i := by
  revert hi truth
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi truth
    by_cases hin : i < n
    · have eq : i = start := of_decide_eq_true ((init i hin).symm.trans truth)
      subst i
      exact .refl
    · let j := i - n
      have eq : i = n + j := by dsimp [j]; omega
      have hj : j < C.gates.length := by omega
      let g := C.gates[j]
      have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
      obtain ⟨hop, a, b, ins, ha, hb⟩ := wf j g hg
      obtain ⟨ra, ro⟩ := rec j g a b hg ins
      have pa (h : d a = true) :
          Relation.ReflTransGen (activeStep n C base) start a :=
        ih a (by omega) (by omega) h
      have pb (h : d b = true) :
          Relation.ReflTransGen (activeStep n C base) start b :=
        ih b (by omega) (by omega) h
      rcases hop with hand | hor
      · rw [eq, ra hand] at truth
        rcases Bool.or_eq_true_iff.mp truth with h | h
        · obtain ⟨hbase, hd⟩ := Bool.and_eq_true_iff.mp h
          exact (pb hd).tail ⟨j, a, g, eq, hg, Or.inr ins, Or.inr hbase⟩
        · obtain ⟨hd, hbase⟩ := Bool.and_eq_true_iff.mp h
          exact (pa hd).tail ⟨j, b, g, eq, hg, Or.inl ins, Or.inr hbase⟩
      · rw [eq, ro hor] at truth
        rcases Bool.or_eq_true_iff.mp truth with h | h
        · exact (pa h).tail ⟨j, b, g, eq, hg, Or.inl ins, Or.inl hor⟩
        · exact (pb h).tail ⟨j, a, g, eq, hg, Or.inr ins, Or.inl hor⟩

lemma trace_true_iff_reachable (n : ℕ) (C : Circuit) (base d : ℕ → Bool)
    (wf : ∀ j (g : Gate), C.gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a < n + j ∧ b < n + j)
    (rec : ∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a, b] →
      (g.op = .and → d (n + j) = (base a && d b || d a && base b)) ∧
      (g.op = .or → d (n + j) = (d a || d b)))
    (start : ℕ) (hs : start < n) (init : ∀ k < n, d k = decide (k = start))
    (i : ℕ) (hi : i < n + C.gates.length) :
    d i = true ↔ Relation.ReflTransGen (activeStep n C base) start i := by
  constructor
  · exact true_trace_reachable n C base d wf rec start init i hi
  · exact trace_carries n C base d (fun j g h => (wf j g h).1) rec
      ((init start hs).trans (by simp))

lemma trace_unique (n : ℕ) (C : Circuit) (base d e : ℕ → Bool)
    (wf : ∀ j (g : Gate), C.gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a < n + j ∧ b < n + j)
    (rec : ∀ f ∈ [d, e], ∀ j (g : Gate) a b, C.gates[j]? = some g →
      g.inputs = [a, b] →
      (g.op = .and → f (n + j) = (base a && f b || f a && base b)) ∧
      (g.op = .or → f (n + j) = (f a || f b)))
    (start : ℕ) (hs : start < n)
    (init : ∀ f ∈ [d, e], ∀ k < n, f k = decide (k = start))
    (i : ℕ) (hi : i < n + C.gates.length) : d i = e i := by
  have hd := trace_true_iff_reachable n C base d wf (rec d (by simp)) start hs
    (init d (by simp)) i hi
  have he := trace_true_iff_reachable n C base e wf (rec e (by simp)) start hs
    (init e (by simp)) i hi
  have h := hd.trans he.symm
  cases hdi : d i <;> cases hei : e i <;> simp_all

end PEqualNP.Outside.L_meta_2602_aux
