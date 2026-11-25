import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1886_aux.InputRelabel

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wire (p : Fin 10 → Fin 10) (i : ℕ) : ℕ :=
  if h : i < 10 then (p ⟨i,h⟩).val else i

def gate (p : Fin 10 → Fin 10) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (wire p)⟩

def circuit (p : Fin 10 → Fin 10) (C : Circuit) : Circuit :=
  ⟨C.gates.map (gate p),wire p C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Related (p : Fin 10 → Fin 10) (old new : List Bool) : Prop :=
  10 ≤ old.length ∧ new.length = old.length ∧
    ∀ i : ℕ, new.getD (wire p i) false = old.getD i false

lemma related_step (p : Fin 10 → Fin 10) (old new : List Bool) (g : Gate)
    (h : Related p old new) : Related p (step old g) (step new (gate p g)) := by
  obtain ⟨h1,h2,h3⟩ := h
  have hv : (gate p g).op.eval ((gate p g).inputs.map fun i => new.getD i false) =
      g.op.eval (g.inputs.map fun i => old.getD i false) := by
    simp only [gate,List.map_map]
    congr 1
    exact List.map_congr_left (fun i _ => h3 i)
  refine ⟨by simp [step]; omega, by simp [step,h2],?_⟩
  intro i
  simp only [step,hv]
  rcases Nat.lt_trichotomy i old.length with hi | hi | hi
  · have mapped : wire p i < new.length := by
      unfold wire
      split
      · have := (p ⟨i,by assumption⟩).isLt
        omega
      · omega
    rw [List.getD_append _ _ _ _ mapped,List.getD_append _ _ _ _ hi]
    exact h3 i
  · have mapped : wire p i = new.length := by
      unfold wire
      split <;> omega
    rw [mapped,hi]
    simp
  · have mapped : new.length + 1 ≤ wire p i := by
      unfold wire
      split <;> omega
    rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]

lemma related_fold (p : Fin 10 → Fin 10) (gs : List Gate) :
    ∀ old new : List Bool, Related p old new →
      Related p (gs.foldl step old) ((gs.map (gate p)).foldl step new) := by
  induction gs with
  | nil => intro old new h; exact h
  | cons g gs ih =>
    intro old new h
    exact ih _ _ (related_step p old new g h)

lemma related_init (p : Fin 10 → Fin 10) (x : Fin 10 → Bool) (extra : List Bool) :
    Related p (List.ofFn (x ∘ p) ++ extra) (List.ofFn x ++ extra) := by
  refine ⟨by simp,by simp,?_⟩
  intro i
  unfold wire
  split
  · rename_i hi
    rw [List.getD_append _ _ _ _ (by simp),List.getD_append _ _ _ _ (by simpa using hi)]
    rw [List.getD_eq_getElem _ _ (by simp),List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_ofFn,Function.comp_apply]
  · rename_i hi
    rw [List.getD_append_right _ _ _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by simp; omega)]
    simp

lemma circuit_eval (p : Fin 10 → Fin 10) (C : Circuit) (x : Fin 10 → Bool) (extra : List Bool) :
    (circuit p C).eval (List.ofFn x ++ extra) = C.eval (List.ofFn (x ∘ p) ++ extra) := by
  exact (related_fold p C.gates _ _ (related_init p x extra)).2.2 C.output

lemma circuit_legal (p : Fin 10 → Fin 10) (C : Circuit) (h : FanInTwo C) :
    FanInTwo (circuit p C) := by
  intro g hg
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
  exact ⟨(h q hq).1,by simpa [gate] using (h q hq).2⟩

lemma circuit_mono (p : Fin 10 → Fin 10) (C : Circuit) (h : Monotone2 C) :
    Monotone2 (circuit p C) := by
  intro g hg
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
  exact ⟨(h q hq).1,by simpa [gate] using (h q hq).2⟩

lemma circuit_size (p : Fin 10 → Fin 10) (C : Circuit) : (circuit p C).size = C.size := by
  simp [circuit,Circuit.size]

lemma wire_fixed (p : Fin 10 → Fin 10) (i : ℕ) (h : 10 ≤ i) : wire p i = i := by
  simp [wire,Nat.not_lt.mpr h]

end PEqualNP.Outside.L_meta_1886_aux.InputRelabel
