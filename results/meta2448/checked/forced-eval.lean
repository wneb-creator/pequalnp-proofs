import ReaderDeletionCount

namespace PEqualNP.Outside.L_meta_2448_aux.ForcedEval

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2448_aux.ReaderDeletion
open PEqualNP.Outside.L_meta_2448_aux.ReaderDeletionCount

lemma wiresFrom_below (gs : List Gate) (hmono : ∀ g ∈ gs, MonoGate g)
    (w w' : List Bool) (hlen : w.length = w'.length) (hbelow : Below w w') :
    Below (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs generalizing w w' with
  | nil => exact hbelow
  | cons g gs ih =>
    exact ih (fun q hq => hmono q (List.mem_cons_of_mem _ hq))
      (step g w) (step g w') (by simpa [step] using hlen)
      (step_below g (hmono g List.mem_cons_self) w w' hlen hbelow)

lemma ofFn_below (n : Nat) (x y : Fin n → Bool)
    (hxy : ∀ v, x v = true → y v = true) : Below (List.ofFn x) (List.ofFn y) := by
  intro i hi
  by_cases h : i < n
  · simpa [h] using hxy ⟨i, h⟩ (by simpa [h] using hi)
  · simp [h] at hi

lemma snoc_below (w w' : List Bool) (b b' : Bool)
    (hlen : w.length = w'.length) (hw : Below w w') (hb : b = true → b' = true) :
    Below (w ++ [b]) (w' ++ [b']) := by
  intro i hi
  by_cases he : i = w.length
  · subst i
    rw [getD_snoc_eq] at hi
    rw [hlen, getD_snoc_eq]
    exact hb hi
  · rw [getD_snoc_ne _ _ _ _ he] at hi
    rw [getD_snoc_ne _ _ _ _ (by omega)]
    exact hw i hi

theorem forced_mono (n : Nat) (pre post : List Gate) (out : Nat)
    (hpre : ∀ g ∈ pre, MonoGate g) (hpost : ∀ g ∈ post, MonoGate g)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) :
    forcedEval n pre post out x = true → forcedEval n pre post out y = true := by
  have hlen : (wiresFrom pre (List.ofFn x)).length =
      (wiresFrom pre (List.ofFn y)).length := by simp [length_wiresFrom]
  have hp := wiresFrom_below pre hpre (List.ofFn x) (List.ofFn y)
    (by simp) (ofFn_below n x y hxy)
  have hs := snoc_below _ _ false false hlen hp (fun h => h)
  exact wiresFrom_below post hpost _ _ (by simpa using hlen) hs out

theorem forced_le (n : Nat) (C : Circuit) (pre post : List Gate) (g : Gate)
    (hC : C.gates = pre ++ g :: post) (hpost : ∀ q ∈ post, MonoGate q)
    (x : Fin n → Bool) :
    forcedEval n pre post C.output x = true → C.eval (List.ofFn x) = true := by
  let w := wiresFrom pre (List.ofFn x)
  have hb : Below (w ++ [false]) (step g w) :=
    snoc_below w w false _ rfl (fun _ h => h) (by simp)
  have hs := wiresFrom_below post hpost (w ++ [false]) (step g w)
    (by simp [step]) hb C.output
  intro hx
  change (wiresFrom C.gates (List.ofFn x)).getD C.output false = true
  rw [hC, wiresFrom_append]
  exact hs hx

theorem forced_eq_of_gate_false (n : Nat) (C : Circuit) (pre post : List Gate)
    (g : Gate) (hC : C.gates = pre ++ g :: post) (x : Fin n → Bool)
    (hg : g.op.eval (g.inputs.map fun i =>
      (wiresFrom pre (List.ofFn x)).getD i false) = false) :
    forcedEval n pre post C.output x = C.eval (List.ofFn x) := by
  change _ = (wiresFrom C.gates (List.ofFn x)).getD C.output false
  rw [hC, wiresFrom_append]
  change _ = (wiresFrom post (wiresFrom pre (List.ofFn x) ++
    [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)])).getD C.output false
  rw [hg]
  rfl

end PEqualNP.Outside.L_meta_2448_aux.ForcedEval
