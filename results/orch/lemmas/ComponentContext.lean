namespace component

def oldBoundaryLength (n : ℕ) (gs : List Gate) : ℕ :=
  n + 1 + (joinedBlock n gs).length

def newBoundaryLength (n : ℕ) (gs : List Gate) (outs : List ℕ) : ℕ :=
  n + 1 + (extractedBlock gs outs).length

def InterfaceRead (n : ℕ) (gs : List Gate) (outs : List ℕ) (rho : ℕ → ℕ) (i : ℕ) : Prop :=
  (i < n + 1 ∧ rho i = i) ∨
    ∃ j, ∃ hj : j < outs.length,
      i = n + 1 + outs[j] ∧ rho i = n + 1 + gs.length + j

def oldContext (n : ℕ) (gs tail : List Gate) (o : ℕ) : Circuit :=
  ⟨joinedBlock n gs ++ tail, o⟩

def extractedContext (n : ℕ) (gs : List Gate) (outs : List ℕ) (tail : List Gate)
    (rho : ℕ → ℕ) (o : ℕ) : Circuit :=
  let re := renameWire (oldBoundaryLength n gs) (newBoundaryLength n gs outs) rho
  ⟨extractedBlock gs outs ++ tail.map (renameGate re), re o⟩

lemma interface_values (n : ℕ) (gs : List Gate) (outs : List ℕ) (rho : ℕ → ℕ)
    (u : Bool) (x : List Bool) (hx : x.length = n)
    (hcore : ClosedCore n gs) (houts : ∀ i ∈ outs, i < n + gs.length)
    (i : ℕ) (hi : InterfaceRead n gs outs rho i) :
    rho i < (wf (extractedBlock gs outs) (u :: x)).length ∧
      (wf (extractedBlock gs outs) (u :: x)).getD (rho i) false =
        (wf (joinedBlock n gs) (u :: x)).getD i false := by
  subst n
  rcases hi with ⟨hi, hr⟩ | ⟨j, hj, hi, hr⟩
  · rw [hr]
    constructor
    · rw [wf_len]
      simp only [List.length_cons]
      omega
    · rw [wf_keep _ _ _ (by simpa using hi), wf_keep _ _ _ (by simpa using hi)]
  · rw [hr, hi]
    constructor
    · rw [wf_len, extractedBlock_length]
      simp only [List.length_cons]
      omega
    · exact component_output gs outs u x hcore houts j hj

lemma component_context_eval (n : ℕ) (gs : List Gate) (outs : List ℕ) (tail : List Gate)
    (rho : ℕ → ℕ) (o : ℕ) (hcore : ClosedCore n gs)
    (houts : ∀ i ∈ outs, i < n + gs.length)
    (hreads : ∀ g ∈ tail, ∀ i ∈ g.inputs, i < oldBoundaryLength n gs →
      InterfaceRead n gs outs rho i)
    (hout : o < oldBoundaryLength n gs → InterfaceRead n gs outs rho o)
    (u : Bool) (x : List Bool) (hx : x.length = n) :
    (extractedContext n gs outs tail rho o).eval (u :: x) =
      (oldContext n gs tail o).eval (u :: x) := by
  let old := wf (joinedBlock n gs) (u :: x)
  let new := wf (extractedBlock gs outs) (u :: x)
  have hold : old.length = oldBoundaryLength n gs := by
    simp [old, wf_len, hx, oldBoundaryLength]
  have hnew : new.length = newBoundaryLength n gs outs := by
    simp [new, wf_len, hx, newBoundaryLength]
  have hread : ∀ g ∈ tail, ∀ i ∈ g.inputs, i < old.length →
      rho i < new.length ∧ new.getD (rho i) false = old.getD i false := by
    intro g hg i hi hio
    exact interface_values n gs outs rho u x hx hcore houts i
      (hreads g hg i hi (by simpa [hold] using hio))
  have hout' : o < old.length →
      rho o < new.length ∧ new.getD (rho o) false = old.getD o false := by
    intro ho
    exact interface_values n gs outs rho u x hx hcore houts o (hout (by simpa [hold] using ho))
  have he := output_rename_prefix tail old new rho hread o hout'
  change (wf (extractedBlock gs outs ++ tail.map (renameGate
      (renameWire (oldBoundaryLength n gs) (newBoundaryLength n gs outs) rho))) (u :: x)).getD
      (renameWire (oldBoundaryLength n gs) (newBoundaryLength n gs outs) rho o) false =
    (wf (joinedBlock n gs ++ tail) (u :: x)).getD o false
  have happ (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := List.foldl_append
  rw [happ, happ]
  simpa only [hold, hnew] using he

lemma component_context_eval_list (n : ℕ) (gs : List Gate) (outs : List ℕ) (tail : List Gate)
    (rho : ℕ → ℕ) (o : ℕ) (hcore : ClosedCore n gs)
    (houts : ∀ i ∈ outs, i < n + gs.length)
    (hreads : ∀ g ∈ tail, ∀ i ∈ g.inputs, i < oldBoundaryLength n gs →
      InterfaceRead n gs outs rho i)
    (hout : o < oldBoundaryLength n gs → InterfaceRead n gs outs rho o)
    (z : List Bool) (hz : z.length = n + 1) :
    (extractedContext n gs outs tail rho o).eval z = (oldContext n gs tail o).eval z := by
  cases z with
  | nil => simp at hz
  | cons u x =>
    exact component_context_eval n gs outs tail rho o hcore houts hreads hout u x (by simpa using hz)

lemma component_context_function (n : ℕ) (gs : List Gate) (outs : List ℕ) (tail : List Gate)
    (rho : ℕ → ℕ) (o : ℕ) (hcore : ClosedCore n gs)
    (houts : ∀ i ∈ outs, i < n + gs.length)
    (hreads : ∀ g ∈ tail, ∀ i ∈ g.inputs, i < oldBoundaryLength n gs →
      InterfaceRead n gs outs rho i)
    (hout : o < oldBoundaryLength n gs → InterfaceRead n gs outs rho o) :
    PEqualNP.MetaComplexity.circuitFun (n + 1) (extractedContext n gs outs tail rho o) =
      PEqualNP.MetaComplexity.circuitFun (n + 1) (oldContext n gs tail o) := by
  funext x
  exact component_context_eval_list n gs outs tail rho o hcore houts hreads hout (List.ofFn x) (by simp)

lemma extractedContext_mono (n : ℕ) (gs : List Gate) (outs : List ℕ) (tail : List Gate)
    (rho : ℕ → ℕ) (o : ℕ)
    (hcore : PEqualNP.MetaComplexity.Monotone2 ⟨gs, 0⟩)
    (htail : PEqualNP.MetaComplexity.Monotone2 ⟨tail, 0⟩) :
    PEqualNP.MetaComplexity.Monotone2 (extractedContext n gs outs tail rho o) :=
  append_mono _ _ _ (extractedBlock_mono gs outs 0 hcore) (rename_mono tail _ 0 htail)

lemma context_gate_saving (n : ℕ) (gs : List Gate) (outs : List ℕ) (tail : List Gate)
    (rho : ℕ → ℕ) (o : ℕ) :
    (extractedContext n gs outs tail rho o).size + n =
      (oldContext n gs tail o).size + outs.length := by
  simp only [extractedContext, oldContext, Circuit.size, List.length_append, List.length_map,
    extractedBlock_length, joinedBlock_length]
  omega

lemma context_no_larger (n : ℕ) (gs : List Gate) (outs : List ℕ) (tail : List Gate)
    (rho : ℕ → ℕ) (o : ℕ) (hboundary : outs.length ≤ n) :
    (extractedContext n gs outs tail rho o).size ≤ (oldContext n gs tail o).size := by
  have := context_gate_saving n gs outs tail rho o
  omega

end component
