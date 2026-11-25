import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448.keep_left

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wide (n s a b : ℕ) : Circuit :=
  ⟨[⟨.or, [s,a]⟩, ⟨.or, [s,b]⟩, ⟨.and, [n,n+1]⟩], n+2⟩

def kept (n s a b : ℕ) : Circuit :=
  ⟨[⟨.or, [s,a]⟩, ⟨.and, [a,b]⟩, ⟨.or, [s,n+1]⟩], n+2⟩

lemma read_append_left (w v : List Bool) (i : ℕ) (h : i < w.length) :
    (w ++ v).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma read_snoc_last (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma block_eval (w : List Bool) (s a b : ℕ)
    (hs : s < w.length) (ha : a < w.length) (hb : b < w.length) :
    (wide w.length s a b).eval w = (kept w.length s a b).eval w := by
  simp [wide, kept, Circuit.eval, Circuit.wires, GateOp.eval,
    List.getElem?_append_left hs, List.getElem?_append_left ha,
    List.getElem?_append_left hb, hs, ha, hb]
  cases w[s] <;> cases w[a] <;> cases w[b] <;> rfl

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wf (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

lemma wf_length (gs : List Gate) (w : List Bool) :
    (wf gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (wf gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

lemma wf_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wf gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (wf gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact read_append_left _ _ _ hi

def Agree (m : ℕ) (A B : List Bool) : Prop :=
  A.length = B.length ∧ m < A.length ∧
    ∀ i, i ≠ m → A.getD i false = B.getD i false

lemma agree_append (m : ℕ) (A B : List Bool) (v : Bool) (h : Agree m A B) :
    Agree m (A ++ [v]) (B ++ [v]) := by
  obtain ⟨hlen, hlong, hread⟩ := h
  refine ⟨by simp [hlen], by simp; omega, ?_⟩
  intro i hi
  by_cases hlt : i < A.length
  · rw [read_append_left _ _ _ hlt, read_append_left _ _ _ (by omega)]
    exact hread i hi
  · by_cases he : i = A.length
    · subst i
      rw [read_snoc_last, hlen, read_snoc_last]
    · have ha : (A ++ [v]).length ≤ i := by simp; omega
      have hb : (B ++ [v]).length ≤ i := by simp; omega
      rw [List.getD_eq_default _ _ ha, List.getD_eq_default _ _ hb]

lemma agree_step (m : ℕ) (A B : List Bool) (g : Gate) (h : Agree m A B)
    (hread : m ∉ g.inputs) : Agree m (step A g) (step B g) := by
  have hv : g.op.eval (g.inputs.map fun i => A.getD i false) =
      g.op.eval (g.inputs.map fun i => B.getD i false) := by
    congr 1
    apply List.map_congr_left
    intro i hi
    exact h.2.2 i (fun he => hread (he ▸ hi))
  unfold step
  rw [← hv]
  exact agree_append m A B _ h

lemma agree_fold (m : ℕ) (A B : List Bool) (gs : List Gate) (h : Agree m A B)
    (hread : ∀ g ∈ gs, m ∉ g.inputs) : Agree m (wf gs A) (wf gs B) := by
  induction gs generalizing A B with
  | nil => exact h
  | cons g gs ih =>
    change Agree m (wf gs (step A g)) (wf gs (step B g))
    exact ih _ _ (agree_step m A B g h (hread g List.mem_cons_self))
      (fun g hg => hread g (List.mem_cons_of_mem _ hg))

lemma initial_agree (w : List Bool) (s a b : ℕ)
    (hs : s < w.length) (ha : a < w.length) (hb : b < w.length) :
    Agree (w.length+1) (wf (wide w.length s a b).gates w)
      (wf (kept w.length s a b).gates w) := by
  have hL : (wf (wide w.length s a b).gates w).length = w.length + 3 := by
    simp [wf_length, wide]
  have hL' : (wf (kept w.length s a b).gates w).length = w.length + 3 := by
    simp [wf_length, kept]
  refine ⟨by omega, by omega, ?_⟩
  intro i hi
  by_cases hlt : i < w.length
  · rw [wf_keep _ _ _ hlt, wf_keep _ _ _ hlt]
  · by_cases he : i = w.length
    · subst i
      simp [wf, wide, kept, step, GateOp.eval, List.getElem?_append_left hs,
        List.getElem?_append_left ha, List.getElem?_append_left hb, hs, ha, hb]
    · by_cases he2 : i = w.length+2
      · subst i
        exact block_eval w s a b hs ha hb
      · have hge : (wf (wide w.length s a b).gates w).length ≤ i := by omega
        have hge' : (wf (kept w.length s a b).gates w).length ≤ i := by omega
        rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ hge']

def oldCircuit (n : ℕ) (pre post : List Gate) (s a b output : ℕ) : Circuit :=
  ⟨pre ++ (wide (n+pre.length) s a b).gates ++ post, output⟩

def newCircuit (n : ℕ) (pre post : List Gate) (s a b output : ℕ) : Circuit :=
  ⟨pre ++ (kept (n+pre.length) s a b).gates ++ post, output⟩

lemma repair_fun (n : ℕ) (pre post : List Gate) (s a b output : ℕ)
    (hs : s < n+pre.length) (ha : a < n+pre.length) (hb : b < n+pre.length)
    (hread : ∀ g ∈ post, n+pre.length+1 ∉ g.inputs)
    (hout : output ≠ n+pre.length+1) :
    circuitFun n (oldCircuit n pre post s a b output) =
      circuitFun n (newCircuit n pre post s a b output) := by
  funext x
  let w := wf pre (List.ofFn x)
  have hw : w.length = n+pre.length := by simp [w, wf_length]
  have hA : Agree (n+pre.length+1) (wf (wide (n+pre.length) s a b).gates w)
      (wf (kept (n+pre.length) s a b).gates w) := by
    rw [← hw]
    exact initial_agree w s a b (by simpa [hw]) (by simpa [hw]) (by simpa [hw])
  have hF := agree_fold (n+pre.length+1) _ _ post hA hread
  have result := hF.2.2 output hout
  have hstep : step = (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
  simp only [wf, w, hstep] at result
  simpa only [circuitFun, Circuit.eval, Circuit.wires, oldCircuit, newCircuit,
    List.foldl_append] using result

lemma repair_mono (n : ℕ) (pre post : List Gate) (s a b output : ℕ)
    (hm : Monotone2 (oldCircuit n pre post s a b output)) :
    Monotone2 (newCircuit n pre post s a b output) := by
  intro g hg
  change g ∈ pre ++ (kept (n+pre.length) s a b).gates ++ post at hg
  rcases List.mem_append.mp hg with hg | hp
  · rcases List.mem_append.mp hg with hp | hn
    · exact hm g (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hp))))
    · have hnarrow : Monotone2 (kept (n+pre.length) s a b) := by simp [Monotone2, kept]
      exact hnarrow g hn
  · exact hm g (List.mem_append.mpr (Or.inr hp))

lemma repair_size (n : ℕ) (pre post : List Gate) (s a b output : ℕ) :
    (newCircuit n pre post s a b output).size = (oldCircuit n pre post s a b output).size := by
  simp [newCircuit, oldCircuit, kept, wide, Circuit.size]

lemma repair_minimal (n : ℕ) (pre post : List Gate) (s a b output : ℕ)
    (hs : s < n+pre.length) (ha : a < n+pre.length) (hb : b < n+pre.length)
    (hread : ∀ g ∈ post, n+pre.length+1 ∉ g.inputs)
    (hout : output ≠ n+pre.length+1)
    (h : IsMinimalMonoCircuit n (oldCircuit n pre post s a b output)) :
    IsMinimalMonoCircuit n (newCircuit n pre post s a b output) := by
  refine ⟨repair_mono n pre post s a b output h.1, ?_⟩
  intro D hD hfun
  rw [repair_size]
  exact h.2 D hD (hfun.trans (repair_fun n pre post s a b output hs ha hb hread hout).symm)

end PEqualNP.Outside.L_meta_2448.keep_left
