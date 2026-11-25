import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448.matching

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wide (n p q a b c d : ℕ) : Circuit :=
  ⟨[⟨.and, [p,q]⟩, ⟨.or, [a,d]⟩, ⟨.or, [b,c]⟩,
    ⟨.and, [n+1,n+2]⟩, ⟨.and, [n,n+3]⟩], n+4⟩

def narrow (n a b c d : ℕ) : Circuit :=
  ⟨[⟨.and, [a,b]⟩, ⟨.and, [c,d]⟩, ⟨.or, [n,n+1]⟩], n+2⟩

lemma read_append_left (w v : List Bool) (i : ℕ) (h : i < w.length) :
    (w ++ v).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma read_snoc_last (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma matching_eval (w : List Bool) (p q a b c d : ℕ)
    (hp : p < w.length) (hq : q < w.length)
    (ha : a < w.length) (hb : b < w.length) (hc : c < w.length) (hd : d < w.length)
    (hP : w.getD p false = (w.getD a false || w.getD c false))
    (hQ : w.getD q false = (w.getD b false || w.getD d false)) :
    (wide w.length p q a b c d).eval w = (narrow w.length a b c d).eval w := by
  have hP' : w[p] = (w[a] || w[c]) := by
    simpa [List.getD_eq_getElem?_getD, hp, ha, hc] using hP
  have hQ' : w[q] = (w[b] || w[d]) := by
    simpa [List.getD_eq_getElem?_getD, hq, hb, hd] using hQ
  simp [wide, narrow, Circuit.eval, Circuit.wires, GateOp.eval,
    List.getElem?_append_left ha, List.getElem?_append_left hb,
    List.getElem?_append_left hc, List.getElem?_append_left hd,
    hp, hq, ha, hb, hc, hd, hP', hQ']
  cases w[a] <;> cases w[b] <;> cases w[c] <;> cases w[d] <;> rfl

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

def rew (m i : ℕ) : ℕ := if m+4 ≤ i then i-2 else i

def renGate (m : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rew m)⟩

def Agree (m : ℕ) (A B : List Bool) : Prop :=
  A.length = B.length + 2 ∧ m+4 < A.length ∧
    ∀ i, (i < m ∨ m+4 ≤ i) → A.getD i false = B.getD (rew m i) false

lemma agree_append (m : ℕ) (A B : List Bool) (v : Bool) (h : Agree m A B) :
    Agree m (A ++ [v]) (B ++ [v]) := by
  obtain ⟨hlen, hlong, hread⟩ := h
  refine ⟨by simp; omega, by simp; omega, ?_⟩
  intro i hi
  by_cases hlt : i < A.length
  · have hlt' : rew m i < B.length := by
      unfold rew
      split_ifs <;> omega
    rw [read_append_left _ _ _ hlt, read_append_left _ _ _ hlt']
    exact hread i hi
  · by_cases he : i = A.length
    · subst i
      have hr : rew m A.length = B.length := by
        simp only [rew, ite_eq_left (by omega : m + 4 ≤ A.length)]
        omega
      rw [hr, read_snoc_last, read_snoc_last]
    · have ha : (A ++ [v]).length ≤ i := by simp; omega
      have hb : (B ++ [v]).length ≤ rew m i := by
        simp only [List.length_append, List.length_singleton, rew]
        split_ifs <;> omega
      rw [List.getD_eq_default _ _ ha, List.getD_eq_default _ _ hb]

lemma agree_step (m : ℕ) (A B : List Bool) (g : Gate) (h : Agree m A B)
    (hread : ∀ i ∈ g.inputs, i < m ∨ m+4 ≤ i) :
    Agree m (step A g) (step B (renGate m g)) := by
  have hv : g.op.eval (g.inputs.map fun i => A.getD i false) =
      (renGate m g).op.eval ((renGate m g).inputs.map fun i => B.getD i false) := by
    simp only [renGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact h.2.2 i (hread i hi)
  unfold step
  rw [← hv]
  exact agree_append m A B _ h

lemma agree_fold (m : ℕ) (A B : List Bool) (gs : List Gate) (h : Agree m A B)
    (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i < m ∨ m+4 ≤ i) :
    Agree m (wf gs A) (wf (gs.map (renGate m)) B) := by
  induction gs generalizing A B with
  | nil => exact h
  | cons g gs ih =>
    change Agree m (wf gs (step A g)) (wf (gs.map (renGate m)) (step B (renGate m g)))
    exact ih _ _ (agree_step m A B g h (hread g List.mem_cons_self))
      (fun g hg => hread g (List.mem_cons_of_mem _ hg))

lemma initial_agree (w : List Bool) (p q a b c d : ℕ)
    (hp : p < w.length) (hq : q < w.length)
    (ha : a < w.length) (hb : b < w.length) (hc : c < w.length) (hd : d < w.length)
    (hP : w.getD p false = (w.getD a false || w.getD c false))
    (hQ : w.getD q false = (w.getD b false || w.getD d false)) :
    Agree w.length (wf (wide w.length p q a b c d).gates w)
      (wf (narrow w.length a b c d).gates w) := by
  have hL : (wf (wide w.length p q a b c d).gates w).length = w.length + 5 := by
    simp [wf_length, wide]
  have hL' : (wf (narrow w.length a b c d).gates w).length = w.length + 3 := by
    simp [wf_length, narrow]
  refine ⟨by omega, by omega, ?_⟩
  intro i hi
  by_cases hlt : i < w.length
  · have hr : rew w.length i = i := by simp [rew]; omega
    rw [hr, wf_keep _ _ _ hlt, wf_keep _ _ _ hlt]
  · by_cases he : i = w.length+4
    · subst i
      have hr : rew w.length (w.length+4) = w.length+2 := by simp [rew]
      rw [hr]
      exact matching_eval w p q a b c d hp hq ha hb hc hd hP hQ
    · have hge : (wf (wide w.length p q a b c d).gates w).length ≤ i := by omega
      have hge' : (wf (narrow w.length a b c d).gates w).length ≤ rew w.length i := by
        unfold rew
        split_ifs <;> omega
      rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ hge']


def oldCircuit (n : ℕ) (pre post : List Gate) (p q a b c d output : ℕ) : Circuit :=
  ⟨pre ++ (wide (n+pre.length) p q a b c d).gates ++ post, output⟩

def newCircuit (n : ℕ) (pre post : List Gate) (a b c d output : ℕ) : Circuit :=
  ⟨pre ++ (narrow (n+pre.length) a b c d).gates ++ post.map (renGate (n+pre.length)),
    rew (n+pre.length) output⟩

lemma repair_fun (n : ℕ) (pre post : List Gate) (p q a b c d output : ℕ)
    (hp : p < n+pre.length) (hq : q < n+pre.length)
    (ha : a < n+pre.length) (hb : b < n+pre.length) (hc : c < n+pre.length) (hd : d < n+pre.length)
    (hP : ∀ x : Fin n → Bool, let w := wf pre (List.ofFn x)
      w.getD p false = (w.getD a false || w.getD c false))
    (hQ : ∀ x : Fin n → Bool, let w := wf pre (List.ofFn x)
      w.getD q false = (w.getD b false || w.getD d false))
    (hread : ∀ g ∈ post, ∀ i ∈ g.inputs, i < n+pre.length ∨ n+pre.length+4 ≤ i)
    (hout : output < n+pre.length ∨ n+pre.length+4 ≤ output) :
    circuitFun n (oldCircuit n pre post p q a b c d output) =
      circuitFun n (newCircuit n pre post a b c d output) := by
  funext x
  let w := wf pre (List.ofFn x)
  have hw : w.length = n+pre.length := by simp [w, wf_length]
  have hA : Agree (n+pre.length) (wf (wide (n+pre.length) p q a b c d).gates w)
      (wf (narrow (n+pre.length) a b c d).gates w) := by
    rw [← hw]
    exact initial_agree w p q a b c d (by simpa [hw]) (by simpa [hw])
      (by simpa [hw]) (by simpa [hw]) (by simpa [hw]) (by simpa [hw]) (hP x) (hQ x)
  have hF := agree_fold (n+pre.length) _ _ post hA hread
  have result := hF.2.2 output hout
  have hstep : step = (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
  simp only [wf, w, hstep] at result
  simpa only [circuitFun, Circuit.eval, Circuit.wires, oldCircuit, newCircuit,
    List.foldl_append] using result

lemma repair_mono (n : ℕ) (pre post : List Gate) (p q a b c d output : ℕ)
    (hm : Monotone2 (oldCircuit n pre post p q a b c d output)) :
    Monotone2 (newCircuit n pre post a b c d output) := by
  intro g hg
  change g ∈ pre ++ (narrow (n+pre.length) a b c d).gates ++ post.map (renGate (n+pre.length)) at hg
  rcases List.mem_append.mp hg with hg | hg
  · rcases List.mem_append.mp hg with hp | hn
    · exact hm g (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hp))))
    · have hnarrow : Monotone2 (narrow (n+pre.length) a b c d) := by simp [Monotone2, narrow]
      exact hnarrow g hn
  · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    have h' := hm g' (List.mem_append.mpr (Or.inr hg'))
    simpa [renGate] using h'

lemma repair_size (n : ℕ) (pre post : List Gate) (p q a b c d output : ℕ) :
    (newCircuit n pre post a b c d output).size + 2 =
      (oldCircuit n pre post p q a b c d output).size := by
  simp [newCircuit, oldCircuit, narrow, wide, Circuit.size]
  omega

lemma not_minimal_matching (n : ℕ) (pre post : List Gate) (p q a b c d output : ℕ)
    (hp : p < n+pre.length) (hq : q < n+pre.length)
    (ha : a < n+pre.length) (hb : b < n+pre.length) (hc : c < n+pre.length) (hd : d < n+pre.length)
    (hP : ∀ x : Fin n → Bool, let w := wf pre (List.ofFn x)
      w.getD p false = (w.getD a false || w.getD c false))
    (hQ : ∀ x : Fin n → Bool, let w := wf pre (List.ofFn x)
      w.getD q false = (w.getD b false || w.getD d false))
    (hread : ∀ g ∈ post, ∀ i ∈ g.inputs, i < n+pre.length ∨ n+pre.length+4 ≤ i)
    (hout : output < n+pre.length ∨ n+pre.length+4 ≤ output) :
    ¬ IsMinimalMonoCircuit n (oldCircuit n pre post p q a b c d output) := by
  intro h
  have hsize := h.2 (newCircuit n pre post a b c d output)
    (repair_mono n pre post p q a b c d output h.1)
    (repair_fun n pre post p q a b c d output hp hq ha hb hc hd hP hQ hread hout).symm
  have he := repair_size n pre post p q a b c d output
  omega

end PEqualNP.Outside.L_meta_2448.matching
