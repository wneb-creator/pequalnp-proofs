import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448.sharedContext

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wide (n u v p q : ℕ) : Circuit :=
  ⟨[⟨.and, [p,q]⟩, ⟨.or, [u,v]⟩, ⟨.and, [n,n+1]⟩], n+2⟩

def stars (n u v p q : ℕ) : Circuit :=
  ⟨[⟨.and, [u,p]⟩, ⟨.and, [v,q]⟩, ⟨.or, [n,n+1]⟩], n+2⟩

lemma block_identity (a b p q : Bool)
    (ha : a = true → q = true) (hb : b = true → p = true) :
    ((p && q) && (a || b)) = ((a && p) || (b && q)) := by
  cases a <;> cases b <;> cases p <;> cases q <;> simp_all

lemma read_append_left (w z : List Bool) (i : ℕ) (h : i < w.length) :
    (w ++ z).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma read_snoc_last (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma block_eval (w : List Bool) (u v p q : ℕ)
    (hu : u < w.length) (hv : v < w.length)
    (hp : p < w.length) (hq : q < w.length)
    (huq : w.getD u false = true → w.getD q false = true)
    (hvp : w.getD v false = true → w.getD p false = true) :
    (wide w.length u v p q).eval w = (stars w.length u v p q).eval w := by
  have ha : w[u] = true → w[q] = true := by
    simpa [List.getD_eq_getElem?_getD, hu, hq] using huq
  have hb : w[v] = true → w[p] = true := by
    simpa [List.getD_eq_getElem?_getD, hv, hp] using hvp
  simpa [wide, stars, Circuit.eval, Circuit.wires, GateOp.eval,
    List.getElem?_append_left hu, List.getElem?_append_left hv,
    List.getElem?_append_left hp, List.getElem?_append_left hq,
    hu, hv, hp, hq] using block_identity w[u] w[v] w[p] w[q] ha hb

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
  A.length = B.length ∧ m+1 < A.length ∧
    ∀ i, i ≠ m → i ≠ m+1 → A.getD i false = B.getD i false

lemma agree_append (m : ℕ) (A B : List Bool) (v : Bool) (h : Agree m A B) :
    Agree m (A ++ [v]) (B ++ [v]) := by
  obtain ⟨hlen, hlong, hread⟩ := h
  refine ⟨by simp [hlen], by simp; omega, ?_⟩
  intro i hi hi1
  by_cases hlt : i < A.length
  · rw [read_append_left _ _ _ hlt, read_append_left _ _ _ (by omega)]
    exact hread i hi hi1
  · by_cases he : i = A.length
    · subst i
      rw [read_snoc_last, hlen, read_snoc_last]
    · have ha : (A ++ [v]).length ≤ i := by simp; omega
      have hb : (B ++ [v]).length ≤ i := by simp; omega
      rw [List.getD_eq_default _ _ ha, List.getD_eq_default _ _ hb]

lemma agree_step (m : ℕ) (A B : List Bool) (g : Gate) (h : Agree m A B)
    (hread : m ∉ g.inputs ∧ m+1 ∉ g.inputs) :
    Agree m (step A g) (step B g) := by
  have hval : g.op.eval (g.inputs.map fun i => A.getD i false) =
      g.op.eval (g.inputs.map fun i => B.getD i false) := by
    congr 1
    apply List.map_congr_left
    intro i hi
    exact h.2.2 i (fun he => hread.1 (he ▸ hi)) (fun he => hread.2 (he ▸ hi))
  unfold step
  rw [← hval]
  exact agree_append m A B _ h

lemma agree_fold (m : ℕ) (A B : List Bool) (gs : List Gate) (h : Agree m A B)
    (hread : ∀ g ∈ gs, m ∉ g.inputs ∧ m+1 ∉ g.inputs) :
    Agree m (wf gs A) (wf gs B) := by
  induction gs generalizing A B with
  | nil => exact h
  | cons g gs ih =>
    change Agree m (wf gs (step A g)) (wf gs (step B g))
    exact ih _ _ (agree_step m A B g h (hread g List.mem_cons_self))
      (fun g hg => hread g (List.mem_cons_of_mem _ hg))

lemma initial_agree (w : List Bool) (u v p q : ℕ)
    (hu : u < w.length) (hv : v < w.length)
    (hp : p < w.length) (hq : q < w.length)
    (huq : w.getD u false = true → w.getD q false = true)
    (hvp : w.getD v false = true → w.getD p false = true) :
    Agree w.length (wf (wide w.length u v p q).gates w)
      (wf (stars w.length u v p q).gates w) := by
  have hL : (wf (wide w.length u v p q).gates w).length = w.length + 3 := by
    simp [wf_length, wide]
  have hL' : (wf (stars w.length u v p q).gates w).length = w.length + 3 := by
    simp [wf_length, stars]
  refine ⟨by omega, by omega, ?_⟩
  intro i hi hi1
  by_cases hlt : i < w.length
  · rw [wf_keep _ _ _ hlt, wf_keep _ _ _ hlt]
  · by_cases he : i = w.length+2
    · subst i
      exact block_eval w u v p q hu hv hp hq huq hvp
    · have hge : (wf (wide w.length u v p q).gates w).length ≤ i := by omega
      have hge' : (wf (stars w.length u v p q).gates w).length ≤ i := by omega
      rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ hge']

def oldCircuit (n : ℕ) (pre post : List Gate) (u v p q output : ℕ) : Circuit :=
  ⟨pre ++ (wide (n+pre.length) u v p q).gates ++ post, output⟩

def newCircuit (n : ℕ) (pre post : List Gate) (u v p q output : ℕ) : Circuit :=
  ⟨pre ++ (stars (n+pre.length) u v p q).gates ++ post, output⟩

lemma repair_fun (n : ℕ) (pre post : List Gate) (u v p q output : ℕ)
    (hu : u < n+pre.length) (hv : v < n+pre.length)
    (hp : p < n+pre.length) (hq : q < n+pre.length)
    (hcross : ∀ x : Fin n → Bool,
      ((wf pre (List.ofFn x)).getD u false = true →
        (wf pre (List.ofFn x)).getD q false = true) ∧
      ((wf pre (List.ofFn x)).getD v false = true →
        (wf pre (List.ofFn x)).getD p false = true))
    (hread : ∀ g ∈ post, n+pre.length ∉ g.inputs ∧ n+pre.length+1 ∉ g.inputs)
    (hout : output ≠ n+pre.length ∧ output ≠ n+pre.length+1) :
    circuitFun n (oldCircuit n pre post u v p q output) =
      circuitFun n (newCircuit n pre post u v p q output) := by
  funext x
  let w := wf pre (List.ofFn x)
  have hw : w.length = n+pre.length := by simp [w, wf_length]
  have hA : Agree (n+pre.length) (wf (wide (n+pre.length) u v p q).gates w)
      (wf (stars (n+pre.length) u v p q).gates w) := by
    rw [← hw]
    exact initial_agree w u v p q (by simpa [hw]) (by simpa [hw])
      (by simpa [hw]) (by simpa [hw]) (hcross x).1 (hcross x).2
  have hF := agree_fold (n+pre.length) _ _ post hA hread
  have result := hF.2.2 output hout.1 hout.2
  have hstep : step = (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
  simp only [wf, w, hstep] at result
  simpa only [circuitFun, Circuit.eval, Circuit.wires, oldCircuit, newCircuit,
    List.foldl_append] using result

lemma repair_mono (n : ℕ) (pre post : List Gate) (u v p q output : ℕ)
    (hm : Monotone2 (oldCircuit n pre post u v p q output)) :
    Monotone2 (newCircuit n pre post u v p q output) := by
  intro g hg
  change g ∈ pre ++ (stars (n+pre.length) u v p q).gates ++ post at hg
  rcases List.mem_append.mp hg with hg | hg
  · rcases List.mem_append.mp hg with hg | hg
    · exact hm g (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hg))))
    · have hs : Monotone2 (stars (n+pre.length) u v p q) := by simp [Monotone2, stars]
      exact hs g hg
  · exact hm g (List.mem_append.mpr (Or.inr hg))

lemma repair_size (n : ℕ) (pre post : List Gate) (u v p q output : ℕ) :
    (newCircuit n pre post u v p q output).size =
      (oldCircuit n pre post u v p q output).size := by
  simp [newCircuit, oldCircuit, stars, wide, Circuit.size]

lemma repair_minimal (n : ℕ) (pre post : List Gate) (u v p q output : ℕ)
    (hu : u < n+pre.length) (hv : v < n+pre.length)
    (hp : p < n+pre.length) (hq : q < n+pre.length)
    (hcross : ∀ x : Fin n → Bool,
      ((wf pre (List.ofFn x)).getD u false = true →
        (wf pre (List.ofFn x)).getD q false = true) ∧
      ((wf pre (List.ofFn x)).getD v false = true →
        (wf pre (List.ofFn x)).getD p false = true))
    (hread : ∀ g ∈ post, n+pre.length ∉ g.inputs ∧ n+pre.length+1 ∉ g.inputs)
    (hout : output ≠ n+pre.length ∧ output ≠ n+pre.length+1)
    (h : IsMinimalMonoCircuit n (oldCircuit n pre post u v p q output)) :
    IsMinimalMonoCircuit n (newCircuit n pre post u v p q output) := by
  refine ⟨repair_mono n pre post u v p q output h.1, ?_⟩
  intro D hD hfun
  rw [repair_size]
  exact h.2 D hD (hfun.trans
    (repair_fun n pre post u v p q output hu hv hp hq hcross hread hout).symm)

open PEqualNP.EdgeOwnership

lemma first_value (n : ℕ) (pre post : List Gate) (u v p q output : ℕ)
    (x : Fin n → Bool) :
    gateVal n (newCircuit n pre post u v p q output) pre.length x =
      ((wf pre (List.ofFn x)).getD u false &&
        (wf pre (List.ofFn x)).getD p false) := by
  let w := wf pre (List.ofFn x)
  have hw : w.length = n+pre.length := by simp [w, wf_length]
  simp only [gateVal, newCircuit, Circuit.wires, List.foldl_append]
  change (wf post (wf (stars (n+pre.length) u v p q).gates w)).getD
    (n+pre.length) false = _
  rw [wf_keep _ _ _ (by simp [wf_length, stars, hw])]
  change (wf [⟨.and, [v,q]⟩, ⟨.or, [n+pre.length,n+pre.length+1]⟩]
    (step w ⟨.and, [u,p]⟩)).getD (n+pre.length) false = _
  rw [wf_keep _ _ _ (by simp [step, hw])]
  rw [← hw]
  simp [step, GateOp.eval, read_snoc_last, w]

lemma second_value (n : ℕ) (pre post : List Gate) (u v p q output : ℕ)
    (hv : v < n+pre.length) (hq : q < n+pre.length) (x : Fin n → Bool) :
    gateVal n (newCircuit n pre post u v p q output) (pre.length+1) x =
      ((wf pre (List.ofFn x)).getD v false &&
        (wf pre (List.ofFn x)).getD q false) := by
  let w := wf pre (List.ofFn x)
  have hw : w.length = n+pre.length := by simp [w, wf_length]
  simp only [gateVal, newCircuit, Circuit.wires, List.foldl_append]
  change (wf post (wf (stars (n+pre.length) u v p q).gates w)).getD
    (n+(pre.length+1)) false = _
  rw [wf_keep _ _ _ (by simp [wf_length, stars, hw]; omega)]
  change (wf [⟨.or, [n+pre.length,n+pre.length+1]⟩]
    (step (step w ⟨.and, [u,p]⟩) ⟨.and, [v,q]⟩)).getD
      (n+(pre.length+1)) false = _
  rw [wf_keep _ _ _ (by simp [step, hw]; omega)]
  have hlen : (step w ⟨.and, [u,p]⟩).length = n+(pre.length+1) := by
    simp [step, hw, Nat.add_assoc]
  rw [← hlen]
  simp only [step, read_snoc_last, GateOp.eval, List.map_cons, List.map_nil,
    List.all_cons, List.all_nil, id, Bool.and_true]
  rw [read_append_left _ _ _ (by omega), read_append_left _ _ _ (by omega)]

lemma first_owns_star (n : ℕ) (pre post : List Gate) (u v p q output : ℕ)
    (hu : u < n) (a b : Fin n)
    (ho : Owns n (newCircuit n pre post u v p q output) pre.length a b) :
    a = ⟨u,hu⟩ ∨ b = ⟨u,hu⟩ := by
  have hval := ho.2.2.1
  rw [first_value] at hval
  simp only [Bool.and_eq_true] at hval
  have hinput := hval.1
  rw [wf_keep _ _ _ (by simpa using hu)] at hinput
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hu,
    dite_true, Option.getD_some, pairInput, decide_eq_true_eq] at hinput
  exact hinput.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)

lemma second_owns_star (n : ℕ) (pre post : List Gate) (u v p q output : ℕ)
    (hv : v < n) (hq : q < n+pre.length) (a b : Fin n)
    (ho : Owns n (newCircuit n pre post u v p q output) (pre.length+1) a b) :
    a = ⟨v,hv⟩ ∨ b = ⟨v,hv⟩ := by
  have hval := ho.2.2.1
  rw [second_value n pre post u v p q output (by omega) hq] at hval
  simp only [Bool.and_eq_true] at hval
  have hinput := hval.1
  rw [wf_keep _ _ _ (by simpa using hv)] at hinput
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hv,
    dite_true, Option.getD_some, pairInput, decide_eq_true_eq] at hinput
  exact hinput.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)

end PEqualNP.Outside.L_meta_2448.sharedContext

#print axioms PEqualNP.Outside.L_meta_2448.sharedContext.repair_minimal
#print axioms PEqualNP.Outside.L_meta_2448.sharedContext.first_owns_star
#print axioms PEqualNP.Outside.L_meta_2448.sharedContext.second_owns_star
