import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884.Semantic
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def neighbor (i : Fin 10) : Fin 10 :=
  ([1,0,1,2,3,7,9,5,6,7] : List (Fin 10)).getD i.val 0

def lowProbe (i : Fin 10) : Fin 10 → Bool := fun v => decide (v=neighbor i)
def highProbe (i : Fin 10) : Fin 10 → Bool := fun v => decide (v=neighbor i ∨ v=i)

lemma probe_values : ∀ i : Fin 10, target (lowProbe i)=false ∧ target (highProbe i)=true := by
  decide +kernel

lemma probe_agreement (i v : Fin 10) (h : v≠i) : lowProbe i v=highProbe i v := by
  simp [lowProbe,highProbe,h]

lemma map_covers_nonzero (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (hcompute : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)])=target x) :
    ∀ i : Fin 10,i≠0 → ∃ j,σ j=i := by
  intro i hi
  by_contra hn
  have hmap : ∀ j,σ j≠i := by simpa using hn
  have hfn : lowProbe i ∘ σ=highProbe i ∘ σ := by
    funext j
    exact probe_agreement i (σ j) (hmap j)
  have h0 := probe_agreement i 0 (Ne.symm hi)
  have he : C.eval (List.ofFn (lowProbe i ∘ σ) ++ [u (lowProbe i 0)]) =
      C.eval (List.ofFn (highProbe i ∘ σ) ++ [u (highProbe i 0)]) := by rw [hfn,h0]
  rw [hcompute,hcompute,(probe_values i).1,(probe_values i).2] at he
  cases he

lemma map_surjective_or_missing_zero (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (hcompute : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)])=target x) :
    Function.Surjective σ ∨ ∀ j,σ j≠0 := by
  by_cases hz : ∃ j,σ j=0
  · left
    intro i
    by_cases hi : i=0
    · simpa [hi] using hz
    · exact map_covers_nonzero C σ u hcompute i hi
  · right
    simpa using hz

lemma missing_zero_unary_nonconstant (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (hcompute : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)])=target x)
    (hmissing : ∀ j,σ j≠0) : u false≠u true := by
  intro hu
  have hfn : lowProbe 0 ∘ σ=highProbe 0 ∘ σ := by
    funext j
    exact probe_agreement 0 (σ j) (hmissing j)
  have hlo : lowProbe 0 0=false := by decide
  have hhi : highProbe 0 0=true := by decide
  have he : C.eval (List.ofFn (lowProbe 0 ∘ σ) ++ [u (lowProbe 0 0)]) =
      C.eval (List.ofFn (highProbe 0 ∘ σ) ++ [u (highProbe 0 0)]) := by
    rw [hfn,hlo,hhi,hu]
  rw [hcompute,hcompute,(probe_values 0).1,(probe_values 0).2] at he
  cases he

lemma nonconstant_unary (u : Bool → Bool) (h : u false≠u true) :
    u=id ∨ u=Bool.not := by
  cases h0 : u false <;> cases h1 : u true
  · exact (h (h0.trans h1.symm)).elim
  · left
    funext b
    cases b <;> assumption
  · right
    funext b
    cases b <;> assumption
  · exact (h (h0.trans h1.symm)).elim

lemma input_classification (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (hcompute : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)])=target x) :
    Function.Surjective σ ∨ ((∀ j,σ j≠0) ∧ (u=id ∨ u=Bool.not)) := by
  rcases map_surjective_or_missing_zero C σ u hcompute with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h,nonconstant_unary u (missing_zero_unary_nonconstant C σ u hcompute h)⟩

-- The two-run invariant below is adapted from the checked L_meta_7312.
def Rd (x2 : Gate) (x3 : ℕ) : Prop :=
  x2.op = GateOp.not ∧ x2.inputs.head? = Option.some x3 ∨ x2.op ≠ GateOp.not ∧ x3 ∈ x2.inputs

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

theorem getD_big (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_lt (l : List Bool) (a : Bool) (i : ℕ) (h : i < l.length) :
    (l ++ [a]).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_new (l : List Bool) (a : Bool) : (l ++ [a]).getD l.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem len_stp (w : List Bool) (g : Gate) : (stp w g).length = w.length + 1 := by
  simp [stp]

theorem getD_foldl (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl stp w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i h
    rw [List.foldl_cons, ih _ _ (by rw [len_stp]; omega)]
    exact getD_lt _ _ _ h

theorem mono_all (l : List ℕ) (fu fv : ℕ → Bool) (h : ∀ i ∈ l, fu i = true ∨ fv i = false) :
    (l.map fu).all id = true ∨ (l.map fv).all id = false := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.all_cons, id]
    rcases h a (by simp) with h1 | h1 <;>
      rcases ih (fun i hi => h i (by simp [hi])) with h2 | h2 <;> simp [h1, h2]

theorem mono_any (l : List ℕ) (fu fv : ℕ → Bool) (h : ∀ i ∈ l, fu i = true ∨ fv i = false) :
    (l.map fu).any id = true ∨ (l.map fv).any id = false := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, id]
    rcases h a (by simp) with h1 | h1 <;>
      rcases ih (fun i hi => h i (by simp [hi])) with h2 | h2 <;> simp [h1, h2]

theorem inv2 (gs : List Gate) : ∀ u v : List Bool, u.length = v.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
    (∀ g ∈ gs, ¬ Rd g 0) →
    (∀ i, i ≠ 0 → (u.getD i false = true ∨ v.getD i false = false)) →
    (∀ j, j < gs.length → ∀ g, gs[j]? = some g → g.op = GateOp.not →
      ¬((gs.foldl stp u).getD (u.length + j) false = false ∧
        (gs.foldl stp v).getD (u.length + j) false = true)) →
    ∀ i, i ≠ 0 → ((gs.foldl stp u).getD i false = true ∨ (gs.foldl stp v).getD i false = false) := by
  induction gs with
  | nil => intro u v _ _ _ h _; simpa using h
  | cons g gs ih =>
    intro u v hl hop hrd hinv hnot
    simp only [List.foldl_cons]
    have eu : (stp u g).getD u.length false =
        g.op.eval (g.inputs.map fun i => u.getD i false) := getD_new _ _
    have ev : (stp v g).getD u.length false =
        g.op.eval (g.inputs.map fun i => v.getD i false) := by rw [hl]; exact getD_new _ _
    apply ih (stp u g) (stp v g) (by rw [len_stp, len_stp, hl])
      (fun g' hg' => hop g' (by simp [hg'])) (fun g' hg' => hrd g' (by simp [hg']))
    · intro i hi
      rcases lt_trichotomy i u.length with h | h | h
      · have hv : i < v.length := hl ▸ h
        rw [stp, stp, getD_lt _ _ _ h, getD_lt _ _ _ hv]
        exact hinv i hi
      · subst h
        rw [eu, ev]
        rcases hop g (by simp) with ho | ho | ho
        · rw [ho]; simp only [GateOp.eval]
          apply mono_all
          intro k hk
          apply hinv
          rintro rfl
          exact hrd g (by simp) (Or.inr ⟨(by rw [ho]; intro hh; cases hh), hk⟩)
        · rw [ho]; simp only [GateOp.eval]
          apply mono_any
          intro k hk
          apply hinv
          rintro rfl
          exact hrd g (by simp) (Or.inr ⟨(by rw [ho]; intro hh; cases hh), hk⟩)
        · have := hnot 0 (by simp) g (by simp) ho
          simp only [List.foldl_cons, Nat.add_zero] at this
          rw [getD_foldl _ _ _ (by rw [len_stp]; omega),
            getD_foldl _ _ _ (by rw [len_stp]; omega), eu, ev] at this
          revert this
          cases g.op.eval (g.inputs.map fun i => u.getD i false) <;>
            cases g.op.eval (g.inputs.map fun i => v.getD i false) <;> simp
      · right
        apply getD_big
        rw [len_stp]; omega
    · intro j hj g' hg' ho
      have := hnot (j + 1) (by simp; omega) g' (by simpa using hg') ho
      simp only [List.foldl_cons] at this
      rw [len_stp, show u.length + 1 + j = u.length + (j + 1) by omega]
      exact this


def pairLow (k : Fin 10) : Fin 10 → Bool := fun i => decide (i=k)
def pairHigh (k : Fin 10) : Fin 10 → Bool := fun i => decide (i=k ∨ i=0)
def pairInput (k : Fin 10) (b : Bool) : List Bool :=
  let x := if b then pairHigh k else pairLow k
  List.ofFn x ++ [!x 0]

lemma pairInput_length (k : Fin 10) (b : Bool) : (pairInput k b).length=11 := by
  simp [pairInput]

lemma pairs_target : ∀ k : Fin 10,k∈([1,4,5] : List (Fin 10)) →
    target (pairLow k)=false ∧ target (pairHigh k)=true := by decide +kernel

lemma pairInput_order : ∀ k : Fin 10,k∈([1,4,5] : List (Fin 10)) →
    ∀ i : Fin 11,i.val≠0 →
    (pairInput k false).getD i.val false=true ∨ (pairInput k true).getD i.val false=false := by
  decide +kernel

lemma unique_not_flips (C : Circuit) (hfan : FanInTwo C)
    (hcompute : ∀ x : Fin 10 → Bool,C.eval (List.ofFn x ++ [!x 0])=target x)
    (hno : ∀ g∈C.gates,¬Rd g 0)
    (jnot : Fin C.gates.length)
    (hunique : ∀ j : Fin C.gates.length,(C.gates.get j).op=GateOp.not → j=jnot)
    (k : Fin 10) (hk : k∈([1,4,5] : List (Fin 10))) :
    (C.wires (pairInput k false)).getD (11+jnot.val) false=false ∧
    (C.wires (pairInput k true)).getD (11+jnot.val) false=true := by
  have hop : ∀ g∈C.gates,g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not := by
    intro g hg
    simpa using (hfan g hg).1
  have hlo : C.eval (pairInput k false)=false := by
    change C.eval (List.ofFn (pairLow k) ++ [!pairLow k 0])=false
    rw [hcompute,(pairs_target k hk).1]
  have hhi : C.eval (pairInput k true)=true := by
    change C.eval (List.ofFn (pairHigh k) ++ [!pairHigh k 0])=true
    rw [hcompute,(pairs_target k hk).2]
  have hout : C.output≠0 := by
    intro h
    have hv := hcompute (fun i => decide (i=0))
    rw [Circuit.eval,wires_eq,h,getD_foldl _ _ _ (by simp)] at hv
    have htrue : (List.ofFn (fun i : Fin 10 => decide (i=0)) ++ [!decide ((0 : Fin 10)=0)]).getD 0 false=true := by decide
    rw [htrue] at hv
    have hfalse : target (fun i : Fin 10 => decide (i=0))=false := by decide
    rw [hfalse] at hv
    cases hv
  by_contra hflip
  have hinv : ∀ i : ℕ,i≠0 →
      (pairInput k false).getD i false=true ∨ (pairInput k true).getD i false=false := by
    intro i hi
    by_cases hlt : i<11
    · exact pairInput_order k hk ⟨i,hlt⟩ hi
    · right
      exact getD_big _ i (by rw [pairInput_length];omega)
  have hnot : ∀ j,j<C.gates.length → ∀ g,C.gates[j]?=some g → g.op=GateOp.not →
      ¬((C.gates.foldl stp (pairInput k false)).getD ((pairInput k false).length+j) false=false ∧
        (C.gates.foldl stp (pairInput k true)).getD ((pairInput k false).length+j) false=true) := by
    intro j hj g hg hgn hfl
    have hget : C.gates.get ⟨j,hj⟩=g := by
      rw [List.get_eq_getElem]
      simpa only [List.getElem?_eq_getElem hj,Option.some.injEq] using hg
    have heq := hunique ⟨j,hj⟩ (by rw [hget];exact hgn)
    have hv : j=jnot.val := congrArg Fin.val heq
    apply hflip
    simpa [wires_eq,pairInput_length,hv] using hfl
  have hfinal := inv2 C.gates (pairInput k false) (pairInput k true)
    (by rw [pairInput_length,pairInput_length]) hop hno hinv hnot C.output hout
  change C.eval (pairInput k false)=true ∨ C.eval (pairInput k true)=false at hfinal
  rw [hlo,hhi] at hfinal
  simp at hfinal

end PEqualNP.Outside.L_meta_1884.Semantic
