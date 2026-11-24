import PEqualNP.Outside.L_meta_3451

namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

-- Essential edges are those lost when the selected gate is replaced by false.
def lcKill (C : Circuit) (pre post : List Gate) : Circuit :=
  ⟨pre ++ ⟨GateOp.or, []⟩ :: post, C.output⟩

def lcOutputImproves (N : ℕ) (I : Fin N → Fin N → Prop) (C D : Circuit) : Prop :=
  Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size = C.size ∧
    (∀ z : Fin (N + N) → Bool, ∀ i,
      (D.wires (List.ofFn z)).getD i false = true →
      (C.wires (List.ofFn z)).getD i false = true) ∧
    (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)

lemma lcReplaceEq (n : ℕ) (C : Circuit) (pre post : List Gate) (g r : Gate)
    (hsplit : C.gates = pre ++ g :: post) (z : Fin n → Bool)
    (heq : r.op.eval (r.inputs.map fun i =>
        (pre.foldl decStep (List.ofFn z)).getD i false) =
      g.op.eval (g.inputs.map fun i =>
        (pre.foldl decStep (List.ofFn z)).getD i false)) :
    (⟨pre ++ r :: post, C.output⟩ : Circuit).wires (List.ofFn z) = C.wires (List.ofFn z) := by
  change (pre ++ r :: post).foldl decStep _ = C.gates.foldl decStep _
  rw [hsplit, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
  simp only [decStep, heq]

lemma lcKillBelow (n : ℕ) (C : Circuit) (pre post : List Gate) (r : Gate)
    (hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (z : Fin n → Bool) :
    ∀ i, ((lcKill C pre post).wires (List.ofFn z)).getD i false = true →
      ((⟨pre ++ r :: post, C.output⟩ : Circuit).wires (List.ofFn z)).getD i false = true := by
  change ∀ i, ((pre ++ ⟨GateOp.or, []⟩ :: post).foldl decStep _).getD i false = true →
    ((pre ++ r :: post).foldl decStep _).getD i false = true
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
  apply decFoldMono post hpost
  · simp [decStep]
  · apply lcSnocMono
    simp [GateOp.eval]

lemma lcReplacementOutput (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (pre post : List Gate) (g r : Gate) (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (hrop : r.op = GateOp.and ∨ r.op = GateOp.or) (hrsize : r.inputs.length ≤ 2)
    (hrread : ∀ a ∈ r.inputs, a < N + N + pre.length)
    (hrle : ∀ z : Fin (N + N) → Bool,
      r.op.eval (r.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) = true →
      g.op.eval (g.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) = true)
    (hreq : ∀ p l : Fin N, I p l →
      circuitFun (N + N) (⟨pre ++ r :: post, C.output⟩ : Circuit) (lcPair N p l) = true) :
    lcOutputImproves N I C ⟨pre ++ r :: post, C.output⟩ := by
  let D : Circuit := ⟨pre ++ r :: post, C.output⟩
  have hm : Monotone2 D := by
    intro a ha
    change a ∈ pre ++ r :: post at ha
    simp only [List.mem_append, List.mem_cons] at ha
    rcases ha with ha | rfl | ha
    · exact hmono a (by rw [hsplit]; simp [ha])
    · exact ⟨hrop, hrsize⟩
    · exact hmono a (by rw [hsplit]; simp [ha])
  have hr : ReadsBack (N + N) D := by
    intro k hk a ha
    by_cases he : k = pre.length
    · subst k
      have har : a ∈ r.inputs := by simpa [gateAt, D] using ha
      exact hrread a har
    · have hg := lcGetDReplace pre post g r ⟨GateOp.or, []⟩ k he
      have hak : a ∈ (gateAt C k).inputs := by
        change a ∈ ((pre ++ r :: post).getD k ⟨GateOp.or, []⟩).inputs at ha
        rw [hg] at ha
        simpa only [gateAt, hsplit] using ha
      exact hreads k (by simpa [hsplit, D] using hk) a hak
  have hle : ∀ z : Fin (N + N) → Bool, ∀ i,
      (D.wires (List.ofFn z)).getD i false = true → (C.wires (List.ofFn z)).getD i false = true := by
    intro z
    change ∀ i, ((pre ++ r :: post).foldl decStep (List.ofFn z)).getD i false = true →
      (C.gates.foldl decStep (List.ofFn z)).getD i false = true
    rw [hsplit, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
    apply decFoldMono post (fun a ha => (hmono a (by rw [hsplit]; simp [ha])).1)
    · simp [decStep]
    · exact lcSnocMono _ _ _ (hrle z)
  refine ⟨hm, hr, by simp [Circuit.size, hsplit], hle, ?_⟩
  apply lcPairCompleteness N I C D hfun hm (fun z => hle z C.output)
  intro p l hpl
  exact (hreq p l hpl).trans
    ((hfun _).mpr ⟨p, l, hpl, (lcPairTrue N p l).1, (lcPairTrue N p l).2⟩).symm

lemma lcEssentialAccepted (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (pre post : List Gate) (g : Gate) (hsplit : C.gates = pre ++ g :: post)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (p l : Fin N) (hI : I p l)
    (he : circuitFun (N + N) (lcKill C pre post) (lcPair N p l) = false) :
    (C.wires (List.ofFn (lcPair N p l))).getD (N + N + pre.length) false = true := by
  by_contra hn
  have hz := Bool.eq_false_iff.mpr hn
  rw [lcCircuitGate (N + N) C pre post g hsplit] at hz
  have heq := lcReplaceEq (N + N) C pre post g ⟨GateOp.or, []⟩ hsplit (lcPair N p l) hz.symm
  have hc := (hfun _).mpr ⟨p, l, hI, (lcPairTrue N p l).1, (lcPairTrue N p l).2⟩
  have hout := congrArg (fun w : List Bool => w.getD C.output false) heq
  change circuitFun (N + N) (lcKill C pre post) (lcPair N p l) =
    circuitFun (N + N) C (lcPair N p l) at hout
  rw [he, hc] at hout
  cases hout

lemma lcZeroEssential (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (pre post : List Gate) (g : Gate) (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (hnone : ∀ p l : Fin N, I p l →
      circuitFun (N + N) (lcKill C pre post) (lcPair N p l) = true) :
    ∃ D : Circuit, lcOutputImproves N I C D ∧
      (∀ k, k ≠ pre.length → gateAt D k = gateAt C k) ∧
      (gateAt D pre.length).op = GateOp.or ∧
      (∀ z : Fin (N + N) → Bool,
        (D.wires (List.ofFn z)).getD (N + N + pre.length) false = false) := by
  let r : Gate := ⟨GateOp.or, []⟩
  let D : Circuit := lcKill C pre post
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · exact lcReplacementOutput N I C pre post g r hsplit hmono hreads hfun (Or.inr rfl)
      (by simp [r]) (by simp [r]) (by simp [r, GateOp.eval]) hnone
  · exact mdReplacementShape C pre post g r hsplit
  · simp [gateAt, D, lcKill]
  · intro z
    rw [lcCircuitGate (N + N) D pre post r rfl]
    rfl

lemma lcOneEssential (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (pre post : List Gate) (g : Gate) (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (p0 l0 : Fin N) (hI : I p0 l0)
    (hessential : circuitFun (N + N) (lcKill C pre post) (lcPair N p0 l0) = false)
    (honly : ∀ p l : Fin N, I p l →
      circuitFun (N + N) (lcKill C pre post) (lcPair N p l) = false → p = p0 ∧ l = l0) :
    ∃ D : Circuit, lcOutputImproves N I C D ∧
      (∀ k, k ≠ pre.length → gateAt D k = gateAt C k) ∧
      (gateAt D pre.length).op = GateOp.and ∧
      (∀ z : Fin (N + N) → Bool,
        (D.wires (List.ofFn z)).getD (N + N + pre.length) false = true →
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
  have haccept := lcEssentialAccepted N I C pre post g hsplit hfun p0 l0 hI hessential
  let r : Gate := ⟨GateOp.and, [p0.val, N + l0.val]⟩
  let D : Circuit := ⟨pre ++ r :: post, C.output⟩
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · apply lcReplacementOutput N I C pre post g r hsplit hmono hreads hfun (Or.inl rfl)
    · simp [r]
    · intro a ha
      simp only [r, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> omega
    · intro z hz
      change GateOp.and.eval _ = true at hz
      rw [lcRawPairEval] at hz
      simp only [Bool.and_eq_true] at hz
      rw [← lcCircuitGate (N + N) C pre post g hsplit]
      exact decWireMono (N + N) C hmono _ z (lcPairLe N p0 l0 z hz.1 hz.2)
        (N + N + pre.length) haccept
    · intro p l hpl
      by_cases he : circuitFun (N + N) (lcKill C pre post) (lcPair N p l) = false
      · obtain ⟨hp, hl⟩ := honly p l hpl he
        subst p
        subst l
        have heq : r.op.eval (r.inputs.map fun i =>
            (pre.foldl decStep (List.ofFn (lcPair N p0 l0))).getD i false) =
            g.op.eval (g.inputs.map fun i =>
              (pre.foldl decStep (List.ofFn (lcPair N p0 l0))).getD i false) := by
          change GateOp.and.eval _ = _
          rw [lcRawPairEval, ← lcCircuitGate (N + N) C pre post g hsplit, haccept]
          simp only [(lcPairTrue N p0 l0).1, (lcPairTrue N p0 l0).2, Bool.true_and]
        have hw := lcReplaceEq (N + N) C pre post g r hsplit (lcPair N p0 l0) heq
        have hout := congrArg (fun w : List Bool => w.getD C.output false) hw
        exact hout.trans ((hfun _).mpr
          ⟨p0, l0, hI, (lcPairTrue N p0 l0).1, (lcPairTrue N p0 l0).2⟩)
      · have hz : circuitFun (N + N) (lcKill C pre post) (lcPair N p l) = true :=
          Bool.eq_true_of_ne_false he
        exact lcKillBelow (N + N) C pre post r
          (fun a ha => (hmono a (by rw [hsplit]; simp [ha])).1) _ C.output hz
  · exact mdReplacementShape C pre post g r hsplit
  · simp [gateAt, D, r]
  · intro z hz
    rw [lcCircuitGate (N + N) D pre post r rfl] at hz
    change GateOp.and.eval _ = true at hz
    rw [lcRawPairEval] at hz
    simp only [Bool.and_eq_true] at hz
    exact ⟨p0, l0, hI, hz.1, hz.2⟩

def lcEssential (N : ℕ) (C : Circuit) (j : ℕ) (p l : Fin N) : Prop :=
  circuitFun (N + N) (lcKill C (C.gates.take j) (C.gates.drop (j + 1))) (lcPair N p l) = false

lemma minimum_dirty_essential (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hmono : Monotone2 C) (hreads : ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, mdDirty N I D j →
        ∃ p l : Fin N, I p l ∧ lcEssential N D j p l ∧
          ∃ p' l' : Fin N, I p' l' ∧ lcEssential N D j p' l' ∧ (p ≠ p' ∨ l ≠ l')) := by
  classical
  let P : ℕ → Prop := fun k => ∃ D : Circuit,
    Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
    (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
    mdCount N I D = k
  have hex : ∃ k, P k := ⟨mdCount N I C, C, hmono, hreads, le_rfl, hfun, rfl⟩
  obtain ⟨D, hm, hr, hs, hf, hcount⟩ := Nat.find_spec hex
  have hmin (E : Circuit) (he : lcOutputImproves N I D E) : mdCount N I D ≤ mdCount N I E := by
    rw [hcount]
    obtain ⟨hem, her, hes, _, hef⟩ := he
    exact Nat.find_min' hex ⟨E, hem, her, hes ▸ hs, hef, rfl⟩
  refine ⟨D, hm, hr, hs, hf, ?_⟩
  intro j hj hdirty
  by_contra htwo
  let pre := D.gates.take j
  let post := D.gates.drop (j + 1)
  let g := gateAt D j
  have hpre : pre.length = j := List.length_take_of_le hj.le
  have hsplit : D.gates = pre ++ g :: post := by
    dsimp [pre, post, g, gateAt]
    rw [List.getD_eq_getElem _ _ hj]
    simp
  by_cases hsupport : ∃ p l : Fin N, I p l ∧ lcEssential N D j p l
  · obtain ⟨p0, l0, hI, haccept⟩ := hsupport
    have honly : ∀ p l : Fin N, I p l →
        circuitFun (N + N) (lcKill D pre post) (lcPair N p l) = false →
        p = p0 ∧ l = l0 := by
      intro p l hpl ht
      by_contra hne
      have hd : p0 ≠ p ∨ l0 ≠ l := by
        by_cases hp : p = p0
        · right
          intro hl
          exact hne ⟨hp, hl.symm⟩
        · exact Or.inl (Ne.symm hp)
      exact htwo ⟨p0, l0, hI, haccept, p, l, hpl, ht, hd⟩
    obtain ⟨E, he, hshape, _, hbelow⟩ := lcOneEssential N I D pre post g hsplit hm hr hf
      p0 l0 hI haccept honly
    have hclean := mdCleanFromBelow N I E pre.length hbelow
    have hdec := mdCountDecrease N I D E j hj he.2.2.1 he.2.2.2.1
      (by simpa only [hpre] using hshape) hdirty (by simpa only [hpre] using hclean)
    exact (Nat.not_lt_of_ge (hmin E he)) hdec
  · have hnone : ∀ p l : Fin N, I p l →
        circuitFun (N + N) (lcKill D pre post) (lcPair N p l) = true := by
      intro p l hpl
      apply Bool.eq_true_of_ne_false
      intro ht
      exact hsupport ⟨p, l, hpl, ht⟩
    obtain ⟨E, he, hshape, hor, _⟩ := lcZeroEssential N I D pre post g hsplit hm hr hf hnone
    have hclean : ¬ mdDirty N I E pre.length := by
      rintro ⟨hand, _⟩
      rw [hor] at hand
      cases hand
    have hdec := mdCountDecrease N I D E j hj he.2.2.1 he.2.2.2.1
      (by simpa only [hpre] using hshape) hdirty (by simpa only [hpre] using hclean)
    exact (Nat.not_lt_of_ge (hmin E he)) hdec

end PEqualNP.Outside.L_meta_3451
