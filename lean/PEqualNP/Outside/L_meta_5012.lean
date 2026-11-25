import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_5012

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

abbrev matching : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun u v => u.val + v.val = 3

def nestedCircuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 5]⟩,
    ⟨.or, [0, 2]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [1, 3]⟩,
    ⟨.and, [8, 9]⟩], 10⟩

def directCircuit : Circuit :=
  ⟨[⟨.and, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩], 6⟩

def promotedCircuit : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [4, 5]⟩,
    ⟨.or, [1, 3]⟩, ⟨.and, [6, 7]⟩], 8⟩

lemma matching_bipartite :
    ∀ u v : Fin 4, matching.Adj u v →
      decide (u.val < 2) ≠ decide (v.val < 2) := by decide

lemma matching_noFourCycle : NoFourCycle matching := by decide

lemma nested_ao : IsAO2 4 nestedCircuit := by decide

lemma nested_computes : circuitFun 4 nestedCircuit = graphFun matching ∅ := by
  funext x
  have h : ∀ x : Fin 4 → Bool,
      circuitFun 4 nestedCircuit x = graphFun matching ∅ x := by decide
  exact h x

lemma nested_top : TopForm matching nestedCircuit := by decide

lemma nested_two_junk : junk matching nestedCircuit = {2, 4} := by decide

lemma direct_ao : IsAO2 4 directCircuit := by decide

lemma direct_computes : circuitFun 4 directCircuit = graphFun matching ∅ := by
  funext x
  have h : ∀ x : Fin 4 → Bool,
      circuitFun 4 directCircuit x = graphFun matching ∅ x := by decide
  exact h x

lemma nested_not_least : ¬ IsLeastAO matching nestedCircuit := by
  intro h
  have hs := h.2.2 directCircuit direct_ao direct_computes
  change 7 ≤ 3 at hs
  omega

lemma promoted_ao : IsAO2 5 promotedCircuit := by decide

lemma promoted_pairs_false : ∀ u v : Fin 5,
    circuitFun 5 promotedCircuit (pairInput u v) = false := by decide

lemma promoted_all_true :
    circuitFun 5 promotedCircuit (fun _ => true) = true := by decide

lemma graphFun_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma promoted_not_graph (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] :
    circuitFun 5 promotedCircuit ≠ graphFun G ∅ := by
  intro h
  have ht : graphFun G ∅ (fun _ => true) = true := by
    rw [← h]
    exact promoted_all_true
  obtain ⟨u, v, huv, _, _⟩ := (graphFun_iff G _).1 ht
  have hp : graphFun G ∅ (pairInput u v) = true :=
    (graphFun_iff G _).2 ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
  rw [← h, promoted_pairs_false] at hp
  cases hp

lemma promoted_substitute : ∀ x : Fin 4 → Bool,
    circuitFun 5 promotedCircuit
      (Fin.lastCases (gateVal 4 nestedCircuit 2 x) x) =
      circuitFun 4 nestedCircuit x := by decide

lemma least_of_extension_budget {n m : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    (C D : Circuit) (k : ℕ) (hC : IsLeastAO G C)
    (hD : IsAO2 m D) (hfun : circuitFun m D = graphFun H ∅)
    (hbudget : D.size + k = C.size)
    (hlift : ∀ E : Circuit, IsAO2 m E → circuitFun m E = graphFun H ∅ →
      ∃ E' : Circuit, IsAO2 n E' ∧ circuitFun n E' = graphFun G ∅ ∧
        E'.size ≤ E.size + k) : IsLeastAO H D := by
  refine ⟨hD, hfun, ?_⟩
  intro E hE hEF
  obtain ⟨E', hE', hEF', hs⟩ := hlift E hE hEF
  have hmin := hC.2.2 E' hE' hEF'
  omega

end PEqualNP.Outside.L_meta_5012

namespace PEqualNP.Outside.L_meta_5012.OneOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

abbrev BF (n : ℕ) := (Fin n → Bool) → Bool

def mono {n : ℕ} (S : Finset (Option (Fin n))) : BF n :=
  fun x => decide (∀ i ∈ S, i.elim false x = true)

def Pure {n : ℕ} (f : BF n) : Prop := ∃ S, f = mono S

def Two {n : ℕ} (f : BF n) : Prop :=
  ∃ S T : Finset (Option (Fin n)), f = fun x => mono S x || mono T x

def Ext {n : ℕ} (z f : BF n) : Prop :=
  ∃ S : Finset (Option (Fin n)), ∃ b : Bool,
    f = fun x => mono S x && (if b then z x else true)

lemma mono_union {n : ℕ} (S T : Finset (Option (Fin n))) :
    mono (S ∪ T) = fun x => mono S x && mono T x := by
  funext x
  simp [mono, Finset.mem_union, or_imp, forall_and]

lemma pure_false {n : ℕ} : Pure (n := n) (fun _ => false) := by
  refine ⟨{none}, ?_⟩
  funext x
  simp [mono]

lemma pure_input {n : ℕ} (i : Fin n) : Pure (fun x => x i) := by
  refine ⟨{some i}, ?_⟩
  funext x
  simp [mono]

lemma pure_and {n : ℕ} {f g : BF n} (hf : Pure f) (hg : Pure g) :
    Pure (fun x => f x && g x) := by
  obtain ⟨S, rfl⟩ := hf
  obtain ⟨T, rfl⟩ := hg
  exact ⟨S ∪ T, (mono_union S T).symm⟩

lemma pure_two {n : ℕ} {f : BF n} (hf : Pure f) : Two f := by
  obtain ⟨S, rfl⟩ := hf
  exact ⟨S, S, by simp⟩

lemma pure_ext {n : ℕ} (z : BF n) {f : BF n} (hf : Pure f) : Ext z f := by
  obtain ⟨S, rfl⟩ := hf
  exact ⟨S, false, by simp⟩

lemma ext_self {n : ℕ} (z : BF n) : Ext z z := by
  exact ⟨∅, true, by simp [mono]⟩

lemma ext_and {n : ℕ} {z f g : BF n} (hf : Ext z f) (hg : Ext z g) :
    Ext z (fun x => f x && g x) := by
  obtain ⟨S, b, rfl⟩ := hf
  obtain ⟨T, c, rfl⟩ := hg
  refine ⟨S ∪ T, b || c, ?_⟩
  rw [mono_union]
  funext x
  dsimp only
  cases b <;> cases c <;> cases mono S x <;> cases mono T x <;> cases z x <;> rfl

lemma ext_two {n : ℕ} {z f : BF n} (hz : Two z) (hf : Ext z f) : Two f := by
  obtain ⟨A, B, rfl⟩ := hz
  obtain ⟨S, b, rfl⟩ := hf
  cases b
  · exact pure_two ⟨S, by simp⟩
  · refine ⟨S ∪ A, S ∪ B, ?_⟩
    rw [mono_union, mono_union]
    funext x
    dsimp only
    cases mono S x <;> cases mono A x <;> cases mono B x <;> rfl

def step {n : ℕ} (ws : List (BF n)) (g : Gate) : List (BF n) :=
  ws ++ [fun x => g.op.eval (g.inputs.map fun i => (ws.getD i (fun _ => false)) x)]

def vals {n : ℕ} (gs : List Gate) (ws : List (BF n)) : List (BF n) :=
  gs.foldl step ws

lemma getD_property {α : Type} (P : α → Prop) (d : α) (hd : P d)
    (ws : List α) (hw : ∀ f ∈ ws, P f) (i : ℕ) : P (ws.getD i d) := by
  induction ws generalizing i with
  | nil => simpa using hd
  | cons f fs ih =>
    cases i with
    | zero => exact hw f (by simp)
    | succ i => exact ih (fun g hg => hw g (by simp [hg])) i

lemma step_closed {n : ℕ} (P : BF n → Prop)
    (hfalse : P (fun _ => false))
    (hand : ∀ f g, P f → P g → P (fun x => f x && g x))
    (ws : List (BF n)) (hw : ∀ f ∈ ws, P f)
    (g : Gate) (hop : g.op = .and) (hlen : g.inputs.length = 2) :
    ∀ f ∈ step ws g, P f := by
  obtain ⟨op, ins⟩ := g
  dsimp at hop hlen
  subst op
  obtain ⟨a, b, rfl⟩ : ∃ a b, ins = [a,b] := by
    cases ins with
    | nil => simp at hlen
    | cons a ins =>
      cases ins with
      | nil => simp at hlen
      | cons b ins =>
        have hi : ins = [] := by simpa using hlen
        subst ins
        exact ⟨a, b, rfl⟩
  intro f hf
  simp only [step, List.mem_append, List.mem_singleton] at hf
  rcases hf with hf | rfl
  · exact hw f hf
  · simpa [GateOp.eval] using hand (ws.getD a (fun _ => false))
      (ws.getD b (fun _ => false)) (getD_property P _ hfalse ws hw a)
      (getD_property P _ hfalse ws hw b)

lemma vals_closed {n : ℕ} (P : BF n → Prop)
    (hfalse : P (fun _ => false))
    (hand : ∀ f g, P f → P g → P (fun x => f x && g x))
    (gs : List Gate) (hg : ∀ g ∈ gs, g.op = .and ∧ g.inputs.length = 2)
    (ws : List (BF n)) (hw : ∀ f ∈ ws, P f) : ∀ f ∈ vals gs ws, P f := by
  induction gs generalizing ws with
  | nil => exact hw
  | cons g gs ih =>
    exact ih (fun k hk => hg k (by simp [hk])) (step ws g)
      (step_closed P hfalse hand ws hw g (hg g (by simp)).1 (hg g (by simp)).2)

lemma step_or {n : ℕ} (ws : List (BF n)) (hw : ∀ f ∈ ws, Pure f)
    (g : Gate) (hop : g.op = .or) (hlen : g.inputs.length = 2) :
    ∃ z : BF n, Two z ∧ ∀ f ∈ step ws g, Ext z f := by
  obtain ⟨op, ins⟩ := g
  dsimp at hop hlen
  subst op
  obtain ⟨a, b, rfl⟩ : ∃ a b, ins = [a,b] := by
    cases ins with
    | nil => simp at hlen
    | cons a ins =>
      cases ins with
      | nil => simp at hlen
      | cons b ins =>
        have hi : ins = [] := by simpa using hlen
        subst ins
        exact ⟨a, b, rfl⟩
  obtain ⟨S, hS⟩ := getD_property Pure _ pure_false ws hw a
  obtain ⟨T, hT⟩ := getD_property Pure _ pure_false ws hw b
  let z : BF n := fun x => mono S x || mono T x
  refine ⟨z, ⟨S, T, rfl⟩, ?_⟩
  intro f hf
  simp only [step, List.mem_append, List.mem_singleton] at hf
  rcases hf with hf | rfl
  · exact pure_ext z (hw f hf)
  · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [hS, hT]
    exact ext_self z

def isOr (g : Gate) : Bool :=
  match g.op with
  | .or => true
  | _ => false

lemma vals_one_or {n : ℕ} (gs : List Gate)
    (hao : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (hcnt : (gs.filter isOr).length ≤ 1)
    (ws : List (BF n)) (hw : ∀ f ∈ ws, Pure f) :
    ∀ f ∈ vals gs ws, Two f := by
  induction gs generalizing ws with
  | nil => exact fun f hf => pure_two (hw f hf)
  | cons g gs ih =>
    have hg := hao g (by simp)
    rcases hg.1 with hgand | hgor
    · apply ih (fun k hk => hao k (by simp [hk]))
      · simpa [isOr, hgand] using hcnt
      · exact step_closed Pure pure_false (fun _ _ => pure_and) ws hw g hgand hg.2
    · obtain ⟨z, hz, hwz⟩ := step_or ws hw g hgor hg.2
      have hrest : ∀ k ∈ gs, k.op = .and ∧ k.inputs.length = 2 := by
        intro k hk
        obtain ⟨hkand | hkor, hklen⟩ := hao k (by simp [hk])
        · exact ⟨hkand, hklen⟩
        · have hc : (gs.filter isOr).length = 0 := by
            simpa [isOr, hgor] using hcnt
          have hm : k ∈ gs.filter isOr := by simp [isOr, hk, hkor]
          have he := List.eq_nil_of_length_eq_zero hc
          rw [he] at hm
          cases hm
      intro f hf
      exact ext_two hz (vals_closed (Ext z) (pure_ext z pure_false)
        (fun _ _ => ext_and) gs hrest (step ws g) hwz f hf)



lemma getD_eval {n : ℕ} (ws : List (BF n)) (i : ℕ) (x : Fin n → Bool) :
    (ws.map (fun f => f x)).getD i false = (ws.getD i (fun _ => false)) x := by
  induction ws generalizing i with
  | nil => simp
  | cons f fs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

lemma map_step {n : ℕ} (ws : List (BF n)) (g : Gate) (x : Fin n → Bool) :
    (step ws g).map (fun f => f x) =
      (ws.map (fun f => f x)) ++
        [g.op.eval (g.inputs.map fun i => (ws.map (fun f => f x)).getD i false)] := by
  simp only [step, List.map_append, List.map_cons, List.map_nil]
  simp_rw [getD_eval]

lemma map_vals {n : ℕ} (gs : List Gate) (ws : List (BF n)) (x : Fin n → Bool) :
    (vals gs ws).map (fun f => f x) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (ws.map (fun f => f x)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    change (vals gs (step ws g)).map (fun f => f x) = _
    rw [ih, map_step]
    rfl

lemma circuit_one_or {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (hcnt : (C.gates.filter isOr).length ≤ 1) : Two (circuitFun n C) := by
  let ws : List (BF n) := List.ofFn (fun i : Fin n => fun x => x i)
  have hw : ∀ f ∈ ws, Pure f := by
    intro f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    exact pure_input i
  have hvals : ∀ f ∈ vals C.gates ws, Two f :=
    vals_one_or C.gates (fun g hg => ⟨hC.1 g hg, hC.2.2 g hg⟩) hcnt ws hw
  have hout := getD_property Two _ (pure_two pure_false) (vals C.gates ws) hvals C.output
  have heq : circuitFun n C = (vals C.gates ws).getD C.output (fun _ => false) := by
    funext x
    unfold circuitFun Circuit.eval Circuit.wires
    rw [← getD_eval, map_vals]
    congr 1
    simp [ws, List.map_ofFn, Function.comp_def]
  rw [heq]
  exact hout

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma graph_true_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) : graphFun G ∅ x = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma mono_graph_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Option (Fin n)))
    (hbelow : ∀ x, mono S x = true → graphFun G ∅ x = true) :
    ∃ E : Finset (Sym2 (Fin n)), E.card ≤ 1 ∧
      ∀ u v, G.Adj u v → mono S (pairInput u v) = true → s(u,v) ∈ E := by
  classical
  by_cases hn : none ∈ S
  · refine ⟨∅, by simp, ?_⟩
    intro u v huv hm
    have hh := of_decide_eq_true hm none hn
    contradiction
  · let x : Fin n → Bool := fun i => decide (some i ∈ S)
    have hm : mono S x = true := by
      apply decide_eq_true
      intro i hi
      cases i with
      | none => exact False.elim (hn hi)
      | some i => simpa [x] using hi
    have hf := hbelow x hm
    simp only [graphFun] at hf
    simp at hf
    obtain ⟨a, b, hab, ha, hb⟩ := hf
    have haS : some a ∈ S := by simpa [x] using ha
    have hbS : some b ∈ S := by simpa [x] using hb
    refine ⟨{s(a,b)}, by simp, ?_⟩
    intro u v huv hmuv
    have haUV := of_decide_eq_true hmuv (some a) haS
    have hbUV := of_decide_eq_true hmuv (some b) hbS
    have ha : a = u ∨ a = v := by simpa [pairInput] using haUV
    have hb : b = u ∨ b = v := by simpa [pairInput] using hbUV
    have hne : a ≠ b := hab.ne
    simp only [Finset.mem_singleton, Sym2.eq_iff]
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (hne rfl)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact False.elim (hne rfl)

lemma graph_two_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : Two (graphFun G ∅)) : G.edgeFinset.card ≤ 2 := by
  classical
  obtain ⟨S, T, hST⟩ := hG
  have hS : ∀ x, mono S x = true → graphFun G ∅ x = true := by
    intro x hx
    simp [hST, hx]
  have hT : ∀ x, mono T x = true → graphFun G ∅ x = true := by
    intro x hx
    simp [hST, hx]
  obtain ⟨E, hE, hES⟩ := mono_graph_cover G S hS
  obtain ⟨F, hF, hFT⟩ := mono_graph_cover G T hT
  have hsub : G.edgeFinset ⊆ E ∪ F := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have huv : G.Adj u v := by simpa using he
      have hf : graphFun G ∅ (pairInput u v) = true := by
        exact (graph_true_iff G _).2 ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
      rw [hST] at hf
      have hor : mono S (pairInput u v) = true ∨ mono T (pairInput u v) = true := by simpa using hf
      rcases hor with hs | ht
      · exact Finset.mem_union_left _ (hES u v huv hs)
      · exact Finset.mem_union_right _ (hFT u v huv ht)
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le E F
  omega

lemma circuit_one_or_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅)
    (hcnt : (C.gates.filter isOr).length ≤ 1) : G.edgeFinset.card ≤ 2 := by
  apply graph_two_card G
  rw [← hfun]
  exact circuit_one_or C hC hcnt

lemma circuit_no_or {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (hcnt : (C.gates.filter isOr).length = 0) : Pure (circuitFun n C) := by
  have hall : ∀ g ∈ C.gates, g.op = .and ∧ g.inputs.length = 2 := by
    intro g hg
    refine ⟨?_, hC.2.2 g hg⟩
    rcases hC.1 g hg with ha | ho
    · exact ha
    · have hm : g ∈ C.gates.filter isOr := by simp [isOr, hg, ho]
      have he := List.eq_nil_of_length_eq_zero hcnt
      rw [he] at hm
      cases hm
  let ws : List (BF n) := List.ofFn (fun i : Fin n => fun x => x i)
  have hw : ∀ f ∈ ws, Pure f := by
    intro f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    exact pure_input i
  have hvals : ∀ f ∈ vals C.gates ws, Pure f :=
    vals_closed Pure pure_false (fun _ _ => pure_and) C.gates hall ws hw
  have hout := getD_property Pure _ pure_false (vals C.gates ws) hvals C.output
  have heq : circuitFun n C = (vals C.gates ws).getD C.output (fun _ => false) := by
    funext x
    unfold circuitFun Circuit.eval Circuit.wires
    rw [← getD_eval, map_vals]
    congr 1
    simp [ws, List.map_ofFn, Function.comp_def]
  rw [heq]
  exact hout

lemma graph_pure_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : Pure (graphFun G ∅)) : G.edgeFinset.card ≤ 1 := by
  classical
  obtain ⟨S, hS⟩ := hG
  obtain ⟨E, hE, hES⟩ := mono_graph_cover G S (by simp [← hS])
  have hsub : G.edgeFinset ⊆ E := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have huv : G.Adj u v := by simpa using he
      apply hES u v huv
      rw [← hS]
      exact (graph_true_iff G _).2 ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
  exact (Finset.card_le_card hsub).trans hE

lemma circuit_no_or_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅)
    (hcnt : (C.gates.filter isOr).length = 0) : G.edgeFinset.card ≤ 1 := by
  apply graph_pure_card G
  rw [← hfun]
  exact circuit_no_or C hC hcnt

end PEqualNP.Outside.L_meta_5012.OneOr

namespace PEqualNP.Outside.L_meta_5012.Trace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

lemma acceptedTop (hL : IsLeastAO G C) {u v : Fin n} (hadj : G.Adj u v) :
    ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true := by
  have hout (x : Fin n → Bool) : val C (List.ofFn x) C.output = graphFun G ∅ x :=
    congrFun hL.2.1 x
  obtain ⟨a, hl, ho, hr, hv⟩ :=
    edge_trace G (graphFun G ∅) (fun k l => (graphFun_pair G k l).mp)
      hout u v ((graphFun_pair G u v).mpr hadj)
  have hand := (hL.1.1 _ (gateAt_mem hl)).resolve_right ho
  have hb : BelowF G C a := fun x hx =>
    below_of_reach (graphFun G ∅) hout a hr x (gateVal_eq_val n C a x ▸ hx)
  refine ⟨a, ?_, hv⟩
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
    And.intro hl (And.intro hand hb)

end PEqualNP.Outside.L_meta_5012.Trace

namespace PEqualNP.Outside.L_meta_5012.Small

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def twoEdges {n : ℕ} (u v a b : Fin n) : Circuit :=
  ⟨[⟨.and, [u.val, v.val]⟩, ⟨.and, [a.val, b.val]⟩,
    ⟨.or, [n, n + 1]⟩], n + 2⟩

lemma twoEdges_ao {n : ℕ} (u v a b : Fin n) : IsAO2 n (twoEdges u v a b) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [AndOrOnly, twoEdges]
  · intro j hj w hw
    change j < 3 at hj
    interval_cases j <;> simp [twoEdges, gateAt] at hw
    all_goals rcases hw with rfl | rfl <;> omega
  · simp [twoEdges]

lemma getD_ofFn {n : ℕ} (x : Fin n → Bool) (u : Fin n) :
    (List.ofFn x).getD u.val false = x u := by
  simp [List.getD_eq_getElem?_getD, u.isLt]

lemma getD_append_lt (w z : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ z).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_at (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma twoEdges_eval {n : ℕ} (u v a b : Fin n) (x : Fin n → Bool) :
    circuitFun n (twoEdges u v a b) x = ((x u && x v) || (x a && x b)) := by
  simp only [circuitFun, twoEdges, Circuit.eval, Circuit.wires,
    List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil,
    GateOp.eval, List.all_cons, List.all_nil, Bool.and_true,
    List.any_cons, List.any_nil, Bool.or_false, id_eq, getD_ofFn]
  simp only [getD_append_lt _ _ _ (by simp : a.val < (List.ofFn x).length),
    getD_append_lt _ _ _ (by simp : b.val < (List.ofFn x).length), getD_ofFn]
  have h0 : (List.ofFn x).length = n := List.length_ofFn
  simp [List.getD_eq_getElem?_getD, h0]

lemma graphFun_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma graphFun_twoEdges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v a b : Fin n) (hE : G.edgeFinset = {s(u, v), s(a, b)}) :
    circuitFun n (twoEdges u v a b) = graphFun G ∅ := by
  funext x
  rw [twoEdges_eval]
  have hadj : ∀ p q, G.Adj p q ↔ s(p, q) = s(u, v) ∨ s(p, q) = s(a, b) := by
    intro p q
    have he : s(p, q) ∈ G.edgeFinset ↔ s(p, q) ∈ ({s(u, v), s(a, b)} : Finset _) := by rw [hE]
    simpa using he
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, graphFun_iff, hadj, Sym2.eq_iff]
  constructor
  · rintro (⟨hu, hv⟩ | ⟨ha, hb⟩)
    · exact ⟨u, v, Or.inl (Or.inl ⟨rfl, rfl⟩), hu, hv⟩
    · exact ⟨a, b, Or.inr (Or.inl ⟨rfl, rfl⟩), ha, hb⟩
  · rintro ⟨p, q, ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)), hp, hq⟩
    · exact Or.inl ⟨hp, hq⟩
    · exact Or.inl ⟨hq, hp⟩
    · exact Or.inr ⟨hp, hq⟩
    · exact Or.inr ⟨hq, hp⟩

lemma least_size_zero_of_empty {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsLeastAO G C)
    (hE : G.edgeFinset = ∅) : C.size = 0 := by
  have hG : G = ⊥ := G.edgeFinset_eq_empty.mp hE
  have hfun : circuitFun n (⟨[], n⟩ : Circuit) = graphFun G ∅ := by
    subst G
    funext x
    simp [circuitFun, Circuit.eval, Circuit.wires, graphFun]
  have hmin := hC.2.2 ⟨[], n⟩
    (by simp [IsAO2, AndOrOnly, ReadsBack]) hfun
  simpa [Circuit.size] using hmin

lemma least_size_le_three_of_two_edges {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsLeastAO G C)
    (hE : G.edgeFinset.card ≤ 2) : C.size ≤ 3 := by
  by_cases he : G.edgeFinset = ∅
  · rw [least_size_zero_of_empty G C hC he]
    omega
  have hp : 0 < G.edgeFinset.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
  obtain ⟨e, f, hef⟩ : ∃ e f, G.edgeFinset = {e, f} := by
    by_cases h1 : G.edgeFinset.card = 1
    · obtain ⟨e, he⟩ := Finset.card_eq_one.mp h1
      exact ⟨e, e, by simpa using he⟩
    · obtain ⟨e, f, _, hef⟩ := Finset.card_eq_two.mp (by omega : G.edgeFinset.card = 2)
      exact ⟨e, f, hef⟩
  induction e using Sym2.inductionOn with
  | hf u v =>
    induction f using Sym2.inductionOn with
    | hf a b =>
      exact hC.2.2 (twoEdges u v a b) (twoEdges_ao u v a b)
        (graphFun_twoEdges G u v a b hef)

def oneEdge {n : ℕ} (u v : Fin n) : Circuit :=
  ⟨[⟨.and, [u.val, v.val]⟩], n⟩

lemma oneEdge_ao {n : ℕ} (u v : Fin n) : IsAO2 n (oneEdge u v) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [AndOrOnly, oneEdge]
  · intro j hj w hw
    change j < 1 at hj
    have hj0 : j = 0 := by omega
    subst j
    simp [oneEdge, gateAt] at hw
    rcases hw with rfl | rfl <;> omega
  · simp [oneEdge]

lemma oneEdge_eval {n : ℕ} (u v : Fin n) (x : Fin n → Bool) :
    circuitFun n (oneEdge u v) x = (x u && x v) := by
  simp [circuitFun, oneEdge, Circuit.eval, Circuit.wires, GateOp.eval,
    List.getD_eq_getElem?_getD]

lemma least_size_le_one_of_one_edge {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsLeastAO G C)
    (hE : G.edgeFinset.card ≤ 1) : C.size ≤ 1 := by
  by_cases he : G.edgeFinset = ∅
  · rw [least_size_zero_of_empty G C hC he]
    omega
  have hp : 0 < G.edgeFinset.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp (by omega : G.edgeFinset.card = 1)
  induction e using Sym2.inductionOn with
  | hf u v =>
    have hfun := graphFun_twoEdges G u v u v (by simpa using he)
    have hsingle : circuitFun n (oneEdge u v) = graphFun G ∅ := by
      funext x
      rw [← hfun, twoEdges_eval, oneEdge_eval, Bool.or_self]
    exact hC.2.2 (oneEdge u v) (oneEdge_ao u v) hsingle

end PEqualNP.Outside.L_meta_5012.Small
namespace PEqualNP.Outside.L_meta_5012.Count

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.Outside.L_meta_5012.OneOr

lemma map_getD_range {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [hj]

lemma or_indices_card (C : Circuit) :
    ((Finset.range C.gates.length).filter fun i => isOr (gateAt C i) = true).card =
      (C.gates.filter isOr).length := by
  have hc := (List.nodup_range (n := C.gates.length)).card_eq_countP
    (P := fun i => isOr (gateAt C i) = true)
  simp only [List.toFinset_range] at hc
  rw [hc, ← List.countP_eq_length_filter]
  have hm := map_getD_range C.gates ⟨.or, []⟩
  have hp := congrArg (List.countP isOr) hm
  rw [List.countP_map] at hp
  simpa [gateAt, Function.comp_def] using hp

lemma junk_or_clean_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hclean : ∃ a, a ∈ tops G C) :
    (junk G C).card + (C.gates.filter isOr).length + 1 ≤ C.size := by
  classical
  obtain ⟨a, ha⟩ := hclean
  have hat : a ∈ Finset.range C.gates.length ∧
      (gateAt C a).op = .and ∧ BelowF G C a := by
    simpa only [tops, gatesWhere, Finset.mem_filter] using ha
  have haop : (gateAt C a).op = .and := hat.2.1
  have habelow : BelowF G C a := hat.2.2
  let O := (Finset.range C.gates.length).filter fun i => isOr (gateAt C i) = true
  have haj : a ∉ junk G C := by
    intro haj
    have hd : IsDirtyAnd n G C a := (Finset.mem_filter.mp haj).2
    obtain ⟨x, hx, hfalse⟩ := hd.2.2
    have htrue := habelow x hx
    rw [htrue] at hfalse
    contradiction
  have hao : a ∉ O := by
    intro haO
    have hi : isOr (gateAt C a) = true := (Finset.mem_filter.mp haO).2
    simp [isOr, haop] at hi
  have hdis : Disjoint (junk G C) O := by
    apply Finset.disjoint_left.mpr
    intro i hij hio
    have hia : (gateAt C i).op = .and := (Finset.mem_filter.mp hij).2.1
    have hior : isOr (gateAt C i) = true := (Finset.mem_filter.mp hio).2
    simp [isOr, hia] at hior
  have han : a ∉ junk G C ∪ O := by simp [haj, hao]
  have hsub : insert a (junk G C ∪ O) ⊆ Finset.range C.gates.length := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hat.1
    · rcases Finset.mem_union.mp hi with hi | hi
      · exact (Finset.mem_filter.mp hi).1
      · exact (Finset.mem_filter.mp hi).1
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem han, Finset.card_union_of_disjoint hdis,
    Finset.card_range] at hc
  have ho : O.card = (C.gates.filter isOr).length := or_indices_card C
  rw [ho] at hc
  exact hc

end PEqualNP.Outside.L_meta_5012.Count

namespace PEqualNP.Outside.L_meta_5012.Small

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma no_two_junk_size_le_four {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsLeastAO G C)
    (hs : C.size ≤ 4) : (junk G C).card ≠ 2 := by
  intro hj
  have hE : G.edgeFinset.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    have hz := least_size_zero_of_empty G C hC he
    have hsub : junk G C ⊆ Finset.range C.gates.length := Finset.filter_subset _ _
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_range, hj] at hcard
    simp only [Circuit.size] at hz
    omega
  have hclean : ∃ a, a ∈ tops G C := by
    obtain ⟨e, he⟩ := hE
    induction e using Sym2.inductionOn with
    | hf u v =>
      have huv : G.Adj u v := by simpa using he
      obtain ⟨a, ha, _⟩ := Trace.acceptedTop G C hC huv
      exact ⟨a, ha⟩
  have hcount := Count.junk_or_clean_count G C hclean
  have hor : (C.gates.filter OneOr.isOr).length ≤ 1 := by omega
  have hs3 := least_size_le_three_of_two_edges G C hC
    (OneOr.circuit_one_or_edges G C hC.1 hC.2.1 hor)
  have hor0 : (C.gates.filter OneOr.isOr).length = 0 := by omega
  have hs1 := least_size_le_one_of_one_edge G C hC
    (OneOr.circuit_no_or_edges G C hC.1 hC.2.1 hor0)
  omega

end PEqualNP.Outside.L_meta_5012.Small
