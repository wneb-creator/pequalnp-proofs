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


namespace PEqualNP.Outside.L_meta_5012.Twin

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def collapse {n : ℕ} (v : Fin n) (i : Fin (n + 1)) : Fin n :=
  if hi : i.val < n then ⟨i.val, hi⟩ else v

lemma collapse_castSucc {n : ℕ} (v i : Fin n) : collapse v i.castSucc = i := by
  simp [collapse, i.isLt]

lemma collapse_last {n : ℕ} (v : Fin n) : collapse v (Fin.last n) = v := by
  simp [collapse]

lemma collapse_inj_of_ne {n : ℕ} (v : Fin n) (a b : Fin (n + 1))
    (hab : collapse v a = collapse v b) (ha : collapse v a ≠ v) : a = b := by
  have han : a.val < n := by
    by_contra h
    exact ha (by simp [collapse, h])
  have hbn : b.val < n := by
    by_contra h
    exact ha (hab.trans (by simp [collapse, h]))
  apply Fin.ext
  have := congrArg Fin.val hab
  simpa [collapse, han, hbn] using this

abbrev graph {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : SimpleGraph (Fin (n + 1)) :=
  G.comap (collapse v)

lemma graph_bip {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (s : Fin n → Bool)
    (hbip : ∀ a b, G.Adj a b → s a ≠ s b) :
    ∀ a b, (graph G v).Adj a b → (s ∘ collapse v) a ≠ (s ∘ collapse v) b := by
  intro a b h
  exact hbip _ _ h

lemma graph_noFour {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) (h4 : NoFourCycle G)
    (hdeg : ∀ a b : Fin n, G.Adj v a → G.Adj v b → a = b) :
    NoFourCycle (graph G v) := by
  intro a b hab
  apply Finset.card_le_one.mpr
  intro c hc d hd
  obtain ⟨_, hac, hbc⟩ := Finset.mem_filter.mp hc
  obtain ⟨_, had, hbd⟩ := Finset.mem_filter.mp hd
  change G.Adj (collapse v a) (collapse v c) at hac
  change G.Adj (collapse v b) (collapse v c) at hbc
  change G.Adj (collapse v a) (collapse v d) at had
  change G.Adj (collapse v b) (collapse v d) at hbd
  have hcd : collapse v c = collapse v d := by
    by_cases habc : collapse v a = collapse v b
    · have hav : collapse v a = v := by
        by_contra h
        exact hab (collapse_inj_of_ne v a b habc h)
      exact hdeg _ _ (by simpa only [hav] using hac) (by simpa only [hav] using had)
    · exact Finset.card_le_one.mp (h4 _ _ habc) (collapse v c)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hac, hbc⟩)
        (collapse v d) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, had, hbd⟩)
  apply collapse_inj_of_ne v c d hcd
  intro hcv
  have habc : collapse v a = collapse v b :=
    hdeg _ _ (by simpa only [hcv] using hac.symm) (by simpa only [hcv] using hbc.symm)
  have hav : collapse v a = v := by
    by_contra h
    exact hab (collapse_inj_of_ne v a b habc h)
  exact (show G.Adj v v from by simpa only [hav, hcv] using hac).ne rfl

def merged {n : ℕ} (v : Fin n) (x : Fin (n + 1) → Bool) (i : Fin n) : Bool :=
  x i.castSucc || (decide (i = v) && x (Fin.last n))

lemma merged_true {n : ℕ} (v : Fin n) (x : Fin (n + 1) → Bool) (i : Fin n) :
    merged v x i = true ↔ ∃ a : Fin (n + 1), collapse v a = i ∧ x a = true := by
  simp only [merged, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨hi, h⟩)
    · exact ⟨i.castSucc, collapse_castSucc v i, h⟩
    · exact ⟨Fin.last n, (collapse_last v).trans hi.symm, h⟩
  · rintro ⟨a, hai, hxa⟩
    rcases Fin.eq_castSucc_or_eq_last a with ⟨j, rfl⟩ | rfl
    · rw [collapse_castSucc] at hai
      subst j
      exact Or.inl hxa
    · rw [collapse_last] at hai
      subst i
      exact Or.inr ⟨rfl, hxa⟩

lemma graphFun_merged {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) (x : Fin (n + 1) → Bool) :
    graphFun (graph G v) ∅ x = graphFun G ∅ (merged v x) := by
  unfold graphFun
  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨a, b, hab, hxa, hxb⟩
    exact ⟨collapse v a, collapse v b, hab,
      (merged_true v x _).mpr ⟨a, rfl, hxa⟩,
      (merged_true v x _).mpr ⟨b, rfl, hxb⟩⟩
  · rintro ⟨a, b, hab, hxa, hxb⟩
    obtain ⟨c, hc, hxc⟩ := (merged_true v x a).mp hxa
    obtain ⟨d, hd, hxd⟩ := (merged_true v x b).mp hxb
    refine ⟨c, d, ?_, hxc, hxd⟩
    change G.Adj (collapse v c) (collapse v d)
    rwa [hc, hd]

def mapWire {n : ℕ} (v : Fin n) (w : ℕ) : ℕ :=
  if w < n then if w = v.val then n + 1 else w else w + 2

def mapGate {n : ℕ} (v : Fin n) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (mapWire v)⟩

def liftCircuit {n : ℕ} (v : Fin n) (C : Circuit) : Circuit :=
  ⟨⟨GateOp.or, [v.val, n]⟩ :: C.gates.map (mapGate v), mapWire v C.output⟩

lemma liftCircuit_size {n : ℕ} (v : Fin n) (C : Circuit) :
    (liftCircuit v C).size = C.size + 1 := by
  simp [liftCircuit, Circuit.size]

lemma mapWire_ge {n : ℕ} (v : Fin n) (i : ℕ) (hi : n ≤ i) :
    mapWire v i = i + 2 := by
  simp [mapWire, Nat.not_lt.mpr hi]

lemma mapWire_lt {n : ℕ} (v : Fin n) {i k : ℕ} (hn : n ≤ k) (hi : i < k) :
    mapWire v i < k + 2 := by
  unfold mapWire
  split_ifs <;> omega

lemma gateAt_liftCircuit_succ {n : ℕ} (v : Fin n) (C : Circuit) (j : ℕ) :
    gateAt (liftCircuit v C) (j + 1) = mapGate v (gateAt C j) := by
  change (C.gates.map (mapGate v)).getD j ⟨GateOp.or, []⟩ =
    mapGate v (C.gates.getD j ⟨GateOp.or, []⟩)
  exact List.getD_map C.gates (⟨GateOp.or, []⟩ : Gate) (n := j) (mapGate v)

lemma liftCircuit_ao {n : ℕ} (v : Fin n) (C : Circuit) (h : IsAO2 n C) :
    IsAO2 (n + 1) (liftCircuit v C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [liftCircuit, List.mem_cons, List.mem_map] at hg
    rcases hg with rfl | ⟨g0, hg0, rfl⟩
    · exact Or.inr rfl
    · exact h.1 g0 hg0
  · intro j hj i hi
    cases j with
    | zero =>
      change i ∈ [v.val, n] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact Nat.lt_succ_of_lt v.isLt
      · omega
    | succ j =>
      have hj0 : j < C.gates.length := by simpa [liftCircuit] using hj
      rw [gateAt_liftCircuit_succ] at hi
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hi
      have hw0 := h.2.1 j hj0 w hw
      have hm := mapWire_lt v (Nat.le_add_right n j) hw0
      omega
  · intro g hg
    simp only [liftCircuit, List.mem_cons, List.mem_map] at hg
    rcases hg with rfl | ⟨g0, hg0, rfl⟩
    · rfl
    · simpa [mapGate] using h.2.2 g0 hg0

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_sim {n : ℕ} (v : Fin n) (gs : List Gate) (x y : List Bool)
    (hn : n ≤ x.length) (hlen : y.length = x.length + 2)
    (h : ∀ i, y.getD (mapWire v i) false = x.getD i false) :
    ∀ i, (run (gs.map (mapGate v)) y).getD (mapWire v i) false = (run gs x).getD i false := by
  induction gs generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    have heval : g.op.eval (g.inputs.map fun i => y.getD (mapWire v i) false) =
        g.op.eval (g.inputs.map fun i => x.getD i false) := by
      simp only [h]
    simp only [List.map_cons, run, List.foldl_cons, mapGate, List.map_map]
    change ∀ i, (run (gs.map (mapGate v))
      (y ++ [g.op.eval (g.inputs.map fun i => y.getD (mapWire v i) false)])).getD (mapWire v i) false =
      (run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])).getD i false
    rw [heval]
    apply ih
    · simpa using hn.trans (Nat.le_add_right x.length 1)
    · simp [hlen]
    · intro i
      by_cases hi : i < x.length
      · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact mapWire_lt v hn hi), List.getD_append _ _ _ _ hi]
        exact h i
      · have hni : n ≤ i := hn.trans (Nat.le_of_not_gt hi)
        rw [mapWire_ge v i hni, List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hi), hlen]
        simp

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp only [List.getElem_ofFn]

lemma initial_sim {n : ℕ} (v : Fin n) (x : Fin (n + 1) → Bool) :
    ∀ i, (List.ofFn x ++ [x v.castSucc || x (Fin.last n)]).getD (mapWire v i) false =
      (List.ofFn (merged v x)).getD i false := by
  intro i
  by_cases hi : i < n
  · by_cases hiv : i = v.val
    · subst i
      rw [show mapWire v v.val = n + 1 from by simp [mapWire, v.isLt]]
      rw [List.getD_append_right _ _ _ _ (by simp), ofFn_getD]
      simp only [List.length_ofFn, Nat.sub_self, List.getD_cons_zero, merged,
        decide_true, Bool.true_and]
    · rw [show mapWire v i = i from by simp [mapWire, hi, hiv]]
      rw [List.getD_append _ _ _ _ (by simpa using Nat.lt_succ_of_lt hi)]
      change (List.ofFn x).getD (⟨i, hi⟩ : Fin n).castSucc.val false =
        (List.ofFn (merged v x)).getD (⟨i, hi⟩ : Fin n).val false
      rw [ofFn_getD, ofFn_getD]
      have hne : (⟨i, hi⟩ : Fin n) ≠ v := fun hh => hiv (congrArg Fin.val hh)
      simp only [merged, hne, decide_false, Bool.false_and, Bool.or_false]
  · rw [mapWire_ge v i (Nat.le_of_not_gt hi)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma liftCircuit_eval {n : ℕ} (v : Fin n) (C : Circuit) (x : Fin (n + 1) → Bool) :
    circuitFun (n + 1) (liftCircuit v C) x = circuitFun n C (merged v x) := by
  have hsim := run_sim v C.gates (List.ofFn (merged v x))
    (List.ofFn x ++ [x v.castSucc || x (Fin.last n)]) (by simp) (by simp) (initial_sim v x) C.output
  have heval : GateOp.or.eval ([v.val, n].map fun i => (List.ofFn x).getD i false) =
      (x v.castSucc || x (Fin.last n)) := by
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    change ((List.ofFn x).getD v.castSucc.val false || (List.ofFn x).getD (Fin.last n).val false) = _
    rw [ofFn_getD, ofFn_getD]
  change (run ((liftCircuit v C).gates) (List.ofFn x)).getD (liftCircuit v C).output false = _
  simp only [liftCircuit, run, List.foldl_cons, heval]
  exact hsim

lemma liftCircuit_computes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) (C : Circuit) (hc : circuitFun n C = graphFun G ∅) :
    circuitFun (n + 1) (liftCircuit v C) = graphFun (graph G v) ∅ := by
  funext x
  rw [liftCircuit_eval, hc, graphFun_merged]

lemma merged_false {n : ℕ} (v : Fin n) (x : Fin n → Bool) :
    merged v (Fin.lastCases false x) = x := by
  funext i
  simp [merged]

lemma graphFun_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) (x : Fin n → Bool) :
    graphFun (graph G v) ∅ (Fin.lastCases false x) = graphFun G ∅ x := by
  rw [graphFun_merged, merged_false]

lemma least_size_transfer {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) (C D : Circuit) (hC : IsLeastAO (graph G v) C)
    (hD : IsAO2 n D) (hcD : circuitFun n D = graphFun G ∅)
    (hsize : D.size + 1 ≤ C.size) : IsLeastAO G D := by
  refine ⟨hD, hcD, ?_⟩
  intro E hE hcE
  have hb := hC.2.2 (liftCircuit v E) (liftCircuit_ao v E hE)
    (liftCircuit_computes G v E hcE)
  rw [liftCircuit_size] at hb
  omega

lemma least_size_upper {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) (C D : Circuit) (hC : IsLeastAO (graph G v) C)
    (hD : IsAO2 n D) (hcD : circuitFun n D = graphFun G ∅) :
    C.size ≤ D.size + 1 := by
  have hb := hC.2.2 (liftCircuit v D) (liftCircuit_ao v D hD)
    (liftCircuit_computes G v D hcD)
  simpa only [liftCircuit_size] using hb

lemma run_noRead (gs : List Gate) (z : ℕ) (x y : List Bool)
    (hz : ∀ g ∈ gs, z ∉ g.inputs) (hlen : x.length = y.length)
    (h : ∀ i, i ≠ z → x.getD i false = y.getD i false) :
    ∀ i, i ≠ z → (run gs x).getD i false = (run gs y).getD i false := by
  induction gs generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    have hg : z ∉ g.inputs := hz g (List.mem_cons_self ..)
    have hgs : ∀ g ∈ gs, z ∉ g.inputs := fun g hg => hz g (List.mem_cons_of_mem _ hg)
    have hmap : (g.inputs.map fun i => x.getD i false) = (g.inputs.map fun i => y.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact h i (fun hh => hg (hh ▸ hi))
    change ∀ i, i ≠ z →
      (run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])).getD i false =
      (run gs (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)])).getD i false
    rw [hmap]
    apply ih _ _ hgs
    · simpa using hlen
    · intro i hiz
      by_cases hi : i < x.length
      · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hlen ▸ hi)]
        exact h i hiz
      · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hi),
          List.getD_append_right _ _ _ _ (by omega), hlen]

lemma circuit_noRead {n : ℕ} (C : Circuit) (z : ℕ) (x y : Fin n → Bool)
    (hz : ∀ g ∈ C.gates, z ∉ g.inputs) (hout : C.output ≠ z)
    (hxy : ∀ i : Fin n, i.val ≠ z → x i = y i) :
    circuitFun n C x = circuitFun n C y := by
  apply run_noRead C.gates z (List.ofFn x) (List.ofFn y) hz (by simp) _ C.output hout
  intro i hiz
  by_cases hi : i < n
  · change (List.ofFn x).getD (⟨i, hi⟩ : Fin n).val false =
      (List.ofFn y).getD (⟨i, hi⟩ : Fin n).val false
    rw [ofFn_getD, ofFn_getD]
    exact hxy _ hiz
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])).getD i false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

lemma circuit_output_input {n : ℕ} (C : Circuit) (i : Fin n) (hi : C.output = i.val)
    (x : Fin n → Bool) : circuitFun n C x = x i := by
  change (run C.gates (List.ofFn x)).getD C.output false = x i
  rw [hi, run_input _ _ _ (by simp), ofFn_getD]

lemma graphFun_singleton {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i : Fin n) :
    graphFun G ∅ (pairInput i i) = false := by
  unfold graphFun
  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
  apply decide_eq_false
  rintro ⟨a, b, hab, ha, hb⟩
  have hai : a = i := by simpa [pairInput] using ha
  have hbi : b = i := by simpa [pairInput] using hb
  exact hab.ne (hai.trans hbi.symm)

lemma graphFun_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : Fin n) (hab : G.Adj a b) : graphFun G ∅ (pairInput a b) = true := by
  unfold graphFun
  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
    decide_eq_true_eq]
  exact ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩

lemma graph_output_not_input {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hc : circuitFun n C = graphFun G ∅) (i : Fin n) : C.output ≠ i.val := by
  intro h
  have hv := circuit_output_input C i h (pairInput i i)
  rw [hc, graphFun_singleton] at hv
  simp [pairInput] at hv

lemma cloned_input_read {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v q : Fin n) (hvq : G.Adj v q) (C : Circuit)
    (hc : circuitFun (n + 1) C = graphFun (graph G v) ∅) :
    ∃ g ∈ C.gates, n ∈ g.inputs := by
  by_contra h
  push Not at h
  have ho : C.output ≠ n := graph_output_not_input (graph G v) C hc (Fin.last n)
  have he := circuit_noRead C n (pairInput q.castSucc q.castSucc)
    (pairInput q.castSucc (Fin.last n)) h ho (by
      intro i hi
      have hine : i ≠ Fin.last n := fun hh => hi (congrArg Fin.val hh)
      simp [pairInput, hine])
  have hadj : (graph G v).Adj q.castSucc (Fin.last n) := by
    change G.Adj (collapse v q.castSucc) (collapse v (Fin.last n))
    simpa only [collapse_castSucc, collapse_last] using hvq.symm
  rw [hc, graphFun_singleton, graphFun_edge _ _ _ hadj] at he
  contradiction

namespace Merge

def input {n : ℕ} (v z : Fin n) (x : Fin n → Bool) (i : Fin n) : Bool :=
  x i || (decide (i = v) && x z)

def wire {n : ℕ} (v : Fin n) (w : ℕ) : ℕ :=
  if w < n then if w = v.val then n else w else w + 1

def gate {n : ℕ} (v : Fin n) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wire v)⟩

def circuit {n : ℕ} (v z : Fin n) (C : Circuit) : Circuit :=
  ⟨⟨GateOp.or, [v.val, z.val]⟩ :: C.gates.map (gate v), wire v C.output⟩

lemma size {n : ℕ} (v z : Fin n) (C : Circuit) :
    (circuit v z C).size = C.size + 1 := by simp [circuit, Circuit.size]

lemma wire_ge {n : ℕ} (v : Fin n) (i : ℕ) (hi : n ≤ i) : wire v i = i + 1 := by
  simp [wire, Nat.not_lt.mpr hi]

lemma wire_lt {n : ℕ} (v : Fin n) {i k : ℕ} (hn : n ≤ k) (hi : i < k) :
    wire v i < k + 1 := by
  unfold wire
  split_ifs <;> omega

lemma gateAt_succ {n : ℕ} (v z : Fin n) (C : Circuit) (j : ℕ) :
    gateAt (circuit v z C) (j + 1) = gate v (gateAt C j) := by
  change (C.gates.map (gate v)).getD j ⟨GateOp.or, []⟩ =
    gate v (C.gates.getD j ⟨GateOp.or, []⟩)
  exact List.getD_map C.gates (⟨GateOp.or, []⟩ : Gate) (n := j) (gate v)

lemma ao {n : ℕ} (v z : Fin n) (C : Circuit) (h : IsAO2 n C) : IsAO2 n (circuit v z C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.mem_map] at hg
    rcases hg with rfl | ⟨g0, hg0, rfl⟩
    · exact Or.inr rfl
    · exact h.1 g0 hg0
  · intro j hj i hi
    cases j with
    | zero =>
      change i ∈ [v.val, z.val] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact v.isLt
      · exact z.isLt
    | succ j =>
      have hj0 : j < C.gates.length := by simpa [circuit] using hj
      rw [gateAt_succ] at hi
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hi
      have hw0 := h.2.1 j hj0 w hw
      have hm := wire_lt v (Nat.le_add_right n j) hw0
      omega
  · intro g hg
    simp only [circuit, List.mem_cons, List.mem_map] at hg
    rcases hg with rfl | ⟨g0, hg0, rfl⟩
    · rfl
    · simpa [gate] using h.2.2 g0 hg0

lemma run_sim {n : ℕ} (v : Fin n) (gs : List Gate) (x y : List Bool)
    (hn : n ≤ x.length) (hlen : y.length = x.length + 1)
    (h : ∀ i, y.getD (wire v i) false = x.getD i false) :
    ∀ i, (run (gs.map (gate v)) y).getD (wire v i) false = (run gs x).getD i false := by
  induction gs generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    have heval : g.op.eval (g.inputs.map fun i => y.getD (wire v i) false) =
        g.op.eval (g.inputs.map fun i => x.getD i false) := by simp only [h]
    simp only [List.map_cons, run, List.foldl_cons, gate, List.map_map]
    change ∀ i, (run (gs.map (gate v))
      (y ++ [g.op.eval (g.inputs.map fun i => y.getD (wire v i) false)])).getD (wire v i) false =
      (run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])).getD i false
    rw [heval]
    apply ih
    · simpa using hn.trans (Nat.le_add_right x.length 1)
    · simp [hlen]
    · intro i
      by_cases hi : i < x.length
      · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact wire_lt v hn hi),
          List.getD_append _ _ _ _ hi]
        exact h i
      · have hni : n ≤ i := hn.trans (Nat.le_of_not_gt hi)
        rw [wire_ge v i hni, List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hi), hlen]
        simp

lemma initial {n : ℕ} (v z : Fin n) (x : Fin n → Bool) :
    ∀ i, (List.ofFn x ++ [x v || x z]).getD (wire v i) false =
      (List.ofFn (input v z x)).getD i false := by
  intro i
  by_cases hi : i < n
  · by_cases hiv : i = v.val
    · subst i
      rw [show wire v v.val = n from by simp [wire, v.isLt]]
      rw [List.getD_append_right _ _ _ _ (by simp), ofFn_getD]
      simp only [List.length_ofFn, Nat.sub_self, List.getD_cons_zero, input,
        decide_true, Bool.true_and]
    · rw [show wire v i = i from by simp [wire, hi, hiv]]
      rw [List.getD_append _ _ _ _ (by simpa using hi)]
      change (List.ofFn x).getD (⟨i, hi⟩ : Fin n).val false =
        (List.ofFn (input v z x)).getD (⟨i, hi⟩ : Fin n).val false
      rw [ofFn_getD, ofFn_getD]
      have hne : (⟨i, hi⟩ : Fin n) ≠ v := fun hh => hiv (congrArg Fin.val hh)
      simp only [input, hne, decide_false, Bool.false_and, Bool.or_false]
  · rw [wire_ge v i (Nat.le_of_not_gt hi)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma eval {n : ℕ} (v z : Fin n) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n (circuit v z C) x = circuitFun n C (input v z x) := by
  have hsim := run_sim v C.gates (List.ofFn (input v z x))
    (List.ofFn x ++ [x v || x z]) (by simp) (by simp) (initial v z x) C.output
  have heval : GateOp.or.eval ([v.val, z.val].map fun i => (List.ofFn x).getD i false) =
      (x v || x z) := by
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [ofFn_getD, ofFn_getD]
  change (run ((circuit v z C).gates) (List.ofFn x)).getD (circuit v z C).output false = _
  simp only [circuit, run, List.foldl_cons, heval]
  exact hsim

end Merge

abbrev eraseVertex {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n) : SimpleGraph (Fin n) :=
  ⟨fun a b => G.Adj a b ∧ a ≠ z ∧ b ≠ z,
    ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩, ⟨fun _ h => h.1.ne rfl⟩⟩

lemma graphFun_eraseVertex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) (x : Fin n → Bool) :
    graphFun (eraseVertex G z) ∅ x = graphFun G ∅ (Function.update x z false) := by
  unfold graphFun
  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨a, b, ⟨hab, haz, hbz⟩, hxa, hxb⟩
    exact ⟨a, b, hab, by simpa [Function.update_of_ne haz] using hxa,
      by simpa [Function.update_of_ne hbz] using hxb⟩
  · rintro ⟨a, b, hab, hxa, hxb⟩
    have haz : a ≠ z := by intro hh; subst a; simp at hxa
    have hbz : b ≠ z := by intro hh; subst b; simp at hxb
    exact ⟨a, b, ⟨hab, haz, hbz⟩, by simpa [Function.update_of_ne haz] using hxa,
      by simpa [Function.update_of_ne hbz] using hxb⟩

lemma merged_merge_update {n : ℕ} (v : Fin n) (x : Fin (n + 1) → Bool) :
    merged v (Function.update (Merge.input v.castSucc (Fin.last n) x) (Fin.last n) false) =
      merged v x := by
  funext i
  simp [merged, Merge.input, Fin.castSucc_inj]

lemma restore_erased {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) (x : Fin (n + 1) → Bool) :
    graphFun (eraseVertex (graph G v) (Fin.last n)) ∅
      (Merge.input v.castSucc (Fin.last n) x) = graphFun (graph G v) ∅ x := by
  rw [graphFun_eraseVertex, graphFun_merged, merged_merge_update, graphFun_merged]

lemma restore_circuit {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) (C : Circuit)
    (hc : circuitFun (n + 1) C = graphFun (eraseVertex (graph G v) (Fin.last n)) ∅) :
    circuitFun (n + 1) (Merge.circuit v.castSucc (Fin.last n) C) = graphFun (graph G v) ∅ := by
  funext x
  rw [Merge.eval, hc, restore_erased]

lemma erased_bip {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n) (s : Fin n → Bool)
    (hbip : ∀ a b, G.Adj a b → s a ≠ s b) :
    ∀ a b, (eraseVertex G z).Adj a b → s a ≠ s b := by
  intro a b h
  exact hbip _ _ h.1

lemma erased_noFour {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) (h4 : NoFourCycle G) : NoFourCycle (eraseVertex G z) := by
  intro a b hab
  apply (Finset.card_le_card _).trans (h4 a b hab)
  intro c hc
  obtain ⟨_, hac, hbc⟩ := Finset.mem_filter.mp hc
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hac.1, hbc.1⟩

namespace Restriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover


def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

lemma getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

lemma run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

lemma run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

def Ok (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ o s t, gs[j] = ⟨o, [s, t]⟩ ∧ (o = GateOp.and ∨ o = GateOp.or) ∧
    s < n + j ∧ t < n + j

lemma ok_snoc {n : ℕ} {gs : List Gate} (h : Ok n gs) {o : GateOp} {s t : ℕ}
    (ho : o = GateOp.and ∨ o = GateOp.or) (hs : s < n + gs.length) (ht : t < n + gs.length) :
    Ok n (gs ++ [⟨o, [s, t]⟩]) := by
  intro j hj
  by_cases hlt : j < gs.length
  · rw [List.getElem_append_left hlt]; exact h j hlt
  · have : j = gs.length := by simp at hj; omega
    subst this
    exact ⟨o, s, t, by simp, ho, hs, ht⟩

def ov (gs : List Gate) (x : List Bool) (o : Option ℕ) : Bool :=
  match o with
  | none => false
  | some w => (run gs x).getD w false

lemma ov_ext (gs hs : List Gate) (x : List Bool) (o : Option ℕ)
    (h : ∀ w, o = some w → w < x.length + gs.length) : ov (gs ++ hs) x o = ov gs x o := by
  cases o with
  | none => rfl
  | some w => exact run_prefix gs hs x w (h w rfl)

lemma ov_new (gs : List Gate) (n : ℕ) (x : List Bool) (hx : x.length = n) (o : GateOp) (s t : ℕ)
    (hs : s < n + gs.length) (ht : t < n + gs.length) :
    ov (gs ++ [⟨o, [s, t]⟩]) x (some (n + gs.length)) =
      o.eval [(run gs x).getD s false, (run gs x).getD t false] := by
  unfold ov
  simp only
  rw [run_snoc]
  have : n + gs.length = (run gs x).length := by rw [run_length, hx]
  rw [this, getD_at]
  rfl

lemma ok_ao {n : ℕ} {gs : List Gate} {w : ℕ} (hok : Ok n gs) : TopForm.IsAO2 n ⟨gs, w⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; exact h2
  · intro j hj i hi
    obtain ⟨o', s', t', h1, h2, h3, h4⟩ := hok j hj
    have e1 : gateAt ⟨gs, w⟩ j = gs[j] := List.getD_eq_getElem _ _ hj
    rw [e1, h1] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; rfl


lemma ao_ok {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) : Ok n C.gates := by
  intro j hj
  have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hm : gateAt C j ∈ C.gates := by rw [e]; exact List.getElem_mem hj
  obtain ⟨s, t, hst⟩ := List.length_eq_two.1 (h.2.2 _ hm)
  refine ⟨(gateAt C j).op, s, t, ?_, h.1 _ hm, ?_, ?_⟩
  · rw [← e]
    cases hg : gateAt C j
    simpa [hg] using hst
  · exact h.2.1 j hj s (by rw [hst]; simp)
  · exact h.2.1 j hj t (by rw [hst]; simp)

lemma restrict_build (n : ℕ) (z : Fin n) (gs : List Gate) (hok : Ok n gs) :
    ∃ (hs : List Gate) (m : ℕ → Option ℕ), Ok n hs ∧ hs.length ≤ gs.length ∧
      (hs.length = gs.length → ∀ g ∈ gs, z.val ∉ g.inputs) ∧ m z.val = none ∧
      ∀ w < n + gs.length,
        (∀ w', m w = some w' → w' < n + hs.length) ∧
        ∀ x : Fin n → Bool, ov hs (List.ofFn x) (m w) =
          (run gs (List.ofFn (Function.update x z false))).getD w false := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], (fun w => if w = z.val then none else some w), ?_, by simp, by simp,
      by simp, ?_⟩
    · intro j hj; simp at hj
    · intro w hw
      have hw' : w < n := by simpa using hw
      by_cases hz : w = z.val
      · subst w
        simp [ov, run]
      · refine ⟨?_, ?_⟩
        · intro w' he
          simp only [if_neg hz, Option.some.injEq] at he
          subst w'; simpa using hw'
        · intro x
          simp [ov, run, hz, List.getD_eq_getElem?_getD, hw',
            show (⟨w, hw'⟩ : Fin n) ≠ z from fun h => hz (congrArg Fin.val h)]
  | append_singleton gs g ih =>
    have hpre : Ok n gs := by
      intro j hj
      have h := hok j (by simp; omega)
      simpa only [List.getElem_append_left hj] using h
    obtain ⟨o, s, t, hg, ho, hs, ht⟩ := hok gs.length (by simp)
    have hgg : g = ⟨o, [s, t]⟩ := by simpa using hg
    subst g
    obtain ⟨ks, m, hk, hlen, heq, hz, hm⟩ := ih hpre
    obtain ⟨hms, hvs⟩ := hm s hs
    obtain ⟨hmt, hvt⟩ := hm t ht
    suffices hstep : ∃ (ls : List Gate) (v : Option ℕ), Ok n (ks ++ ls) ∧
        ls.length ≤ 1 ∧ (ls.length = 1 → s ≠ z.val ∧ t ≠ z.val) ∧
        (∀ w, v = some w → w < n + (ks ++ ls).length) ∧
        ∀ x : Fin n → Bool, ov (ks ++ ls) (List.ofFn x) v =
          o.eval [(run gs (List.ofFn (Function.update x z false))).getD s false,
            (run gs (List.ofFn (Function.update x z false))).getD t false] by
      obtain ⟨ls, v, hkl, hll, hnz, hv, hval⟩ := hstep
      refine ⟨ks ++ ls, Function.update m (n + gs.length) v, hkl, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]; omega
      · intro he g hmem
        have hklen : ks.length = gs.length := by
          simp only [List.length_append, List.length_singleton] at he
          omega
        have hls : ls.length = 1 := by
          simp only [List.length_append, List.length_singleton] at he
          omega
        rcases List.mem_append.1 hmem with hmem | hmem
        · exact heq hklen g hmem
        · simp only [List.mem_singleton] at hmem
          subst g
          simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or, ne_eq, eq_comm] using hnz hls
      · rw [Function.update_of_ne (by omega), hz]
      · intro w hw
        by_cases hwnew : w = n + gs.length
        · subst w
          rw [Function.update_self]
          refine ⟨hv, fun x => ?_⟩
          rw [hval x, run_snoc]
          have hl : (run gs (List.ofFn (Function.update x z false))).length = n + gs.length :=
            by rw [run_length, List.length_ofFn]
          rw [← hl, getD_at]
          rfl
        · rw [Function.update_of_ne hwnew]
          obtain ⟨hb, he⟩ := hm w (by simp only [List.length_append, List.length_singleton] at hw; omega)
          refine ⟨fun w' hw' => by have := hb w' hw'; simp; omega, fun x => ?_⟩
          rw [ov_ext ks ls _ _ (by simpa using hb), he x, run_snoc,
            getD_lt _ _ _ (by
              rw [run_length, List.length_ofFn]
              simp only [List.length_append, List.length_singleton] at hw
              omega)]
    cases hso : m s with
    | none =>
      cases ho with
      | inl hoa =>
        subst o
        refine ⟨[], none, by simpa using hk, by simp, by simp, by simp, fun x => ?_⟩
        rw [← hvs x, ← hvt x, hso]
        simp [ov, GateOp.eval]
      | inr hoa =>
        subst o
        refine ⟨[], m t, by simpa using hk, by simp, by simp, by simpa using hmt, fun x => ?_⟩
        rw [← hvs x, ← hvt x, hso]
        simp [ov, GateOp.eval]
    | some a =>
      cases hto : m t with
      | none =>
        cases ho with
        | inl hoa =>
          subst o
          refine ⟨[], none, by simpa using hk, by simp, by simp, by simp, fun x => ?_⟩
          rw [← hvs x, ← hvt x, hto]
          simp [ov, GateOp.eval]
        | inr hoa =>
          subst o
          refine ⟨[], m s, by simpa using hk, by simp, by simp, by simpa using hms, fun x => ?_⟩
          rw [← hvs x, ← hvt x, hto]
          simp [ov, GateOp.eval]
      | some b =>
        have ha := hms a hso
        have hb := hmt b hto
        refine ⟨[⟨o, [a, b]⟩], some (n + ks.length), ok_snoc hk ho ha hb,
          by simp, ?_, ?_, fun x => ?_⟩
        · intro _
          constructor
          · intro he; rw [he, hz] at hso; contradiction
          · intro he; rw [he, hz] at hto; contradiction
        · intro w hw; cases hw; simp
        · rw [ov_new ks n _ (by simp) _ _ _ ha hb, ← hvs x, ← hvt x, hso, hto]
          rfl

lemma restrict_circuit (n : ℕ) (C : Circuit) (z : Fin n)
    (hAO : PEqualNP.TopForm.IsAO2 n C) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size ≤ C.size ∧
      (D.size = C.size → ∀ g ∈ C.gates, z.val ∉ g.inputs) ∧
      ∀ x : Fin n → Bool, circuitFun n D x = circuitFun n C (Function.update x z false) := by
  classical
  obtain ⟨gs, m, hok, hlen, heq, _, hm⟩ := restrict_build n z C.gates (ao_ok hAO)
  let v := if C.output < n + C.gates.length then m C.output else none
  let w := v.getD (n + gs.length)
  refine ⟨⟨gs, w⟩, ok_ao hok, hlen, heq, fun x => ?_⟩
  change (run gs (List.ofFn x)).getD w false =
    (run C.gates (List.ofFn (Function.update x z false))).getD C.output false
  have hw : (run gs (List.ofFn x)).getD w false = ov gs (List.ofFn x) v := by
    cases hv : v with
    | none => simp [w, hv, ov, List.getD_eq_default, run_length]
    | some a => simp [w, hv, ov]
  rw [hw]
  by_cases ho : C.output < n + C.gates.length
  · simpa [v, ho] using (hm C.output ho).2 x
  · simp [v, ho, ov, List.getD_eq_default, run_length,
      show n + C.gates.length ≤ C.output by omega]

end Restriction

lemma restrict_clone_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v q : Fin n) (hvq : G.Adj v q) (C : Circuit) (hC : IsLeastAO (graph G v) C) :
    ∃ D : Circuit, IsLeastAO (eraseVertex (graph G v) (Fin.last n)) D ∧
      D.size + 1 = C.size ∧
      ∀ x : Fin (n + 1) → Bool,
        circuitFun (n + 1) D x = circuitFun (n + 1) C (Function.update x (Fin.last n) false) := by
  obtain ⟨D, hAO, hle, heq, hval⟩ := Restriction.restrict_circuit (n + 1) C (Fin.last n) hC.1
  have hne : D.size ≠ C.size := by
    intro hs
    obtain ⟨g, hg, hgn⟩ := cloned_input_read G v q hvq C hC.2.1
    exact heq hs g hg hgn
  have hcD : circuitFun (n + 1) D = graphFun (eraseVertex (graph G v) (Fin.last n)) ∅ := by
    funext x
    rw [hval x, hC.2.1, ← graphFun_eraseVertex]
  have hupper : ∀ E : Circuit, IsAO2 (n + 1) E →
      circuitFun (n + 1) E = graphFun (eraseVertex (graph G v) (Fin.last n)) ∅ →
      C.size ≤ E.size + 1 := by
    intro E hE hcE
    have h := hC.2.2 (Merge.circuit v.castSucc (Fin.last n) E)
      (Merge.ao _ _ E hE) (restore_circuit G v E hcE)
    simpa only [Merge.size] using h
  refine ⟨D, ⟨hAO, hcD, ?_⟩, ?_, hval⟩
  · intro E hE hcE
    have := hupper E hE hcE
    omega
  · have := hupper D hAO hcD
    omega

end PEqualNP.Outside.L_meta_5012.Twin


namespace PEqualNP.Outside.L_meta_5012.Singleton

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def product {n : ℕ} (v : Fin n) (A B : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  x v || (decide (∃ a ∈ A, x a = true) && decide (∃ b ∈ B, x b = true))

lemma product_eq {n : ℕ} (v : Fin n) (A B : Finset (Fin n)) (x : Fin n → Bool) :
    ((x v || decide (∃ a ∈ A, x a = true)) &&
      (x v || decide (∃ b ∈ B, x b = true))) = product v A B x := by
  cases hx : x v <;> simp [product, hx]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : Fin n) : graphFun G ∅ (pairInput a b) = true ↔ G.Adj a b := by
  unfold graphFun
  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
    decide_eq_true_eq]
  constructor
  · rintro ⟨u, w, huw, hu, hw⟩
    have hua : u = a ∨ u = b := by simpa [pairInput] using hu
    have hwa : w = a ∨ w = b := by simpa [pairInput] using hw
    rcases hua with rfl | rfl <;> rcases hwa with rfl | rfl
    · exact False.elim (huw.ne rfl)
    · exact huw
    · exact huw.symm
    · exact False.elim (huw.ne rfl)
  · intro hab
    exact ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩

lemma filter_adjacent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) (A B : Finset (Fin n)) (w : Fin n)
    (hclean : ∀ x : Fin n → Bool, product v A B x = true → x w = true → graphFun G ∅ x = true) :
    G.Adj v w := by
  apply (graphFun_pair G v w).mp
  apply hclean
  · simp [product, pairInput]
  · simp [pairInput]

lemma filter_of_nonedge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) (A B : Finset (Fin n)) (a b w : Fin n)
    (ha : a ∈ A) (hb : b ∈ B) (hnon : ¬ G.Adj a b)
    (hclean : ∀ x : Fin n → Bool, product v A B x = true → x w = true → graphFun G ∅ x = true) :
    G.Adj a w ∨ G.Adj b w := by
  let x : Fin n → Bool := fun i => decide (i = a ∨ i = b ∨ i = w)
  have hprod : product v A B x = true := by
    simp only [product, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨⟨a, ha, by simp [x]⟩, ⟨b, hb, by simp [x]⟩⟩
  have hF := hclean x hprod (by simp [x])
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq] at hF
  obtain ⟨u, t, hut, hu, ht⟩ := hF
  have hua : u = a ∨ u = b ∨ u = w := by simpa [x] using hu
  have hta : t = a ∨ t = b ∨ t = w := by simpa [x] using ht
  rcases hua with rfl | rfl | rfl <;> rcases hta with rfl | rfl | rfl
  · exact False.elim (hut.ne rfl)
  · exact False.elim (hnon hut)
  · exact Or.inl hut
  · exact False.elim (hnon hut.symm)
  · exact False.elim (hut.ne rfl)
  · exact Or.inr hut
  · exact Or.inl hut.symm
  · exact Or.inr hut.symm
  · exact False.elim (hut.ne rfl)

lemma neighbors_in_filters {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (v : Fin n) (W : Finset (Fin n))
    (hW : ∀ w ∈ W, G.Adj v w) (a : Fin n) (ha : a ≠ v) :
    (W.filter fun w => G.Adj a w).card ≤ 1 := by
  apply (Finset.card_le_card _).trans (h4 a v ha)
  intro w hw
  obtain ⟨hw, haw⟩ := Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, haw, hW w hw⟩

lemma three_filters_cross {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (v : Fin n) (A B W : Finset (Fin n))
    (hvA : v ∉ A) (hvB : v ∉ B) (hcard : 3 ≤ W.card)
    (hclean : ∀ w ∈ W, ∀ x : Fin n → Bool,
      product v A B x = true → x w = true → graphFun G ∅ x = true) :
    ∀ a ∈ A, ∀ b ∈ B, G.Adj a b := by
  intro a ha b hb
  by_contra hnon
  have hav : a ≠ v := by intro h; subst a; exact hvA ha
  have hbv : b ≠ v := by intro h; subst b; exact hvB hb
  have hW : ∀ w ∈ W, G.Adj v w := fun w hw => filter_adjacent G v A B w (hclean w hw)
  have hA := neighbors_in_filters G h4 v W hW a hav
  have hB := neighbors_in_filters G h4 v W hW b hbv
  have hsub : W ⊆ (W.filter fun w => G.Adj a w) ∪ (W.filter fun w => G.Adj b w) := by
    intro w hw
    rcases filter_of_nonedge G v A B a b w ha hb hnon (hclean w hw) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, h⟩)
  have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

lemma complete_cross_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B : Finset (Fin n))
    (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) : A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_cases hA : A.card ≤ 1
  · exact Or.inl hA
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
  apply Or.inr
  apply (Finset.card_le_card _).trans (h4 a b hab)
  intro w hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcross a ha w hw, hcross b hb w hw⟩

lemma three_filters_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (v : Fin n) (A B W : Finset (Fin n))
    (hvA : v ∉ A) (hvB : v ∉ B) (hcard : 3 ≤ W.card)
    (hclean : ∀ w ∈ W, ∀ x : Fin n → Bool,
      product v A B x = true → x w = true → graphFun G ∅ x = true) :
    (∀ a ∈ A, ∀ b ∈ B, G.Adj a b) ∧ (A.card ≤ 1 ∨ B.card ≤ 1) := by
  have hcross := three_filters_cross G h4 v A B W hvA hvB hcard hclean
  exact ⟨hcross, complete_cross_star G h4 A B hcross⟩

lemma three_wmax_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (C : Circuit) (g : ℕ) (v : Fin n) (A B : Finset (Fin n))
    (hvA : v ∉ A) (hvB : v ∉ B) (hcard : 3 ≤ (wmax G C g).card)
    (heval : ∀ x : Fin n → Bool, gateVal n C g x =
      ((x v || decide (∃ a ∈ A, x a = true)) &&
        (x v || decide (∃ b ∈ B, x b = true)))) :
    (∀ a ∈ A, ∀ b ∈ B, G.Adj a b) ∧ (A.card ≤ 1 ∨ B.card ≤ 1) := by
  apply three_filters_star G h4 v A B (wmax G C g) hvA hvB hcard
  intro w hw x hx hxw
  apply (Finset.mem_filter.mp hw).2 x _ hxw
  rw [heval, product_eq]
  exact hx

end PEqualNP.Outside.L_meta_5012.Singleton


namespace PEqualNP.Outside.L_meta_5012.Overlap

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def rawOr {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ A, x a = true)

def product {n : ℕ} (A B : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  rawOr A x && rawOr B x

def CleanFilter {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (w : Fin n) : Prop :=
  ∀ x, (product A B x && x w) = true → graphFun G ∅ x = true

def cleanFilters {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun w =>
    ∀ x, (product A B x && x w) = true → graphFun G ∅ x = true

lemma mem_cleanFilters {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (w : Fin n) :
    w ∈ cleanFilters G A B ↔ CleanFilter G A B w := by
  simp [cleanFilters, CleanFilter]

def CleanMutual {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C D : Finset (Fin n)) : Prop :=
  ∀ x, (product A B x && product C D x) = true → graphFun G ∅ x = true

lemma graphFun_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) : graphFun G ∅ x = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  rw [graphFun_true]
  simp only [pairInput, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro huv
    exact ⟨u, v, huv, Or.inl rfl, Or.inr rfl⟩

lemma rawOr_true {n : ℕ} {A : Finset (Fin n)} {x : Fin n → Bool}
    {a : Fin n} (ha : a ∈ A) (hx : x a = true) : rawOr A x = true :=
  decide_eq_true ⟨a, ha, hx⟩

lemma product_overlap_true {n : ℕ} {A B : Finset (Fin n)} {x : Fin n → Bool}
    {a : Fin n} (ha : a ∈ A ∩ B) (hx : x a = true) : product A B x = true := by
  simp only [product, rawOr_true (Finset.mem_inter.mp ha).1 hx,
    rawOr_true (Finset.mem_inter.mp ha).2 hx, Bool.and_self]

lemma cleanFilter_adj_overlap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) {w a : Fin n} (hw : CleanFilter G A B w)
    (ha : a ∈ A ∩ B) : G.Adj w a := by
  apply (graphFun_pair G w a).1
  apply hw
  have hp := product_overlap_true ha (x := pairInput w a) (by simp [pairInput])
  simp [hp, pairInput]

lemma filters_card_le_one_of_overlap {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A B : Finset (Fin n)) (hG : NoFourCycle G)
    (hAB : 2 ≤ (A ∩ B).card) : (cleanFilters G A B).card ≤ 1 := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (A ∩ B).card)
  have hsub : cleanFilters G A B ⊆
      Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
    intro w hw
    have hwf : CleanFilter G A B w := (mem_cleanFilters G A B w).1 hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(cleanFilter_adj_overlap G A B hwf ha).symm,
      (cleanFilter_adj_overlap G A B hwf hb).symm⟩
  exact (Finset.card_le_card hsub).trans (hG a b hab)

lemma cleanFilter_factor_opposite {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A B : Finset (Fin n)) (c : Fin n → Bool)
    (hc : ∀ u v, G.Adj u v → c u ≠ c v) {w : Fin n}
    (hw : CleanFilter G A B w) :
    (∀ a ∈ A, c a ≠ c w) ∨ (∀ b ∈ B, c b ≠ c w) := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨⟨a, ha, haw⟩, ⟨b, hb, hbw⟩⟩ := hn
  let x : Fin n → Bool := fun i => decide (c i = c w)
  have haX : x a = true := by simp [x, haw]
  have hbX : x b = true := by simp [x, hbw]
  have hp : product A B x = true := by
    simp [product, rawOr_true ha haX, rawOr_true hb hbX]
  have hf : graphFun G ∅ x = true := hw x (by simp [hp, x])
  obtain ⟨u, v, huv, hu, hv⟩ := (graphFun_true G x).1 hf
  have hu' : c u = c w := by simpa [x] using hu
  have hv' : c v = c w := by simpa [x] using hv
  exact hc u v huv (hu'.trans hv'.symm)

lemma cleanFilter_overlap_same_color {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A B : Finset (Fin n)) (c : Fin n → Bool)
    (hc : ∀ u v, G.Adj u v → c u ≠ c v) {w u v : Fin n}
    (hw : CleanFilter G A B w) (hu : u ∈ A ∩ B) (hv : v ∈ A ∩ B) : c u = c v := by
  have hwu := hc w u (cleanFilter_adj_overlap G A B hw hu)
  have hwv := hc w v (cleanFilter_adj_overlap G A B hw hv)
  cases hwc : c w <;> cases huc : c u <;> cases hvc : c v <;> simp_all

lemma filters_empty_of_mixed_overlap {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A B : Finset (Fin n)) (c : Fin n → Bool)
    (hc : ∀ u v, G.Adj u v → c u ≠ c v)
    (hmix : ∃ u ∈ A ∩ B, ∃ v ∈ A ∩ B, c u ≠ c v) : cleanFilters G A B = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hwf : CleanFilter G A B w := (mem_cleanFilters G A B w).1 hw
  obtain ⟨u, hu, v, hv, huv⟩ := hmix
  exact huv (cleanFilter_overlap_same_color G A B c hc hwf hu hv)

lemma cleanMutual_adj_overlaps {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A B C D : Finset (Fin n))
    (hclean : CleanMutual G A B C D) {u v : Fin n}
    (hu : u ∈ A ∩ B) (hv : v ∈ C ∩ D) : G.Adj u v := by
  apply (graphFun_pair G u v).1
  apply hclean
  have hp := product_overlap_true hu (x := pairInput u v) (by simp [pairInput])
  have hq := product_overlap_true hv (x := pairInput u v) (by simp [pairInput])
  simp [hp, hq]

lemma cleanMutual_small_overlap {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A B C D : Finset (Fin n)) (hG : NoFourCycle G)
    (hclean : CleanMutual G A B C D) : (A ∩ B).card ≤ 1 ∨ (C ∩ D).card ≤ 1 := by
  by_cases hAB : (A ∩ B).card ≤ 1
  · exact Or.inl hAB
  · right
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (A ∩ B).card)
    have hsub : C ∩ D ⊆ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨cleanMutual_adj_overlaps G A B C D hclean ha hw,
        cleanMutual_adj_overlaps G A B C D hclean hb hw⟩
    exact (Finset.card_le_card hsub).trans (hG a b hab)



abbrev pathGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun u v =>
    (u.val = 0 ∧ (v.val = 1 ∨ v.val = 2)) ∨ (u.val = 2 ∧ v.val = 3)

lemma pathGraph_bipartite :
    ∀ u v : Fin 4, pathGraph.Adj u v →
      decide (u.val = 0 ∨ u.val = 3) ≠ decide (v.val = 0 ∨ v.val = 3) := by decide

lemma pathGraph_noFourCycle : NoFourCycle pathGraph := by decide

lemma path_singleton_overlap : ({0, 2} ∩ {1, 2} : Finset (Fin 4)) = {2} := by decide

lemma path_two_cleanFilters : cleanFilters pathGraph {0, 2} {1, 2} = {0, 3} := by decide



lemma bool_overlap_distribute (v a b w : Bool) (hvb : v = true → b = true)
    (haw : a = true → w = true) :
    (((v || a) && b) && w) = ((a && b) || (v && w)) := by
  cases v <;> cases a <;> cases b <;> cases w <;> simp_all

lemma rawOr_pair {n : ℕ} (v a : Fin n) (x : Fin n → Bool) :
    rawOr {v, a} x = (x v || x a) := by
  simp [rawOr]

lemma overlap_distribute {n : ℕ} (v a : Fin n) (B W : Finset (Fin n))
    (hv : v ∈ B) (ha : a ∈ W) (x : Fin n → Bool) :
    (product {v, a} B x && rawOr W x) =
      ((x a && rawOr B x) || (x v && rawOr W x)) := by
  rw [product, rawOr_pair]
  exact bool_overlap_distribute (x v) (x a) (rawOr B x) (rawOr W x)
    (fun h => rawOr_true hv h) (fun h => rawOr_true ha h)

lemma overlap_distribute_clean {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (v a : Fin n) (B W : Finset (Fin n))
    (hv : v ∈ B) (ha : a ∈ W)
    (hclean : ∀ x, (product {v, a} B x && rawOr W x) = true → graphFun G ∅ x = true) :
    (∀ x, (x a && rawOr B x) = true → graphFun G ∅ x = true) ∧
      (∀ x, (x v && rawOr W x) = true → graphFun G ∅ x = true) := by
  constructor
  · intro x hx
    apply hclean x
    rw [overlap_distribute v a B W hv ha, hx]
    rfl
  · intro x hx
    apply hclean x
    rw [overlap_distribute v a B W hv ha, hx]
    simp

end PEqualNP.Outside.L_meta_5012.Overlap
