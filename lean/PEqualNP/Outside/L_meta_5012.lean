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



namespace PEqualNP.Outside.L_meta_5012.CriticalEdge

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

lemma run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



def u (n : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del : Finset ℕ) (L : ℕ → List ℕ) (x : List Bool)
    (w : ℕ) : Bool :=
  if w < n then x.getD w false
  else if w - n ∈ Del then false
  else if A (w - n) = true then
    ((if _h : a (w - n) < w then u n A a b Del L x (a (w - n)) else false) ||
      (L (w - n)).any (fun t => x.getD t false)) &&
    (if _h : b (w - n) < w then u n A a b Del L x (b (w - n)) else false)
  else
    (if _h : a (w - n) < w then u n A a b Del L x (a (w - n)) else false) ||
    (if _h : b (w - n) < w then u n A a b Del L x (b (w - n)) else false)
termination_by w

section WireLemmas
variable {n : ℕ} {A : ℕ → Bool} {a b : ℕ → ℕ} {Del : Finset ℕ} {L : ℕ → List ℕ} {x : List Bool}

lemma u_in {w : ℕ} (h : w < n) : u n A a b Del L x w = x.getD w false := by
  rw [u, if_pos h]

lemma u_del {j : ℕ} (h : j ∈ Del) : u n A a b Del L x (n + j) = false := by
  rw [u, if_neg (by omega), Nat.add_sub_cancel_left, if_pos h]

lemma u_and {j : ℕ} (h : j ∉ Del) (hA : A j = true) (ha : a j < n + j) (hb : b j < n + j) :
    u n A a b Del L x (n + j) = ((u n A a b Del L x (a j) ||
      (L j).any (fun t => x.getD t false)) && u n A a b Del L x (b j)) := by
  rw [u, if_neg (by omega), Nat.add_sub_cancel_left, if_neg h, if_pos hA, dif_pos ha, dif_pos hb]

lemma u_or {j : ℕ} (h : j ∉ Del) (hA : A j = false) (ha : a j < n + j) (hb : b j < n + j) :
    u n A a b Del L x (n + j) = (u n A a b Del L x (a j) || u n A a b Del L x (b j)) := by
  rw [u, if_neg (by omega), Nat.add_sub_cancel_left, if_neg h, if_neg (by simp [hA]), dif_pos ha,
    dif_pos hb]
end WireLemmas

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

open Classical in
noncomputable def dc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) : ℕ :=
  ((Finset.range gs.length).filter fun i => (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧
    ∃ x : Fin n → Bool, (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false).card

open Classical in
lemma dc_snoc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) (g : Gate) :
    dc n F (gs ++ [g]) ≤ dc n F gs + if g.op = GateOp.and ∧
      ∃ x : Fin n → Bool, (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = true ∧
        F x = false then 1 else 0 := by
  unfold dc
  rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert]
  have e : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
    simp [List.getD_eq_getElem?_getD]
  rw [e]
  have h1 : ((Finset.range gs.length).filter fun i =>
      ((gs ++ [g]).getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run (gs ++ [g]) (List.ofFn x)).getD (n + i) false = true ∧ F x = false) =
      (Finset.range gs.length).filter fun i =>
      (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false := by
    refine Finset.filter_congr fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [getD_ltz _ _ _ _ hi']
    refine and_congr_right fun _ => exists_congr fun x => ?_
    rw [run_prefix gs [g] _ _ (by simp; omega)]
  rw [h1]
  split_ifs with h
  · exact (Finset.card_insert_le _ _)
  · simp

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

lemma chain (n : ℕ) (F : (Fin n → Bool) → Bool) : ∀ (l : List ℕ), (∀ t ∈ l, t < n) →
    ∀ (gs : List Gate), Ok n gs → ∀ o : Option ℕ, (∀ w, o = some w → w < n + gs.length) →
    ∃ (hs : List Gate) (o' : Option ℕ), Ok n (gs ++ hs) ∧ hs.length ≤ l.length ∧
      dc n F (gs ++ hs) ≤ dc n F gs ∧ (∀ w, o' = some w → w < n + (gs ++ hs).length) ∧
      ∀ x : Fin n → Bool, ov (gs ++ hs) (List.ofFn x) o' =
        (ov gs (List.ofFn x) o || l.any (fun t => (List.ofFn x).getD t false)) := by
  intro l
  induction l with
  | nil =>
    intro _ gs hgs o ho
    exact ⟨[], o, by simpa using hgs, by simp, by simp, by simpa using ho, by simp⟩
  | cons t l ih =>
    intro hl gs hgs o ho
    have ht : t < n := hl t (by simp)
    have hl' : ∀ t ∈ l, t < n := fun s hs => hl s (by simp [hs])
    cases o with
    | none =>
      obtain ⟨hs, o', h1, h2, h3, h4, h5⟩ := ih hl' gs hgs (some t) (by
        intro w hw; cases hw; omega)
      refine ⟨hs, o', h1, by simp; omega, h3, h4, fun x => ?_⟩
      rw [h5 x]
      have : ov gs (List.ofFn x) (some t) = (List.ofFn x).getD t false :=
        run_input _ _ _ (by simpa using ht)
      rw [this]; simp [ov]
    | some w =>
      have hw := ho w rfl
      obtain ⟨hs, o', h1, h2, h3, h4, h5⟩ := ih hl' (gs ++ [⟨GateOp.or, [w, t]⟩])
        (ok_snoc hgs (Or.inr rfl) hw (by omega)) (some (n + gs.length)) (by
          intro w hw; cases hw; simp)
      refine ⟨⟨GateOp.or, [w, t]⟩ :: hs, o', by simpa using h1, by simp; omega, ?_,
        by simpa using h4, fun x => ?_⟩
      · have := dc_snoc n F gs ⟨GateOp.or, [w, t]⟩
        rw [if_neg (by simp)] at this
        have e : gs ++ ⟨GateOp.or, [w, t]⟩ :: hs = gs ++ [⟨GateOp.or, [w, t]⟩] ++ hs := by simp
        rw [e]; omega
      · have e : gs ++ ⟨GateOp.or, [w, t]⟩ :: hs = gs ++ [⟨GateOp.or, [w, t]⟩] ++ hs := by simp
        rw [e, h5 x, ov_new gs n _ (by simp) _ _ _ hw (by omega)]
        rw [run_input gs (List.ofFn x) t (by simpa using ht)]
        simp [ov, GateOp.eval, Bool.or_assoc]

open Classical in
lemma build (n : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del R : Finset ℕ) (L : ℕ → List ℕ)
    (F : (Fin n → Bool) → Bool) (hL : ∀ j, ∀ t ∈ L j, t < n)
    (hR : ∀ j ∈ R, A j = false ∧ j ∉ Del ∧ ∃ d ∈ Del, d < j ∧ (a j = n + d ∨ b j = n + d)) :
    ∀ p, (∀ j < p, a j < n + j ∧ b j < n + j) →
    ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧
      (∀ w < n + p, (∀ w', m w = some w' → w' < n + gs.length) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) = u n A a b Del L (List.ofFn x) w) ∧
      (∀ d ∈ Del, d < p → m (n + d) = none) ∧
      gs.length + ((Finset.range p).filter (· ∈ Del)).card +
        ((Finset.range p).filter (· ∈ R)).card ≤ p + ∑ j ∈ Finset.range p, (L j).length ∧
      dc n F gs ≤ ((Finset.range p).filter fun j => A j = true ∧ j ∉ Del ∧
        ∃ x : Fin n → Bool, u n A a b Del L (List.ofFn x) (n + j) = true ∧ F x = false).card := by
  intro p
  induction p with
  | zero =>
    intro _
    refine ⟨[], fun w => some w, by intro j hj; simp at hj, ?_, by simp, by simp, by simp [dc]⟩
    intro w hw
    refine ⟨by intro w' h; cases h; simpa using hw, fun x => ?_⟩
    rw [u_in (by omega)]; rfl
  | succ p ih =>
    intro hab
    obtain ⟨gs, m, hok, hm, hd, hc, hj⟩ := ih fun j hj => hab j (by omega)
    obtain ⟨hap, hbp⟩ := hab p (by omega)
    suffices hh : ∃ (hs : List Gate) (o : Option ℕ), Ok n (gs ++ hs) ∧
        (∀ w, o = some w → w < n + (gs ++ hs).length) ∧ (p ∈ Del → o = none) ∧
        (∀ x : Fin n → Bool, ov (gs ++ hs) (List.ofFn x) o =
          u n A a b Del L (List.ofFn x) (n + p)) ∧
        hs.length + (if p ∈ Del then 1 else 0) + (if p ∈ R then 1 else 0) ≤ 1 + (L p).length ∧
        dc n F (gs ++ hs) ≤ dc n F gs + if A p = true ∧ p ∉ Del ∧ ∃ x : Fin n → Bool,
          u n A a b Del L (List.ofFn x) (n + p) = true ∧ F x = false then 1 else 0 by
      obtain ⟨hs, o, h1, h2, h3, h4, h5, h6⟩ := hh
      refine ⟨gs ++ hs, Function.update m (n + p) o, h1, ?_, ?_, ?_, ?_⟩
      · intro w hw
        by_cases hwp : w = n + p
        · subst hwp; rw [Function.update_self]; exact ⟨h2, h4⟩
        · rw [Function.update_of_ne hwp]
          obtain ⟨q1, q2⟩ := hm w (by omega)
          refine ⟨fun w' hw' => by have := q1 w' hw'; simp; omega, fun x => ?_⟩
          rw [ov_ext gs hs _ _ (by simpa using q1), q2]
      · intro d hdd hdp
        by_cases hdp' : d = p
        · subst hdp'; rw [Function.update_self]; exact h3 hdd
        · rw [Function.update_of_ne (by omega)]; exact hd d hdd (by omega)
      · rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert,
          Finset.sum_insert (by simp), List.length_append]
        split_ifs at h5 ⊢ with q1 q2 q2 <;>
          (try rw [Finset.card_insert_of_notMem (by simp)]) <;>
          (try rw [Finset.card_insert_of_notMem (by simp)]) <;> omega
      · rw [Finset.range_add_one, Finset.filter_insert]
        split_ifs at h6 ⊢ with q1
        · rw [Finset.card_insert_of_notMem (by simp)]; omega
        · omega
    by_cases hpd : p ∈ Del
    · have hpR : p ∉ R := fun h => (hR p h).2.1 hpd
      refine ⟨[], none, by simpa using hok, by simp, fun _ => rfl, fun x => ?_, ?_, by simp⟩
      · rw [u_del hpd]; rfl
      · rw [if_pos hpd, if_neg hpR]; simp
    obtain ⟨a1, a2⟩ := hm (a p) hap
    obtain ⟨b1, b2⟩ := hm (b p) hbp
    cases hA : A p with
    | false =>
      have hu := fun x : Fin n → Bool => u_or (L := L) (x := List.ofFn x) hpd hA hap hbp
      rcases ha0 : m (a p) with _ | s
      · refine ⟨[], m (b p), by simpa using hok, by simpa using b1, fun h => absurd h hpd,
          fun x => ?_, ?_, by simp⟩
        · rw [hu x, ← a2 x, ← b2 x, ha0]; simp [ov]
        · rw [if_neg hpd]; split_ifs <;> simp
      rcases hb0 : m (b p) with _ | t
      · refine ⟨[], m (a p), by simpa using hok, by simpa using a1, fun h => absurd h hpd,
          fun x => ?_, ?_, by simp⟩
        · rw [hu x, ← a2 x, ← b2 x, hb0]; simp [ov]
        · rw [if_neg hpd]; split_ifs <;> simp
      have hpR : p ∉ R := by
        intro h
        obtain ⟨_, _, d, hd1, hd2, hd3⟩ := hR p h
        have := hd d hd1 hd2
        rcases hd3 with h | h
        · rw [h, this] at ha0; cases ha0
        · rw [h, this] at hb0; cases hb0
      have hs := a1 s ha0
      have ht := b1 t hb0
      refine ⟨[⟨GateOp.or, [s, t]⟩], some (n + gs.length), ok_snoc hok (Or.inr rfl) hs ht,
        by intro w hw; cases hw; simp, fun h => absurd h hpd, fun x => ?_, ?_, ?_⟩
      · rw [ov_new gs n _ (by simp) _ _ _ hs ht, hu x, ← a2 x, ← b2 x, ha0, hb0]
        simp [ov, GateOp.eval]
      · rw [if_neg hpd, if_neg hpR]; simp
      · have := dc_snoc n F gs ⟨GateOp.or, [s, t]⟩
        rw [if_neg (by simp)] at this
        omega
    | true =>
      have hu := fun x : Fin n → Bool => u_and (L := L) (x := List.ofFn x) hpd hA hap hbp
      have hpR : p ∉ R := fun h => by rw [(hR p h).1] at hA; cases hA
      obtain ⟨hs, o', c1, c2, c3, c4, c5⟩ := chain n F (L p) (hL p) gs hok (m (a p)) a1
      rcases ho : o' with _ | s
      · refine ⟨hs, none, c1, by simp, fun _ => rfl, fun x => ?_, ?_, by omega⟩
        · have := c5 x
          rw [ho, a2 x] at this
          rw [hu x, ← this]; simp [ov]
        · rw [if_neg hpd, if_neg hpR]; omega
      rcases hb0 : m (b p) with _ | t
      · refine ⟨hs, none, c1, by simp, fun _ => rfl, fun x => ?_, ?_, by omega⟩
        · have := b2 x
          rw [hb0] at this
          rw [hu x, ← this]; simp [ov]
        · rw [if_neg hpd, if_neg hpR]; omega
      have hs' := c4 s ho
      have ht : t < n + (gs ++ hs).length := by have := b1 t hb0; simp; omega
      have hval : ∀ x : Fin n → Bool, ov (gs ++ hs ++ [⟨GateOp.and, [s, t]⟩]) (List.ofFn x)
          (some (n + (gs ++ hs).length)) = u n A a b Del L (List.ofFn x) (n + p) := by
        intro x
        rw [ov_new (gs ++ hs) n _ (by simp) _ _ _ hs' ht, hu x, ← a2 x, ← b2 x, ← c5 x, ho, hb0,
          ← ov_ext gs hs (List.ofFn x) (some t) (by intro w hw; cases hw; simpa using b1 t hb0)]
        simp [ov, GateOp.eval]
      refine ⟨hs ++ [⟨GateOp.and, [s, t]⟩], some (n + (gs ++ hs).length), ?_, ?_,
        fun h => absurd h hpd, fun x => ?_, ?_, ?_⟩
      · rw [← List.append_assoc]; exact ok_snoc c1 (Or.inl rfl) hs' ht
      · intro w hw; cases hw; simp
      · rw [← List.append_assoc]; exact hval x
      · rw [if_neg hpd, if_neg hpR]; simp; omega
      · rw [← List.append_assoc]
        have := dc_snoc n F (gs ++ hs) ⟨GateOp.and, [s, t]⟩
        have e : ((⟨GateOp.and, [s, t]⟩ : Gate).op = GateOp.and ∧ ∃ x : Fin n → Bool,
            (run (gs ++ hs ++ [⟨GateOp.and, [s, t]⟩]) (List.ofFn x)).getD
              (n + (gs ++ hs).length) false = true ∧ F x = false) ↔
            (true = true ∧ p ∉ Del ∧ ∃ x : Fin n → Bool,
              u n A a b Del L (List.ofFn x) (n + p) = true ∧ F x = false) := by
          refine ⟨fun h => ⟨rfl, hpd, ?_⟩, fun h => ⟨rfl, ?_⟩⟩
          · obtain ⟨x, h1, h2⟩ := h.2
            exact ⟨x, by rw [← hval x]; exact h1, h2⟩
          · obtain ⟨x, h1, h2⟩ := h.2.2
            exact ⟨x, by rw [← hval x] at h1; exact h1, h2⟩
        rw [if_congr e rfl rfl] at this
        omega

lemma gf {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ p q, G.Adj p q ∧ x p = true ∧ x q = true := by
  simp [graphFun]

lemma gD {n : ℕ} (x : Fin n → Bool) (p : Fin n) : (List.ofFn x).getD p.val false = x p := by
  simp [List.getD_eq_getElem?_getD]

lemma u_mono {n N : ℕ} {A : ℕ → Bool} {a b : ℕ → ℕ} {Del : Finset ℕ} {L : ℕ → List ℕ}
    (hab : ∀ j < N, a j < n + j ∧ b j < n + j) (x y : List Bool)
    (h : ∀ t, x.getD t false = true → y.getD t false = true) :
    ∀ w < n + N, u n A a b Del L x w = true → u n A a b Del L y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hx
    by_cases h9 : w < n
    · rw [u_in h9] at hx ⊢; exact h _ hx
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    obtain ⟨ha, hb⟩ := hab j (by omega)
    by_cases hd : j ∈ Del
    · rw [u_del hd] at hx; cases hx
    have ia := ih (a j) ha (by omega)
    have ib := ih (b j) hb (by omega)
    cases hA : A j with
    | true =>
      rw [u_and hd hA ha hb, Bool.and_eq_true, Bool.or_eq_true] at hx ⊢
      refine ⟨?_, ib hx.2⟩
      rcases hx.1 with h1 | h1
      · exact Or.inl (ia h1)
      · right
        rw [List.any_eq_true] at h1 ⊢
        obtain ⟨t, h2, h3⟩ := h1
        exact ⟨t, h2, h t h3⟩
    | false =>
      rw [u_or hd hA ha hb, Bool.or_eq_true] at hx ⊢
      rcases hx with h1 | h1
      · exact Or.inl (ia h1)
      · exact Or.inr (ib h1)

lemma gate2 {n : ℕ} {C : Circuit} (h : TopForm.IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    C.gates[j] = gateAt C j ∧ (gateAt C j).inputs = [TopForm.opnd C j 0, TopForm.opnd C j 1] ∧
    TopForm.opnd C j 0 < n + j ∧ TopForm.opnd C j 1 < n + j ∧
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hm : gateAt C j ∈ C.gates := by rw [e]; exact List.getElem_mem hj
  have hl := h.2.2 _ hm
  obtain ⟨s, t, hst⟩ := List.length_eq_two.1 hl
  have hb := h.2.1 j hj
  rw [hst] at hb
  have e0 : TopForm.opnd C j 0 = s := by unfold TopForm.opnd; rw [hst]; rfl
  have e1 : TopForm.opnd C j 1 = t := by unfold TopForm.opnd; rw [hst]; rfl
  refine ⟨e.symm, by rw [hst, e0, e1], by rw [e0]; exact hb s (by simp),
    by rw [e1]; exact hb t (by simp), h.1 _ hm⟩

lemma veq (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length) (o : GateOp)
    (s t : ℕ) (e : gs[j] = ⟨o, [s, t]⟩) (hs : s < n + j) (ht : t < n + j) :
    (run gs (List.ofFn x)).getD (n + j) false = o.eval [(run gs (List.ofFn x)).getD s false,
      (run gs (List.ofFn x)).getD t false] := by
  have := run_gate gs (List.ofFn x) j hj
  rw [List.length_ofFn, e] at this
  rw [this]
  simp [hs, ht]

lemma gate_eta {g : Gate} {o : GateOp} {l : List ℕ} (h1 : g.op = o) (h2 : g.inputs = l) :
    g = ⟨o, l⟩ := by
  cases g; cases h1; cases h2; rfl

lemma gDv {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := gD x ⟨w, hw⟩
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

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def isAnd (C : Circuit) (j : ℕ) : Bool :=
  match (gateAt C j).op with
  | .and => true
  | _ => false

def val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (run C.gates (List.ofFn x)).getD w false

def cutVal (n : ℕ) (C : Circuit) (Del : Finset ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  u n (isAnd C) (fun j => opnd C j 0) (fun j => opnd C j 1) Del (fun _ => []) (List.ofFn x) w

lemma val_in {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val n C x w = (List.ofFn x).getD w false := by
  exact run_input C.gates (List.ofFn x) w (by simpa using hw)

lemma val_rec {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    val n C x (n + j) = if isAnd C j = true then
      val n C x (opnd C j 0) && val n C x (opnd C j 1)
    else val n C x (opnd C j 0) || val n C x (opnd C j 1) := by
  obtain ⟨heq, hin, ha, hb, hop⟩ := gate2 hC hj
  have hr := run_gate C.gates (List.ofFn x) j hj
  rw [List.length_ofFn, heq, hin] at hr
  rcases hop with hop | hop
  · simp only [val, hr, hop, List.map_cons, List.map_nil, if_pos ha, if_pos hb]
    simp [isAnd, hop, GateOp.eval]
  · simp only [val, hr, hop, List.map_cons, List.map_nil, if_pos ha, if_pos hb]
    simp [isAnd, hop, GateOp.eval]

lemma cutVal_le {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (Del : Finset ℕ)
    (x : Fin n → Bool) :
    ∀ w < n + C.gates.length, cutVal n C Del x w = true → val n C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw h
    by_cases hin : w < n
    · simpa only [cutVal, u_in hin, val_in C x w hin] using h
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    obtain ⟨_, _, ha, hb, _⟩ := gate2 hC hj
    by_cases hd : j ∈ Del
    · simp only [cutVal, u_del hd] at h
      cases h
    rw [val_rec C hC x j hj]
    cases hA : isAnd C j with
    | false =>
      simp only [hA, Bool.false_eq_true, ↓reduceIte]
      rw [cutVal, u_or hd hA ha hb, Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Bool.or_eq_true]; exact Or.inl (ih _ ha (by omega) h)
      · rw [Bool.or_eq_true]; exact Or.inr (ih _ hb (by omega) h)
    | true =>
      simp only [hA, ↓reduceIte]
      rw [cutVal, u_and hd hA ha hb] at h
      simp only [List.any_nil, Bool.or_false, Bool.and_eq_true] at h
      rw [Bool.and_eq_true]; exact ⟨ih _ ha (by omega) h.1, ih _ hb (by omega) h.2⟩

lemma cutVal_eq_of_zero {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j : ℕ)
    (x : Fin n → Bool) (hz : val n C x (n + j) = false) :
    ∀ w < n + C.gates.length, cutVal n C {j} x w = val n C x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hin : w < n
    · simp only [cutVal, u_in hin, val_in C x w hin]
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    obtain ⟨_, _, ha, hb, _⟩ := gate2 hC hk
    by_cases hd : k ∈ ({j} : Finset ℕ)
    · have hkj : k = j := Finset.mem_singleton.mp hd
      subst k
      rw [cutVal, u_del (Finset.mem_singleton_self j), hz]
    rw [val_rec C hC x k hk]
    have ia := ih (opnd C k 0) ha (by omega)
    have ib := ih (opnd C k 1) hb (by omega)
    cases hA : isAnd C k with
    | false =>
      simp only [hA, Bool.false_eq_true, ↓reduceIte]
      rw [cutVal, u_or hd hA ha hb]
      exact congrArg₂ Bool.or ia ib
    | true =>
      simp only [hA, ↓reduceIte]
      rw [cutVal, u_and hd hA ha hb]
      simp only [List.any_nil, Bool.or_false]
      exact congrArg₂ Bool.and ia ib

lemma cutVal_mono {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (Del : Finset ℕ)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) (hw : w < n + C.gates.length) :
    cutVal n C Del x w = true → cutVal n C Del y w = true := by
  have hab : ∀ j < C.gates.length, opnd C j 0 < n + j ∧ opnd C j 1 < n + j := by
    intro j hj
    exact ⟨(gate2 hC hj).2.2.1, (gate2 hC hj).2.2.2.1⟩
  have hget : ∀ t, (List.ofFn x).getD t false = true → (List.ofFn y).getD t false = true := by
    intro t ht
    by_cases ht' : t < n
    · rw [gDv y t ht']
      exact hxy ⟨t, ht'⟩ (by simpa only [gDv x t ht'] using ht)
    · have : (List.ofFn x).getD t false = false :=
        List.getD_eq_default _ _ (by simp; omega)
      rw [this] at ht
      cases ht
  exact u_mono hab (List.ofFn x) (List.ofFn y) hget w hw

lemma val_out {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    val n C x C.output = circuitFun n C x := rfl

lemma output_lt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hF : circuitFun n C = graphFun G ∅) (hE : G.edgeFinset.Nonempty) :
    C.output < n + C.gates.length := by
  have hE' : ∃ p q, G.Adj p q := by
    obtain ⟨e, he⟩ := hE
    induction e using Sym2.ind with
    | _ p q => exact ⟨p, q, by simpa using he⟩
  obtain ⟨p, q, hpq⟩ := hE'
  have htrue : val n C (fun _ => true) C.output = true := by
    rw [val_out, hF]
    exact (gf G _).mpr ⟨p, q, hpq, rfl, rfl⟩
  by_contra h
  have hfalse : val n C (fun _ => true) C.output = false :=
    List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)
  rw [hfalse] at htrue
  cases htrue

lemma compile_cut {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (hout : C.output < n + C.gates.length) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧
      ∀ x : Fin n → Bool, circuitFun n D x = cutVal n C {j} x C.output := by
  obtain ⟨gs, m, hok, hm, _, hsize, _⟩ := build n (isAnd C)
    (fun k => opnd C k 0) (fun k => opnd C k 1) {j} ∅ (fun _ => [])
    (fun _ => false) (by simp) (by simp) C.gates.length
    (fun k hk => ⟨(gate2 hC hk).2.2.1, (gate2 hC hk).2.2.2.1⟩)
  have hcard : ((Finset.range C.gates.length).filter (· ∈ ({j} : Finset ℕ))).card = 1 := by
    have : (Finset.range C.gates.length).filter (· ∈ ({j} : Finset ℕ)) = {j} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      omega
    rw [this]
    simp
  simp only [hcard, Finset.notMem_empty, Finset.filter_false, Finset.card_empty,
    Nat.add_zero, List.length_nil, Finset.sum_const_zero] at hsize
  rcases hm C.output hout with ⟨hbound, heq⟩
  cases ho : m C.output with
  | none =>
    refine ⟨⟨gs, n + gs.length⟩, ok_ao hok, by simp only [Circuit.size]; omega, ?_⟩
    intro x
    have hfalse : (run gs (List.ofFn x)).getD (n + gs.length) false = false :=
      List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn])
    change (run gs (List.ofFn x)).getD (n + gs.length) false = _
    rw [hfalse]
    have hh := heq x
    simpa only [ho, ov, cutVal] using hh
  | some w =>
    refine ⟨⟨gs, w⟩, ok_ao hok, by simp only [Circuit.size]; omega, ?_⟩
    intro x
    change (run gs (List.ofFn x)).getD w false = _
    have hh := heq x
    simpa only [ho, ov, cutVal] using hh

lemma least_gate_critical {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hE : G.edgeFinset.Nonempty) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ p q : Fin n, G.Adj p q ∧ cutVal n C {j} (pairInput p q) C.output = false := by
  have hout := output_lt G C hL.2.1 hE
  by_contra h
  push Not at h
  have hF : ∀ x : Fin n → Bool, cutVal n C {j} x C.output = graphFun G ∅ x := by
    intro x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      have hval := cutVal_le C hL.1 {j} x C.output hout hx
      rwa [val_out, hL.2.1] at hval
    · intro hx
      obtain ⟨p, q, hpq, hp, hq⟩ := (gf G x).mp hx
      have hedge : cutVal n C {j} (pairInput p q) C.output = true := by
        cases ht : cutVal n C {j} (pairInput p q) C.output
        · exact (h p q hpq ht).elim
        · rfl
      apply cutVal_mono C hL.1 {j} (pairInput p q) x ?_ C.output hout hedge
      intro i hi
      have : i = p ∨ i = q := by simpa [pairInput] using hi
      rcases this with rfl | rfl <;> assumption
  obtain ⟨D, hAO, hsize, heq⟩ := compile_cut C hL.1 j hj hout
  have hDF : circuitFun n D = graphFun G ∅ := funext fun x => (heq x).trans (hF x)
  have hmin := hL.2.2 D hAO hDF
  omega

lemma least_gate_hits_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hE : G.edgeFinset.Nonempty) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ p q : Fin n, G.Adj p q ∧ gateVal n C j (pairInput p q) = true := by
  obtain ⟨p, q, hpq, hcut⟩ := least_gate_critical G C hL hE j hj
  refine ⟨p, q, hpq, ?_⟩
  cases hz : gateVal n C j (pairInput p q) with
  | true => rfl
  | false =>
    have heq := cutVal_eq_of_zero C hL.1 j (pairInput p q) hz C.output
      (output_lt G C hL.2.1 hE)
    rw [hcut, val_out, hL.2.1] at heq
    have hf : graphFun G ∅ (pairInput p q) = true :=
      (gf G _).mpr ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩
    rw [hf] at heq
    cases heq

lemma least_gammaE_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hE : G.edgeFinset.Nonempty) (j : ℕ)
    (hj : j < C.gates.length) : (gammaE G C j).Nonempty := by
  obtain ⟨p, q, hpq, hjpq⟩ := least_gate_hits_edge G C hL hE j hj
  exact ⟨s(p, q), Finset.mem_filter.mpr ⟨by simpa using hpq, p, q, rfl, hjpq⟩⟩

lemma cutVal_eq_set {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j : ℕ)
    (x : Fin n → Bool) :
    ∀ w < n + C.gates.length,
      cutVal n C {j} x w =
        (run (C.gates.set j ⟨GateOp.or, []⟩) (List.ofFn x)).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hin : w < n
    · rw [cutVal, u_in hin, run_input _ _ w (by simpa using hin)]
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    have hk' : k < (C.gates.set j ⟨GateOp.or, []⟩).length := by simpa using hk
    have hrec := run_gate (C.gates.set j ⟨GateOp.or, []⟩) (List.ofFn x) k hk'
    rw [List.length_ofFn] at hrec
    by_cases hkj : k = j
    · subst k
      rw [cutVal, u_del (Finset.mem_singleton_self j), hrec]
      simp [GateOp.eval]
    have hnot : k ∉ ({j} : Finset ℕ) := by simpa using hkj
    have hgt : (C.gates.set j ⟨GateOp.or, []⟩)[k] = C.gates[k] := by
      simp [List.getElem_set, hkj, Ne.symm hkj]
    obtain ⟨heq, hinp, ha, hb, hop⟩ := gate2 hC hk
    rw [hgt, heq, hinp] at hrec
    simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb] at hrec
    have ia := ih (opnd C k 0) ha (by omega)
    have ib := ih (opnd C k 1) hb (by omega)
    rcases hop with hop | hop
    · have hA : isAnd C k = true := by simp [isAnd, hop]
      rw [cutVal, u_and hnot hA ha hb, hrec, hop]
      simp only [List.any_nil, Bool.or_false, GateOp.eval, List.all_cons, List.all_nil,
        Bool.and_true, id_eq]
      exact congrArg₂ Bool.and ia ib
    · have hA : isAnd C k = false := by simp [isAnd, hop]
      rw [cutVal, u_or hnot hA ha hb, hrec, hop]
      simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq]
      exact congrArg₂ Bool.or ia ib

lemma least_gate_critical_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hE : G.edgeFinset.Nonempty) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ p q : Fin n, G.Adj p q ∧ gateVal n C j (pairInput p q) = true ∧
      circuitFun n ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ (pairInput p q) = false := by
  obtain ⟨p, q, hpq, hcut⟩ := least_gate_critical G C hL hE j hj
  have hkill : circuitFun n ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ (pairInput p q) = false := by
    change (run (C.gates.set j ⟨GateOp.or, []⟩) (List.ofFn (pairInput p q))).getD C.output false = false
    rw [← cutVal_eq_set C hL.1 j (pairInput p q) C.output (output_lt G C hL.2.1 hE)]
    exact hcut
  refine ⟨p, q, hpq, ?_, hkill⟩
  cases hz : gateVal n C j (pairInput p q) with
  | true => rfl
  | false =>
    have heq := cutVal_eq_of_zero C hL.1 j (pairInput p q) hz C.output
      (output_lt G C hL.2.1 hE)
    rw [hcut, val_out, hL.2.1] at heq
    have hf : graphFun G ∅ (pairInput p q) = true :=
      (gf G _).mpr ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩
    rw [hf] at heq
    cases heq

lemma least_nonempty_of_gate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length) :
    G.edgeFinset.Nonempty := by
  by_contra hempty
  have hempty : G.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  have hadj : ∀ p q : Fin n, ¬ G.Adj p q := by
    intro p q hpq
    have he : s(p, q) ∈ G.edgeFinset := by simpa using hpq
    rw [hempty] at he
    exact Finset.notMem_empty _ he
  let D : Circuit := ⟨[], n⟩
  have hAO : IsAO2 n D := by
    simp [IsAO2, AndOrOnly, ReadsBack, D]
  have hF : circuitFun n D = graphFun G ∅ := by
    funext x
    have hfalse : graphFun G ∅ x = false := by
      cases hx : graphFun G ∅ x with
      | false => rfl
      | true =>
        obtain ⟨p, q, hpq, _, _⟩ := (gf G x).mp hx
        exact (hadj p q hpq).elim
    rw [hfalse]
    simp [circuitFun, D, Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD]
  have hsize := hL.2.2 D hAO hF
  simp only [Circuit.size, D, List.length_nil] at hsize
  omega

lemma least_gate_critical_edge_of_least {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ p q : Fin n, G.Adj p q ∧ gateVal n C j (pairInput p q) = true ∧
      circuitFun n ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ (pairInput p q) = false := by
  exact least_gate_critical_edge G C hL (least_nonempty_of_gate G C hL j hj) j hj

lemma least_gammaE_nonempty_of_least {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C) (j : ℕ)
    (hj : j < C.gates.length) : (gammaE G C j).Nonempty := by
  exact least_gammaE_nonempty G C hL (least_nonempty_of_gate G C hL j hj) j hj

end PEqualNP.Outside.L_meta_5012.CriticalEdge

namespace PEqualNP.Outside.L_meta_5012.CriticalEdge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def aliasWire (n j b w : ℕ) : ℕ := if w = n + j then b else w

def aliasVal (n : ℕ) (C : Circuit) (j b : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  u n (isAnd C) (fun k => aliasWire n j b (opnd C k 0))
    (fun k => aliasWire n j b (opnd C k 1)) {j} (fun _ => []) (List.ofFn x) (aliasWire n j b w)

lemma alias_le {n j b w : ℕ} (hb : b < n + j) : aliasWire n j b w ≤ w := by
  unfold aliasWire
  split_ifs with h <;> omega

lemma aliasVal_in {n : ℕ} (C : Circuit) (j b : ℕ) (x : Fin n → Bool)
    (w : ℕ) (hw : w < n) : aliasVal n C j b x w = (List.ofFn x).getD w false := by
  have h : w ≠ n + j := by omega
  simp only [aliasVal, aliasWire, if_neg h, u_in hw]

lemma aliasVal_here {n : ℕ} (C : Circuit) (j b : ℕ) (hb : b < n + j)
    (x : Fin n → Bool) : aliasVal n C j b x (n + j) = aliasVal n C j b x b := by
  simp [aliasVal, aliasWire, Nat.ne_of_lt hb]

lemma aliasVal_rec {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j b : ℕ)
    (hb : b < n + j) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hkj : k ≠ j) :
    aliasVal n C j b x (n + k) = if isAnd C k = true then
      aliasVal n C j b x (opnd C k 0) && aliasVal n C j b x (opnd C k 1)
    else aliasVal n C j b x (opnd C k 0) || aliasVal n C j b x (opnd C k 1) := by
  obtain ⟨_, _, ha, hc, _⟩ := gate2 hC hk
  have hnkj : n + k ≠ n + j := by omega
  have hnot : k ∉ ({j} : Finset ℕ) := by simpa using hkj
  have ha' : aliasWire n j b (opnd C k 0) < n + k := lt_of_le_of_lt (alias_le hb) ha
  have hc' : aliasWire n j b (opnd C k 1) < n + k := lt_of_le_of_lt (alias_le hb) hc
  unfold aliasVal
  rw [show aliasWire n j b (n + k) = n + k by unfold aliasWire; exact if_neg hnkj]
  cases hA : isAnd C k with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact u_or hnot hA ha' hc'
  | true =>
    simp only [↓reduceIte]
    simpa only [List.any_nil, Bool.or_false] using u_and (L := fun _ => []) hnot hA ha' hc'

lemma aliasVal_le {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j b : ℕ)
    (hb : b < n + j) (x : Fin n → Bool)
    (hsmall : val n C x b = true → val n C x (n + j) = true) :
    ∀ w < n + C.gates.length, aliasVal n C j b x w = true → val n C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hx
    by_cases hin : w < n
    · simpa only [aliasVal_in C j b x w hin, val_in C x w hin] using hx
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    by_cases hkj : k = j
    · subst k
      rw [aliasVal_here C j b hb x] at hx
      exact hsmall (ih b hb (by omega) hx)
    obtain ⟨_, _, ha, hc, _⟩ := gate2 hC hk
    rw [aliasVal_rec C hC j b hb x k hk hkj] at hx
    rw [val_rec C hC x k hk]
    cases hA : isAnd C k with
    | false =>
      simp only [hA, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true] at hx ⊢
      rcases hx with h | h
      · exact Or.inl (ih _ ha (by omega) h)
      · exact Or.inr (ih _ hc (by omega) h)
    | true =>
      simp only [hA, ↓reduceIte, Bool.and_eq_true] at hx ⊢
      exact ⟨ih _ ha (by omega) hx.1, ih _ hc (by omega) hx.2⟩

lemma aliasVal_eq {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j b : ℕ)
    (hb : b < n + j) (x : Fin n → Bool) (heq : val n C x b = val n C x (n + j)) :
    ∀ w < n + C.gates.length, aliasVal n C j b x w = val n C x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hin : w < n
    · simp only [aliasVal_in C j b x w hin, val_in C x w hin]
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    by_cases hkj : k = j
    · subst k
      rw [aliasVal_here C j b hb x, ih b hb (by omega), heq]
    obtain ⟨_, _, ha, hc, _⟩ := gate2 hC hk
    rw [aliasVal_rec C hC j b hb x k hk hkj, val_rec C hC x k hk,
      ih _ ha (by omega), ih _ hc (by omega)]

lemma aliasVal_mono {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j b : ℕ)
    (hb : b < n + j) (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) (hw : w < n + C.gates.length) :
    aliasVal n C j b x w = true → aliasVal n C j b y w = true := by
  have hab : ∀ k < C.gates.length,
      aliasWire n j b (opnd C k 0) < n + k ∧ aliasWire n j b (opnd C k 1) < n + k := by
    intro k hk
    exact ⟨lt_of_le_of_lt (alias_le hb) (gate2 hC hk).2.2.1,
      lt_of_le_of_lt (alias_le hb) (gate2 hC hk).2.2.2.1⟩
  have hget : ∀ t, (List.ofFn x).getD t false = true → (List.ofFn y).getD t false = true := by
    intro t ht
    by_cases ht' : t < n
    · rw [gDv y t ht']
      exact hxy ⟨t, ht'⟩ (by simpa only [gDv x t ht'] using ht)
    · have : (List.ofFn x).getD t false = false :=
        List.getD_eq_default _ _ (by simp; omega)
      rw [this] at ht
      cases ht
  exact u_mono hab (List.ofFn x) (List.ofFn y) hget _ (lt_of_le_of_lt (alias_le hb) hw)

lemma compile_alias {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j b : ℕ)
    (hb : b < n + j) (hj : j < C.gates.length) (hout : C.output < n + C.gates.length) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧
      ∀ x : Fin n → Bool, circuitFun n D x = aliasVal n C j b x C.output := by
  have hab : ∀ k < C.gates.length,
      aliasWire n j b (opnd C k 0) < n + k ∧ aliasWire n j b (opnd C k 1) < n + k := by
    intro k hk
    exact ⟨lt_of_le_of_lt (alias_le hb) (gate2 hC hk).2.2.1,
      lt_of_le_of_lt (alias_le hb) (gate2 hC hk).2.2.2.1⟩
  obtain ⟨gs, m, hok, hm, _, hsize, _⟩ := build n (isAnd C)
    (fun k => aliasWire n j b (opnd C k 0)) (fun k => aliasWire n j b (opnd C k 1))
    {j} ∅ (fun _ => []) (fun _ => false) (by simp) (by simp) C.gates.length hab
  have hcard : ((Finset.range C.gates.length).filter (· ∈ ({j} : Finset ℕ))).card = 1 := by
    have : (Finset.range C.gates.length).filter (· ∈ ({j} : Finset ℕ)) = {j} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      omega
    rw [this]
    simp
  simp only [hcard, Finset.notMem_empty, Finset.filter_false, Finset.card_empty,
    Nat.add_zero, List.length_nil, Finset.sum_const_zero] at hsize
  rcases hm (aliasWire n j b C.output) (lt_of_le_of_lt (alias_le hb) hout) with ⟨hbound, heq⟩
  cases ho : m (aliasWire n j b C.output) with
  | none =>
    refine ⟨⟨gs, n + gs.length⟩, ok_ao hok, by simp only [Circuit.size]; omega, ?_⟩
    intro x
    have hfalse : (run gs (List.ofFn x)).getD (n + gs.length) false = false :=
      List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn])
    change (run gs (List.ofFn x)).getD (n + gs.length) false = _
    rw [hfalse]
    have hh := heq x
    simpa only [ho, ov, aliasVal] using hh
  | some w =>
    refine ⟨⟨gs, w⟩, ok_ao hok, by simp only [Circuit.size]; omega, ?_⟩
    intro x
    change (run gs (List.ofFn x)).getD w false = _
    have hh := heq x
    simpa only [ho, ov, aliasVal] using hh

lemma least_alias_impossible {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (j b : ℕ) (hb : b < n + j)
    (hj : j < C.gates.length)
    (hsmall : ∀ x : Fin n → Bool, val n C x b = true → val n C x (n + j) = true)
    (hedge : ∀ p q : Fin n, G.Adj p q → val n C (pairInput p q) b = val n C (pairInput p q) (n + j)) :
    False := by
  have hE := least_nonempty_of_gate G C hL j hj
  have hout := output_lt G C hL.2.1 hE
  have hF : ∀ x : Fin n → Bool, aliasVal n C j b x C.output = graphFun G ∅ x := by
    intro x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      have hval := aliasVal_le C hL.1 j b hb x (hsmall x) C.output hout hx
      rwa [val_out, hL.2.1] at hval
    · intro hx
      obtain ⟨p, q, hpq, hp, hq⟩ := (gf G x).mp hx
      have hpair : aliasVal n C j b (pairInput p q) C.output = true := by
        rw [aliasVal_eq C hL.1 j b hb (pairInput p q) (hedge p q hpq) C.output hout,
          val_out, hL.2.1]
        exact (gf G _).mpr ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩
      apply aliasVal_mono C hL.1 j b hb (pairInput p q) x ?_ C.output hout hpair
      intro i hi
      have : i = p ∨ i = q := by simpa [pairInput] using hi
      rcases this with rfl | rfl <;> assumption
  obtain ⟨D, hAO, hsize, heq⟩ := compile_alias C hL.1 j b hb hj hout
  have hDF : circuitFun n D = graphFun G ∅ := funext fun x => (heq x).trans (hF x)
  have hmin := hL.2.2 D hAO hDF
  omega

lemma least_read_input_incident {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length)
    (z : Fin n) (hread : z.val ∈ (gateAt C j).inputs) : ∃ v : Fin n, G.Adj z v := by
  by_contra hiso
  push Not at hiso
  have hzpair : ∀ p q : Fin n, G.Adj p q → val n C (pairInput p q) z.val = false := by
    intro p q hpq
    rw [val_in C _ z.val z.isLt, gD]
    cases hz : pairInput p q z with
    | false => rfl
    | true =>
      have : z = p ∨ z = q := by simpa [pairInput] using hz
      rcases this with rfl | rfl
      · exact (hiso q hpq).elim
      · exact (hiso p hpq.symm).elim
  obtain ⟨_, hinp, ha, hb, hop⟩ := gate2 hL.1 hj
  rw [hinp] at hread
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hread
  rcases hop with hop | hop
  · obtain ⟨p, q, hpq, hgate, _⟩ := least_gate_critical_edge_of_least G C hL j hj
    have hval : val n C (pairInput p q) (n + j) = true := hgate
    rw [val_rec C hL.1 _ j hj] at hval
    have hA : isAnd C j = true := by simp [isAnd, hop]
    simp only [hA, ↓reduceIte, Bool.and_eq_true] at hval
    rcases hread with h | h
    · have := hval.1
      rw [← h, hzpair p q hpq] at this
      cases this
    · have := hval.2
      rw [← h, hzpair p q hpq] at this
      cases this
  · have hA : isAnd C j = false := by simp [isAnd, hop]
    rcases hread with h | h
    · apply least_alias_impossible G C hL j (opnd C j 1) hb hj
      · intro x hx
        rw [val_rec C hL.1 x j hj]
        simp [hA, hx]
      · intro p q hpq
        rw [val_rec C hL.1 _ j hj]
        simp [hA, ← h, hzpair p q hpq]
    · apply least_alias_impossible G C hL j (opnd C j 0) ha hj
      · intro x hx
        rw [val_rec C hL.1 x j hj]
        simp [hA, hx]
      · intro p q hpq
        rw [val_rec C hL.1 _ j hj]
        simp [hA, ← h, hzpair p q hpq]

lemma least_no_edge_equivalent_earlier_wire {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C) (j b : ℕ)
    (hb : b < n + j) (hj : j < C.gates.length)
    (hsmall : ∀ x : Fin n → Bool, wireVal n C b x = true → gateVal n C j x = true)
    (hedge : ∀ p q : Fin n, G.Adj p q →
      wireVal n C b (pairInput p q) = gateVal n C j (pairInput p q)) : False := by
  exact least_alias_impossible G C hL j b hb hj hsmall hedge

lemma least_edge_separates_earlier_wire {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C) (j b : ℕ)
    (hb : b < n + j) (hj : j < C.gates.length)
    (hsmall : ∀ x : Fin n → Bool, wireVal n C b x = true → gateVal n C j x = true) :
    ∃ p q : Fin n, G.Adj p q ∧ gateVal n C j (pairInput p q) = true ∧
      wireVal n C b (pairInput p q) = false := by
  by_contra h
  push Not at h
  apply least_no_edge_equivalent_earlier_wire G C hL j b hb hj hsmall
  intro p q hpq
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact hsmall (pairInput p q)
  · intro hjtrue
    have hbnot := h p q hpq hjtrue
    cases heq : wireVal n C b (pairInput p q) with
    | false => exact (hbnot heq).elim
    | true => rfl

end PEqualNP.Outside.L_meta_5012.CriticalEdge


namespace PEqualNP.Outside.L_meta_5012.Diamond

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
  PEqualNP.CleanedNonEdge

lemma pairInput_comm {n : ℕ} (b c : Fin n) : pairInput b c = pairInput c b := by
  funext i
  simp [pairInput, or_comm]

lemma residual_critical {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (g t : ℕ) (b c : Fin n)
    (ht : t < n + g) (hg : g < C.gates.length) (hbc : b ≠ c)
    (heval : ∀ x : Fin n → Bool, gateVal n C g x =
      ((wireVal n C t x || x b) && (wireVal n C t x || x c))) :
    G.Adj b c ∧ wireVal n C t (pairInput b c) = false := by
  have hsmall : ∀ x : Fin n → Bool,
      wireVal n C t x = true → gateVal n C g x = true := by
    intro x hx
    rw [heval, hx]
    rfl
  obtain ⟨p, q, hpq, hgtrue, htfalse⟩ :=
    CriticalEdge.least_edge_separates_earlier_wire G C hL g t ht hg hsmall
  rw [heval, htfalse] at hgtrue
  have hpair : pairInput p q b = true ∧ pairInput p q c = true := by simpa using hgtrue
  have hb : b = p ∨ b = q := by simpa [pairInput] using hpair.1
  have hc : c = p ∨ c = q := by simpa [pairInput] using hpair.2
  rcases hb with rfl | rfl <;> rcases hc with rfl | rfl
  · exact False.elim (hbc rfl)
  · exact ⟨hpq, htfalse⟩
  · exact ⟨hpq.symm, by simpa only [pairInput_comm] using htfalse⟩
  · exact False.elim (hbc rfl)

lemma residual_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (g t : ℕ) (b c : Fin n)
    (ht : t < n + g) (hg : g < C.gates.length) (hbc : b ≠ c)
    (heval : ∀ x : Fin n → Bool, gateVal n C g x =
      ((wireVal n C t x || x b) && (wireVal n C t x || x c))) : G.Adj b c :=
  (residual_critical G C hL g t b c ht hg hbc heval).1

lemma duplicate_alias_impossible {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (g t w : ℕ) (b : Fin n)
    (hw : w < n + g) (hg : g < C.gates.length)
    (heval : ∀ x : Fin n → Bool, gateVal n C g x =
      ((wireVal n C t x || x b) && (wireVal n C t x || x b)))
    (hwire : ∀ x : Fin n → Bool, wireVal n C w x = (wireVal n C t x || x b)) : False := by
  have heq : ∀ x : Fin n → Bool, wireVal n C w x = gateVal n C g x := by
    intro x
    rw [hwire, heval]
    simp
  apply CriticalEdge.least_no_edge_equivalent_earlier_wire G C hL g w hw hg
  · intro x hx
    rw [← heq]
    exact hx
  · intro p q _
    exact heq (pairInput p q)



lemma pair_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p q : Fin n) : graphFun G ∅ (pairInput p q) = true ↔ G.Adj p q := by
  rw [CriticalEdge.gf]
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    have hu' : u = p ∨ u = q := by simpa [pairInput] using hu
    have hv' : v = p ∨ v = q := by simpa [pairInput] using hv
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
    · exact False.elim (huv.ne rfl)
    · exact huv
    · exact huv.symm
    · exact False.elim (huv.ne rfl)
  · intro hpq
    exact ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩

def RootFilter {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool) (b w : Fin n) : Prop :=
  ∀ x, (f x || x b) = true → x w = true → graphFun G ∅ x = true

lemma rootFilter_color {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (f : (Fin n → Bool) → Bool) (d b w : Fin n)
    (hlower : ∀ x, x d = true → f x = true) (hw : RootFilter G f b w) : s d = s b := by
  have hdw : G.Adj d w := by
    apply (pair_edge G d w).1
    apply hw
    · rw [hlower _ (by simp [pairInput])]
      rfl
    · simp [pairInput]
  have hbw : G.Adj b w := by
    apply (pair_edge G b w).1
    apply hw
    · simp [pairInput]
    · simp [pairInput]
  have hd := hbip d w hdw
  have hb := hbip b w hbw
  cases hdv : s d <;> cases hbv : s b <;> cases hwv : s w <;> simp_all

lemma one_root_without_filters {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (f : (Fin n → Bool) → Bool) (d b c : Fin n)
    (hlower : ∀ x, x d = true → f x = true) (hbc : G.Adj b c) :
    (¬ ∃ w, RootFilter G f b w) ∨ (¬ ∃ w, RootFilter G f c w) := by
  classical
  by_cases hbf : ∃ w, RootFilter G f b w
  · right
    rintro ⟨z, hz⟩
    obtain ⟨w, hw⟩ := hbf
    have hdb := rootFilter_color G s hbip f d b w hlower hw
    have hdc := rootFilter_color G s hbip f d c z hlower hz
    exact hbip b c hbc (hdb.symm.trans hdc)
  · exact Or.inl hbf

lemma singleton_one_root_without_filters {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (C : Circuit) (hL : IsLeastAO G C) (g t : ℕ) (d b c : Fin n)
    (ht : t < n + g) (hg : g < C.gates.length) (hbc : b ≠ c)
    (hlower : ∀ x, x d = true → wireVal n C t x = true)
    (heval : ∀ x : Fin n → Bool, gateVal n C g x =
      ((wireVal n C t x || x b) && (wireVal n C t x || x c))) :
    (¬ ∃ w, RootFilter G (wireVal n C t) b w) ∨
      (¬ ∃ w, RootFilter G (wireVal n C t) c w) := by
  exact one_root_without_filters G s hbip (wireVal n C t) d b c hlower
    (residual_edge G C hL g t b c ht hg hbc heval)

end PEqualNP.Outside.L_meta_5012.Diamond



namespace PEqualNP.Outside.L_meta_5012.Absorption

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

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
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def patch {n : ℕ} (C : Circuit) (r g t : ℕ) (b c : Fin n) : Circuit :=
  ⟨(C.gates.set r ⟨GateOp.and, [b.val, c.val]⟩).set g ⟨GateOp.or, [t, n + r]⟩, C.output⟩

lemma patch_length {n : ℕ} (C : Circuit) (r g t : ℕ) (b c : Fin n) :
    (patch C r g t b c).gates.length = C.gates.length := by simp [patch]

lemma patch_size {n : ℕ} (C : Circuit) (r g t : ℕ) (b c : Fin n) :
    (patch C r g t b c).size = C.size := by simp [patch, Circuit.size]

lemma patch_r {n : ℕ} (C : Circuit) (r g t : ℕ) (b c : Fin n)
    (hr : r < C.gates.length) (hrg : r ≠ g) :
    gateAt (patch C r g t b c) r = ⟨GateOp.and, [b.val, c.val]⟩ := by
  simp [gateAt, patch, List.getD_eq_getElem?_getD, hr, hrg.symm]

lemma patch_g {n : ℕ} (C : Circuit) (r g t : ℕ) (b c : Fin n)
    (hg : g < C.gates.length) :
    gateAt (patch C r g t b c) g = ⟨GateOp.or, [t, n + r]⟩ := by
  simp [gateAt, patch, List.getD_eq_getElem?_getD, hg]

lemma patch_other {n : ℕ} (C : Circuit) (r g t : ℕ) (b c : Fin n)
    (j : ℕ) (hjr : j ≠ r) (hjg : j ≠ g) :
    gateAt (patch C r g t b c) j = gateAt C j := by
  simp [gateAt, patch, List.getD_eq_getElem?_getD, hjr.symm, hjg.symm]

lemma binary_eval {n : ℕ} (C : Circuit) (j a b : ℕ) (o : GateOp)
    (hj : j < C.gates.length) (hgate : gateAt C j = ⟨o, [a, b]⟩)
    (ha : a < n + j) (hb : b < n + j) (x : Fin n → Bool) :
    val C (List.ofFn x) (n + j) = o.eval [val C (List.ofFn x) a, val C (List.ofFn x) b] := by
  rw [val_gate (n := n) (by simp) hj, hgate]
  simp [ha, hb]

lemma or_raw_eval {n : ℕ} (C : Circuit) (j t : ℕ) (b : Fin n)
    (hj : j < C.gates.length) (hgate : gateAt C j = ⟨GateOp.or, [t, b.val]⟩)
    (ht : t < n + j) (x : Fin n → Bool) :
    val C (List.ofFn x) (n + j) = (val C (List.ofFn x) t || x b) := by
  rw [binary_eval C j t b.val GateOp.or hj hgate ht (by have := b.isLt; omega), val_ofFn]
  simp [GateOp.eval]

lemma patched_r_eval {n : ℕ} (C : Circuit) (r g t : ℕ) (b c : Fin n)
    (hr : r < C.gates.length) (hrg : r ≠ g) (x : Fin n → Bool) :
    val (patch C r g t b c) (List.ofFn x) (n + r) = (x b && x c) := by
  rw [binary_eval _ r b.val c.val GateOp.and (by simpa [patch_length] using hr)
    (patch_r C r g t b c hr hrg) (by have := b.isLt; omega) (by have := c.isLt; omega),
    val_ofFn, val_ofFn]
  simp [GateOp.eval]

lemma original_g_eval {n : ℕ} (C : Circuit) (r s g t : ℕ) (b c : Fin n)
    (hg : g < C.gates.length) (hrg : r < g) (hsg : s < g) (htr : t < n + r) (hts : t < n + s)
    (hr : gateAt C r = ⟨GateOp.or, [t, b.val]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, c.val]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩) (x : Fin n → Bool) :
    val C (List.ofFn x) (n + g) =
      ((val C (List.ofFn x) t || x b) && (val C (List.ofFn x) t || x c)) := by
  rw [binary_eval C g (n + r) (n + s) GateOp.and hg hgate (by omega) (by omega),
    or_raw_eval C r t b (by omega) hr htr, or_raw_eval C s t c (by omega) hs hts]
  simp [GateOp.eval]

lemma patched_g_eval {n : ℕ} (C : Circuit) (r g t : ℕ) (b c : Fin n)
    (hg : g < C.gates.length) (hrg : r < g) (htr : t < n + r) (x : Fin n → Bool) :
    val (patch C r g t b c) (List.ofFn x) (n + g) =
      (val (patch C r g t b c) (List.ofFn x) t || (x b && x c)) := by
  rw [binary_eval _ g t (n + r) GateOp.or (by simpa [patch_length] using hg)
    (patch_g C r g t b c hg) (by omega) (by omega),
    patched_r_eval C r g t b c (by omega) (Nat.ne_of_lt hrg)]
  simp [GateOp.eval]

lemma patch_ao {n : ℕ} (C : Circuit) (r g t : ℕ) (b c : Fin n)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hrg : r < g) (htr : t < n + r) :
    IsAO2 n (patch C r g t b c) := by
  have hidx : ∀ j < (patch C r g t b c).gates.length,
      ((gateAt (patch C r g t b c) j).op = GateOp.and ∨
        (gateAt (patch C r g t b c) j).op = GateOp.or) ∧
      (gateAt (patch C r g t b c) j).inputs.length = 2 ∧
      ∀ w ∈ (gateAt (patch C r g t b c) j).inputs, w < n + j := by
    intro j hj
    have hj0 : j < C.gates.length := by simpa only [patch_length] using hj
    by_cases hjr : j = r
    · subst j
      rw [patch_r C r g t b c (by omega) (Nat.ne_of_lt hrg)]
      refine ⟨Or.inl rfl, rfl, ?_⟩
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> [have := b.isLt; have := c.isLt] <;> omega
    by_cases hjg : j = g
    · subst j
      rw [patch_g C r g t b c hg]
      refine ⟨Or.inr rfl, rfl, ?_⟩
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> omega
    rw [patch_other C r g t b c j hjr hjg]
    exact ⟨hAO.1 _ (gateAt_mem hj0), hAO.2.2 _ (gateAt_mem hj0), hAO.2.1 j hj0⟩
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    have hh := (hidx j hj).1
    rwa [gateAt_eq hj] at hh
  · intro j hj w hw
    exact (hidx j hj).2.2 w hw
  · intro q hq
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    have hh := (hidx j hj).2.1
    rwa [gateAt_eq hj] at hh

lemma patched_gate_values {n : ℕ} (C : Circuit) (r s g t : ℕ) (b c : Fin n)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hrg : r < g) (hsg : s < g)
    (hr : gateAt C r = ⟨GateOp.or, [t, b.val]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, c.val]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hread : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g)
    (x : Fin n → Bool) :
    ∀ j < C.gates.length, j ≠ r →
      val (patch C r g t b c) (List.ofFn x) (n + j) = val C (List.ofFn x) (n + j) := by
  have htr : t < n + r := hAO.2.1 r (by omega) t (by rw [hr]; simp)
  have hts : t < n + s := hAO.2.1 s (by omega) t (by rw [hs]; simp)
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hjr
    have earlier : ∀ w, w < n + j → w ≠ n + r →
        val (patch C r g t b c) (List.ofFn x) w = val C (List.ofFn x) w := by
      intro w hw hwr
      by_cases hwn : w < n
      · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
      · have hwrepr : w = n + (w - n) := by omega
        rw [hwrepr]
        exact ih (w - n) (by omega) (by omega) (by omega)
    by_cases hjg : j = g
    · subst j
      rw [patched_g_eval C r g t b c hg hrg htr,
        original_g_eval C r s g t b c hg hrg hsg htr hts hr hs hgate,
        earlier t (by omega) (Nat.ne_of_lt htr)]
      cases val C (List.ofFn x) t <;> cases x b <;> cases x c <;> rfl
    rw [val_gate (n := n) (by simp) (by simpa only [patch_length] using hj),
      val_gate (n := n) (by simp) hj, patch_other C r g t b c j hjr hjg]
    congr 1
    apply List.map_congr_left
    intro w hw
    have hwl : w < n + j := hAO.2.1 j hj w hw
    have hwr : w ≠ n + r := by
      intro hh
      exact hjg (hread j hj (hh ▸ hw))
    simp only [ite_eq_left hwl]
    exact earlier w hwl hwr

lemma patched_wire_values {n : ℕ} (C : Circuit) (r s g t : ℕ) (b c : Fin n)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hrg : r < g) (hsg : s < g)
    (hr : gateAt C r = ⟨GateOp.or, [t, b.val]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, c.val]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hread : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g)
    (x : Fin n → Bool) (w : ℕ) (hwr : w ≠ n + r) :
    val (patch C r g t b c) (List.ofFn x) w = val C (List.ofFn x) w := by
  by_cases hwn : w < n
  · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
  by_cases hwC : w < n + C.gates.length
  · have hwrepr : w = n + (w - n) := by omega
    rw [hwrepr]
    exact patched_gate_values C r s g t b c hAO hg hrg hsg hr hs hgate hread x
      (w - n) (by omega) (by omega)
  · rw [val_ge (n := n) (by simp) (by rw [patch_length]; omega),
      val_ge (n := n) (by simp) (by omega)]

lemma graphFun_singleton {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i : Fin n) :
    graphFun G ∅ (pairInput i i) = false := by
  unfold graphFun
  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
  apply decide_eq_false
  rintro ⟨a, b, hab, ha, hb⟩
  have hai : a = i := by simpa [pairInput] using ha
  have hbi : b = i := by simpa [pairInput] using hb
  exact hab.ne (hai.trans hbi.symm)

lemma r_not_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r t : ℕ) (b : Fin n) (hr : r < C.gates.length) (htr : t < n + r)
    (hgate : gateAt C r = ⟨GateOp.or, [t, b.val]⟩)
    (hc : circuitFun n C = graphFun G ∅) : C.output ≠ n + r := by
  intro hout
  have he := congrFun hc (pairInput b b)
  change val C (List.ofFn (pairInput b b)) C.output = _ at he
  rw [hout, or_raw_eval C r t b hr hgate htr, graphFun_singleton] at he
  simp [pairInput] at he

lemma patch_computes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r s g t : ℕ) (b c : Fin n)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hrg : r < g) (hsg : s < g)
    (hr : gateAt C r = ⟨GateOp.or, [t, b.val]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, c.val]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hread : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g)
    (hc : circuitFun n C = graphFun G ∅) :
    circuitFun n (patch C r g t b c) = graphFun G ∅ := by
  have htr : t < n + r := hAO.2.1 r (by omega) t (by rw [hr]; simp)
  have ho := r_not_output G C r t b (by omega) htr hr hc
  funext x
  change val (patch C r g t b c) (List.ofFn x) C.output = _
  rw [patched_wire_values C r s g t b c hAO hg hrg hsg hr hs hgate hread x C.output ho]
  exact congrFun hc x

lemma mem_junk_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) : j ∈ junk G C ↔
      j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
        ∃ x : Fin n → Bool, gateVal n C j x = true ∧ graphFun G ∅ x = false := by
  unfold junk gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]
  simp only [IsDirtyAnd, IsDirty]
  tauto

lemma r_not_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r t : ℕ) (b : Fin n)
    (hr : gateAt C r = ⟨GateOp.or, [t, b.val]⟩) : r ∉ junk G C := by
  intro h
  have hop := (mem_junk_iff G C r).mp h |>.2.1
  rw [hr] at hop
  cases hop

lemma patch_r_not_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r g t : ℕ) (b c : Fin n)
    (hr : r < C.gates.length) (hrg : r ≠ g) (hbc : G.Adj b c) :
    r ∉ junk G (patch C r g t b c) := by
  intro h
  obtain ⟨_, _, x, hx, hF⟩ := (mem_junk_iff G _ r).mp h
  rw [gateVal_eq_val, patched_r_eval C r g t b c hr hrg] at hx
  rw [Bool.and_eq_true] at hx
  obtain ⟨hxb, hxc⟩ := hx
  have htrue : graphFun G ∅ x = true := by
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨b, c, hbc, hxb, hxc⟩
  rw [htrue] at hF
  cases hF

lemma patch_g_not_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r g t : ℕ) (b c : Fin n) (hg : g < C.gates.length) :
    g ∉ junk G (patch C r g t b c) := by
  intro h
  have hop := (mem_junk_iff G _ g).mp h |>.2.1
  rw [patch_g C r g t b c hg] at hop
  cases hop

lemma patch_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r s g t : ℕ) (b c : Fin n)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hrg : r < g) (hsg : s < g)
    (hr : gateAt C r = ⟨GateOp.or, [t, b.val]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, c.val]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hread : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g)
    (hbc : G.Adj b c) : junk G (patch C r g t b c) = (junk G C).erase g := by
  apply Finset.ext
  intro j
  by_cases hjr : j = r
  · subst j
    simp only [Finset.mem_erase, patch_r_not_junk G C r g t b c (by omega) (Nat.ne_of_lt hrg) hbc,
      r_not_junk G C r t b hr, and_false]
  by_cases hjg : j = g
  · subst j
    simp only [Finset.mem_erase, patch_g_not_junk G C r g t b c hg, ne_eq, not_true_eq_false, false_and]
  by_cases hj : j < C.gates.length
  · have hvals : ∀ x : Fin n → Bool,
        gateVal n (patch C r g t b c) j x = gateVal n C j x := by
      intro x
      exact patched_gate_values C r s g t b c hAO hg hrg hsg hr hs hgate hread x j hj hjr
    simp only [Finset.mem_erase, mem_junk_iff, patch_length,
      patch_other C r g t b c j hjr hjg, hvals, ne_eq, hjg, not_false_eq_true, true_and]
  · simp only [Finset.mem_erase, mem_junk_iff, patch_length, hj, false_and, and_false]

lemma patch_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r s g t : ℕ) (b c : Fin n)
    (hL : IsLeastAO G C) (hg : g < C.gates.length) (hrg : r < g) (hsg : s < g)
    (hr : gateAt C r = ⟨GateOp.or, [t, b.val]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, c.val]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hread : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g) :
    IsLeastAO G (patch C r g t b c) := by
  have htr : t < n + r := hL.1.2.1 r (by omega) t (by rw [hr]; simp)
  refine ⟨patch_ao C r g t b c hL.1 hg hrg htr,
    patch_computes G C r s g t b c hL.1 hg hrg hsg hr hs hgate hread hL.2.1, ?_⟩
  intro D hD hcD
  rw [patch_size]
  exact hL.2.2 D hD hcD

lemma absorption_contradiction
    (firstRung : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (color : Fin n → Bool),
      (∀ u v, G.Adj u v → color u ≠ color v) → NoFourCycle G → IsLeastAO G C →
      (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v) (h4 : NoFourCycle G)
    (hL : IsLeastAO G C) (hcard : (junk G C).card = 2)
    (r s g t : ℕ) (b c : Fin n) (hgJ : g ∈ junk G C) (hrg : r < g) (hsg : s < g)
    (hr : gateAt C r = ⟨GateOp.or, [t, b.val]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, c.val]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hread : readers n C r = {g}) (hbc : G.Adj b c) : False := by
  have hg : g < C.gates.length := (mem_junk_iff G C g).mp hgJ |>.1
  have hread' : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g := by
    intro j hj hw
    have hjmem : j ∈ readers n C r := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hw⟩
    simpa only [hread, Finset.mem_singleton] using hjmem
  have hPL := patch_least G C r s g t b c hL hg hrg hsg hr hs hgate hread'
  apply firstRung n G (patch C r g t b c) color hbip h4 hPL
  rw [patch_junk G C r s g t b c hL.1 hg hrg hsg hr hs hgate hread' hbc,
    Finset.card_erase_of_mem hgJ, hcard]

end PEqualNP.Outside.L_meta_5012.Absorption


namespace PEqualNP.Outside.L_meta_5012.Absorption

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma diamond_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r s g t : ℕ) (b c : Fin n)
    (hL : IsLeastAO G C) (hg : g < C.gates.length) (hrg : r < g) (hsg : s < g)
    (hr : gateAt C r = ⟨GateOp.or, [t, b.val]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, c.val]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩) : G.Adj b c := by
  have htr : t < n + r := hL.1.2.1 r (by omega) t (by rw [hr]; simp)
  have hts : t < n + s := hL.1.2.1 s (by omega) t (by rw [hs]; simp)
  have heval : ∀ x : Fin n → Bool, gateVal n C g x =
      ((wireVal n C t x || x b) && (wireVal n C t x || x c)) := by
    intro x
    exact original_g_eval C r s g t b c hg hrg hsg htr hts hr hs hgate x
  by_cases hbc : b = c
  · subst c
    apply False.elim
    apply Diamond.duplicate_alias_impossible G C hL g t (n + r) b (by omega) hg heval
    intro x
    exact or_raw_eval C r t b (by omega) hr htr x
  · exact Diamond.residual_edge G C hL g t b c (by omega) hg hbc heval

lemma diamond_no_two_junk
    (firstRung : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (color : Fin n → Bool),
      (∀ u v, G.Adj u v → color u ≠ color v) → NoFourCycle G → IsLeastAO G C →
      (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v) (h4 : NoFourCycle G)
    (hL : IsLeastAO G C) (hcard : (junk G C).card = 2)
    (r s g t : ℕ) (b c : Fin n) (hgJ : g ∈ junk G C) (hrg : r < g) (hsg : s < g)
    (hr : gateAt C r = ⟨GateOp.or, [t, b.val]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, c.val]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hread : readers n C r = {g}) : False := by
  have hg : g < C.gates.length := (mem_junk_iff G C g).mp hgJ |>.1
  exact absorption_contradiction firstRung G C color hbip h4 hL hcard
    r s g t b c hgJ hrg hsg hr hs hgate hread
    (diamond_edge G C r s g t b c hL hg hrg hsg hr hs hgate)

end PEqualNP.Outside.L_meta_5012.Absorption



namespace PEqualNP.Outside.L_meta_5012

namespace Lift

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_wires_getD_gate (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ k ∈ gs[j].inputs, k < acc.length + j) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD
        (acc.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun k =>
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun m => w.getD m false)]) acc).getD
          k false) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero] at hback ⊢
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen : acc.length < acc'.length := by
        simp only [acc', List.length_append, List.length_singleton]; omega
      rw [foldl_wires_getD_lt gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length false = g.op.eval (g.inputs.map fun k => acc.getD k false) := by
        simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hka : k < acc.length := hback k hk
      have hka' : k < acc'.length := by omega
      rw [foldl_wires_getD_lt gs acc' k hka']
      simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_left hka]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      apply ih acc' j' hj'
      intro k hk
      have hbk := hback k (by simpa using hk)
      omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wires_len C.gates x

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlt : i < (List.ofFn x).length := by simp [hi]
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlt]
  simp [List.getD_eq_getElem?_getD, hi]

lemma gateVal_eq_wval {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wval C x (n + j) := rfl

lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  rw [List.getD_eq_getElem?_getD]
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    rw [wires_length, List.length_ofFn]
  rw [List.getElem?_eq_none (by omega)]
  rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  unfold opnd
  match h : (gateAt C j).inputs with
  | [a, b] => simp
  | [] => rw [h] at hlen; simp at hlen
  | [_] => rw [h] at hlen; simp at hlen
  | _ :: _ :: _ :: _ => rw [h] at hlen; simp at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hback : ∀ k ∈ C.gates[j].inputs, k < (List.ofFn x).length + j := by
    intro k hk; rw [hlen, ← gateAt_eq hj] at *; exact hAO.2.1 j hj k hk
  have h := foldl_wires_getD_gate C.gates (List.ofFn x) j hj hback
  rw [hlen] at h
  rw [h, ← gateAt_eq hj, gate_inputs_eq hAO hj]
  simp

lemma wval_gate_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wval C x (n + j) = (wval C x (opnd C j 0) && wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]

lemma wval_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]

lemma foldl_cones_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_cones_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (coneStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones; rw [foldl_cones_len]; simp

lemma foldl_cones_getD_gate (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (coneStep n) acc).getD (acc.length + j) [] =
      (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (acc.length + j)))).flatMap
        (fun w => (w - n) :: (gs.foldl (coneStep n) acc).getD (w - n) []) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero]
      set acc' := coneStep n acc g
      have hlen : acc.length < acc'.length := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]; omega
      rw [foldl_cones_getD_lt n gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + acc.length))).flatMap
            (fun w => (w - n) :: acc.getD (w - n) []) := by
        simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      apply List.flatMap_congr
      intro w hw
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      have hwn : w - n < acc.length := by omega
      have hwn' : w - n < acc'.length := by omega
      rw [foldl_cones_getD_lt n gs acc' (w - n) hwn']
      simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := coneStep n acc g
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      exact ih acc' j' hj'

lemma inCone_lt_len {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : j < C.gates.length := by
  by_contra hge
  unfold InCone at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [cones_length]; omega)] at h
  simp at h

lemma inCone_iff {n : ℕ} {C : Circuit} {i j : ℕ} (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone cones
  have h := foldl_cones_getD_gate n C.gates [] j hj
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h, ← gateAt_eq hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩; exact ⟨w, hw1, hw2, hw3, hw4⟩
  · rintro ⟨w, hw1, hw2, hw3, hw4⟩; exact ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩

lemma inCone_lt {n : ℕ} {C : Circuit} {i j : ℕ} : InCone n C i j → i < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro h
    have hj := inCone_lt_len h
    rw [inCone_iff hj] at h
    rcases h with ⟨w, _, hnw, hwnj, rfl | hsub⟩
    · omega
    · have := ih (w - n) (by omega) hsub; omega

lemma inCone_trans {n : ℕ} {C : Circuit} {i j k : ℕ} (h1 : InCone n C i j) (h2 : InCone n C j k) :
    InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    have hk := inCone_lt_len h2
    rw [inCone_iff hk] at h2 ⊢
    rcases h2 with ⟨w, hw, hnw, hwnk, rfl | hsub⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr h1⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr (ih (w - n) (by omega) hsub)⟩

lemma graphFun_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  unfold graphFun; simp

lemma graphFun_unit_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    graphFun G ∅ (fun w => decide (w = v)) = false := by
  rw [Bool.eq_false_iff, ne_eq, graphFun_iff]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  subst ha; subst hb
  exact G.loopless.irrefl _ hab

lemma input_not_belowF {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {w : ℕ} (hw : w < n) :
    ¬ ∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true := by
  intro h
  have := h (fun i => decide (i = ⟨w, hw⟩)) (by rw [wval_input C _ w hw]; simp)
  rw [graphFun_unit_false] at this
  cases this

lemma below_wire_contains_top {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (w : ℕ) (hw : w < n + C.gates.length)
    (hb : ∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true) :
    ∃ r, r < C.gates.length ∧ (gateAt C r).op = GateOp.and ∧ BelowF G C r ∧
      (r = w - n ∨ InCone n C r (w - n)) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    have hn : n ≤ w := by
      by_contra h
      exact input_not_belowF (by omega : w < n) hb
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hj : j < C.gates.length := by omega
    have hjb : BelowF G C j := hb
    rcases hAO.1 _ (gateAt_mem hj) with hand | hor
    · exact ⟨j, hj, hand, hjb, Or.inl (by omega)⟩
    · have hwb : ∀ x : Fin n → Bool, wval C x (opnd C j 0) = true → graphFun G ∅ x = true := by
        intro x hx
        apply hjb x
        rw [gateVal_eq_wval, wval_gate_or hAO x hj hor, Bool.or_eq_true]
        exact Or.inl hx
      have hlt := opnd_lt hAO hj 0
      have hn0 : n ≤ opnd C j 0 := by
        by_contra h
        exact input_not_belowF (by omega : opnd C j 0 < n) hwb
      obtain ⟨r, hr, hro, hrb, hrc⟩ := ih (opnd C j 0) hlt (by omega) hwb
      refine ⟨r, hr, hro, hrb, Or.inr ?_⟩
      simp only [Nat.add_sub_cancel_left]
      exact (inCone_iff hj).mpr ⟨opnd C j 0, opnd_mem hAO hj 0, hn0, hlt, hrc⟩

lemma cone_propagates_through_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {i j : ℕ} (hcone : InCone n C i j)
    (hor : ∀ k, InCone n C i k → (gateAt C k).op = GateOp.or)
    (x : Fin n → Bool) (hi : gateVal n C i x = true) : gateVal n C j x = true := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    have hj := inCone_lt_len hcone
    have hop := hor j hcone
    obtain ⟨w, hw, hnw, hwj, hsub⟩ := (inCone_iff hj).mp hcone
    have hwv : wval C x w = true := by
      rcases hsub with he | hsub
      · rw [he, gateVal_eq_wval, Nat.add_sub_of_le hnw] at hi
        exact hi
      · have hg := ih (w - n) (by omega) hsub
        rw [gateVal_eq_wval, Nat.add_sub_of_le hnw] at hg
        exact hg
    rw [gateVal_eq_wval, wval_gate_or hAO x hj hop, Bool.or_eq_true]
    rw [gate_inputs_eq hAO hj] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inl hwv
    · exact Or.inr hwv

lemma topForm_isLiftFixedPoint {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (hT : TopForm G C) : IsLiftFixedPoint G C := by
  rintro ⟨h, hh, b, hLive, _, hNot, hImp⟩
  have hwlt := opnd_lt hAO hh b
  obtain ⟨r, hr, hro, hrb, hrc⟩ :=
    below_wire_contains_top hAO (opnd C h b) (by omega) hImp.1
  have hwn : n ≤ opnd C h b := by
    by_contra hlt
    exact input_not_belowF (by omega : opnd C h b < n) hImp.1
  have hrh : InCone n C r h :=
    (inCone_iff hh).mpr ⟨opnd C h b, opnd_mem hAO hh b, hwn, hwlt, hrc⟩
  have hor : ∀ k, InCone n C h k → (gateAt C k).op = GateOp.or := by
    intro k hk
    have hkl := inCone_lt_len hk
    rcases hAO.1 _ (gateAt_mem hkl) with hand | hkor
    · exact False.elim (hT r hr k hkl hro hrb hand (inCone_trans hrh hk))
    · exact hkor
  apply hNot
  intro x hx
  have hout : wval C x C.output = true := by
    rcases hLive.2 with hout | ⟨houtn, hcone⟩
    · rw [hout]
      exact hx
    · have hc := cone_propagates_through_or hAO hcone hor x hx
      rw [gateVal_eq_wval, Nat.add_sub_of_le houtn] at hc
      exact hc
  change circuitFun n C x = true at hout
  rwa [hF] at hout

end Lift

namespace Patch

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo
open Lift

def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩

lemma patch_length (C : Circuit) (j : ℕ) (g : Gate) :
    (patch C j g).gates.length = C.gates.length := by
  simp [patch]

lemma gateAt_patch_ne (C : Circuit) (j k : ℕ) (g : Gate) (hne : j ≠ k) :
    gateAt (patch C j g) k = gateAt C k := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma gateAt_patch_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (g : Gate) :
    gateAt (patch C j g) j = g := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, hj]

lemma patch_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (j : ℕ) (g : Gate)
    (hOp : g.op = GateOp.and ∨ g.op = GateOp.or) (hLen : g.inputs.length = 2)
    (hBack : ∀ w ∈ g.inputs, w < n + j) : IsAO2 n (patch C j g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    change k ∈ C.gates.set j g at hk
    rcases List.mem_or_eq_of_mem_set hk with hk | rfl
    · exact hAO.1 k hk
    · exact hOp
  · intro k hk w hw
    have hkC : k < C.gates.length := by simpa only [patch_length] using hk
    by_cases hkj : k = j
    · subst k
      rw [gateAt_patch_eq hkC] at hw
      exact hBack w hw
    · rw [gateAt_patch_ne C j k g (Ne.symm hkj)] at hw
      exact hAO.2.1 k hkC w hw
  · intro k hk
    change k ∈ C.gates.set j g at hk
    rcases List.mem_or_eq_of_mem_set hk with hk | rfl
    · exact hAO.2.2 k hk
    · exact hLen

lemma patch_gateVal_eq_of_not_inCone {n : ℕ} {C : Circuit} {j : ℕ} {g : Gate}
    (hAO : IsAO2 n C) (hAO' : IsAO2 n (patch C j g)) (k : ℕ)
    (hne : j ≠ k) (hCone : ¬ InCone n C j k) (x : Fin n → Bool) :
    gateVal n (patch C j g) k x = gateVal n C k x := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases hk : k < C.gates.length
    · have hk' : k < (patch C j g).gates.length := by simpa only [patch_length] using hk
      have hgate := gateAt_patch_ne C j k g hne
      have hopnd (b : Fin 2) : opnd (patch C j g) k b = opnd C k b := by
        unfold opnd
        rw [hgate]
      have hval (b : Fin 2) : wval (patch C j g) x (opnd C k b) =
          wval C x (opnd C k b) := by
        by_cases hw : opnd C k b < n
        · rw [wval_input _ _ _ hw, wval_input _ _ _ hw]
        · have hw' : n ≤ opnd C k b := by omega
          have hlt := opnd_lt hAO hk b
          have hsub_ne : j ≠ opnd C k b - n := by
            intro he
            apply hCone
            exact (inCone_iff hk).mpr ⟨opnd C k b, opnd_mem hAO hk b, hw', hlt, Or.inl he⟩
          have hsub_cone : ¬ InCone n C j (opnd C k b - n) := by
            intro he
            apply hCone
            exact (inCone_iff hk).mpr ⟨opnd C k b, opnd_mem hAO hk b, hw', hlt, Or.inr he⟩
          have hv := ih (opnd C k b - n) (by omega) hsub_ne hsub_cone
          rw [gateVal_eq_wval, gateVal_eq_wval, Nat.add_sub_of_le hw'] at hv
          exact hv
      rw [gateVal_eq_wval, gateVal_eq_wval, wval_gate_eval hAO' x hk',
        wval_gate_eval hAO x hk, hgate, hopnd 0, hopnd 1, hval 0, hval 1]
    · rw [gateVal_eq_wval, gateVal_eq_wval, wval_ge_len _ _ (by rw [patch_length]; omega),
        wval_ge_len _ _ (by omega)]

lemma patch_wireVal_eq_of_not_inCone {n : ℕ} {C : Circuit} {j : ℕ} {g : Gate}
    (hAO : IsAO2 n C) (hAO' : IsAO2 n (patch C j g)) (w : ℕ)
    (h : n ≤ w → j ≠ w - n ∧ ¬ InCone n C j (w - n)) (x : Fin n → Bool) :
    wval (patch C j g) x w = wval C x w := by
  by_cases hw : w < n
  · rw [wval_input _ _ _ hw, wval_input _ _ _ hw]
  · have hwn : n ≤ w := by omega
    have hv := patch_gateVal_eq_of_not_inCone hAO hAO' (w - n) (h hwn).1 (h hwn).2 x
    rw [gateVal_eq_wval, gateVal_eq_wval, Nat.add_sub_of_le hwn] at hv
    exact hv

lemma patch_size (C : Circuit) (j : ℕ) (g : Gate) : (patch C j g).size = C.size := by
  simp [Circuit.size, patch_length]

lemma patch_isLeastAO {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {j : ℕ} {g : Gate} (hL : IsLeastAO G C)
    (hAO' : IsAO2 n (patch C j g)) (hF' : circuitFun n (patch C j g) = graphFun G ∅) :
    IsLeastAO G (patch C j g) := by
  refine ⟨hAO', hF', ?_⟩
  intro D hD hDF
  rw [patch_size]
  exact hL.2.2 D hD hDF

lemma patch_junk_mem_iff_of_not_inCone {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {j : ℕ} {g : Gate} (hAO : IsAO2 n C) (hAO' : IsAO2 n (patch C j g))
    {k : ℕ} (hne : j ≠ k) (hCone : ¬ InCone n C j k) :
    k ∈ junk G (patch C j g) ↔ k ∈ junk G C := by
  change (k ∈ (Finset.range (patch C j g).gates.length).filter (fun i => IsDirtyAnd n G (patch C j g) i)) ↔
    k ∈ (Finset.range C.gates.length).filter (fun i => IsDirtyAnd n G C i)
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_range, IsDirtyAnd, IsDirty, patch_length,
    gateAt_patch_ne C j k g hne, patch_gateVal_eq_of_not_inCone hAO hAO' k hne hCone]


lemma patch_cone_subset_of_raw_inputs {n : ℕ} {C : Circuit} {r : ℕ} {g : Gate}
    (hraw : ∀ w ∈ g.inputs, w < n) {i j : ℕ} :
    InCone n (patch C r g) i j → InCone n C i j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hc
    have hj' := inCone_lt_len hc
    have hj : j < C.gates.length := by simpa only [patch_length] using hj'
    obtain ⟨w,hw,hnw,hwj,hsub⟩ := (inCone_iff hj').mp hc
    by_cases hjr : j = r
    · subst j
      rw [gateAt_patch_eq hj] at hw
      have := hraw w hw
      omega
    · rw [gateAt_patch_ne C r j g (Ne.symm hjr)] at hw
      apply (inCone_iff hj).mpr
      refine ⟨w,hw,hnw,hwj,?_⟩
      rcases hsub with he | hc'
      · exact Or.inl he
      · exact Or.inr (ih (w-n) (by omega) hc')

lemma topForm_of_cone_subset {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C D : Circuit} (hlen : D.gates.length = C.gates.length)
    (hop : ∀ i < C.gates.length, (gateAt D i).op = (gateAt C i).op)
    (hcone : ∀ i j, InCone n D i j → InCone n C i j)
    (hjunk : junk G C ⊆ junk G D) (hT : TopForm G C) : TopForm G D := by
  intro i hi j hj hiand hib hjand hc
  have hiC : i < C.gates.length := by omega
  have hjC : j < C.gates.length := by omega
  have hiop : (gateAt C i).op = GateOp.and := (hop i hiC).symm.trans hiand
  have hjop : (gateAt C j).op = GateOp.and := (hop j hjC).symm.trans hjand
  have hibC : BelowF G C i := by
    intro x hx
    by_contra hf
    have hm : i ∈ junk G C := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hiC,hiop,hiC,x,hx,
        Bool.eq_false_iff.mpr hf⟩
    obtain ⟨_,_,_,y,hy,hyF⟩ := Finset.mem_filter.mp (hjunk hm)
    have := hib y hy
    rw [hyF] at this
    cases this
  exact hT i hiC j hjC hiop hibC hjop (hcone i j hc)

end Patch
namespace IndependentDescent

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def product {n : ℕ} (P Q : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)

def Safe {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (w : Fin n) : Prop :=
  ∀ x : Fin n → Bool, product P Q x = true → x w = true → graphFun G ∅ x = true

def leftCenters {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) : Finset (Fin n) :=
  P.filter fun p => ∀ q ∈ Q, G.Adj p q

def rightCenters {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) : Finset (Fin n) :=
  Q.filter fun q => ∀ p ∈ P, G.Adj p q

def Useful {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (u v : Fin n) : Prop :=
  G.Adj u v ∧ product P Q (pairInput u v) = true ∧
    (Safe G P Q u ∨ Safe G P Q v)

lemma product_true {n : ℕ} (P Q : Finset (Fin n)) (x : Fin n → Bool) :
    product P Q x = true ↔ (∃ p ∈ P, x p = true) ∧ ∃ q ∈ Q, x q = true := by
  simp [product]

lemma wmax_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ) (P Q : Finset (Fin n))
    (heval : ∀ x : Fin n → Bool, gateVal n C g x = product P Q x) (w : Fin n) :
    w ∈ wmax G C g ↔ Safe G P Q w := by
  simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and, Safe]
  simp_rw [heval]

lemma graph_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

end IndependentDescent

namespace Cases

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core

lemma edge_nonempty_of_junk_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hJ : (junk G C).Nonempty) :
    G.edgeFinset.Nonempty := by
  by_contra hE
  have hnone : ∀ u v : Fin n, ¬ G.Adj u v := by
    intro u v huv
    exact hE ⟨s(u,v), by simpa using huv⟩
  let D : Circuit := ⟨[], n⟩
  have hD : IsAO2 n D := by simp [IsAO2, AndOrOnly, ReadsBack, D]
  have hDF : circuitFun n D = graphFun G ∅ := by
    funext x
    simp [circuitFun, Circuit.eval, Circuit.wires, D, graphFun, hnone]
  have hsize := hL.2.2 D hD hDF
  obtain ⟨j, hj⟩ := hJ
  have hjlt : j < C.gates.length := by
    exact Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  simp only [Circuit.size, D, List.length_nil] at hsize
  omega

end Cases

namespace CleanReplacement

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm

def gateBit (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def stepWire (w : List Bool) (g : Gate) : List Bool := w ++ [gateBit w g]

def WiresLE (w z : List Bool) : Prop :=
  w.length = z.length ∧ ∀ i, w.getD i false = true → z.getD i false = true

def IsMonoGate (g : Gate) : Prop := g.op = GateOp.and ∨ g.op = GateOp.or

lemma monoGate_of_mem {C : Circuit} (hC : Monotone2 C) {g : Gate} (hg : g ∈ C.gates) :
    IsMonoGate g := by
  simpa [IsMonoGate] using (hC g hg).1

lemma bit_mono {w z : List Bool} (h : WiresLE w z) {g : Gate} (hg : IsMonoGate g)
    (hw : gateBit w g = true) : gateBit z g = true := by
  rcases hg with hop | hop
  · simp only [gateBit, hop, GateOp.eval, List.all_map, List.all_eq_true,
      Function.comp_apply, id_eq] at hw ⊢
    exact fun i hi => h.2 i (hw i hi)
  · simp only [gateBit, hop, GateOp.eval, List.any_map, List.any_eq_true,
      Function.comp_apply, id_eq] at hw ⊢
    obtain ⟨i, hi, hv⟩ := hw
    exact ⟨i, hi, h.2 i hv⟩

lemma append_mono {w z : List Bool} {a b : Bool} (h : WiresLE w z)
    (hab : a = true → b = true) : WiresLE (w ++ [a]) (z ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  rw [List.getD_eq_getElem?_getD] at hi ⊢
  by_cases hlt : i < w.length
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.getElem?_append_left (by rwa [← h.1])]
    simpa only [List.getD_eq_getElem?_getD] using h.2 i
      (by simpa only [List.getD_eq_getElem?_getD] using hi)
  · rw [List.getElem?_append_right (Nat.le_of_not_gt hlt)] at hi
    rw [List.getElem?_append_right (by rw [← h.1]; omega), ← h.1]
    cases hd : i - w.length with
    | zero =>
      simp only [hd, List.getElem?_cons_zero, Option.getD_some] at hi ⊢
      exact hab hi
    | succ k => simp [hd] at hi

lemma fold_mono (gs : List Gate) (hg : ∀ g ∈ gs, IsMonoGate g)
    {w z : List Bool} (h : WiresLE w z) :
    WiresLE (gs.foldl stepWire w) (gs.foldl stepWire z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun k hk => hg k (List.mem_cons_of_mem _ hk))
      (append_mono h (bit_mono h (hg g (by simp))))

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (stepWire w g) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : Fin n) :
    (List.ofFn x).getD u.val false = x u := by
  simp [List.getD_eq_getElem?_getD]

lemma ofFn_mono {n : ℕ} {x y : Fin n → Bool} (h : ∀ u, x u = true → y u = true) :
    WiresLE (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hlt : i < n
  · rw [ofFn_getD y ⟨i, hlt⟩]
    exact h ⟨i, hlt⟩ (by simpa only [ofFn_getD x ⟨i, hlt⟩] using hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hlt)] at hi
    cases hi

def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩

def earlierWires (C : Circuit) (j : ℕ) (w : List Bool) : List Bool :=
  (C.gates.take j).foldl stepWire w

def off : Gate := ⟨GateOp.or, []⟩

def edgeGate {n : ℕ} (u v : Fin n) : Gate := ⟨GateOp.and, [u.val, v.val]⟩

lemma off_bit (w : List Bool) : gateBit w off = false := rfl

lemma edge_bit {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) (u v : Fin n) :
    gateBit (earlierWires C j (List.ofFn x)) (edgeGate u v) = (x u && x v) := by
  simp only [gateBit, edgeGate, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, id_eq, Bool.and_true]
  unfold earlierWires
  rw [fold_getD_lt _ _ _ (by simp), fold_getD_lt _ _ _ (by simp),
    ofFn_getD, ofFn_getD]

lemma wires_patch {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (g : Gate) (w : List Bool) :
    (patch C j g).wires w = (C.gates.drop (j + 1)).foldl stepWire (stepWire (earlierWires C j w) g) := by
  change (C.gates.set j g).foldl stepWire w = _
  rw [List.set_eq_take_append_cons_drop, ite_eq_left hj, List.foldl_append, List.foldl_cons]
  rfl

lemma original_patch {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    patch C j C.gates[j] = C := by
  cases C with
  | mk gates output =>
    change Circuit.mk (gates.set j gates[j]) output = Circuit.mk gates output
    congr 1
    exact List.set_getElem_self hj

lemma patch_mono {C : Circuit} (hC : Monotone2 C) {j : ℕ} (hj : j < C.gates.length)
    (g h : Gate) (w : List Bool)
    (hbit : gateBit (earlierWires C j w) g = true → gateBit (earlierWires C j w) h = true) :
    WiresLE ((patch C j g).wires w) ((patch C j h).wires w) := by
  rw [wires_patch hj, wires_patch hj]
  apply fold_mono _ (fun k hk => monoGate_of_mem hC (List.mem_of_mem_drop hk))
  exact append_mono ⟨rfl, fun _ h => h⟩ hbit

lemma patch_bit {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
    (g : Gate) (x : Fin n → Bool) :
    gateVal n (patch C j g) j x = gateBit (earlierWires C j (List.ofFn x)) g := by
  have hlen : (earlierWires C j (List.ofFn x)).length = n + j := by
    unfold earlierWires
    rw [fold_length]
    simp [Nat.min_eq_left (Nat.le_of_lt hj)]
  unfold gateVal
  rw [wires_patch hj, fold_getD_lt _ _ _ (by simp [stepWire, hlen]), ← hlen]
  simp [stepWire, List.getD_eq_getElem?_getD]

lemma patch_isMono {C : Circuit} (hC : Monotone2 C) {j : ℕ} {g : Gate}
    (hg : IsMonoGate g) (hlen : g.inputs.length ≤ 2) : Monotone2 (patch C j g) := by
  intro k hk
  change k ∈ C.gates.set j g at hk
  rcases List.mem_or_eq_of_mem_set hk with hk | rfl
  · exact hC k hk
  · exact ⟨by simpa [IsMonoGate] using hg, hlen⟩

lemma gateAt_patch_ne (C : Circuit) (j k : ℕ) (g : Gate) (hne : j ≠ k) :
    gateAt (patch C j g) k = gateAt C k := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma pair_le {n : ℕ} {x : Fin n → Bool} {u v : Fin n}
    (hu : x u = true) (hv : x v = true) (k : Fin n) :
    pairInput u v k = true → x k = true := by
  simp only [pairInput, decide_eq_true_eq]
  rintro (rfl | rfl)
  · exact hu
  · exact hv

lemma circuit_mono {n : ℕ} {C : Circuit} (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ u, x u = true → y u = true) :
    circuitFun n C x = true → circuitFun n C y = true :=
  (fold_mono C.gates (fun _ hg => monoGate_of_mem hC hg) (ofFn_mono hxy)).2 C.output

lemma mem_junk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {j : ℕ} :
    j ∈ junk G C ↔ j < C.gates.length ∧ IsDirtyAnd n G C j := by
  unfold junk gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]


lemma ao2_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) : Monotone2 C := by
  intro g hg
  exact ⟨by simpa using hAO.1 g hg, Nat.le_of_eq (hAO.2.2 g hg)⟩

lemma no_clean_independent_replacement {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
    (hCone : ¬ InCone n C j k) (R : Gate)
    (hOp : R.op = GateOp.and ∨ R.op = GateOp.or)
    (hLen : R.inputs.length = 2) (hBack : ∀ w ∈ R.inputs, w < n + j)
    (hClean : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
      gateBit (earlierWires C j (List.ofFn x)) R = false)
    (hCover : ∀ u v : Fin n, G.Adj u v →
      circuitFun n (patch C j off) (pairInput u v) = false →
      gateBit (earlierWires C j (List.ofFn (pairInput u v))) R = true) : False := by
  have hjmem : j ∈ junk G C := by rw [hJ]; simp
  have hkmem : k ∈ junk G C := by rw [hJ]; simp
  have hj : j < C.gates.length := (mem_junk.mp hjmem).1
  have hmono : Monotone2 C := ao2_mono hL.1
  let D := patch C j R
  have hDAO : IsAO2 n D := Patch.patch_isAO2 hL.1 j R hOp hLen hBack
  have hDM : Monotone2 D := ao2_mono hDAO
  have hnegative (x : Fin n → Bool) (hf : graphFun G ∅ x = false) :
      WiresLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x)) := by
    have h := patch_mono hmono hj R C.gates[j] (List.ofFn x)
      (by intro hh; rw [hClean x hf] at hh; cases hh)
    rwa [original_patch hj] at h
  have hEdges (u v : Fin n) (huv : G.Adj u v) :
      circuitFun n D (pairInput u v) = true := by
    have hF : circuitFun n C (pairInput u v) = true := by
      rw [hL.2.1]
      exact (graph_true G _).mpr ⟨u,v,huv,by simp [pairInput],by simp [pairInput]⟩
    cases hCut : circuitFun n (patch C j off) (pairInput u v) with
    | false =>
      have h := patch_mono hmono hj C.gates[j] R (List.ofFn (pairInput u v))
        (fun _ => hCover u v huv hCut)
      rw [original_patch hj] at h
      exact h.2 C.output hF
    | true =>
      exact (patch_mono hmono hj off R (List.ofFn (pairInput u v))
        (by intro hh; simp [off_bit] at hh)).2 C.output hCut
  have hDF : circuitFun n D = graphFun G ∅ := by
    funext x
    cases hf : graphFun G ∅ x with
    | false =>
      cases hd : circuitFun n D x with
      | false => rfl
      | true =>
        have hh : circuitFun n C x = true := (hnegative x hf).2 C.output hd
        rw [hL.2.1,hf] at hh
        cases hh
    | true =>
      obtain ⟨u,v,huv,hu,hv⟩ := (graph_true G x).mp hf
      exact circuit_mono hDM (pair_le hu hv) (hEdges u v huv)
  have hNoJ : j ∉ junk G D := by
    intro hmem
    obtain ⟨_,_,_,x,hx,hf⟩ := mem_junk.mp hmem
    change gateVal n (patch C j R) j x = true at hx
    rw [patch_bit hj, hClean x hf] at hx
    cases hx
  have hSub : junk G D ⊆ junk G C := by
    intro a ha
    have hja : j ≠ a := by intro he; exact hNoJ (he.symm ▸ ha)
    obtain ⟨haLen,haAnd,_,x,hx,hf⟩ := mem_junk.mp ha
    have haC : a < C.gates.length := by simpa [D,patch] using haLen
    have haOp : (gateAt C a).op = GateOp.and := by
      change (gateAt (patch C j R) a).op = GateOp.and at haAnd
      rwa [gateAt_patch_ne C j a R hja] at haAnd
    exact mem_junk.mpr ⟨haC,haOp,haC,x,(hnegative x hf).2 (n+a) hx,hf⟩
  have hkD : k ∈ junk G D :=
    (Patch.patch_junk_mem_iff_of_not_inCone hL.1 hDAO hne hCone).mpr hkmem
  have hJD : junk G D = {k} := by
    apply Finset.ext
    intro a
    constructor
    · intro ha
      have hao := hSub ha
      rw [hJ] at hao
      simp only [Finset.mem_insert,Finset.mem_singleton] at hao ⊢
      rcases hao with rfl | he
      · exact (hNoJ ha).elim
      · exact he
    · intro ha
      have he := Finset.mem_singleton.mp ha
      exact he ▸ hkD
  have hDL : IsLeastAO G D := Patch.patch_isLeastAO hL hDAO hDF
  exact hOne D hDL (by rw [hJD]; simp)

end CleanReplacement
namespace FlagReduction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo
open CleanReplacement IndependentDescent

lemma earlier_wire_eq {n : ℕ} (C : Circuit) (j : ℕ) (hj : j ≤ C.gates.length)
    (x : Fin n → Bool) {w : ℕ} (hw : w < n + j) :
    (earlierWires C j (List.ofFn x)).getD w false = wval C x w := by
  have hlen : (earlierWires C j (List.ofFn x)).length = n + j := by
    unfold earlierWires
    rw [fold_length]
    simp [Nat.min_eq_left hj]
  have hsplit : C.wires (List.ofFn x) =
      (C.gates.drop j).foldl stepWire (earlierWires C j (List.ofFn x)) := by
    change C.gates.foldl stepWire _ = _
    conv_lhs => rw [← List.take_append_drop j C.gates, List.foldl_append]
    rfl
  unfold wval
  rw [hsplit, fold_getD_lt _ _ _ (by omega)]

lemma star_gate_bit {n : ℕ} (C : Circuit) (j : ℕ) (hj : j ≤ C.gates.length)
    (z : Fin n) (w : ℕ) (hw : w < n + j) (x : Fin n → Bool) :
    gateBit (earlierWires C j (List.ofFn x)) ⟨GateOp.and,[z.val,w]⟩ =
      (x z && wval C x w) := by
  simp only [gateBit, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, id_eq, Bool.and_true]
  rw [earlier_wire_eq C j hj x (by have := z.isLt; omega),
    earlier_wire_eq C j hj x hw, Lift.wval_input C x z.val z.isLt]

end FlagReduction

namespace RawOperands


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in
lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

open PEqualNP.CleanedNonEdge in
lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have h3 := orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩


lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.or) (i : ℕ) (hi : i ∈ (gateAt C r).inputs)
    (hlt : i < n + r) (hv : W n C x i = true) : W n C x (n + r) = true := by
  rw [W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  exact ⟨i, hi, by rw [ite_eq_left hlt]; exact hv⟩

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.and)
    (h : ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ W n C x i = true) :
    W n C x (n + r) = true := by
  rw [W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  intro i hi
  rw [ite_eq_left (h i hi).1]; exact (h i hi).2

open PEqualNP.CleanedNonEdge in
lemma reach_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
    (hv : W n C x (n + g) = true) :
    ∀ k, k < C.gates.length → g ∈ (orSets n C).getD k [] → W n C x (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hmem
    rcases (orSets_mem_iff n C k g hk).mp hmem with h | ⟨hop, w, hw, hn, hlt, hx⟩
    · rw [← h]; exact hv
    · have h3 := ih (w - n) (by omega) (by omega) hx
      have e : n + (w - n) = w := by omega
      rw [e] at h3
      exact W_or n C x k hk hop w hw hlt h3

open PEqualNP.CleanedNonEdge in
lemma reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w g : ℕ)
    (h : OrReaches n C w g) (hv : W n C x (n + g) = true) : W n C x w = true := by
  obtain ⟨hn, hmem⟩ := h
  by_cases hk : w - n < C.gates.length
  · have h3 := reach_val n C x g hv (w - n) hk hmem
    have e : n + (w - n) = w := by omega
    rw [e] at h3
    exact h3
  · exfalso
    have hlen : (orSets n C).length = C.gates.length := by
      unfold orSets; rw [orFold_length]; simp
    have hge : (orSets n C).length ≤ w - n := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hmem
    simp at hmem

lemma mem_filter_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α)
    (h : a ∈ @Finset.filter α p d s) : p a :=
  ((@Finset.mem_filter α p d s a).mp h).2

lemma side_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (b : Fin 2) (i : Fin n)
    (hi : i ∈ PEqualNP.TopForm.side (n := n) C j b) (hx : x i = true) :
    W n C x (PEqualNP.TopForm.opnd C j b) = true := by
  unfold PEqualNP.TopForm.side PEqualNP.TopForm.orIn at hi
  have hi2 := mem_filter_gen _ _ _ _ hi
  rcases hi2 with h | ⟨k, hk, hreach, hop, hin⟩
  · rw [← h, W_input n C x i.val i.isLt]; exact hx
  · have hk1 : W n C x (n + k) = true := by
      apply W_or n C x k hk hop i.val hin (by have := i.isLt; omega)
      rw [W_input n C x i.val i.isLt]; exact hx
    exact reach_up n C x _ k hreach hk1

open PEqualNP.EdgeOwnership in
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3


lemma gateAt_mem' (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq C j hj]; exact List.getElem_mem hj

open PEqualNP.EdgeOwnership in
lemma inCone_lt (n : ℕ) (C : Circuit) : ∀ j i, InCone n C i j → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i h
    obtain ⟨_, k, hk, _, h3⟩ := (inCone_iff n C i j).mp h
    rcases h3 with h3 | h3
    · omega
    · have := ih k hk i h3; omega

open PEqualNP.CleanedNonEdge in
lemma orReach_trans (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (w : ℕ) (hw : w ∈ (gateAt C k).inputs)
    (hlt : w < n + k) (g : ℕ) (h : OrReaches n C w g) : OrReaches n C (n + k) g := by
  obtain ⟨hn, hmem⟩ := h
  refine ⟨by omega, ?_⟩
  have e : n + k - n = k := by omega
  rw [e]
  exact (orSets_mem_iff n C k g hk).mpr (Or.inr ⟨hop, w, hw, hn, hlt, hmem⟩)

open PEqualNP.CleanedNonEdge in
lemma orReach_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) k := by
  refine ⟨by omega, ?_⟩
  have e : n + k - n = k := by omega
  rw [e]
  exact (orSets_mem_iff n C k k hk).mpr (Or.inl rfl)

lemma orIn_mem (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

open PEqualNP.CleanedNonEdge in
lemma down (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hAO : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ w, W n C x w = true → (∃ i : Fin n, i ∈ PEqualNP.TopForm.orIn n C w ∧ x i = true) ∨
      ∃ k, k < C.gates.length ∧ OrReaches n C w k ∧ (gateAt C k).op = GateOp.and ∧
        W n C x (n + k) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hwn : w < n
    · left
      refine ⟨⟨w, hwn⟩, (orIn_mem n C w _).mpr (Or.inl rfl), ?_⟩
      rw [← W_input n C x w hwn]; exact hv
    · by_cases hk : w - n < C.gates.length
      · have hw : w = n + (w - n) := by omega
        set k := w - n with hkdef
        rcases hAO k hk with hop | hop
        · right
          refine ⟨k, hk, ?_, hop, ?_⟩
          · rw [hw]; exact orReach_self n C k hk
          · rw [← hw]; exact hv
        · have hv2 := hv
          rw [hw, W_gate n C x k hk, hop] at hv2
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hv2
          obtain ⟨i, hi, hiv⟩ := hv2
          split_ifs at hiv with hlt
          rcases ih i (by omega) hiv with ⟨j, hj, hxj⟩ | ⟨k', hk', hr, hop', hv'⟩
          · left
            refine ⟨j, ?_, hxj⟩
            rw [orIn_mem] at hj ⊢
            right
            rcases hj with hj | ⟨k'', hk'', hr, hop'', hin⟩
            · refine ⟨k, hk, ?_, hop, ?_⟩
              · rw [hw]; exact orReach_self n C k hk
              · rw [hj]; exact hi
            · refine ⟨k'', hk'', ?_, hop'', hin⟩
              rw [hw]; exact orReach_trans n C k hk hop i hi hlt k'' hr
          · right
            refine ⟨k', hk', ?_, hop', hv'⟩
            rw [hw]; exact orReach_trans n C k hk hop i hi hlt k' hr
      · exfalso
        have hl := wires_length n C x
        have : W n C x w = false := getD_ge_length _ w (by omega)
        rw [this] at hv; exact Bool.false_ne_true hv

open PEqualNP.EdgeOwnership in
lemma orSets_cone (n : ℕ) (C : Circuit) : ∀ m, m < C.gates.length → ∀ k,
    k ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD m [] → k = m ∨ InCone n C k m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm k hk
    rcases (orSets_mem_iff n C m k hm).mp hk with h | ⟨_, w, hw, hn, hlt, hx⟩
    · exact Or.inl h
    · right
      have h2 := ih (w - n) (by omega) (by omega) k hx
      have e : n + (w - n) = w := by omega
      exact (inCone_iff n C k m).mpr ⟨hm, w - n, by omega, by rw [e]; exact hw, h2⟩

open PEqualNP.EdgeOwnership in
lemma reach_cone (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (o : ℕ)
    (ho : o ∈ (gateAt C j).inputs) (hlt : o < n + j) (k : ℕ)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C o k) : InCone n C k j := by
  obtain ⟨hn, hmem⟩ := h
  have h2 := orSets_cone n C (o - n) (by omega) k hmem
  have e : n + (o - n) = o := by omega
  exact (inCone_iff n C k j).mpr ⟨hj, o - n, by omega, by rw [e]; exact ho, h2⟩

open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

lemma junk_data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (hj : j ∈ junk G C) :
    j < C.gates.length ∧ (gateAt C j).op = GateOp.and := by
  obtain ⟨hjl, hja, _⟩ := Finset.mem_filter.mp hj
  exact ⟨Finset.mem_range.mp hjl, hja⟩

lemma operand_mem {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  have hlen := hAO.2.2 _ (gateAt_mem' C j hj)
  unfold opnd
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  exact List.getElem_mem _

lemma raw_operand_of_no_junk_cone {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hno : ∀ k ∈ junk G C, ¬ InCone n C k j) (b : Fin 2) (x : Fin n → Bool) :
    PEqualNP.ReadTwo.wval C x (opnd C j b) =
      decide (∃ u ∈ side (n := n) C j b, x u = true) := by
  have hm := operand_mem C hAO j hj b
  have hlt := hAO.2.1 j hj _ hm
  have hi : W n C x (opnd C j b) = true ↔
      ∃ u ∈ side (n := n) C j b, x u = true := by
    constructor
    · intro hv
      have hops : ∀ k < C.gates.length,
          (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or :=
        fun k hk => hAO.1 _ (gateAt_mem' C k hk)
      rcases down n C x hops _ hv with hraw | ⟨k, hk, hr, hop, _⟩
      · exact hraw
      · have hc := reach_cone n C j hj _ hm hlt k hr
        have hnb : ¬ BelowF G C k := fun hb => hTop k hk j hj hop hb hand hc
        have hd : ∃ y : Fin n → Bool, gateVal n C k y = true ∧ graphFun G ∅ y = false := by
          by_contra hn
          apply hnb
          intro y hy
          by_contra hf
          exact hn ⟨y, hy, Bool.eq_false_iff.mpr hf⟩
        have hkj : k ∈ junk G C :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hop, hk, hd⟩
        exact (hno k hkj hc).elim
    · rintro ⟨u, hu, hxu⟩
      exact side_val n C x j b u hu hxu
  change W n C x (opnd C j b) = _
  by_cases hv : W n C x (opnd C j b) = true
  · simp [hv, hi.mp hv]
  · have hn : ¬ ∃ u ∈ side (n := n) C j b, x u = true := fun h => hv (hi.mpr h)
    simp [Bool.eq_false_iff.mpr hv, hn]

lemma independent_no_junk_ancestors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g h : ℕ) (hJ : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (j : ℕ) (hj : j = g ∨ j = h) :
    ∀ k ∈ junk G C, ¬ InCone n C k j := by
  intro k hk hc
  have hkm : k = g ∨ k = h := by simpa [hJ] using hk
  rcases hj with rfl | rfl <;> rcases hkm with rfl | rfl
  · have := inCone_lt n C _ _ hc
    omega
  · exact hhg hc
  · exact hgh hc
  · have := inCone_lt n C _ _ hc
    omega

lemma independent_operand {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (j : ℕ) (hj : j = g ∨ j = h) (b : Fin 2) (x : Fin n → Bool) :
    PEqualNP.ReadTwo.wval C x (opnd C j b) =
      decide (∃ u ∈ side (n := n) C j b, x u = true) := by
  have hjm : j ∈ junk G C := by simpa [hJ] using hj
  obtain ⟨hjl, hja⟩ := junk_data G C j hjm
  exact raw_operand_of_no_junk_cone G C hAO hTop j hjl hja
    (independent_no_junk_ancestors G C g h hJ hgh hhg j hj) b x

lemma and_gate_eq {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (x : Fin n → Bool) :
    gateVal n C j x =
      (PEqualNP.ReadTwo.wval C x (opnd C j 0) && PEqualNP.ReadTwo.wval C x (opnd C j 1)) := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem' C j hj))
  have ham : a ∈ (gateAt C j).inputs := by simp [hab]
  have hbm : b ∈ (gateAt C j).inputs := by simp [hab]
  have hba := hAO.2.1 j hj a ham
  have hbb := hAO.2.1 j hj b hbm
  change W n C x (n + j) = _
  rw [W_gate n C x j hj, hand, hab]
  simp [GateOp.eval, opnd, hab, hba, hbb, W, PEqualNP.ReadTwo.wval]

lemma independent_product {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (j : ℕ) (hj : j = g ∨ j = h) (x : Fin n → Bool) :
    gateVal n C j x =
      (decide (∃ u ∈ side (n := n) C j 0, x u = true) &&
        decide (∃ u ∈ side (n := n) C j 1, x u = true)) := by
  have hjm : j ∈ junk G C := by simpa [hJ] using hj
  obtain ⟨hjl, hja⟩ := junk_data G C j hjm
  rw [and_gate_eq C hAO j hjl hja x,
    independent_operand G C hAO hTop g h hJ hgh hhg j hj 0 x,
    independent_operand G C hAO hTop g h hJ hgh hhg j hj 1 x]


end RawOperands

namespace Critical.Base

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

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
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩
lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma topData {a : ℕ} (ha : a ∈ tops G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha
lemma junkData {a : ℕ} (ha : a ∈ junk G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
  rcases Finset.mem_filter.mp ha with ⟨hr, hop, hal, hd⟩
  exact ⟨hal, hop, hd⟩
lemma binaryInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
    ∃ p q, (gateAt C a).inputs = [p, q] :=
  List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
lemma opndMem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
  fin_cases b <;> simp [opnd, hpq]
lemma opndBound (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a :=
  hAO.2.1 a ha _ (opndMem hAO ha b)
lemma andValBoth (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔
      val C (List.ofFn x) (opnd C a 0) = true ∧
      val C (List.ofFn x) (opnd C a 1) = true := by
  rw [gateVal_eq_val, val_and (n := n) (by simp) ha hop]
  constructor
  · intro h
    exact ⟨(h _ (opndMem hAO ha 0)).2, (h _ (opndMem hAO ha 1)).2⟩
  · intro h i hi
    refine ⟨hAO.2.1 a ha i hi, ?_⟩
    obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
    rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
    · simpa [opnd, hpq] using h.1
    · have e : i = q := List.mem_singleton.mp hq
      subst i
      simpa [opnd, hpq] using h.2
lemma andValOperands (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  rw [andValBoth hAO ha hop]
  constructor
  · intro h b
    fin_cases b
    · exact h.1
    · exact h.2
  · intro h
    exact ⟨h 0, h 1⟩
lemma operandReachCone (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) :
    InCone n C h a :=
  operand_cone ha (opndMem hAO ha b) (opndBound hAO ha b)
    (orReaches_reach h _ hr).1
lemma operandReachLt (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) : h < a := by
  have hle := orStep_le (orReaches_reach h _ hr).1
  have hb := opndBound hAO ha b
  omega
lemma operandOrAndJunk (hAO : IsAO2 n C) (hT : TopForm G C) {a h : ℕ}
    (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h)
    (hh : (gateAt C h).op = GateOp.and) : h ∈ junk G C := by
  have hlen := (orReaches_reach h _ hr).2
  have hnb : ¬ BelowF G C h :=
    fun hb => hT h hlen a ha hh hb hop (operandReachCone hAO ha hr)
  have hdirty : ∃ x : Fin n → Bool, gateVal n C h x = true ∧ graphFun G ∅ x = false := by
    by_contra hne
    apply hnb
    intro x hx
    by_contra hf
    exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlen, hh, hlen, hdirty⟩
lemma reachVal {w h : ℕ} {x : Fin n → Bool} (hr : OrReaches n C w h)
    (hh : gateVal n C h x = true) : val C (List.ofFn x) w = true :=
  orStep_up (n := n) (by simp) (orReaches_reach h _ hr).1 hh
lemma eitherOperand (b c : Fin 2) : c = b ∨ c = 1 - b := by
  fin_cases b <;> fin_cases c <;> decide
lemma oppositeSideWmax (hAO : IsAO2 n C) {a j : ℕ} (ha : a ∈ tops G C) {b : Fin 2}
    (hr : OrReaches n C (opnd C a b) j) :
    side (n := n) C a (1 - b) ⊆ wmax G C j := by
  intro t ht
  obtain ⟨hal, hao, hab⟩ := topData ha
  simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
  intro x hj hx
  apply hab x
  apply (andValOperands hAO hal hao x).mpr
  intro c
  rcases eitherOperand b c with rfl | rfl
  · exact reachVal hr hj
  · exact reach_var_val x _ t (mem_orIn_reach t ht) hx
lemma orInTrans {w z : ℕ} (hr : Relation.ReflTransGen (OrStep n C) w z) :
    orIn n C z ⊆ orIn n C w :=
  fun x hx => reach_mem_orIn x (hr.trans (mem_orIn_reach x hx))
lemma orStepOpnd (hAO : IsAO2 n C) {m : ℕ} (hm : m < C.gates.length)
    (hop : (gateAt C m).op = GateOp.or) (b : Fin 2) :
    OrStep n C (n + m) (opnd C m b) :=
  ⟨m, hm, rfl, hop, opndMem hAO hm b, opndBound hAO hm b⟩
lemma inputsAsOpnd (hAO : IsAO2 n C) {m z : ℕ} (hm : m < C.gates.length)
    (hz : z ∈ (gateAt C m).inputs) : ∃ b : Fin 2, z = opnd C m b := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO hm
  rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
  · exact ⟨0, by simp [opnd, hpq]⟩
  · have e : z = q := List.mem_singleton.mp hq
    exact ⟨1, by simpa [opnd, hpq] using e⟩
lemma orNOfRaw {m : ℕ} (hm : m < C.gates.length) (hop : (gateAt C m).op = GateOp.or)
    (hn : (orIn n C (n + m)).Nonempty) : m ∈ orN G C := by
  obtain ⟨t, ht⟩ := hn
  simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
  refine ⟨hm, hop, ?_⟩
  intro hb
  have hv : gateVal n C m (pairInput t t) = true :=
    reach_var_val (pairInput t t) _ t (mem_orIn_reach t ht) (pairInput_left t t)
  exact G.irrefl ((graphFun_pair G t t).mp (hb _ hv))
lemma lamAvoidsUstar {m : ℕ} (hm : m ∈ lam G C)
    (hstar : ∀ a ∈ tops G C, ∀ x ∈ side (n := n) C a 0, ∀ y ∈ side C a 1, G.Adj x y) :
    ∃ t : Fin n, ∀ x ∈ orIn n C (n + m), G.Adj t x ∧ s(t, x) ∉ Ustar G C := by
  obtain ⟨_, _, _, a, ha, b, hcard, hr⟩ := Finset.mem_filter.mp hm
  have hsub : orIn n C (n + m) ⊆ side (n := n) C a b :=
    orInTrans (orReaches_reach m _ hr).1
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hcard
  refine ⟨t, fun x hx => ?_⟩
  have hts : t ∈ side (n := n) C a (1 - b) := by simp [ht]
  have hstar' : s(t, x) ∈ starEdges G C := by
    unfold starEdges
    refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ?_⟩
    fin_cases b
    · exact ⟨(x, t), Finset.mem_product.mpr ⟨hsub hx, hts⟩, Sym2.eq_swap⟩
    · exact ⟨(t, x), Finset.mem_product.mpr ⟨hts, hsub hx⟩, rfl⟩
  refine ⟨?_, fun he => (Finset.mem_sdiff.mp he).2 hstar'⟩
  fin_cases b
  · exact (hstar a ha x (hsub hx) t hts).symm
  · exact hstar a ha t hts x (hsub hx)

lemma sideVal {a : ℕ} {b : Fin 2} {x : Fin n → Bool} {t : Fin n}
    (ht : t ∈ side (n := n) C a b) (hx : x t = true) :
    val C (List.ofFn x) (opnd C a b) = true :=
  reach_var_val x _ t (mem_orIn_reach t ht) hx

lemma andFromInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) {x : Fin n → Bool}
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1)
    (xu : x u = true) (xv : x v = true) : gateVal n C a x = true :=
  (andValBoth hAO ha hop x).mpr ⟨sideVal hu xu, sideVal hv xv⟩

lemma topAdj (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) :
    G.Adj u v := by
  obtain ⟨hl, ho, hb⟩ := topData ha
  exact (graphFun_pair G u v).mp
    (hb _ (andFromInputs hAO hl ho hu hv (pairInput_left u v) (pairInput_right u v)))

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

lemma operandSupport (hAO : IsAO2 n C) (hT : TopForm G C) {a : ℕ}
    (ha : a < C.gates.length) (ho : (gateAt C a).op = GateOp.and) {b : Fin 2}
    {u v : Fin n} (h : val C (List.ofFn (pairInput u v)) (opnd C a b) = true) :
    (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
      ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧
        gateVal n C j (pairInput u v) = true := by
  rcases operand_trace (C := C) u v _ h with ⟨t, ht, hr⟩ | ⟨j, hj, hn, hr, hv⟩
  · exact .inl ⟨t, reach_mem_orIn t hr, ht⟩
  · have hr' := reach_orReaches hr j rfl hj
    exact .inr ⟨j, operandOrAndJunk hAO hT ha ho hr'
      ((hAO.1 _ (gateAt_mem hj)).resolve_right hn), hr', hv⟩

lemma memJunkPair {j k a : ℕ} (hs : junk G C = {j,k}) (ha : a ∈ junk G C) :
    a = j ∨ a = k := by
  simpa only [hs, Finset.mem_insert, Finset.mem_singleton] using ha

lemma mem_gammaE_of_pair {u v : Fin n} (he : s(u, v) ∈ G.edgeFinset) {j : ℕ}
    (hv : gateVal n C j (pairInput u v) = true) :
    s(u, v) ∈ gammaE G C j :=
  Finset.mem_filter.mpr ⟨he, u, v, rfl, hv⟩

end Critical.Base

namespace Critical.Patch

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

lemma card_sdiff_eq {α : Type} [DecidableEq α] {A B : Finset α} (h : A ⊆ B) :
    (B \ A).card = B.card - A.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h]


lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_wires_getD_gate (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ k ∈ gs[j].inputs, k < acc.length + j) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD
        (acc.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun k =>
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun m => w.getD m false)]) acc).getD
          k false) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero] at hback ⊢
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen : acc.length < acc'.length := by
        simp only [acc', List.length_append, List.length_singleton]; omega
      rw [foldl_wires_getD_lt gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length false = g.op.eval (g.inputs.map fun k => acc.getD k false) := by
        simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hka : k < acc.length := hback k hk
      have hka' : k < acc'.length := by omega
      rw [foldl_wires_getD_lt gs acc' k hka']
      simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_left hka]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      apply ih acc' j' hj'
      intro k hk
      have hbk := hback k (by simpa using hk)
      omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wires_len C.gates x

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlt : i < (List.ofFn x).length := by simp [hi]
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlt]
  simp [List.getD_eq_getElem?_getD, hi]

lemma gateVal_eq_wval {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wval C x (n + j) := rfl

lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  rw [List.getD_eq_getElem?_getD]
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    rw [wires_length, List.length_ofFn]
  rw [List.getElem?_eq_none (by omega)]
  rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  unfold opnd
  match h : (gateAt C j).inputs with
  | [a, b] => simp
  | [] => rw [h] at hlen; simp at hlen
  | [_] => rw [h] at hlen; simp at hlen
  | _ :: _ :: _ :: _ => rw [h] at hlen; simp at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hback : ∀ k ∈ C.gates[j].inputs, k < (List.ofFn x).length + j := by
    intro k hk; rw [hlen, ← gateAt_eq hj] at *; exact hAO.2.1 j hj k hk
  have h := foldl_wires_getD_gate C.gates (List.ofFn x) j hj hback
  rw [hlen] at h
  rw [h, ← gateAt_eq hj, gate_inputs_eq hAO hj]
  simp

lemma wval_gate_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wval C x (n + j) = (wval C x (opnd C j 0) && wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]

lemma wval_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]

lemma foldl_cones_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_cones_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (coneStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones; rw [foldl_cones_len]; simp

lemma foldl_cones_getD_gate (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (coneStep n) acc).getD (acc.length + j) [] =
      (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (acc.length + j)))).flatMap
        (fun w => (w - n) :: (gs.foldl (coneStep n) acc).getD (w - n) []) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero]
      set acc' := coneStep n acc g
      have hlen : acc.length < acc'.length := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]; omega
      rw [foldl_cones_getD_lt n gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + acc.length))).flatMap
            (fun w => (w - n) :: acc.getD (w - n) []) := by
        simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      apply List.flatMap_congr
      intro w hw
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      have hwn : w - n < acc.length := by omega
      have hwn' : w - n < acc'.length := by omega
      rw [foldl_cones_getD_lt n gs acc' (w - n) hwn']
      simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := coneStep n acc g
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      exact ih acc' j' hj'

lemma inCone_lt_len {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : j < C.gates.length := by
  by_contra hge
  unfold InCone at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [cones_length]; omega)] at h
  simp at h

lemma inCone_iff {n : ℕ} {C : Circuit} {i j : ℕ} (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone cones
  have h := foldl_cones_getD_gate n C.gates [] j hj
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h, ← gateAt_eq hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩; exact ⟨w, hw1, hw2, hw3, hw4⟩
  · rintro ⟨w, hw1, hw2, hw3, hw4⟩; exact ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩

lemma inCone_lt {n : ℕ} {C : Circuit} {i j : ℕ} : InCone n C i j → i < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro h
    have hj := inCone_lt_len h
    rw [inCone_iff hj] at h
    rcases h with ⟨w, _, hnw, hwnj, rfl | hsub⟩
    · omega
    · have := ih (w - n) (by omega) hsub; omega

lemma inCone_trans {n : ℕ} {C : Circuit} {i j k : ℕ} (h1 : InCone n C i j) (h2 : InCone n C j k) :
    InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    have hk := inCone_lt_len h2
    rw [inCone_iff hk] at h2 ⊢
    rcases h2 with ⟨w, hw, hnw, hwnk, rfl | hsub⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr h1⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr (ih (w - n) (by omega) hsub)⟩

def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩

lemma patch_length (C : Circuit) (j : ℕ) (g : Gate) :
    (patch C j g).gates.length = C.gates.length := by
  simp [patch]

lemma gateAt_patch_ne (C : Circuit) (j k : ℕ) (g : Gate) (hne : j ≠ k) :
    gateAt (patch C j g) k = gateAt C k := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma gateAt_patch_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (g : Gate) :
    gateAt (patch C j g) j = g := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, hj]

lemma patch_wval_gate_eval {n : ℕ} {C : Circuit} {j : ℕ} {g : Gate}
    (hAO : IsAO2 n C) (x : Fin n → Bool) {k : ℕ} (hk : k < C.gates.length)
    (hne : j ≠ k) :
    wval (patch C j g) x (n + k) = (gateAt C k).op.eval
      [wval (patch C j g) x (opnd C k 0), wval (patch C j g) x (opnd C k 1)] := by
  have hk' : k < (patch C j g).gates.length := by simpa only [patch_length] using hk
  have hgate := gateAt_patch_ne C j k g hne
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hback : ∀ w ∈ (patch C j g).gates[k].inputs, w < (List.ofFn x).length + k := by
    intro w hw
    rw [← gateAt_eq hk', hgate] at hw
    rw [hlen]
    exact hAO.2.1 k hk w hw
  have heval := foldl_wires_getD_gate (patch C j g).gates (List.ofFn x) k hk' hback
  rw [hlen, ← gateAt_eq hk', hgate, gate_inputs_eq hAO hk] at heval
  simpa only [wval, Circuit.wires, List.map_cons, List.map_nil] using heval

lemma patch_gateVal_eq_of_not_inCone {n : ℕ} {C : Circuit} {j : ℕ} {g : Gate}
    (hAO : IsAO2 n C) (k : ℕ) (hne : j ≠ k) (hCone : ¬ InCone n C j k)
    (x : Fin n → Bool) : gateVal n (patch C j g) k x = gateVal n C k x := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases hk : k < C.gates.length
    · have hval (b : Fin 2) : wval (patch C j g) x (opnd C k b) =
          wval C x (opnd C k b) := by
        by_cases hw : opnd C k b < n
        · rw [wval_input _ _ _ hw, wval_input _ _ _ hw]
        · have hw' : n ≤ opnd C k b := by omega
          have hlt := opnd_lt hAO hk b
          have hsub_ne : j ≠ opnd C k b - n := by
            intro he
            apply hCone
            exact (inCone_iff hk).mpr ⟨opnd C k b, opnd_mem hAO hk b, hw', hlt, Or.inl he⟩
          have hsub_cone : ¬ InCone n C j (opnd C k b - n) := by
            intro he
            apply hCone
            exact (inCone_iff hk).mpr ⟨opnd C k b, opnd_mem hAO hk b, hw', hlt, Or.inr he⟩
          have hv := ih (opnd C k b - n) (by omega) hsub_ne hsub_cone
          rw [gateVal_eq_wval, gateVal_eq_wval, Nat.add_sub_of_le hw'] at hv
          exact hv
      rw [gateVal_eq_wval, gateVal_eq_wval, patch_wval_gate_eval hAO x hk hne,
        wval_gate_eval hAO x hk, hval 0, hval 1]
    · rw [gateVal_eq_wval, gateVal_eq_wval, wval_ge_len _ _ (by rw [patch_length]; omega),
        wval_ge_len _ _ (by omega)]

lemma patch_wireVal_eq_of_not_inCone {n : ℕ} {C : Circuit} {j : ℕ} {g : Gate}
    (hAO : IsAO2 n C) (w : ℕ)
    (h : n ≤ w → j ≠ w - n ∧ ¬ InCone n C j (w - n)) (x : Fin n → Bool) :
    wval (patch C j g) x w = wval C x w := by
  by_cases hw : w < n
  · rw [wval_input _ _ _ hw, wval_input _ _ _ hw]
  · have hwn : n ≤ w := by omega
    have hv := patch_gateVal_eq_of_not_inCone (g := g) hAO (w - n) (h hwn).1 (h hwn).2 x
    rw [gateVal_eq_wval, gateVal_eq_wval, Nat.add_sub_of_le hwn] at hv
    exact hv

end Critical.Patch

namespace Critical

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def offPatch (C : Circuit) (h : ℕ) : Circuit := ⟨C.gates.set h ⟨GateOp.or, []⟩, C.output⟩

lemma offPatch_length (C : Circuit) (h : ℕ) : (offPatch C h).gates.length = C.gates.length := by
  simp [offPatch]

lemma gateAt_offPatch_ne (C : Circuit) (h k : ℕ) (hne : h ≠ k) :
    gateAt (offPatch C h) k = gateAt C k := by
  simp [offPatch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma orStep_offPatch {n : ℕ} {C : Circuit} {h w w' : ℕ}
    (hAnd : (gateAt C h).op = GateOp.and) (hs : Base.OrStep n C w w') :
    Base.OrStep n (offPatch C h) w w' := by
  obtain ⟨k, hk, rfl, hOr, hi, hb⟩ := hs
  have hne : h ≠ k := by
    intro he
    rw [← he, hAnd] at hOr
    cases hOr
  refine ⟨k, by simpa only [offPatch_length] using hk, rfl, ?_, ?_, hb⟩
  · simpa only [gateAt_offPatch_ne C h k hne] using hOr
  · simpa only [gateAt_offPatch_ne C h k hne] using hi

lemma orPath_offPatch {n : ℕ} {C : Circuit} {h w w' : ℕ}
    (hAnd : (gateAt C h).op = GateOp.and)
    (hs : Relation.ReflTransGen (Base.OrStep n C) w w') :
    Relation.ReflTransGen (Base.OrStep n (offPatch C h)) w w' := by
  induction hs using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | head hs _ ih => exact Relation.ReflTransGen.head (orStep_offPatch hAnd hs) ih

lemma offPatch_difference_trace {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {h : ℕ} (hAnd : (gateAt C h).op = GateOp.and) (x : Fin n → Bool) :
    ∀ w, Base.val C (List.ofFn x) w = true → Base.val (offPatch C h) (List.ofFn x) w = false →
    ∃ j, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ OrReaches n C w j ∧
      gateVal n C j x = true ∧ gateVal n (offPatch C h) j x = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hw'
    by_cases hwInput : w < n
    · rw [Base.val_input (n := n) (by simp) hwInput] at hw hw'
      rw [hw] at hw'
      cases hw'
    · by_cases hwLarge : n + C.gates.length ≤ w
      · rw [Base.val_ge (n := n) (by simp) hwLarge] at hw
        cases hw
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hOr : (gateAt C k).op = GateOp.or
        · have hne : h ≠ k := by
            intro he
            rw [← he, hAnd] at hOr
            cases hOr
          obtain ⟨v, hvMem, hvLt, hv⟩ := (Base.val_or (n := n) (by simp) hk hOr).mp hw
          have hv' : Base.val (offPatch C h) (List.ofFn x) v = false := by
            cases hv' : Base.val (offPatch C h) (List.ofFn x) v
            · rfl
            · have hk' : k < (offPatch C h).gates.length := by simpa only [offPatch_length] using hk
              have hOr' : (gateAt (offPatch C h) k).op = GateOp.or := by
                simpa only [gateAt_offPatch_ne C h k hne] using hOr
              have hMem' : v ∈ (gateAt (offPatch C h) k).inputs := by
                simpa only [gateAt_offPatch_ne C h k hne] using hvMem
              have ht := (Base.val_or (n := n) (by simp) hk' hOr').mpr ⟨v, hMem', hvLt, hv'⟩
              rw [hw'] at ht
              cases ht
          obtain ⟨j, hj, hjAnd, hReach, hjv, hjv'⟩ := ih v hvLt hv hv'
          refine ⟨j, hj, hjAnd, ?_, hjv, hjv'⟩
          exact (Base.orReaches_iff n C k j).mpr ⟨hk, Or.inr ⟨hOr, v, hvMem, hvLt, hReach⟩⟩
        · have hAndK : (gateAt C k).op = GateOp.and := (hAO.1 _ (Base.gateAt_mem hk)).resolve_right hOr
          exact ⟨k, hk, hAndK, (Base.orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩, hw, hw'⟩


lemma critical_edge_useful {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (hT : TopForm G C) {g h : ℕ} (hJ : junk G C = {g, h}) (hne : g ≠ h)
    (hIndependent : ¬ InCone n C h g)
    (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) h → ¬ OrReaches n C (opnd C a (1 - b)) g)
    (u v : Fin n) (hAdj : G.Adj u v)
    (hLost : circuitFun n (offPatch C h) (pairInput u v) = false) :
    gateVal n C h (pairInput u v) = true ∧ (u ∈ wmax G C h ∨ v ∈ wmax G C h) := by
  have hhJ : h ∈ junk G C := by rw [hJ]; simp
  obtain ⟨hhLen, hhAnd, hx, hhx, hFx⟩ := Base.junkData hhJ
  have hout (x : Fin n → Bool) : Base.val C (List.ofFn x) C.output = graphFun G ∅ x :=
    congrFun hF x
  obtain ⟨a, haLen, haNotOr, haPath, haVal⟩ :=
    Base.edge_trace G (graphFun G ∅) (fun x y hxy => (Base.graphFun_pair G x y).mp hxy)
      hout u v ((Base.graphFun_pair G u v).mpr hAdj)
  have haAnd : (gateAt C a).op = GateOp.and :=
    (hAO.1 _ (Base.gateAt_mem haLen)).resolve_right haNotOr
  have haBelow : BelowF G C a := fun x hv =>
    Base.below_of_reach (graphFun G ∅) hout a haPath x hv
  have haTop : a ∈ tops G C := by
    simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro haLen (And.intro haAnd haBelow)
  have hha : h ≠ a := by
    intro he
    subst a
    have ht := haBelow hx hhx
    rw [hFx] at ht
    cases ht
  have haOff : gateVal n (offPatch C h) a (pairInput u v) = false := by
    cases hc : gateVal n (offPatch C h) a (pairInput u v)
    · rfl
    · have ho := Base.orStep_up (n := n) (by simp) (orPath_offPatch hhAnd haPath) hc
      change circuitFun n (offPatch C h) (pairInput u v) = true at ho
      rw [hLost] at ho
      cases ho
  have hEval : gateVal n (offPatch C h) a (pairInput u v) =
      (Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 0) &&
       Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 1)) := by
    have he := Patch.patch_wval_gate_eval (j := h) (g := ⟨GateOp.or, []⟩) hAO (pairInput u v) haLen hha
    change gateVal n (offPatch C h) a (pairInput u v) = (gateAt C a).op.eval
      [Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 0),
       Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 1)] at he
    simpa only [haAnd, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true] using he
  obtain ⟨b, hbOff⟩ : ∃ b : Fin 2,
      Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a b) = false := by
    by_cases h0 : Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 0) = false
    · exact ⟨0, h0⟩
    · have h0t := Bool.eq_true_of_not_eq_false h0
      refine ⟨1, ?_⟩
      rw [haOff, h0t, Bool.true_and] at hEval
      exact hEval.symm
  have hbVal := ((Base.andValOperands hAO haLen haAnd (pairInput u v)).mp haVal) b
  obtain ⟨j, hjLen, hjAnd, hjReach, hjVal, hjOff⟩ :=
    offPatch_difference_trace hAO hhAnd (pairInput u v) (opnd C a b) hbVal hbOff
  have hjJ := Base.operandOrAndJunk hAO hT haLen haAnd hjReach hjAnd
  have hjh : j = h := by
    rcases Base.memJunkPair hJ hjJ with hjg | hjh
    · subst j
      have he := Patch.patch_gateVal_eq_of_not_inCone (j := h) (g := ⟨GateOp.or, []⟩)
        hAO g (Ne.symm hne) hIndependent (pairInput u v)
      change gateVal n (offPatch C h) g (pairInput u v) = gateVal n C g (pairInput u v) at he
      rw [he, hjVal] at hjOff
      cases hjOff
    · exact hjh
  subst j
  refine ⟨hjVal, ?_⟩
  have hoVal := ((Base.andValOperands hAO haLen haAnd (pairInput u v)).mp haVal) (1 - b)
  rcases Base.operandSupport hAO hT haLen haAnd hoVal with ⟨t, ht, htu⟩ | ⟨k, hkJ, hkReach, _⟩
  · have htw := Base.oppositeSideWmax hAO haTop hjReach ht
    rcases htu with rfl | rfl
    · exact Or.inl htw
    · exact Or.inr htw
  · rcases Base.memJunkPair hJ hkJ with hkg | hkh
    · subst k
      exact False.elim (hNoCommon a haTop b hjReach hkReach)
    · subst k
      have ht : gateVal n C a hx = true := by
        apply (Base.andValOperands hAO haLen haAnd hx).mpr
        intro c
        rcases Base.eitherOperand b c with rfl | rfl
        · exact Base.reachVal hjReach hhx
        · exact Base.reachVal hkReach hhx
      have hf := haBelow hx ht
      rw [hFx] at hf
      cases hf

end Critical

end PEqualNP.Outside.L_meta_5012


namespace PEqualNP.Outside.L_meta_5012.OverlapCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo
open IndependentDescent CleanReplacement

lemma safe_adj_overlap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) {z a : Fin n} (hz : Safe G P Q z) (ha : a ∈ P ∩ Q) :
    G.Adj z a := by
  apply (graph_pair G z a).mp
  apply hz
  · exact (product_true P Q _).mpr
      ⟨⟨a, (Finset.mem_inter.mp ha).1, by simp [pairInput]⟩,
        a, (Finset.mem_inter.mp ha).2, by simp [pairInput]⟩
  · simp [pairInput]

lemma safe_unique_of_overlap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (h4 : NoFourCycle G) (hPQ : 2 ≤ (P ∩ Q).card)
    {z w : Fin n} (hz : Safe G P Q z) (hw : Safe G P Q w) : z = w := by
  by_contra hne
  have hsub : P ∩ Q ⊆ Finset.univ.filter fun a => G.Adj z a ∧ G.Adj w a := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      safe_adj_overlap G P Q hz ha, safe_adj_overlap G P Q hw ha⟩
  have hc := (Finset.card_le_card hsub).trans (h4 z w hne)
  omega

lemma no_independent_overlap_filter_inside {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hT : TopForm G C) {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
    (hjk : ¬ InCone n C j k) (hkj : ¬ InCone n C k j)
    (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k)
    (h4 : NoFourCycle G)
    (hOverlap : 2 ≤ ((side (n := n) C j 0) ∩ (side (n := n) C j 1)).card)
    {z : Fin n} (hzW : z ∈ wmax G C j)
    (hzIn : z ∈ (side (n := n) C j 0) ∪ (side (n := n) C j 1)) : False := by
  let P := side (n := n) C j 0
  let Q := side (n := n) C j 1
  have hjmem : j ∈ junk G C := by rw [hJ]; simp
  have hj : j < C.gates.length := (mem_junk.mp hjmem).1
  have hOpnd (b : Fin 2) : opnd C j b < n + j := Lift.opnd_lt hL.1 hj b
  have hRaw (b : Fin 2) (x : Fin n → Bool) :
      wval C x (opnd C j b) = decide (∃ p ∈ side (n := n) C j b, x p = true) :=
    RawOperands.independent_operand G C hL.1 hT j k hJ hjk hkj j (Or.inl rfl) b x
  have heval (x : Fin n → Bool) : gateVal n C j x = product P Q x :=
    RawOperands.independent_product G C hL.1 hT j k hJ hjk hkj j (Or.inl rfl) x
  have hzSafe : Safe G P Q z := (wmax_iff G C j P Q heval z).mp hzW
  have hUnique (w : Fin n) (hw : Safe G P Q w) : w = z :=
    safe_unique_of_overlap G P Q h4 hOverlap hw hzSafe
  have hCritical (u v : Fin n) (huv : G.Adj u v)
      (hLost : circuitFun n (patch C j off) (pairInput u v) = false) :
      product P Q (pairInput u v) = true ∧ pairInput u v z = true := by
    have hJ' : junk G C = {k,j} := by rw [hJ, Finset.pair_comm]
    obtain ⟨hjv, hFilter⟩ := Critical.critical_edge_useful hL.1 hL.2.1 hT hJ'
      (Ne.symm hne) hjk hNoCommon u v huv hLost
    refine ⟨(heval _).symm.trans hjv, ?_⟩
    rcases hFilter with hu | hv
    · have huEq := hUnique u ((wmax_iff G C j P Q heval u).mp hu)
      simp [pairInput, ← huEq]
    · have hvEq := hUnique v ((wmax_iff G C j P Q heval v).mp hv)
      simp [pairInput, ← hvEq]
  have hReplace (b : Fin 2)
      (hClean : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
        (x z && wval C x (opnd C j b)) = false)
      (hCover : ∀ u v : Fin n, G.Adj u v →
        circuitFun n (patch C j off) (pairInput u v) = false →
        (pairInput u v z && wval C (pairInput u v) (opnd C j b)) = true) : False := by
    apply no_clean_independent_replacement G C hL hOne hne hJ hjk
      ⟨GateOp.and, [z.val, opnd C j b]⟩ (Or.inl rfl) rfl
    · intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · have := z.isLt; omega
      · exact hOpnd b
    · intro x hf
      rw [FlagReduction.star_gate_bit C j (Nat.le_of_lt hj) z _ (hOpnd b) x]
      exact hClean x hf
    · intro u v huv hLost
      rw [FlagReduction.star_gate_bit C j (Nat.le_of_lt hj) z _ (hOpnd b) _]
      exact hCover u v huv hLost
  rcases Finset.mem_union.mp hzIn with hzP | hzQ
  · apply hReplace 1
    · intro x hf
      rw [hRaw 1 x]
      apply Bool.eq_false_iff.mpr
      intro ht
      simp only [Bool.and_eq_true] at ht
      obtain ⟨hxz, hxQ⟩ := ht
      have hQ : ∃ q ∈ Q, x q = true := of_decide_eq_true hxQ
      have hp : product P Q x = true :=
        (product_true P Q x).mpr ⟨⟨z, hzP, hxz⟩, hQ⟩
      have hg := hzSafe x hp hxz
      rw [hf] at hg
      cases hg
    · intro u v huv hLost
      obtain ⟨hp, hxz⟩ := hCritical u v huv hLost
      rw [hRaw 1 _, hxz, Bool.true_and]
      exact decide_eq_true ((product_true P Q _).mp hp).2
  · apply hReplace 0
    · intro x hf
      rw [hRaw 0 x]
      apply Bool.eq_false_iff.mpr
      intro ht
      simp only [Bool.and_eq_true] at ht
      obtain ⟨hxz, hxP⟩ := ht
      have hP : ∃ p ∈ P, x p = true := of_decide_eq_true hxP
      have hp : product P Q x = true :=
        (product_true P Q x).mpr ⟨hP, z, hzQ, hxz⟩
      have hg := hzSafe x hp hxz
      rw [hf] at hg
      cases hg
    · intro u v huv hLost
      obtain ⟨hp, hxz⟩ := hCritical u v huv hLost
      rw [hRaw 0 _, hxz, Bool.true_and]
      exact decide_eq_true ((product_true P Q _).mp hp).1

lemma independent_apart_wmax_nonempty {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hT : TopForm G C) {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
    (hjk : ¬ InCone n C j k)
    (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k) :
    (wmax G C j).Nonempty := by
  by_contra hn
  have hjmem : j ∈ junk G C := by rw [hJ]; simp
  obtain ⟨e, he⟩ := Cases.edge_nonempty_of_junk_nonempty G C hL ⟨j, hjmem⟩
  obtain ⟨u, v, huv⟩ : ∃ u v : Fin n, G.Adj u v := by
    revert he
    refine Sym2.inductionOn e ?_
    intro u v he
    exact ⟨u, v, by simpa using he⟩
  apply no_clean_independent_replacement G C hL hOne hne hJ hjk
    (edgeGate u v) (Or.inl rfl) rfl
  · intro w hw
    simp only [edgeGate, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> omega
  · intro x hf
    rw [edge_bit]
    apply Bool.eq_false_iff.mpr
    intro ht
    simp only [Bool.and_eq_true] at ht
    obtain ⟨hu, hv⟩ := ht
    have hg := (graph_true G x).mpr ⟨u, v, huv, hu, hv⟩
    rw [hf] at hg
    cases hg
  · intro a b hab hLost
    have hJ' : junk G C = {k,j} := by rw [hJ, Finset.pair_comm]
    obtain ⟨_, ha | hb⟩ := Critical.critical_edge_useful hL.1 hL.2.1 hT hJ'
      (Ne.symm hne) hjk hNoCommon a b hab hLost
    · exact (hn ⟨a, ha⟩).elim
    · exact (hn ⟨b, hb⟩).elim

lemma independent_overlap_unique_outside {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hT : TopForm G C) {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
    (hjk : ¬ InCone n C j k) (hkj : ¬ InCone n C k j)
    (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k)
    (h4 : NoFourCycle G)
    (hOverlap : 2 ≤ ((side (n := n) C j 0) ∩ (side (n := n) C j 1)).card) :
    ∃ z : Fin n, wmax G C j = {z} ∧
      z ∉ (side (n := n) C j 0) ∪ (side (n := n) C j 1) := by
  obtain ⟨z, hz⟩ := independent_apart_wmax_nonempty G C hL hOne hT hne hJ hjk hNoCommon
  have heval (x : Fin n → Bool) : gateVal n C j x =
      product (side (n := n) C j 0) (side (n := n) C j 1) x :=
    RawOperands.independent_product G C hL.1 hT j k hJ hjk hkj j (Or.inl rfl) x
  refine ⟨z, ?_, ?_⟩
  · apply Finset.ext
    intro w
    constructor
    · intro hw
      apply Finset.mem_singleton.mpr
      exact safe_unique_of_overlap G _ _ h4 hOverlap
        ((wmax_iff G C j _ _ heval w).mp hw) ((wmax_iff G C j _ _ heval z).mp hz)
    · intro hw
      have he := Finset.mem_singleton.mp hw
      exact he ▸ hz
  · intro hzIn
    exact no_independent_overlap_filter_inside G C hL hOne hT hne hJ hjk hkj
      hNoCommon h4 hOverlap hz hzIn

end PEqualNP.Outside.L_meta_5012.OverlapCase


namespace PEqualNP.Outside.L_meta_5012.OverlapCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo
open IndependentDescent CleanReplacement

lemma product_pair_overlap_of_outside {n : ℕ} (P Q : Finset (Fin n))
    {z v : Fin n} (hzOut : z ∉ P ∪ Q)
    (hp : product P Q (pairInput z v) = true) : v ∈ P ∩ Q := by
  obtain ⟨⟨p, hp, hxp⟩, q, hq, hxq⟩ := (product_true P Q _).mp hp
  simp only [pairInput, decide_eq_true_eq] at hxp hxq
  have hpv : p = v := hxp.resolve_left
    (fun he => hzOut (Finset.mem_union.mpr (Or.inl (he ▸ hp))))
  have hqv : q = v := hxq.resolve_left
    (fun he => hzOut (Finset.mem_union.mpr (Or.inr (he ▸ hq))))
  exact Finset.mem_inter.mpr ⟨hpv ▸ hp, hqv ▸ hq⟩

lemma no_independent_overlap_existing_intersection_wire {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hT : TopForm G C) {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
    (hjk : ¬ InCone n C j k) (hkj : ¬ InCone n C k j)
    (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k)
    (h4 : NoFourCycle G)
    (hOverlap : 2 ≤ ((side (n := n) C j 0) ∩ (side (n := n) C j 1)).card)
    (t : ℕ) (ht : t < n + j)
    (hWire : ∀ x : Fin n → Bool, wval C x t =
      decide (∃ a ∈ (side (n := n) C j 0) ∩ (side (n := n) C j 1), x a = true)) :
    False := by
  obtain ⟨z, hW, hzOut⟩ := independent_overlap_unique_outside G C hL hOne hT
    hne hJ hjk hkj hNoCommon h4 hOverlap
  let P := side (n := n) C j 0
  let Q := side (n := n) C j 1
  have hzW : z ∈ wmax G C j := by rw [hW]; simp
  have heval (x : Fin n → Bool) : gateVal n C j x = product P Q x :=
    RawOperands.independent_product G C hL.1 hT j k hJ hjk hkj j (Or.inl rfl) x
  have hzSafe : Safe G P Q z := (wmax_iff G C j P Q heval z).mp hzW
  have hjmem : j ∈ junk G C := by rw [hJ]; simp
  have hj : j < C.gates.length := (mem_junk.mp hjmem).1
  apply no_clean_independent_replacement G C hL hOne hne hJ hjk
    ⟨GateOp.and, [z.val, t]⟩ (Or.inl rfl) rfl
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · have := z.isLt; omega
    · exact ht
  · intro x hf
    rw [FlagReduction.star_gate_bit C j (Nat.le_of_lt hj) z t ht x, hWire x]
    apply Bool.eq_false_iff.mpr
    intro hh
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
    obtain ⟨hxz, a, ha, hxa⟩ := hh
    have hp : product P Q x = true := (product_true P Q x).mpr
      ⟨⟨a, (Finset.mem_inter.mp ha).1, hxa⟩, a, (Finset.mem_inter.mp ha).2, hxa⟩
    have hg := hzSafe x hp hxz
    rw [hf] at hg
    cases hg
  · intro u v huv hLost
    have hJ' : junk G C = {k,j} := by rw [hJ, Finset.pair_comm]
    obtain ⟨hjv, hFilter⟩ := Critical.critical_edge_useful hL.1 hL.2.1 hT hJ'
      (Ne.symm hne) hjk hNoCommon u v huv hLost
    have hp : product P Q (pairInput u v) = true := (heval _).symm.trans hjv
    rw [FlagReduction.star_gate_bit C j (Nat.le_of_lt hj) z t ht _, hWire]
    rcases hFilter with hu | hv
    · have hueq : u = z := by simpa [hW] using hu
      subst u
      have hvI := product_pair_overlap_of_outside P Q hzOut hp
      simp only [pairInput, true_or, decide_true, Bool.true_and]
      exact decide_eq_true ⟨v, hvI, by simp⟩
    · have hveq : v = z := by simpa [hW] using hv
      subst v
      have hSwap : pairInput u z = pairInput z u := by
        funext a
        simp [pairInput, or_comm]
      rw [hSwap] at hp
      have huI := product_pair_overlap_of_outside P Q hzOut hp
      simp only [pairInput, or_true, decide_true, Bool.true_and]
      exact decide_eq_true ⟨u, huI, by simp⟩

end PEqualNP.Outside.L_meta_5012.OverlapCase


namespace PEqualNP.Outside.L_meta_5012.OverlapCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo
open IndependentDescent CleanReplacement

lemma no_independent_unique_filter_neighbor_factor {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hT : TopForm G C) {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
    (hjk : ¬ InCone n C j k) (hkj : ¬ InCone n C k j)
    (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k)
    {z : Fin n} (hW : wmax G C j = {z}) (b : Fin 2)
    (hNeighbors : ∀ v ∈ side (n := n) C j b, G.Adj z v) : False := by
  have hjmem : j ∈ junk G C := by rw [hJ]; simp
  have hj : j < C.gates.length := (mem_junk.mp hjmem).1
  have hjAnd : (gateAt C j).op = GateOp.and := (RawOperands.junk_data G C j hjmem).2
  have hOpnd : opnd C j b < n + j := Lift.opnd_lt hL.1 hj b
  have hRaw (x : Fin n → Bool) : wval C x (opnd C j b) =
      decide (∃ v ∈ side (n := n) C j b, x v = true) :=
    RawOperands.independent_operand G C hL.1 hT j k hJ hjk hkj j (Or.inl rfl) b x
  apply no_clean_independent_replacement G C hL hOne hne hJ hjk
    ⟨GateOp.and, [z.val, opnd C j b]⟩ (Or.inl rfl) rfl
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · have := z.isLt; omega
    · exact hOpnd
  · intro x hf
    rw [FlagReduction.star_gate_bit C j (Nat.le_of_lt hj) z _ hOpnd x, hRaw x]
    apply Bool.eq_false_iff.mpr
    intro hh
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
    obtain ⟨hxz, v, hv, hxv⟩ := hh
    have hg := (graph_true G x).mpr ⟨z, v, hNeighbors v hv, hxz, hxv⟩
    rw [hf] at hg
    cases hg
  · intro u v huv hLost
    have hJ' : junk G C = {k,j} := by rw [hJ, Finset.pair_comm]
    obtain ⟨hjv, hFilter⟩ := Critical.critical_edge_useful hL.1 hL.2.1 hT hJ'
      (Ne.symm hne) hjk hNoCommon u v huv hLost
    have hzv : pairInput u v z = true := by
      rcases hFilter with hu | hv
      · have hueq : u = z := by simpa [hW] using hu
        simp [pairInput, ← hueq]
      · have hveq : v = z := by simpa [hW] using hv
        simp [pairInput, ← hveq]
    have hOperand : wval C (pairInput u v) (opnd C j b) = true :=
      ((Critical.Base.andValOperands hL.1 hj hjAnd _).mp hjv) b
    rw [FlagReduction.star_gate_bit C j (Nat.le_of_lt hj) z _ hOpnd _, hzv,
      hOperand, Bool.true_and]

lemma independent_overlap_factors_have_nonneighbor {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hT : TopForm G C) {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
    (hjk : ¬ InCone n C j k) (hkj : ¬ InCone n C k j)
    (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k)
    (h4 : NoFourCycle G)
    (hOverlap : 2 ≤ ((side (n := n) C j 0) ∩ (side (n := n) C j 1)).card) :
    ∃ z : Fin n, wmax G C j = {z} ∧
      z ∉ (side (n := n) C j 0) ∪ (side (n := n) C j 1) ∧
      ∀ b : Fin 2, ∃ v ∈ side (n := n) C j b, ¬ G.Adj z v := by
  obtain ⟨z, hW, hzOut⟩ := independent_overlap_unique_outside G C hL hOne hT
    hne hJ hjk hkj hNoCommon h4 hOverlap
  refine ⟨z, hW, hzOut, ?_⟩
  intro b
  by_contra hn
  have hNeighbors : ∀ v ∈ side (n := n) C j b, G.Adj z v := by
    simpa only [not_exists, not_and, not_not] using hn
  exact no_independent_unique_filter_neighbor_factor G C hL hOne hT hne hJ
    hjk hkj hNoCommon hW b hNeighbors

end PEqualNP.Outside.L_meta_5012.OverlapCase


namespace PEqualNP.Outside.L_meta_5012.SharedFilter

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_5012.Overlap

lemma safe_adj_of_same_color {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (P Q : Finset (Fin n)) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    {p q z : Fin n} (hp : p ∈ P) (hq : q ∈ Q) (hpq : ¬ G.Adj p q)
    (hz : CleanFilter G P Q z) (hcolor : s z = s p) : G.Adj z q := by
  classical
  let x : Fin n → Bool := fun i => decide (i = z ∨ i = p ∨ i = q)
  have hxp : x p = true := by simp [x]
  have hxq : x q = true := by simp [x]
  have hxz : x z = true := by simp [x]
  have hprod : product P Q x = true := by
    simp [product, rawOr_true hp hxp, rawOr_true hq hxq]
  have hF := hz x (by simp [hprod, hxz])
  obtain ⟨u, v, huv, hu, hv⟩ := (graphFun_true G x).mp hF
  have hu' : u = z ∨ u = p ∨ u = q := by simpa [x] using hu
  have hv' : v = z ∨ v = p ∨ v = q := by simpa [x] using hv
  rcases hu' with rfl | rfl | rfl <;> rcases hv' with rfl | rfl | rfl
  · exact False.elim (huv.ne rfl)
  · exact False.elim (hbip _ _ huv hcolor)
  · exact huv
  · exact False.elim (hbip _ _ huv hcolor.symm)
  · exact False.elim (huv.ne rfl)
  · exact False.elim (hpq huv)
  · exact huv.symm
  · exact False.elim (hpq huv.symm)
  · exact False.elim (huv.ne rfl)

lemma common_neighbor_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (I : Finset (Fin n)) (hI : 2 ≤ I.card)
    {q w : Fin n} (hq : ∀ i ∈ I, G.Adj i q) (hw : ∀ i ∈ I, G.Adj i w) :
    q = w := by
  by_contra hne
  have hsub : I ⊆ Finset.univ.filter (fun i => G.Adj q i ∧ G.Adj w i) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(hq i hi).symm, (hw i hi).symm⟩
  have hle := (Finset.card_le_card hsub).trans (h4 q w hne)
  omega

lemma residual_endpoint_eq {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (P Q I : Finset (Fin n)) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (hI : 2 ≤ I.card) {p q w : Fin n} (hp : p ∈ P) (hq : q ∈ Q)
    (hpq : ¬ G.Adj p q) (hSafe : ∀ i ∈ I, CleanFilter G P Q i)
    (hcolor : ∀ i ∈ I, s i = s p) (hw : ∀ i ∈ I, G.Adj i w) : q = w := by
  apply common_neighbor_eq G h4 I hI
  · intro i hi
    exact safe_adj_of_same_color G P Q s hbip hp hq hpq (hSafe i hi) (hcolor i hi)
  · exact hw

lemma cleanFilter_comm {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (z : Fin n) :
    CleanFilter G P Q z ↔ CleanFilter G Q P z := by
  simp only [CleanFilter, product, Bool.and_comm]

lemma overlap_residual_endpoint {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A B P Q : Finset (Fin n)) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (hI : 2 ≤ (A ∩ B).card) {p q w : Fin n} (hp : p ∈ P) (hq : q ∈ Q)
    (hpq : ¬ G.Adj p q) (hcolor : s p ≠ s q)
    (hw : CleanFilter G A B w)
    (hSafe : ∀ i ∈ A ∩ B, CleanFilter G P Q i) : p = w ∨ q = w := by
  have hIW : ∀ i ∈ A ∩ B, G.Adj i w := fun i hi =>
    (cleanFilter_adj_overlap G A B hw hi).symm
  by_cases hpw : s p = s w
  · left
    apply residual_endpoint_eq G Q P (A ∩ B) s hbip h4 hI hq hp
      (fun h => hpq h.symm)
    · intro i hi
      exact (cleanFilter_comm G P Q i).mp (hSafe i hi)
    · intro i hi
      have hneq := hbip i w (hIW i hi)
      cases hsi : s i <;> cases hsp : s p <;> cases hsq : s q <;>
        cases hsw : s w <;> simp_all
    · exact hIW
  · right
    apply residual_endpoint_eq G P Q (A ∩ B) s hbip h4 hI hp hq hpq hSafe
    · intro i hi
      have hneq := hbip i w (hIW i hi)
      cases hsi : s i <;> cases hsp : s p <;> cases hsw : s w <;> simp_all
    · exact hIW

lemma shared_filters_force_clean_factor {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A B P Q : Finset (Fin n)) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (hI : 2 ≤ (A ∩ B).card) {p q w : Fin n} (hp : p ∈ P) (hq : q ∈ Q)
    (hpq : ¬ G.Adj p q) (hcolor : s p ≠ s q)
    (hw : CleanFilter G A B w)
    (hSafe : ∀ i ∈ A ∪ B, CleanFilter G P Q i) :
    (∀ a ∈ A, G.Adj w a) ∨ (∀ b ∈ B, G.Adj w b) := by
  have hSafeI : ∀ i ∈ A ∩ B, CleanFilter G P Q i := by
    intro i hi
    exact hSafe i (Finset.mem_union_left _ (Finset.mem_inter.mp hi).1)
  have hend := overlap_residual_endpoint G A B P Q s hbip h4 hI hp hq hpq hcolor hw hSafeI
  have hOpp (z : Fin n) (hz : z ∈ A ∪ B) (hzw : s z ≠ s w) : G.Adj w z := by
    rcases hend with rfl | rfl
    · have hsq : s z = s q := by
        cases hsz : s z <;> cases hsp : s p <;> cases hsqq : s q <;> simp_all
      exact (safe_adj_of_same_color G Q P s hbip hq hp
        (fun h => hpq h.symm) ((cleanFilter_comm G P Q z).mp (hSafe z hz)) hsq).symm
    · have hsp : s z = s p := by
        cases hsz : s z <;> cases hspp : s p <;> cases hsqq : s q <;> simp_all
      exact (safe_adj_of_same_color G P Q s hbip hp hq hpq (hSafe z hz) hsp).symm
  rcases cleanFilter_factor_opposite G A B s hbip hw with hA | hB
  · exact Or.inl (fun a ha => hOpp a (Finset.mem_union_left _ ha) (hA a ha))
  · exact Or.inr (fun b hb => hOpp b (Finset.mem_union_right _ hb) (hB b hb))

lemma exists_mem_ne_of_two_le {n : ℕ} (P : Finset (Fin n)) (hP : 2 ≤ P.card)
    (a : Fin n) : ∃ p ∈ P, p ≠ a := by
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
  by_cases hua : u = a
  · exact ⟨v, hv, fun hva => huv (hua.trans hva.symm)⟩
  · exact ⟨u, hu, hua⟩

lemma crossstar_noncenter_nonedge {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h4 : NoFourCycle G) {a b p q : Fin n}
    (hpa : p ≠ a) (hqb : q ≠ b) (hab : G.Adj a b)
    (hpb : G.Adj p b) (haq : G.Adj a q) : ¬ G.Adj p q := by
  intro hpq
  have hI : 2 ≤ ({a,p} : Finset (Fin n)).card := by simp [Ne.symm hpa]
  have heq : b = q := common_neighbor_eq G h4 {a,p} hI
    (by intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · exact hab
        · exact hpb)
    (by intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · exact haq
        · exact hpq)
  exact hqb heq.symm

lemma crossstar_opposite_residual {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (P Q : Finset (Fin n)) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (hP : 2 ≤ P.card) (hQ : 2 ≤ Q.card) {a b : Fin n}
    (ha : a ∈ P) (hb : b ∈ Q)
    (hPb : ∀ p ∈ P, G.Adj p b) (haQ : ∀ q ∈ Q, G.Adj a q) :
    ∃ p ∈ P, ∃ q ∈ Q, ¬ G.Adj p q ∧ s p ≠ s q := by
  obtain ⟨p, hp, hpa⟩ := exists_mem_ne_of_two_le P hP a
  obtain ⟨q, hq, hqb⟩ := exists_mem_ne_of_two_le Q hQ b
  refine ⟨p, hp, q, hq, crossstar_noncenter_nonedge G h4 hpa hqb (hPb a ha)
    (hPb p hp) (haQ q hq), ?_⟩
  have hpb := hbip p b (hPb p hp)
  have hab := hbip a b (haQ b hb)
  have haq := hbip a q (haQ q hq)
  cases hsp : s p <;> cases hsb : s b <;> cases hsa : s a <;>
    cases hsq : s q <;> simp_all

lemma crossstar_shared_filters_force_clean_factor {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A B P Q : Finset (Fin n)) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (hI : 2 ≤ (A ∩ B).card) (hP : 2 ≤ P.card) (hQ : 2 ≤ Q.card) {a b w : Fin n}
    (ha : a ∈ P) (hb : b ∈ Q)
    (hPb : ∀ p ∈ P, G.Adj p b) (haQ : ∀ q ∈ Q, G.Adj a q)
    (hw : CleanFilter G A B w)
    (hSafe : ∀ i ∈ A ∪ B, CleanFilter G P Q i) :
    (∀ u ∈ A, G.Adj w u) ∨ (∀ v ∈ B, G.Adj w v) := by
  obtain ⟨p, hp, q, hq, hpq, hcolor⟩ :=
    crossstar_opposite_residual G P Q s hbip h4 hP hQ ha hb hPb haQ
  exact shared_filters_force_clean_factor G A B P Q s hbip h4 hI hp hq hpq hcolor hw hSafe

lemma crossstar_noncenter_singleton {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (P Q I : Finset (Fin n)) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (hP : 2 ≤ P.card) (hQ : 2 ≤ Q.card) (hI : 2 ≤ I.card) {a b w : Fin n}
    (ha : a ∈ P)
    (hPb : ∀ p ∈ P, G.Adj p b) (haQ : ∀ q ∈ Q, G.Adj a q)
    (hSafe : ∀ i ∈ I, CleanFilter G P Q i)
    (hcolor : ∀ i ∈ I, s i = s a) (hw : ∀ i ∈ I, G.Adj i w) :
    Q.erase b = {w} := by
  obtain ⟨p, hp, hpa⟩ := exists_mem_ne_of_two_le P hP a
  have hpaColor : s p = s a := by
    have hpb := hbip p b (hPb p hp)
    have hab := hbip a b (hPb a ha)
    cases hsp : s p <;> cases hsb : s b <;> cases hsa : s a <;> simp_all
  have hAll (q : Fin n) (hq : q ∈ Q.erase b) : q = w := by
    have hqb := (Finset.mem_erase.mp hq).1
    have hqQ := (Finset.mem_erase.mp hq).2
    apply residual_endpoint_eq G P Q I s hbip h4 hI hp hqQ
      (crossstar_noncenter_nonedge G h4 hpa hqb (hPb a ha) (hPb p hp) (haQ q hqQ)) hSafe
    · intro i hi
      exact (hcolor i hi).trans hpaColor.symm
    · exact hw
  obtain ⟨q, hq, hqb⟩ := exists_mem_ne_of_two_le Q hQ b
  have hqE : q ∈ Q.erase b := Finset.mem_erase.mpr ⟨hqb, hq⟩
  have hwE : w ∈ Q.erase b := hAll q hqE ▸ hqE
  ext u
  simp only [Finset.mem_singleton]
  constructor
  · exact hAll u
  · intro heq
    simpa [heq] using hwE

lemma cleanFilter_pair_adj {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (P Q : Finset (Fin n)) {p q z : Fin n}
    (hp : p ∈ P) (hq : q ∈ Q) (hz : CleanFilter G P Q z) :
    G.Adj p q ∨ G.Adj z p ∨ G.Adj z q := by
  classical
  let x : Fin n → Bool := fun i => decide (i = z ∨ i = p ∨ i = q)
  have hxp : x p = true := by simp [x]
  have hxq : x q = true := by simp [x]
  have hxz : x z = true := by simp [x]
  have hprod : product P Q x = true := by
    simp [product, rawOr_true hp hxp, rawOr_true hq hxq]
  obtain ⟨u, v, huv, hu, hv⟩ := (graphFun_true G x).mp (hz x (by simp [hprod, hxz]))
  have hu' : u = z ∨ u = p ∨ u = q := by simpa [x] using hu
  have hv' : v = z ∨ v = p ∨ v = q := by simpa [x] using hv
  rcases hu' with rfl | rfl | rfl <;> rcases hv' with rfl | rfl | rfl
  · exact False.elim (huv.ne rfl)
  · exact Or.inr (Or.inl huv)
  · exact Or.inr (Or.inr huv)
  · exact Or.inr (Or.inl huv.symm)
  · exact False.elim (huv.ne rfl)
  · exact Or.inl huv
  · exact Or.inr (Or.inr huv.symm)
  · exact Or.inl huv.symm
  · exact False.elim (huv.ne rfl)

lemma monochromatic_factors_clean_factor {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A B : Finset (Fin n)) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) {w : Fin n}
    (hcolor : ∀ a ∈ A, ∀ b ∈ B, s a = s b) (hw : CleanFilter G A B w) :
    (∀ a ∈ A, G.Adj w a) ∨ (∀ b ∈ B, G.Adj w b) := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨⟨a, ha, hwa⟩, b, hb, hwb⟩ := hn
  rcases cleanFilter_pair_adj G A B ha hb hw with hab | hwa' | hwb'
  · exact hbip a b hab (hcolor a ha b hb)
  · exact hwa hwa'
  · exact hwb hwb'

lemma shared_filters_nonedge_clean_factor {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A B P Q : Finset (Fin n)) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (hI : 2 ≤ (A ∩ B).card) {p q w : Fin n} (hp : p ∈ P) (hq : q ∈ Q)
    (hpq : ¬ G.Adj p q) (hw : CleanFilter G A B w)
    (hSafe : ∀ i ∈ A ∪ B, CleanFilter G P Q i) :
    (∀ a ∈ A, G.Adj w a) ∨ (∀ b ∈ B, G.Adj w b) := by
  by_cases hpqColor : s p = s q
  · have hCol (z : Fin n) (hz : z ∈ A ∪ B) : s z ≠ s p := by
      rcases cleanFilter_factor_opposite G P Q s hbip (hSafe z hz) with hP | hQ
      · exact Ne.symm (hP p hp)
      · exact fun heq => hQ q hq (hpqColor.symm.trans heq.symm)
    apply monochromatic_factors_clean_factor G A B s hbip _ hw
    intro a ha b hb
    have hca := hCol a (Finset.mem_union_left _ ha)
    have hcb := hCol b (Finset.mem_union_right _ hb)
    cases hsa : s a <;> cases hsb : s b <;> cases hsp : s p <;> simp_all
  · exact shared_filters_force_clean_factor G A B P Q s hbip h4 hI hp hq hpq hpqColor hw hSafe

lemma dirty_product_nonedge {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (P Q : Finset (Fin n))
    (hDirty : ∃ x, product P Q x = true ∧ graphFun G ∅ x = false) :
    ∃ p ∈ P, ∃ q ∈ Q, ¬ G.Adj p q := by
  obtain ⟨x, hx, hF⟩ := hDirty
  have hPQ : (∃ p ∈ P, x p = true) ∧ (∃ q ∈ Q, x q = true) := by
    simpa [product, rawOr] using hx
  obtain ⟨⟨p, hp, hxp⟩, q, hq, hxq⟩ := hPQ
  refine ⟨p, hp, q, hq, ?_⟩
  intro hpq
  have hFt : graphFun G ∅ x = true := (graphFun_true G x).mpr ⟨p,q,hpq,hxp,hxq⟩
  simp [hF] at hFt

lemma shared_filters_dirty_clean_factor {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A B P Q : Finset (Fin n)) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (hI : 2 ≤ (A ∩ B).card) {w : Fin n}
    (hDirty : ∃ x, product P Q x = true ∧ graphFun G ∅ x = false)
    (hw : CleanFilter G A B w)
    (hSafe : ∀ i ∈ A ∪ B, CleanFilter G P Q i) :
    (∀ a ∈ A, G.Adj w a) ∨ (∀ b ∈ B, G.Adj w b) := by
  obtain ⟨p, hp, q, hq, hpq⟩ := dirty_product_nonedge G P Q hDirty
  exact shared_filters_nonedge_clean_factor G A B P Q s hbip h4 hI hp hq hpq hw hSafe

end PEqualNP.Outside.L_meta_5012.SharedFilter


namespace PEqualNP.Outside.L_meta_5012.OverlapCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo
open IndependentDescent CleanReplacement

lemma cleanFilter_of_wmax {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (P Q : Finset (Fin n))
    (heval : ∀ x : Fin n → Bool, gateVal n C j x = product P Q x)
    {z : Fin n} (hz : z ∈ wmax G C j) : Overlap.CleanFilter G P Q z := by
  intro x hx
  simp only [Bool.and_eq_true] at hx
  exact (wmax_iff G C j P Q heval z).mp hz x hx.1 hx.2

lemma no_independent_overlap_all_roots_filter_other {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hT : TopForm G C) {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
    (hjk : ¬ InCone n C j k) (hkj : ¬ InCone n C k j)
    (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k)
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G)
    (hOverlap : 2 ≤ ((side (n := n) C j 0) ∩ (side (n := n) C j 1)).card)
    (hAll : ∀ i ∈ (side (n := n) C j 0) ∪ (side (n := n) C j 1),
      i ∈ wmax G C k) : False := by
  obtain ⟨z, hW, _⟩ := independent_overlap_unique_outside G C hL hOne hT
    hne hJ hjk hkj hNoCommon h4 hOverlap
  have hzW : z ∈ wmax G C j := by rw [hW]; simp
  have hevalj (x : Fin n → Bool) : gateVal n C j x =
      product (side (n := n) C j 0) (side (n := n) C j 1) x :=
    RawOperands.independent_product G C hL.1 hT j k hJ hjk hkj j (Or.inl rfl) x
  have hevalk (x : Fin n → Bool) : gateVal n C k x =
      product (side (n := n) C k 0) (side (n := n) C k 1) x :=
    RawOperands.independent_product G C hL.1 hT j k hJ hjk hkj k (Or.inr rfl) x
  have hDirty : ∃ x, Overlap.product (side (n := n) C k 0) (side (n := n) C k 1) x = true ∧
      graphFun G ∅ x = false := by
    have hkmem : k ∈ junk G C := by rw [hJ]; simp
    obtain ⟨_, _, _, x, hx, hf⟩ := mem_junk.mp hkmem
    exact ⟨x, (hevalk x).symm.trans hx, hf⟩
  have hSafe : ∀ i ∈ (side (n := n) C j 0) ∪ (side (n := n) C j 1),
      Overlap.CleanFilter G (side (n := n) C k 0) (side (n := n) C k 1) i := by
    intro i hi
    exact cleanFilter_of_wmax G C k _ _ hevalk (hAll i hi)
  have hzSafe := cleanFilter_of_wmax G C j _ _ hevalj hzW
  rcases SharedFilter.shared_filters_dirty_clean_factor G
      (side (n := n) C j 0) (side (n := n) C j 1)
      (side (n := n) C k 0) (side (n := n) C k 1) s hbip h4 hOverlap
      hDirty hzSafe hSafe with hLeft | hRight
  · exact no_independent_unique_filter_neighbor_factor G C hL hOne hT hne hJ
      hjk hkj hNoCommon hW 0 hLeft
  · exact no_independent_unique_filter_neighbor_factor G C hL hOne hT hne hJ
      hjk hkj hNoCommon hW 1 hRight

lemma independent_overlap_root_not_filter_other {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hT : TopForm G C) {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
    (hjk : ¬ InCone n C j k) (hkj : ¬ InCone n C k j)
    (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k)
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G)
    (hOverlap : 2 ≤ ((side (n := n) C j 0) ∩ (side (n := n) C j 1)).card) :
    ∃ i ∈ (side (n := n) C j 0) ∪ (side (n := n) C j 1), i ∉ wmax G C k := by
  by_contra hn
  have hAll : ∀ i ∈ (side (n := n) C j 0) ∪ (side (n := n) C j 1), i ∈ wmax G C k := by
    simpa only [not_exists, not_and, not_not] using hn
  exact no_independent_overlap_all_roots_filter_other G C hL hOne hT hne hJ
    hjk hkj hNoCommon s hbip h4 hOverlap hAll

end PEqualNP.Outside.L_meta_5012.OverlapCase


namespace PEqualNP.Outside.L_meta_5012.OverlapCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo
open IndependentDescent CleanReplacement

lemma no_independent_overlap_cover_wire {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hT : TopForm G C) {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
    (hjk : ¬ InCone n C j k) (hkj : ¬ InCone n C k j)
    (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k)
    (z : Fin n) (hW : wmax G C j = {z})
    (hzOut : z ∉ side (n := n) C j 0 ∪ side (n := n) C j 1)
    (t : ℕ) (ht : t < n + j)
    (hClean : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
      (x z && wval C x t) = false)
    (hCover : ∀ v ∈ side (n := n) C j 0 ∩ side (n := n) C j 1,
      wval C (pairInput z v) t = true) : False := by
  let P := side (n := n) C j 0
  let Q := side (n := n) C j 1
  have heval (x : Fin n → Bool) : gateVal n C j x = product P Q x :=
    RawOperands.independent_product G C hL.1 hT j k hJ hjk hkj j (Or.inl rfl) x
  have hjmem : j ∈ junk G C := by rw [hJ]; simp
  have hj : j < C.gates.length := (mem_junk.mp hjmem).1
  apply no_clean_independent_replacement G C hL hOne hne hJ hjk
    ⟨GateOp.and, [z.val, t]⟩ (Or.inl rfl) rfl
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · have := z.isLt; omega
    · exact ht
  · intro x hf
    rw [FlagReduction.star_gate_bit C j (Nat.le_of_lt hj) z t ht x]
    exact hClean x hf
  · intro u v huv hLost
    have hJ' : junk G C = {k,j} := by rw [hJ, Finset.pair_comm]
    obtain ⟨hjv, hFilter⟩ := Critical.critical_edge_useful hL.1 hL.2.1 hT hJ'
      (Ne.symm hne) hjk hNoCommon u v huv hLost
    have hp : product P Q (pairInput u v) = true := (heval _).symm.trans hjv
    rw [FlagReduction.star_gate_bit C j (Nat.le_of_lt hj) z t ht _]
    rcases hFilter with hu | hv
    · have hueq : u = z := by simpa [hW] using hu
      subst u
      have hvI := product_pair_overlap_of_outside P Q hzOut hp
      rw [hCover v hvI]
      simp [pairInput]
    · have hveq : v = z := by simpa [hW] using hv
      subst v
      have hSwap : pairInput u z = pairInput z u := by
        funext a
        simp [pairInput, or_comm]
      rw [hSwap] at hp ⊢
      have huI := product_pair_overlap_of_outside P Q hzOut hp
      rw [hCover u huI]
      simp [pairInput]

lemma no_independent_overlap_neighbor_cover {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hT : TopForm G C) {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
    (hjk : ¬ InCone n C j k) (hkj : ¬ InCone n C k j)
    (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k)
    (z : Fin n) (hW : wmax G C j = {z})
    (hzOut : z ∉ side (n := n) C j 0 ∪ side (n := n) C j 1)
    (S : Finset (Fin n))
    (hI : side (n := n) C j 0 ∩ side (n := n) C j 1 ⊆ S)
    (hS : ∀ v ∈ S, G.Adj z v)
    (t : ℕ) (ht : t < n + j)
    (hWire : ∀ x : Fin n → Bool, wval C x t = decide (∃ v ∈ S, x v = true)) :
    False := by
  apply no_independent_overlap_cover_wire G C hL hOne hT hne hJ hjk hkj
    hNoCommon z hW hzOut t ht
  · intro x hf
    rw [hWire x]
    apply Bool.eq_false_iff.mpr
    intro hh
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
    obtain ⟨hxz, v, hv, hxv⟩ := hh
    have hg := (graph_true G x).mpr ⟨z, v, hS v hv, hxz, hxv⟩
    rw [hf] at hg
    cases hg
  · intro v hv
    rw [hWire]
    exact decide_eq_true ⟨v, hI hv, by simp [pairInput]⟩

end PEqualNP.Outside.L_meta_5012.OverlapCase


namespace PEqualNP.Outside.L_meta_5012.WireAbsorption

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Absorption

def patch (n : ℕ) (C : Circuit) (r g t : ℕ) (u v : ℕ) : Circuit :=
  ⟨(C.gates.set r ⟨GateOp.and, [u, v]⟩).set g ⟨GateOp.or, [t, n + r]⟩, C.output⟩

lemma patch_length {n : ℕ} (C : Circuit) (r g t : ℕ) (u v : ℕ) :
    (patch n C r g t u v).gates.length = C.gates.length := by simp [patch]

lemma patch_size {n : ℕ} (C : Circuit) (r g t : ℕ) (u v : ℕ) :
    (patch n C r g t u v).size = C.size := by simp [patch, Circuit.size]

lemma patch_r {n : ℕ} (C : Circuit) (r g t : ℕ) (u v : ℕ)
    (hr : r < C.gates.length) (hrg : r ≠ g) :
    gateAt (patch n C r g t u v) r = ⟨GateOp.and, [u, v]⟩ := by
  simp [gateAt, patch, List.getD_eq_getElem?_getD, hr, hrg.symm]

lemma patch_g {n : ℕ} (C : Circuit) (r g t : ℕ) (u v : ℕ)
    (hg : g < C.gates.length) :
    gateAt (patch n C r g t u v) g = ⟨GateOp.or, [t, n + r]⟩ := by
  simp [gateAt, patch, List.getD_eq_getElem?_getD, hg]

lemma patch_other {n : ℕ} (C : Circuit) (r g t : ℕ) (u v : ℕ)
    (j : ℕ) (hjr : j ≠ r) (hjg : j ≠ g) :
    gateAt (patch n C r g t u v) j = gateAt C j := by
  simp [gateAt, patch, List.getD_eq_getElem?_getD, hjr.symm, hjg.symm]

lemma or_wire_eval {n : ℕ} (C : Circuit) (j t : ℕ) (u : ℕ)
    (hj : j < C.gates.length) (hgate : gateAt C j = ⟨GateOp.or, [t, u]⟩)
    (ht : t < n + j) (hu : u < n + j) (x : Fin n → Bool) :
    val C (List.ofFn x) (n + j) = (val C (List.ofFn x) t || val C (List.ofFn x) u) := by
  rw [binary_eval C j t u GateOp.or hj hgate ht hu]
  simp [GateOp.eval]

lemma patched_r_eval {n : ℕ} (C : Circuit) (r g t : ℕ) (u v : ℕ)
    (hr : r < C.gates.length) (hrg : r ≠ g) (hu : u < n + r) (hv : v < n + r) (x : Fin n → Bool) :
    val (patch n C r g t u v) (List.ofFn x) (n + r) = (val (patch n C r g t u v) (List.ofFn x) u && val (patch n C r g t u v) (List.ofFn x) v) := by
  rw [binary_eval _ r u v GateOp.and (by simpa [patch_length] using hr)
    (patch_r C r g t u v hr hrg) hu hv]
  simp [GateOp.eval]

lemma original_g_eval {n : ℕ} (C : Circuit) (r s g t : ℕ) (u v : ℕ)
    (hg : g < C.gates.length) (hrg : r < g) (hsg : s < g) (htr : t < n + r) (hts : t < n + s)
    (hu : u < n + r) (hv : v < n + s)
    (hr : gateAt C r = ⟨GateOp.or, [t, u]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, v]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩) (x : Fin n → Bool) :
    val C (List.ofFn x) (n + g) =
      ((val C (List.ofFn x) t || val C (List.ofFn x) u) && (val C (List.ofFn x) t || val C (List.ofFn x) v)) := by
  rw [binary_eval C g (n + r) (n + s) GateOp.and hg hgate (by omega) (by omega),
    or_wire_eval C r t u (by omega) hr htr hu, or_wire_eval C s t v (by omega) hs hts hv]
  simp [GateOp.eval]

lemma patched_g_eval {n : ℕ} (C : Circuit) (r g t : ℕ) (u v : ℕ)
    (hg : g < C.gates.length) (hrg : r < g) (htr : t < n + r) (hu : u < n + r) (hv : v < n + r) (x : Fin n → Bool) :
    val (patch n C r g t u v) (List.ofFn x) (n + g) =
      (val (patch n C r g t u v) (List.ofFn x) t || (val (patch n C r g t u v) (List.ofFn x) u && val (patch n C r g t u v) (List.ofFn x) v)) := by
  rw [binary_eval _ g t (n + r) GateOp.or (by simpa [patch_length] using hg)
    (patch_g C r g t u v hg) (by omega) (by omega),
    patched_r_eval C r g t u v (by omega) (Nat.ne_of_lt hrg) hu hv]
  simp [GateOp.eval]

lemma patch_ao {n : ℕ} (C : Circuit) (r g t : ℕ) (u v : ℕ)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hrg : r < g) (htr : t < n + r) (hu : u < n + r) (hv : v < n + r) :
    IsAO2 n (patch n C r g t u v) := by
  have hidx : ∀ j < (patch n C r g t u v).gates.length,
      ((gateAt (patch n C r g t u v) j).op = GateOp.and ∨
        (gateAt (patch n C r g t u v) j).op = GateOp.or) ∧
      (gateAt (patch n C r g t u v) j).inputs.length = 2 ∧
      ∀ w ∈ (gateAt (patch n C r g t u v) j).inputs, w < n + j := by
    intro j hj
    have hj0 : j < C.gates.length := by simpa only [patch_length] using hj
    by_cases hjr : j = r
    · subst j
      rw [patch_r C r g t u v (by omega) (Nat.ne_of_lt hrg)]
      refine ⟨Or.inl rfl, rfl, ?_⟩
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> omega
    by_cases hjg : j = g
    · subst j
      rw [patch_g C r g t u v hg]
      refine ⟨Or.inr rfl, rfl, ?_⟩
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> omega
    rw [patch_other C r g t u v j hjr hjg]
    exact ⟨hAO.1 _ (gateAt_mem hj0), hAO.2.2 _ (gateAt_mem hj0), hAO.2.1 j hj0⟩
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    have hh := (hidx j hj).1
    rwa [gateAt_eq hj] at hh
  · intro j hj w hw
    exact (hidx j hj).2.2 w hw
  · intro q hq
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    have hh := (hidx j hj).2.1
    rwa [gateAt_eq hj] at hh

lemma patched_gate_values {n : ℕ} (C : Circuit) (r s g t : ℕ) (u v : ℕ)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hrg : r < g) (hsg : s < g)
    (hv : v < n + r)
    (hr : gateAt C r = ⟨GateOp.or, [t, u]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, v]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hread : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g)
    (x : Fin n → Bool) :
    ∀ j < C.gates.length, j ≠ r →
      val (patch n C r g t u v) (List.ofFn x) (n + j) = val C (List.ofFn x) (n + j) := by
  have htr : t < n + r := hAO.2.1 r (by omega) t (by rw [hr]; simp)
  have hts : t < n + s := hAO.2.1 s (by omega) t (by rw [hs]; simp)
  have hu : u < n + r := hAO.2.1 r (by omega) u (by rw [hr]; simp)
  have hvs : v < n + s := hAO.2.1 s (by omega) v (by rw [hs]; simp)
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hjr
    have earlier : ∀ w, w < n + j → w ≠ n + r →
        val (patch n C r g t u v) (List.ofFn x) w = val C (List.ofFn x) w := by
      intro w hw hwr
      by_cases hwn : w < n
      · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
      · have hwrepr : w = n + (w - n) := by omega
        rw [hwrepr]
        exact ih (w - n) (by omega) (by omega) (by omega)
    by_cases hjg : j = g
    · subst j
      rw [patched_g_eval C r g t u v hg hrg htr hu hv,
        original_g_eval C r s g t u v hg hrg hsg htr hts hu hvs hr hs hgate,
        earlier t (by omega) (Nat.ne_of_lt htr),
        earlier u (by omega) (Nat.ne_of_lt hu), earlier v (by omega) (Nat.ne_of_lt hv)]
      cases val C (List.ofFn x) t <;> cases val C (List.ofFn x) u <;> cases val C (List.ofFn x) v <;> rfl
    rw [val_gate (n := n) (by simp) (by simpa only [patch_length] using hj),
      val_gate (n := n) (by simp) hj, patch_other C r g t u v j hjr hjg]
    congr 1
    apply List.map_congr_left
    intro w hw
    have hwl : w < n + j := hAO.2.1 j hj w hw
    have hwr : w ≠ n + r := by
      intro hh
      exact hjg (hread j hj (hh ▸ hw))
    simp only [ite_eq_left hwl]
    exact earlier w hwl hwr

lemma patched_wire_values {n : ℕ} (C : Circuit) (r s g t : ℕ) (u v : ℕ)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hrg : r < g) (hsg : s < g)
    (hv : v < n + r)
    (hr : gateAt C r = ⟨GateOp.or, [t, u]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, v]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hread : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g)
    (x : Fin n → Bool) (w : ℕ) (hwr : w ≠ n + r) :
    val (patch n C r g t u v) (List.ofFn x) w = val C (List.ofFn x) w := by
  by_cases hwn : w < n
  · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
  by_cases hwC : w < n + C.gates.length
  · have hwrepr : w = n + (w - n) := by omega
    rw [hwrepr]
    exact patched_gate_values C r s g t u v hAO hg hrg hsg hv hr hs hgate hread x
      (w - n) (by omega) (by omega)
  · rw [val_ge (n := n) (by simp) (by rw [patch_length]; omega),
      val_ge (n := n) (by simp) (by omega)]


lemma dirty_parent_not_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r s g : ℕ) (hgJ : g ∈ junk G C) (hrg : r < g) (hsg : s < g)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hc : circuitFun n C = graphFun G ∅) : C.output ≠ n + r := by
  obtain ⟨hg, _, x, hx, hF⟩ := (mem_junk_iff G C g).mp hgJ
  intro hout
  rw [gateVal_eq_val, binary_eval C g (n + r) (n + s) GateOp.and hg hgate
    (by omega) (by omega)] at hx
  have hrx : val C (List.ofFn x) (n + r) = true := by
    have hboth : val C (List.ofFn x) (n + r) = true ∧
        val C (List.ofFn x) (n + s) = true := by simpa [GateOp.eval] using hx
    exact hboth.1
  have he := congrFun hc x
  change val C (List.ofFn x) C.output = _ at he
  rw [hout, hrx, hF] at he
  cases he

lemma patch_computes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r s g t u v : ℕ)
    (hAO : IsAO2 n C) (hgJ : g ∈ junk G C) (hrg : r < g) (hsg : s < g)
    (hv : v < n + r)
    (hr : gateAt C r = ⟨GateOp.or, [t, u]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, v]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hread : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g)
    (hc : circuitFun n C = graphFun G ∅) :
    circuitFun n (patch n C r g t u v) = graphFun G ∅ := by
  have hg : g < C.gates.length := (mem_junk_iff G C g).mp hgJ |>.1
  have ho := dirty_parent_not_output G C r s g hgJ hrg hsg hgate hc
  funext x
  change val (patch n C r g t u v) (List.ofFn x) C.output = _
  rw [patched_wire_values C r s g t u v hAO hg hrg hsg hv hr hs hgate hread x C.output ho]
  exact congrFun hc x

lemma r_not_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r t u : ℕ)
    (hr : gateAt C r = ⟨GateOp.or, [t, u]⟩) : r ∉ junk G C := by
  intro h
  have hop := (mem_junk_iff G C r).mp h |>.2.1
  rw [hr] at hop
  cases hop

lemma patch_r_not_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r s g t u v : ℕ)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hrg : r < g) (hsg : s < g)
    (hv : v < n + r)
    (hr : gateAt C r = ⟨GateOp.or, [t, u]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, v]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hread : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g)
    (hclean : ∀ x : Fin n → Bool, wireVal n C u x = true → wireVal n C v x = true →
      graphFun G ∅ x = true) : r ∉ junk G (patch n C r g t u v) := by
  have hu : u < n + r := hAO.2.1 r (by omega) u (by rw [hr]; simp)
  intro h
  obtain ⟨_, _, x, hx, hF⟩ := (mem_junk_iff G _ r).mp h
  rw [gateVal_eq_val, patched_r_eval C r g t u v (by omega) (Nat.ne_of_lt hrg) hu hv,
    patched_wire_values C r s g t u v hAO hg hrg hsg hv hr hs hgate hread x u (by omega),
    patched_wire_values C r s g t u v hAO hg hrg hsg hv hr hs hgate hread x v (by omega),
    Bool.and_eq_true] at hx
  have htrue := hclean x hx.1 hx.2
  rw [htrue] at hF
  cases hF

lemma patch_g_not_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r g t u v : ℕ) (hg : g < C.gates.length) :
    g ∉ junk G (patch n C r g t u v) := by
  intro h
  have hop := (mem_junk_iff G _ g).mp h |>.2.1
  rw [patch_g C r g t u v hg] at hop
  cases hop

lemma patch_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r s g t u v : ℕ)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hrg : r < g) (hsg : s < g)
    (hv : v < n + r)
    (hr : gateAt C r = ⟨GateOp.or, [t, u]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, v]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hread : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g)
    (hclean : ∀ x : Fin n → Bool, wireVal n C u x = true → wireVal n C v x = true →
      graphFun G ∅ x = true) : junk G (patch n C r g t u v) = (junk G C).erase g := by
  apply Finset.ext
  intro j
  by_cases hjr : j = r
  · subst j
    simp only [Finset.mem_erase,
      patch_r_not_junk G C r s g t u v hAO hg hrg hsg hv hr hs hgate hread hclean,
      r_not_junk G C r t u hr, and_false]
  by_cases hjg : j = g
  · subst j
    simp only [Finset.mem_erase, patch_g_not_junk G C r g t u v hg,
      ne_eq, not_true_eq_false, false_and]
  by_cases hj : j < C.gates.length
  · have hvals : ∀ x : Fin n → Bool,
        gateVal n (patch n C r g t u v) j x = gateVal n C j x := by
      intro x
      exact patched_gate_values C r s g t u v hAO hg hrg hsg hv hr hs hgate hread x j hj hjr
    simp only [Finset.mem_erase, mem_junk_iff, patch_length,
      patch_other C r g t u v j hjr hjg, hvals, ne_eq, hjg, not_false_eq_true, true_and]
  · simp only [Finset.mem_erase, mem_junk_iff, patch_length, hj, false_and, and_false]

lemma patch_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r s g t u v : ℕ)
    (hL : IsLeastAO G C) (hgJ : g ∈ junk G C) (hrg : r < g) (hsg : s < g)
    (hv : v < n + r)
    (hr : gateAt C r = ⟨GateOp.or, [t, u]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, v]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hread : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g) :
    IsLeastAO G (patch n C r g t u v) := by
  have hg : g < C.gates.length := (mem_junk_iff G C g).mp hgJ |>.1
  have htr : t < n + r := hL.1.2.1 r (by omega) t (by rw [hr]; simp)
  have hu : u < n + r := hL.1.2.1 r (by omega) u (by rw [hr]; simp)
  refine ⟨patch_ao C r g t u v hL.1 hg hrg htr hu hv,
    patch_computes G C r s g t u v hL.1 hgJ hrg hsg hv hr hs hgate hread hL.2.1, ?_⟩
  intro D hD hcD
  rw [patch_size]
  exact hL.2.2 D hD hcD

lemma absorption_contradiction
    (firstRung : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (color : Fin n → Bool),
      (∀ u v, G.Adj u v → color u ≠ color v) → NoFourCycle G → IsLeastAO G C →
      (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v) (h4 : NoFourCycle G)
    (hL : IsLeastAO G C) (hcard : (junk G C).card = 2)
    (r s g t u v : ℕ) (hgJ : g ∈ junk G C) (hrg : r < g) (hsg : s < g)
    (hv : v < n + r)
    (hr : gateAt C r = ⟨GateOp.or, [t, u]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, v]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hread : readers n C r = {g})
    (hclean : ∀ x : Fin n → Bool, wireVal n C u x = true → wireVal n C v x = true →
      graphFun G ∅ x = true) : False := by
  have hg : g < C.gates.length := (mem_junk_iff G C g).mp hgJ |>.1
  have hread' : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g := by
    intro j hj hw
    have hjmem : j ∈ readers n C r := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hw⟩
    simpa only [hread, Finset.mem_singleton] using hjmem
  have hPL := patch_least G C r s g t u v hL hgJ hrg hsg hv hr hs hgate hread'
  apply firstRung n G (patch n C r g t u v) color hbip h4 hPL
  rw [patch_junk G C r s g t u v hL.1 hg hrg hsg hv hr hs hgate hread' hclean,
    Finset.card_erase_of_mem hgJ, hcard]

end PEqualNP.Outside.L_meta_5012.WireAbsorption


namespace PEqualNP.Outside.L_meta_5012.SharedFilter

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_5012.Overlap

lemma factor_no_common_neighbor {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A B : Finset (Fin n)) (h4 : NoFourCycle G)
    (hI : 2 ≤ (A ∩ B).card) {w : Fin n} (hw : CleanFilter G A B w)
    (hBad : ∃ a ∈ A, ¬ G.Adj w a) :
    ¬ ∃ z : Fin n, ∀ a ∈ A, G.Adj z a := by
  rintro ⟨z, hz⟩
  have heq : z = w := common_neighbor_eq G h4 (A ∩ B) hI
    (fun i hi => (hz i (Finset.mem_inter.mp hi).1).symm)
    (fun i hi => (cleanFilter_adj_overlap G A B hw hi).symm)
  obtain ⟨a, ha, hwa⟩ := hBad
  exact hwa (heq ▸ hz a ha)

lemma no_center_factor_not_subset {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A P : Finset (Fin n))
    (hA : ¬ ∃ z : Fin n, ∀ a ∈ A, G.Adj z a)
    (hP : ∃ z : Fin n, ∀ p ∈ P, G.Adj z p) : ¬ A ⊆ P := by
  intro hsub
  apply hA
  obtain ⟨z, hz⟩ := hP
  exact ⟨z, fun a ha => hz a (hsub ha)⟩

end PEqualNP.Outside.L_meta_5012.SharedFilter


namespace PEqualNP.Outside.L_meta_5012.OrRewrite

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Absorption

def patch (C : Circuit) (g t h : ℕ) : Circuit :=
  ⟨C.gates.set g ⟨GateOp.or, [t, h]⟩, C.output⟩

lemma patch_length (C : Circuit) (g t h : ℕ) :
    (patch C g t h).gates.length = C.gates.length := by simp [patch]

lemma patch_size (C : Circuit) (g t h : ℕ) :
    (patch C g t h).size = C.size := by simp [patch, Circuit.size]

lemma patch_g (C : Circuit) (g t h : ℕ) (hg : g < C.gates.length) :
    gateAt (patch C g t h) g = ⟨GateOp.or, [t, h]⟩ := by
  simp [gateAt, patch, List.getD_eq_getElem?_getD, hg]

lemma patch_other (C : Circuit) (g t h j : ℕ) (hjg : j ≠ g) :
    gateAt (patch C g t h) j = gateAt C j := by
  simp [gateAt, patch, List.getD_eq_getElem?_getD, hjg.symm]

lemma patch_ao {n : ℕ} (C : Circuit) (g t h : ℕ)
    (hAO : IsAO2 n C) (ht : t < n + g) (hh : h < n + g) :
    IsAO2 n (patch C g t h) := by
  have hidx : ∀ j < (patch C g t h).gates.length,
      ((gateAt (patch C g t h) j).op = GateOp.and ∨
        (gateAt (patch C g t h) j).op = GateOp.or) ∧
      (gateAt (patch C g t h) j).inputs.length = 2 ∧
      ∀ w ∈ (gateAt (patch C g t h) j).inputs, w < n + j := by
    intro j hj
    have hj0 : j < C.gates.length := by simpa only [patch_length] using hj
    by_cases hjg : j = g
    · subst j
      rw [patch_g C g t h hj0]
      refine ⟨Or.inr rfl, rfl, ?_⟩
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> assumption
    rw [patch_other C g t h j hjg]
    exact ⟨hAO.1 _ (gateAt_mem hj0), hAO.2.2 _ (gateAt_mem hj0), hAO.2.1 j hj0⟩
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    have hx := (hidx j hj).1
    rwa [gateAt_eq hj] at hx
  · intro j hj w hw
    exact (hidx j hj).2.2 w hw
  · intro q hq
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    have hx := (hidx j hj).2.1
    rwa [gateAt_eq hj] at hx

lemma patched_gate_values {n : ℕ} (C : Circuit) (g t h : ℕ)
    (hAO : IsAO2 n C) (ht : t < n + g) (hh : h < n + g)
    (heval : ∀ x : Fin n → Bool,
      gateVal n C g x = (wireVal n C t x || wireVal n C h x))
    (x : Fin n → Bool) : ∀ j < C.gates.length,
      val (patch C g t h) (List.ofFn x) (n + j) = val C (List.ofFn x) (n + j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    have earlier : ∀ w, w < n + j →
        val (patch C g t h) (List.ofFn x) w = val C (List.ofFn x) w := by
      intro w hw
      by_cases hwn : w < n
      · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
      · have hwrepr : w = n + (w - n) := by omega
        rw [hwrepr]
        exact ih (w - n) (by omega) (by omega)
    by_cases hjg : j = g
    · subst j
      rw [binary_eval _ g t h GateOp.or (by simpa only [patch_length] using hj)
        (patch_g C g t h hj) ht hh, earlier t ht, earlier h hh]
      simpa [GateOp.eval, wireVal, gateVal, val] using (heval x).symm
    rw [val_gate (n := n) (by simp) (by simpa only [patch_length] using hj),
      val_gate (n := n) (by simp) hj, patch_other C g t h j hjg]
    congr 1
    apply List.map_congr_left
    intro w hw
    have hwl : w < n + j := hAO.2.1 j hj w hw
    simp only [ite_eq_left hwl]
    exact earlier w hwl

lemma patched_wire_values {n : ℕ} (C : Circuit) (g t h : ℕ)
    (hAO : IsAO2 n C) (ht : t < n + g) (hh : h < n + g)
    (heval : ∀ x : Fin n → Bool,
      gateVal n C g x = (wireVal n C t x || wireVal n C h x))
    (x : Fin n → Bool) (w : ℕ) :
    val (patch C g t h) (List.ofFn x) w = val C (List.ofFn x) w := by
  by_cases hwn : w < n
  · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
  by_cases hwC : w < n + C.gates.length
  · have hwrepr : w = n + (w - n) := by omega
    rw [hwrepr]
    exact patched_gate_values C g t h hAO ht hh heval x (w - n) (by omega)
  · rw [val_ge (n := n) (by simp) (by rw [patch_length]; omega),
      val_ge (n := n) (by simp) (by omega)]

lemma patch_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g t h : ℕ) (hL : IsLeastAO G C)
    (ht : t < n + g) (hh : h < n + g)
    (heval : ∀ x : Fin n → Bool,
      gateVal n C g x = (wireVal n C t x || wireVal n C h x)) :
    IsLeastAO G (patch C g t h) := by
  refine ⟨patch_ao C g t h hL.1 ht hh, ?_, ?_⟩
  · funext x
    change val (patch C g t h) (List.ofFn x) C.output = _
    rw [patched_wire_values C g t h hL.1 ht hh heval x C.output]
    exact congrFun hL.2.1 x
  · intro D hD hcD
    rw [patch_size]
    exact hL.2.2 D hD hcD

lemma patch_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g t h : ℕ) (hAO : IsAO2 n C)
    (ht : t < n + g) (hh : h < n + g)
    (heval : ∀ x : Fin n → Bool,
      gateVal n C g x = (wireVal n C t x || wireVal n C h x)) :
    junk G (patch C g t h) = (junk G C).erase g := by
  apply Finset.ext
  intro j
  by_cases hjg : j = g
  · subst j
    simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, iff_false]
    intro hJ
    obtain ⟨hg, hop, _⟩ := (mem_junk_iff G _ g).mp hJ
    have hg0 : g < C.gates.length := by simpa only [patch_length] using hg
    rw [patch_g C g t h hg0] at hop
    cases hop
  · have hvals : ∀ x : Fin n → Bool,
        gateVal n (patch C g t h) j x = gateVal n C j x := by
      intro x
      exact patched_wire_values C g t h hAO ht hh heval x (n + j)
    simp only [Finset.mem_erase, mem_junk_iff, patch_length,
      patch_other C g t h j hjg, hvals, ne_eq, hjg, not_false_eq_true, true_and]

lemma no_two_junk
    (firstRung : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (color : Fin n → Bool),
      (∀ u v, G.Adj u v → color u ≠ color v) → NoFourCycle G → IsLeastAO G C →
      (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v) (h4 : NoFourCycle G)
    (hL : IsLeastAO G C) (hcard : (junk G C).card = 2)
    (g t h : ℕ) (hgJ : g ∈ junk G C) (ht : t < n + g) (hh : h < n + g)
    (heval : ∀ x : Fin n → Bool,
      gateVal n C g x = (wireVal n C t x || wireVal n C h x)) : False := by
  apply firstRung n G (patch C g t h) color hbip h4 (patch_least G C g t h hL ht hh heval)
  rw [patch_junk G C g t h hL.1 ht hh heval, Finset.card_erase_of_mem hgJ, hcard]

lemma existing_residual_no_two_junk
    (firstRung : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (color : Fin n → Bool),
      (∀ u v, G.Adj u v → color u ≠ color v) → NoFourCycle G → IsLeastAO G C →
      (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v) (h4 : NoFourCycle G)
    (hL : IsLeastAO G C) (hcard : (junk G C).card = 2)
    (g t u v h : ℕ) (hgJ : g ∈ junk G C) (ht : t < n + g) (hh : h < n + g)
    (heval : ∀ x : Fin n → Bool, gateVal n C g x =
      ((wireVal n C t x || wireVal n C u x) && (wireVal n C t x || wireVal n C v x)))
    (hresidual : ∀ x : Fin n → Bool,
      wireVal n C h x = (wireVal n C u x && wireVal n C v x)) : False := by
  apply no_two_junk firstRung G C color hbip h4 hL hcard g t h hgJ ht hh
  intro x
  rw [heval, hresidual]
  cases wireVal n C t x <;> cases wireVal n C u x <;> cases wireVal n C v x <;> rfl

end PEqualNP.Outside.L_meta_5012.OrRewrite


namespace PEqualNP.Outside.L_meta_5012.SymmetricAbsorption

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Absorption

lemma semantic_gate_values {n : ℕ} (C : Circuit) (r g t : ℕ) (b c : Fin n)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hrg : r < g)
    (hr : gateAt C r = ⟨GateOp.or, [t, b.val]⟩)
    (heval : ∀ x : Fin n → Bool, gateVal n C g x =
      ((wireVal n C t x || x b) && (wireVal n C t x || x c)))
    (hread : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g)
    (x : Fin n → Bool) :
    ∀ j < C.gates.length, j ≠ r →
      val (patch C r g t b c) (List.ofFn x) (n + j) = val C (List.ofFn x) (n + j) := by
  have htr : t < n + r := hAO.2.1 r (by omega) t (by rw [hr]; simp)
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hjr
    have earlier : ∀ w, w < n + j → w ≠ n + r →
        val (patch C r g t b c) (List.ofFn x) w = val C (List.ofFn x) w := by
      intro w hw hwr
      by_cases hwn : w < n
      · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
      · have hwrepr : w = n + (w - n) := by omega
        rw [hwrepr]
        exact ih (w - n) (by omega) (by omega) (by omega)
    by_cases hjg : j = g
    · subst j
      rw [patched_g_eval C r g t b c hg hrg htr,
        earlier t (by omega) (Nat.ne_of_lt htr)]
      have he := heval x
      change val C (List.ofFn x) (n + g) =
        ((val C (List.ofFn x) t || x b) && (val C (List.ofFn x) t || x c)) at he
      rw [he]
      cases val C (List.ofFn x) t <;> cases x b <;> cases x c <;> rfl
    rw [val_gate (n := n) (by simp) (by simpa only [patch_length] using hj),
      val_gate (n := n) (by simp) hj, patch_other C r g t b c j hjr hjg]
    congr 1
    apply List.map_congr_left
    intro w hw
    have hwl : w < n + j := hAO.2.1 j hj w hw
    have hwr : w ≠ n + r := by
      intro hh
      exact hjg (hread j hj (hh ▸ hw))
    simp only [ite_eq_left hwl]
    exact earlier w hwl hwr

lemma semantic_wire_values {n : ℕ} (C : Circuit) (r g t : ℕ) (b c : Fin n)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hrg : r < g)
    (hr : gateAt C r = ⟨GateOp.or, [t, b.val]⟩)
    (heval : ∀ x : Fin n → Bool, gateVal n C g x =
      ((wireVal n C t x || x b) && (wireVal n C t x || x c)))
    (hread : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g)
    (x : Fin n → Bool) (w : ℕ) (hwr : w ≠ n + r) :
    val (patch C r g t b c) (List.ofFn x) w = val C (List.ofFn x) w := by
  by_cases hwn : w < n
  · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
  by_cases hwC : w < n + C.gates.length
  · have hwrepr : w = n + (w - n) := by omega
    rw [hwrepr]
    exact semantic_gate_values C r g t b c hAO hg hrg hr heval hread x
      (w - n) (by omega) (by omega)
  · rw [val_ge (n := n) (by simp) (by rw [patch_length]; omega),
      val_ge (n := n) (by simp) (by omega)]

lemma semantic_patch {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r g t : ℕ) (b c : Fin n)
    (hL : IsLeastAO G C) (hg : g < C.gates.length) (hrg : r < g)
    (hr : gateAt C r = ⟨GateOp.or, [t, b.val]⟩)
    (heval : ∀ x : Fin n → Bool, gateVal n C g x =
      ((wireVal n C t x || x b) && (wireVal n C t x || x c)))
    (hread : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g)
    (hbc : G.Adj b c) :
    IsLeastAO G (patch C r g t b c) ∧ junk G (patch C r g t b c) = (junk G C).erase g := by
  have htr : t < n + r := hL.1.2.1 r (by omega) t (by rw [hr]; simp)
  constructor
  · refine ⟨patch_ao C r g t b c hL.1 hg hrg htr, ?_, ?_⟩
    · funext x
      change val (patch C r g t b c) (List.ofFn x) C.output = _
      rw [semantic_wire_values C r g t b c hL.1 hg hrg hr heval hread x C.output
        (r_not_output G C r t b (by omega) htr hr hL.2.1)]
      exact congrFun hL.2.1 x
    · intro D hD hDF
      rw [patch_size]
      exact hL.2.2 D hD hDF
  · apply Finset.ext
    intro j
    by_cases hjr : j = r
    · subst j
      simp only [Finset.mem_erase,
        patch_r_not_junk G C r g t b c (by omega) (Nat.ne_of_lt hrg) hbc,
        r_not_junk G C r t b hr, and_false]
    by_cases hjg : j = g
    · subst j
      simp only [Finset.mem_erase, patch_g_not_junk G C r g t b c hg,
        ne_eq, not_true_eq_false, false_and]
    · have hvals : ∀ x : Fin n → Bool,
          gateVal n (patch C r g t b c) j x = gateVal n C j x := by
        intro x
        exact semantic_wire_values C r g t b c hL.1 hg hrg hr heval hread x (n + j) (by omega)
      simp only [Finset.mem_erase, mem_junk_iff, patch_length,
        patch_other C r g t b c j hjr hjg, hvals, ne_eq, hjg, not_false_eq_true, true_and]

lemma right_root_no_two_junk
    (firstRung : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (color : Fin n → Bool),
      (∀ u v, G.Adj u v → color u ≠ color v) → NoFourCycle G → IsLeastAO G C →
      (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v) (h4 : NoFourCycle G)
    (hL : IsLeastAO G C) (hcard : (junk G C).card = 2)
    (r s g t : ℕ) (b c : Fin n) (hgJ : g ∈ junk G C) (hrg : r < g) (hsg : s < g)
    (hr : gateAt C r = ⟨GateOp.or, [t, b.val]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, c.val]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hread : readers n C s = {g}) : False := by
  have hg : g < C.gates.length := (mem_junk_iff G C g).mp hgJ |>.1
  have htr : t < n + r := hL.1.2.1 r (by omega) t (by rw [hr]; simp)
  have hts : t < n + s := hL.1.2.1 s (by omega) t (by rw [hs]; simp)
  have heval : ∀ x : Fin n → Bool, gateVal n C g x =
      ((wireVal n C t x || x c) && (wireVal n C t x || x b)) := by
    intro x
    have he := original_g_eval C r s g t b c hg hrg hsg htr hts hr hs hgate x
    exact he.trans (Bool.and_comm _ _)
  have hread' : ∀ j < C.gates.length, n + s ∈ (gateAt C j).inputs → j = g := by
    intro j hj hw
    have hjmem : j ∈ readers n C s := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hw⟩
    simpa only [hread, Finset.mem_singleton] using hjmem
  obtain ⟨hPL, hPJ⟩ := semantic_patch G C s g t c b hL hg hsg hs heval hread'
    (diamond_edge G C r s g t b c hL hg hrg hsg hr hs hgate).symm
  apply firstRung n G (patch C s g t c b) color hbip h4 hPL
  rw [hPJ, Finset.card_erase_of_mem hgJ, hcard]

lemma either_root_no_two_junk
    (firstRung : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (color : Fin n → Bool),
      (∀ u v, G.Adj u v → color u ≠ color v) → NoFourCycle G → IsLeastAO G C →
      (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v) (h4 : NoFourCycle G)
    (hL : IsLeastAO G C) (hcard : (junk G C).card = 2)
    (r s g t : ℕ) (b c : Fin n) (hgJ : g ∈ junk G C) (hrg : r < g) (hsg : s < g)
    (hr : gateAt C r = ⟨GateOp.or, [t, b.val]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, c.val]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hread : readers n C r = {g} ∨ readers n C s = {g}) : False := by
  rcases hread with hread | hread
  · exact diamond_no_two_junk firstRung G C color hbip h4 hL hcard
      r s g t b c hgJ hrg hsg hr hs hgate hread
  · exact right_root_no_two_junk firstRung G C color hbip h4 hL hcard
      r s g t b c hgJ hrg hsg hr hs hgate hread

end PEqualNP.Outside.L_meta_5012.SymmetricAbsorption


namespace PEqualNP.Outside.L_meta_5012.Trace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩

end PEqualNP.Outside.L_meta_5012.Trace

namespace PEqualNP.Outside.L_meta_5012.Frontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma wire_all_true {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) :
    ∀ w < n + C.gates.length, wireVal n C w (fun _ => true) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    change CriticalEdge.val n C (fun _ => true) w = true
    by_cases hwn : w < n
    · rw [CriticalEdge.val_in C (fun _ => true) w hwn]
      simp [List.getD_eq_getElem?_getD, hwn]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨_, _, ha, hb, _⟩ := CriticalEdge.gate2 hAO hj
      rw [CriticalEdge.val_rec C hAO _ j hj]
      have hia := ih (opnd C j 0) ha (by omega)
      have hib := ih (opnd C j 1) hb (by omega)
      change CriticalEdge.val n C (fun _ => true) (opnd C j 0) = true at hia
      change CriticalEdge.val n C (fun _ => true) (opnd C j 1) = true at hib
      rw [hia, hib]
      split <;> rfl

lemma no_clean_and_frontier {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (f : (Fin n → Bool) → Bool)
    (hfilter : ∀ w : Fin n, ¬ ∀ x : Fin n → Bool,
      f x = true → x w = true → graphFun G ∅ x = true)
    (hjunk : ∀ j ∈ junk G C, ∀ x : Fin n → Bool,
      gateVal n C j x = true → f x = true)
    (k p q : ℕ) (hk : k < C.gates.length)
    (hgate : gateAt C k = ⟨GateOp.and, [p, q]⟩ ∨ gateAt C k = ⟨GateOp.and, [q, p]⟩)
    (hdom : ∀ x : Fin n → Bool, f x = true → wireVal n C p x = true)
    (hclean : BelowF G C k) : False := by
  classical
  have hp : p < n + k := hAO.2.1 k hk p (by rcases hgate with h | h <;> rw [h] <;> simp)
  have hq : q < n + k := hAO.2.1 k hk q (by rcases hgate with h | h <;> rw [h] <;> simp)
  have hpair : ∀ x : Fin n → Bool, f x = true → wireVal n C q x = true →
      graphFun G ∅ x = true := by
    intro x hf hqx
    apply hclean x
    change Trace.val C (List.ofFn x) (n + k) = true
    apply (Trace.val_and (n := n) (by simp) hk (by rcases hgate with h | h <;> rw [h])).2
    intro w hw
    have hwpq : w = p ∨ w = q := by
      rcases hgate with h | h <;> rw [h] at hw <;> simpa [or_comm] using hw
    rcases hwpq with rfl | rfl
    · exact ⟨hp, hdom x hf⟩
    · exact ⟨hq, hqx⟩
  have hqtrue := wire_all_true C hAO q (by omega)
  obtain ⟨w, hr, hwtrue, hw⟩ := Trace.or_trace (n := n) (C := C)
    (x := List.ofFn (fun _ : Fin n => true)) (by simp) q hqtrue
  rcases hw with hw | ⟨j, hj, rfl, hnotOr⟩
  · apply hfilter ⟨w, hw⟩
    intro x hf hx
    apply hpair x hf
    exact Trace.reach_var_val x q ⟨w, hw⟩ hr hx
  · have hop : (gateAt C j).op = GateOp.and :=
      (hAO.1 _ (Trace.gateAt_mem hj)).resolve_right hnotOr
    have hcone : InCone n C j k := Trace.operand_cone hk (by rcases hgate with h | h <;> rw [h] <;> simp) hq hr
    have hnclean : ¬ BelowF G C j := by
      intro hb
      exact hTop j hj k hk hop hb (by rcases hgate with h | h <;> rw [h]) hcone
    change ¬ ∀ x : Fin n → Bool, gateVal n C j x = true → graphFun G ∅ x = true at hnclean
    push Not at hnclean
    obtain ⟨x, hx, hFx⟩ := hnclean
    have hFfalse : graphFun G ∅ x = false := by
      cases he : graphFun G ∅ x <;> simp_all
    have hjmem : j ∈ junk G C := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr hj, hop, hj, x, hx, hFfalse⟩
    have hf := hjunk j hjmem x hx
    have hqx : wireVal n C q x = true :=
      Trace.orStep_up (n := n) (by simp) hr hx
    exact hFx (hpair x hf hqx)



lemma gate_op_cases {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
  exact hAO.1 _ (Trace.gateAt_mem hj)

lemma read_index_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {i j : ℕ} (hj : j < C.gates.length)
    (hread : n + i ∈ (gateAt C j).inputs) : i < j := by
  have h := hAO.2.1 j hj (n + i) hread
  omega

lemma sole_reader_of_frontier {n : ℕ} {C : Circuit}
    (hAO : IsAO2 n C) {p g : ℕ} {P : ℕ → Prop}
    (hp : p < C.gates.length) (hg : g < C.gates.length)
    (hpg : n + p ∈ (gateAt C g).inputs) (hPp : P p)
    (hlive : ∀ i < C.gates.length,
      C.output = n + i ∨ ∃ j < C.gates.length, n + i ∈ (gateAt C j).inputs)
    (houtput : ∀ i < C.gates.length, P i → C.output ≠ n + i)
    (hor : ∀ i < C.gates.length, P i → ∀ j < C.gates.length,
      (gateAt C j).op = GateOp.or → n + i ∈ (gateAt C j).inputs → P j)
    (hand : ∀ i < C.gates.length, P i → ∀ j < C.gates.length,
      (gateAt C j).op = GateOp.and → n + i ∈ (gateAt C j).inputs → j = g)
    (hoperand : ∀ i < C.gates.length, P i → n + i ∈ (gateAt C g).inputs → i = p) :
    readers n C p = {g} := by
  have noLater : ∀ d i, C.gates.length - i = d → i < C.gates.length → p < i → P i → False := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro i hdi hi hpi hPi
      rcases hlive i hi with hout | ⟨j, hj, hread⟩
      · exact houtput i hi hPi hout
      · have hij := read_index_lt hAO hj hread
        rcases gate_op_cases hAO hj with handj | horj
        · have hjg := hand i hi hPi j hj handj hread
          subst j
          have := hoperand i hi hPi hread
          omega
        · exact ih (C.gates.length - j) (by omega) j rfl hj (by omega)
            (hor i hi hPi j hj horj hread)
  apply Finset.ext
  intro j
  simp only [readers, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hj, hread⟩
    have hpj := read_index_lt hAO hj hread
    rcases gate_op_cases hAO hj with handj | horj
    · exact hand p hp hPp j hj handj hread
    · exact False.elim (noLater _ j rfl hj hpj (hor p hp hPp j hj horj hread))
  · rintro rfl
    exact ⟨hg, hpg⟩

lemma cutVal_rec {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (j k : ℕ)
    (hk : k < C.gates.length) (hkj : k ≠ j) (x : Fin n → Bool) :
    CriticalEdge.cutVal n C {j} x (n + k) =
      if CriticalEdge.isAnd C k = true then
        (CriticalEdge.cutVal n C {j} x (opnd C k 0) && CriticalEdge.cutVal n C {j} x (opnd C k 1))
      else
        (CriticalEdge.cutVal n C {j} x (opnd C k 0) || CriticalEdge.cutVal n C {j} x (opnd C k 1)) := by
  obtain ⟨_, _, ha, hb, _⟩ := CriticalEdge.gate2 hAO hk
  have hnot : k ∉ ({j} : Finset ℕ) := by simpa using hkj
  cases hA : CriticalEdge.isAnd C k with
  | false =>
    rw [CriticalEdge.cutVal, CriticalEdge.u_or hnot hA ha hb]
    rfl
  | true =>
    rw [CriticalEdge.cutVal, CriticalEdge.u_and hnot hA ha hb]
    simp [CriticalEdge.cutVal]

lemma cutVal_unread {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hread : ∀ k < C.gates.length, n + j ∉ (gateAt C k).inputs)
    (x : Fin n → Bool) :
    ∀ w < n + C.gates.length, w ≠ n + j →
      CriticalEdge.cutVal n C {j} x w = CriticalEdge.val n C x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwj
    by_cases hwn : w < n
    · rw [CriticalEdge.cutVal, CriticalEdge.u_in hwn, CriticalEdge.val_in C x w hwn]
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨_, hin, ha, hb, _⟩ := CriticalEdge.gate2 hAO hk
      have han : opnd C k 0 ≠ n + j := by
        intro he
        apply hread k hk
        rw [hin, ← he]
        simp
      have hbn : opnd C k 1 ≠ n + j := by
        intro he
        apply hread k hk
        rw [hin, ← he]
        simp
      rw [cutVal_rec C hAO j k hk (by omega) x, CriticalEdge.val_rec C hAO x k hk,
        ih _ ha (by omega) han, ih _ hb (by omega) hbn]

lemma least_live {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length) :
    C.output = n + j ∨ ∃ k < C.gates.length, n + j ∈ (gateAt C k).inputs := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨hout, hread⟩ := hn
  have hE := CriticalEdge.least_nonempty_of_gate G C hL j hj
  obtain ⟨p, q, hpq, hcut⟩ := CriticalEdge.least_gate_critical G C hL hE j hj
  have hbound := CriticalEdge.output_lt G C hL.2.1 hE
  rw [cutVal_unread C hL.1 j hread (pairInput p q) C.output hbound hout,
    CriticalEdge.val_out, hL.2.1] at hcut
  have htrue : graphFun G ∅ (pairInput p q) = true :=
    (CriticalEdge.gf G _).2 ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩
  rw [htrue] at hcut
  cases hcut



lemma sole_reader_of_dominated_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hTop : TopForm G C)
    (h g r s : ℕ) (hg : g < C.gates.length) (hrg : r < g) (hhr : h < r)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩ ∨
      gateAt C g = ⟨GateOp.and, [n + s, n + r]⟩)
    (hJ : ∀ j ∈ junk G C, j = g ∨ j = h)
    (hjunk : ∀ j ∈ junk G C, ∀ x : Fin n → Bool,
      gateVal n C j x = true → gateVal n C r x = true)
    (hfilter : ∀ w : Fin n, ¬ ∀ x : Fin n → Bool,
      gateVal n C r x = true → x w = true → graphFun G ∅ x = true)
    (hdirty : ∃ x : Fin n → Bool, gateVal n C r x = true ∧ graphFun G ∅ x = false)
    (hs : ¬ Relation.ReflTransGen (Trace.OrStep n C) (n + s) (n + r)) :
    readers n C r = {g} := by
  classical
  apply sole_reader_of_frontier hL.1
    (P := fun i => Relation.ReflTransGen (Trace.OrStep n C) (n + i) (n + r))
    (by omega) hg (by rcases hgate with h | h <;> rw [h] <;> simp) Relation.ReflTransGen.refl (least_live G C hL)
  · intro i hi hPi hout
    obtain ⟨x, hxr, hFx⟩ := hdirty
    have hxi := Trace.orStep_up (n := n) (by simp) hPi hxr
    rw [← hout] at hxi
    change circuitFun n C x = true at hxi
    rw [hL.2.1, hFx] at hxi
    cases hxi
  · intro i hi hPi j hj hop hread
    exact Relation.ReflTransGen.head
      ⟨j, hj, rfl, hop, hread, hL.1.2.1 j hj _ hread⟩ hPi
  · intro i hi hPi j hj hop hread
    have hdom : ∀ x : Fin n → Bool, gateVal n C r x = true → wireVal n C (n + i) x = true :=
      fun x hx => Trace.orStep_up (n := n) (by simp) hPi hx
    obtain ⟨_, hin, _, _, _⟩ := CriticalEdge.gate2 hL.1 hj
    have hge : gateAt C j = ⟨GateOp.and, [opnd C j 0, opnd C j 1]⟩ :=
      CriticalEdge.gate_eta hop hin
    have hread' : n + i = opnd C j 0 ∨ n + i = opnd C j 1 := by
      rw [hin] at hread
      simpa using hread
    have hnclean : ¬ BelowF G C j := by
      intro hb
      rcases hread' with he | he
      · exact no_clean_and_frontier G C hL.1 hTop (gateVal n C r) hfilter hjunk
          j (opnd C j 0) (opnd C j 1) hj (Or.inl hge)
          (by simpa only [← he] using hdom) hb
      · exact no_clean_and_frontier G C hL.1 hTop (gateVal n C r) hfilter hjunk
          j (opnd C j 1) (opnd C j 0) hj (Or.inr hge)
          (by simpa only [← he] using hdom) hb
    have hjmem : j ∈ junk G C := by
      change ¬ ∀ x : Fin n → Bool, gateVal n C j x = true → graphFun G ∅ x = true at hnclean
      push Not at hnclean
      obtain ⟨x, hx, hf⟩ := hnclean
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr hj, hop, hj, x, hx, by simpa using hf⟩
    rcases hJ j hjmem with hjg | hjh
    · exact hjg
    · have hle := Trace.orStep_le hPi
      have hij := hL.1.2.1 j hj (n + i) hread
      omega
  · intro i hi hPi hread
    have hread' : n + i = n + r ∨ n + i = n + s := by
      rcases hgate with h | h <;> rw [h] at hread <;> simpa [or_comm] using hread
    rcases hread' with he | he
    · omega
    · have his : i = s := by omega
      subst i
      exact False.elim (hs hPi)



lemma wire_mono {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ w < n + C.gates.length, wireVal n C w x = true → wireVal n C w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hx
    change CriticalEdge.val n C x w = true at hx
    change CriticalEdge.val n C y w = true
    by_cases hwn : w < n
    · rw [CriticalEdge.val_in C x w hwn] at hx
      rw [CriticalEdge.val_in C y w hwn]
      have hx' : x ⟨w, hwn⟩ = true := by simpa [List.getD_eq_getElem?_getD, hwn] using hx
      simpa [List.getD_eq_getElem?_getD, hwn] using hxy ⟨w, hwn⟩ hx'
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨_, _, ha, hb, _⟩ := CriticalEdge.gate2 hAO hj
      rw [CriticalEdge.val_rec C hAO x j hj] at hx
      rw [CriticalEdge.val_rec C hAO y j hj]
      cases hA : CriticalEdge.isAnd C j with
      | false =>
        simp only [hA, Bool.false_eq_true, ite_false, Bool.or_eq_true] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (ih _ ha (by omega) hx)
        · exact Or.inr (ih _ hb (by omega) hx)
      | true =>
        simp only [hA, ite_true, Bool.and_eq_true] at hx ⊢
        exact ⟨ih _ ha (by omega) hx.1, ih _ hb (by omega) hx.2⟩

lemma diamond_root_sole {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hTop : TopForm G C)
    (h g r s : ℕ) (b c : Fin n) (hg : g < C.gates.length)
    (hrg : r < g) (hsg : s < g) (hhr : h < r)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩ ∨
      gateAt C g = ⟨GateOp.and, [n + s, n + r]⟩)
    (hJ : ∀ j ∈ junk G C, j = g ∨ j = h)
    (hrval : ∀ x : Fin n → Bool, gateVal n C r x = (gateVal n C h x || x b))
    (hsval : ∀ x : Fin n → Bool, gateVal n C s x = (gateVal n C h x || x c))
    (hbc : b ≠ c) (hcritical : gateVal n C h (pairInput b c) = false)
    (hnofilter : ¬ ∃ w, Diamond.RootFilter G (gateVal n C h) b w) :
    readers n C r = {g} := by
  have hsingle : gateVal n C h (pairInput b b) = false := by
    cases hx : gateVal n C h (pairInput b b) with
    | false => rfl
    | true =>
      have hmono := wire_mono C hL.1 (pairInput b b) (pairInput b c)
        (by
          intro i hi
          have hib : i = b := by simpa [pairInput] using hi
          simp [pairInput, hib])
        (n + h) (by omega) hx
      change gateVal n C h (pairInput b c) = true at hmono
      rw [hcritical] at hmono
      cases hmono
  have hnotreach : ¬ Relation.ReflTransGen (Trace.OrStep n C) (n + s) (n + r) := by
    intro hp
    have hrtrue : gateVal n C r (pairInput b b) = true := by rw [hrval]; simp [pairInput]
    have hstrue := Trace.orStep_up (n := n) (by simp) hp hrtrue
    change gateVal n C s (pairInput b b) = true at hstrue
    rw [hsval, hsingle] at hstrue
    simp [pairInput, hbc.symm] at hstrue
  apply sole_reader_of_dominated_junk G C hL hTop h g r s hg hrg hhr hgate hJ
  · intro j hj x hx
    rcases hJ j hj with hjg | hjh
    · subst j
      have hop : (gateAt C g).op = GateOp.and := by rcases hgate with he | he <;> rw [he]
      have hin : n + r ∈ (gateAt C g).inputs := by rcases hgate with he | he <;> rw [he] <;> simp
      exact ((Trace.val_and (n := n) (by simp) hg hop).1 hx (n + r) hin).2
    · subst j
      rw [hrval, hx]
      rfl
  · intro w hw
    apply hnofilter
    refine ⟨w, ?_⟩
    intro x hx hxw
    exact hw x (by rw [hrval]; exact hx) hxw
  · refine ⟨pairInput b b, ?_, ?_⟩
    · rw [hrval]; simp [pairInput]
    · exact Absorption.graphFun_singleton G b
  · exact hnotreach



lemma nested_diamond_root_choice {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C) (hTop : TopForm G C)
    (h g r s : ℕ) (d b c : Fin n) (hg : g < C.gates.length)
    (hrg : r < g) (hsg : s < g) (hbc : b ≠ c)
    (hr : gateAt C r = ⟨GateOp.or, [n + h, b.val]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [n + h, c.val]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hJ : ∀ j ∈ junk G C, j = g ∨ j = h)
    (hlower : ∀ x : Fin n → Bool, x d = true → gateVal n C h x = true) :
    readers n C r = {g} ∨ readers n C s = {g} := by
  have htr : n + h < n + r := hL.1.2.1 r (by omega) (n + h) (by rw [hr]; simp)
  have hts : n + h < n + s := hL.1.2.1 s (by omega) (n + h) (by rw [hs]; simp)
  have hrval : ∀ x : Fin n → Bool, gateVal n C r x = (gateVal n C h x || x b) := by
    intro x
    exact Absorption.or_raw_eval C r (n + h) b (by omega) hr htr x
  have hsval : ∀ x : Fin n → Bool, gateVal n C s x = (gateVal n C h x || x c) := by
    intro x
    exact Absorption.or_raw_eval C s (n + h) c (by omega) hs hts x
  have heval : ∀ x : Fin n → Bool, gateVal n C g x =
      ((wireVal n C (n + h) x || x b) && (wireVal n C (n + h) x || x c)) := by
    intro x
    exact Absorption.original_g_eval C r s g (n + h) b c hg hrg hsg htr hts hr hs hgate x
  obtain ⟨hedge, hcritical⟩ := Diamond.residual_critical G C hL g (n + h) b c
    (by omega) hg hbc heval
  change gateVal n C h (pairInput b c) = false at hcritical
  rcases Diamond.one_root_without_filters G color hbip (gateVal n C h) d b c hlower hedge with hnr | hns
  · exact Or.inl (diamond_root_sole G C hL hTop h g r s b c hg hrg hsg (by omega)
      (Or.inl hgate) hJ hrval hsval hbc hcritical hnr)
  · exact Or.inr (diamond_root_sole G C hL hTop h g s r c b hg hsg hrg (by omega)
      (Or.inr hgate) hJ hsval hrval hbc.symm
      (by simpa only [Diamond.pairInput_comm] using hcritical) hns)

lemma nested_singleton_gate_diamond_no_two_junk
    (firstRung : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (color : Fin n → Bool),
      (∀ u v, G.Adj u v → color u ≠ color v) → NoFourCycle G → IsLeastAO G C →
      (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v) (h4 : NoFourCycle G)
    (hL : IsLeastAO G C) (hTop : TopForm G C) (hcard : (junk G C).card = 2)
    (h g r s : ℕ) (d b c : Fin n) (hhJ : h ∈ junk G C) (hgJ : g ∈ junk G C)
    (hrg : r < g) (hsg : s < g)
    (hr : gateAt C r = ⟨GateOp.or, [n + h, b.val]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [n + h, c.val]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hlower : ∀ x : Fin n → Bool, x d = true → gateVal n C h x = true) : False := by
  classical
  have hg : g < C.gates.length := (Absorption.mem_junk_iff G C g).mp hgJ |>.1
  have htr : n + h < n + r := hL.1.2.1 r (by omega) (n + h) (by rw [hr]; simp)
  have hgh : g ≠ h := by omega
  have hpair : ({g, h} : Finset ℕ) = junk G C := by
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact hgJ
      · exact hhJ
    · simp [hcard, hgh]
  have hJ : ∀ j ∈ junk G C, j = g ∨ j = h := by
    intro j hj
    rw [← hpair] at hj
    simpa using hj
  have hbc : b ≠ c := (Absorption.diamond_edge G C r s g (n + h) b c hL
    hg hrg hsg hr hs hgate).ne
  apply SymmetricAbsorption.either_root_no_two_junk firstRung G C color hbip h4 hL hcard
    r s g (n + h) b c hgJ hrg hsg hr hs hgate
  exact nested_diamond_root_choice G color hbip C hL hTop h g r s d b c hg
    hrg hsg hbc hr hs hgate hJ hlower

end PEqualNP.Outside.L_meta_5012.Frontier


namespace PEqualNP.Outside.L_meta_5012.BoundaryFilters

open PEqualNP.TopForm
open PEqualNP.Outside.L_meta_5012.Overlap

lemma common_filter_boundary {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h4 : NoFourCycle G) (T I : Finset (Fin n))
    (w z : Fin n) (hIw : ∀ i ∈ I, G.Adj i w)
    (hTz : ∀ t ∈ T, G.Adj t z) (hTI : 2 ≤ (T ∩ I).card) :
    (∀ t ∈ T, G.Adj w t) ∧ z = w := by
  have hzw : z = w := SharedFilter.common_neighbor_eq G h4 (T ∩ I) hTI
    (fun i hi => hTz i (Finset.mem_inter.mp hi).1)
    (fun i hi => hIw i (Finset.mem_inter.mp hi).2)
  refine ⟨?_, hzw⟩
  intro t ht
  exact hzw ▸ (hTz t ht).symm

lemma overlap_filtered_boundary {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h4 : NoFourCycle G) (T I P Q : Finset (Fin n))
    (w : Fin n) (hIw : ∀ i ∈ I, G.Adj i w)
    (hSafe : ∀ t ∈ T, CleanFilter G P Q t) (hPQ : (P ∩ Q).Nonempty)
    (hTI : 2 ≤ (T ∩ I).card) :
    (∀ t ∈ T, G.Adj w t) ∧ P ∩ Q = {w} := by
  have hcenter (z : Fin n) (hz : z ∈ P ∩ Q) :
      (∀ t ∈ T, G.Adj w t) ∧ z = w := by
    exact common_filter_boundary G h4 T I w z hIw
      (fun t ht => cleanFilter_adj_overlap G P Q (hSafe t ht) hz) hTI
  obtain ⟨z, hz⟩ := hPQ
  have hzw := (hcenter z hz).2
  refine ⟨(hcenter z hz).1, ?_⟩
  apply Finset.eq_singleton_iff_unique_mem.mpr
  exact ⟨hzw ▸ hz, fun y hy => (hcenter y hy).2⟩

lemma overlap_safe_boundary_protected {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h4 : NoFourCycle G) (T I P Q : Finset (Fin n))
    (w : Fin n) (hIw : ∀ i ∈ I, G.Adj i w)
    (hSafe : ∀ t ∈ T, CleanFilter G P Q t) (hPQ : (P ∩ Q).Nonempty) :
    (∀ t ∈ T, G.Adj w t) ∨ (T ∩ I).card ≤ 1 := by
  by_cases hTI : (T ∩ I).card ≤ 1
  · exact Or.inr hTI
  · exact Or.inl (overlap_filtered_boundary G h4 T I P Q w hIw hSafe hPQ
      (by omega)).1

end PEqualNP.Outside.L_meta_5012.BoundaryFilters


namespace PEqualNP.Outside.L_meta_5012.OverlapCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

lemma ao2_wire_all_true {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ u < n + C.gates.length, wval C (fun _ : Fin n => true) u = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu
    by_cases hun : u < n
    · rw [Lift.wval_input C (fun _ => true) u hun]
    · obtain ⟨j, rfl⟩ : ∃ j, u = n + j := ⟨u - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have h0 := Lift.opnd_lt hAO hj 0
      have h1 := Lift.opnd_lt hAO hj 1
      have hv0 := ih (opnd C j 0) h0 (by omega)
      have hv1 := ih (opnd C j 1) h1 (by omega)
      rw [Lift.wval_gate_eval hAO _ hj, hv0, hv1]
      rcases hAO.1 _ (Lift.gateAt_mem hj) with hop | hop <;> rw [hop] <;> rfl

lemma top_raw_boundary_dichotomy {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (hTF : TopForm G C)
    {j k : ℕ} (hJ : junk G C = {j,k}) {w : Fin n} (hW : wmax G C j = {w})
    (h4 : NoFourCycle G) (I T : Finset (Fin n))
    (hOverlap : 2 ≤ (T ∩ I).card) (hIw : ∀ i ∈ I, G.Adj w i)
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    (hTside : T ⊆ side (n := n) C a b) :
    (∀ t ∈ T, G.Adj w t) ∨ T ⊆ wmax G C k := by
  obtain ⟨haLen, haAnd, _⟩ := Critical.Base.topData ha
  have hOpBound := Lift.opnd_lt hAO haLen (1-b)
  have hOpTrue : RawOperands.W n C (fun _ : Fin n => true) (opnd C a (1-b)) = true :=
    ao2_wire_all_true hAO _ (by omega)
  have hFlip : 1 - (1 - b) = b := by fin_cases b <;> decide
  have hTopAdj (t r : Fin n) (ht : t ∈ side (n := n) C a b)
      (hr : r ∈ side (n := n) C a (1-b)) : G.Adj t r := by
    fin_cases b
    · exact Critical.Base.topAdj hAO ha ht hr
    · exact (Critical.Base.topAdj hAO ha hr ht).symm
  rcases RawOperands.down n C (fun _ : Fin n => true)
      (fun l hl => hAO.1 _ (RawOperands.gateAt_mem' C l hl)) _ hOpTrue with
    ⟨r, hr, _⟩ | ⟨l, hl, hReach, hlAnd, _⟩
  · left
    have hrw : r = w := by
      by_contra hne
      have hSub : T ∩ I ⊆ Finset.univ.filter fun t => G.Adj r t ∧ G.Adj w t := by
        intro t ht
        obtain ⟨htT, htI⟩ := Finset.mem_inter.mp ht
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (hTopAdj t r (hTside htT) hr).symm, hIw t htI⟩
      have hCard := (Finset.card_le_card hSub).trans (h4 r w hne)
      omega
    intro t ht
    rw [← hrw]
    exact (hTopAdj t r (hTside ht) hr).symm
  · have hlJ : l ∈ junk G C :=
      Critical.Base.operandOrAndJunk hAO hTF haLen haAnd hReach hlAnd
    have hAll : T ⊆ wmax G C l := by
      have hOpp := Critical.Base.oppositeSideWmax hAO ha hReach
      rw [hFlip] at hOpp
      exact hTside.trans hOpp
    rcases Critical.Base.memJunkPair hJ hlJ with rfl | rfl
    · have hSub : T ∩ I ⊆ ({w} : Finset (Fin n)) := by
        intro t ht
        rw [← hW]
        exact hAll (Finset.mem_inter.mp ht).1
      have hCard := Finset.card_le_card hSub
      simp only [Finset.card_singleton] at hCard
      omega
    · exact Or.inr hAll

lemma top_raw_boundary_protected {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (hTF : TopForm G C)
    {j k : ℕ} (hJ : junk G C = {j,k})
    (hjk : ¬ InCone n C j k) (hkj : ¬ InCone n C k j)
    {w : Fin n} (hW : wmax G C j = {w}) (h4 : NoFourCycle G)
    (hKOverlap : ((side (n := n) C k 0) ∩ (side (n := n) C k 1)).Nonempty)
    (I T : Finset (Fin n)) (hIw : ∀ i ∈ I, G.Adj w i)
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    (hTside : T ⊆ side (n := n) C a b) :
    (∀ t ∈ T, G.Adj w t) ∨ (T ∩ I).card ≤ 1 := by
  by_cases hSmall : (T ∩ I).card ≤ 1
  · exact Or.inr hSmall
  · have hLarge : 2 ≤ (T ∩ I).card := by omega
    rcases top_raw_boundary_dichotomy G C hAO hTF hJ hW h4 I T hLarge hIw ha b hTside
        with hNeighbors | hFilter
    · exact Or.inl hNeighbors
    · left
      obtain ⟨z, hz⟩ := hKOverlap
      have heval (x : Fin n → Bool) : gateVal n C k x = IndependentDescent.product
          (side (n := n) C k 0) (side (n := n) C k 1) x :=
        RawOperands.independent_product G C hAO hTF j k hJ hjk hkj k (Or.inr rfl) x
      have hTz (t : Fin n) (ht : t ∈ T) : G.Adj t z :=
        safe_adj_overlap G _ _
          ((IndependentDescent.wmax_iff G C k _ _ heval t).mp (hFilter ht)) hz
      have hzw : z = w := by
        by_contra hne
        have hSub : T ∩ I ⊆ Finset.univ.filter fun t => G.Adj z t ∧ G.Adj w t := by
          intro t ht
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (hTz t (Finset.mem_inter.mp ht).1).symm, hIw t (Finset.mem_inter.mp ht).2⟩
        have hCard := (Finset.card_le_card hSub).trans (h4 z w hne)
        omega
      intro t ht
      exact hzw ▸ (hTz t ht).symm

lemma output_raw_frontier_empty {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hF : circuitFun n C = graphFun G ∅) :
    orIn n C C.output = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hout : circuitFun n C (pairInput v v) = true :=
    Critical.Base.reach_var_val (pairInput v v) C.output v
      (Critical.Base.mem_orIn_reach v hv) (by simp [pairInput])
  rw [hF] at hout
  exact G.irrefl ((Critical.Base.graphFun_pair G v v).mp hout)

end PEqualNP.Outside.L_meta_5012.OverlapCase


namespace PEqualNP.Outside.L_meta_5012.Frontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma diamond_root_sole_common {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hTop : TopForm G C)
    (h g r s t : ℕ) (b c : Fin n) (hg : g < C.gates.length)
    (hrg : r < g) (hsg : s < g) (hhr : h < r) (ht : t < n + g)
    (hdom : ∀ x : Fin n → Bool, gateVal n C h x = true → wireVal n C t x = true)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩ ∨
      gateAt C g = ⟨GateOp.and, [n + s, n + r]⟩)
    (hJ : ∀ j ∈ junk G C, j = g ∨ j = h)
    (hrval : ∀ x : Fin n → Bool, gateVal n C r x = (wireVal n C t x || x b))
    (hsval : ∀ x : Fin n → Bool, gateVal n C s x = (wireVal n C t x || x c))
    (hbc : b ≠ c) (hcritical : wireVal n C t (pairInput b c) = false)
    (hnofilter : ¬ ∃ w, Diamond.RootFilter G (wireVal n C t) b w) :
    readers n C r = {g} := by
  have hsingle : wireVal n C t (pairInput b b) = false := by
    cases hx : wireVal n C t (pairInput b b) with
    | false => rfl
    | true =>
      have hmono := wire_mono C hL.1 (pairInput b b) (pairInput b c)
        (by
          intro i hi
          have hib : i = b := by simpa [pairInput] using hi
          simp [pairInput, hib]) t (by omega) hx
      rw [hcritical] at hmono
      cases hmono
  have hnotreach : ¬ Relation.ReflTransGen (Trace.OrStep n C) (n + s) (n + r) := by
    intro hp
    have hrtrue : gateVal n C r (pairInput b b) = true := by rw [hrval]; simp [pairInput]
    have hstrue := Trace.orStep_up (n := n) (by simp) hp hrtrue
    change gateVal n C s (pairInput b b) = true at hstrue
    rw [hsval, hsingle] at hstrue
    simp [pairInput, hbc.symm] at hstrue
  apply sole_reader_of_dominated_junk G C hL hTop h g r s hg hrg hhr hgate hJ
  · intro j hj x hx
    rcases hJ j hj with hjg | hjh
    · subst j
      have hop : (gateAt C g).op = GateOp.and := by rcases hgate with he | he <;> rw [he]
      have hin : n + r ∈ (gateAt C g).inputs := by rcases hgate with he | he <;> rw [he] <;> simp
      exact ((Trace.val_and (n := n) (by simp) hg hop).1 hx (n + r) hin).2
    · subst j
      rw [hrval, hdom x hx]
      rfl
  · intro w hw
    apply hnofilter
    refine ⟨w, ?_⟩
    intro x hx hxw
    exact hw x (by rw [hrval]; exact hx) hxw
  · refine ⟨pairInput b b, ?_, ?_⟩
    · rw [hrval]; simp [pairInput]
    · exact Absorption.graphFun_singleton G b
  · exact hnotreach

lemma common_diamond_root_choice {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C) (hTop : TopForm G C)
    (h g r s t : ℕ) (d b c : Fin n) (hg : g < C.gates.length)
    (hrg : r < g) (hsg : s < g) (hhr : h < r) (hhs : h < s) (hbc : b ≠ c)
    (hr : gateAt C r = ⟨GateOp.or, [t, b.val]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, c.val]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hJ : ∀ j ∈ junk G C, j = g ∨ j = h)
    (hdom : ∀ x : Fin n → Bool, gateVal n C h x = true → wireVal n C t x = true)
    (hlower : ∀ x : Fin n → Bool, x d = true → wireVal n C t x = true) :
    readers n C r = {g} ∨ readers n C s = {g} := by
  have htr : t < n + r := hL.1.2.1 r (by omega) t (by rw [hr]; simp)
  have hts : t < n + s := hL.1.2.1 s (by omega) t (by rw [hs]; simp)
  have hrval : ∀ x : Fin n → Bool, gateVal n C r x = (wireVal n C t x || x b) := by
    intro x
    exact Absorption.or_raw_eval C r t b (by omega) hr htr x
  have hsval : ∀ x : Fin n → Bool, gateVal n C s x = (wireVal n C t x || x c) := by
    intro x
    exact Absorption.or_raw_eval C s t c (by omega) hs hts x
  have heval : ∀ x : Fin n → Bool, gateVal n C g x =
      ((wireVal n C t x || x b) && (wireVal n C t x || x c)) := by
    intro x
    exact Absorption.original_g_eval C r s g t b c hg hrg hsg htr hts hr hs hgate x
  obtain ⟨hedge, hcritical⟩ := Diamond.residual_critical G C hL g t b c
    (by omega) hg hbc heval
  rcases Diamond.one_root_without_filters G color hbip (wireVal n C t) d b c hlower hedge with hnr | hns
  · exact Or.inl (diamond_root_sole_common G C hL hTop h g r s t b c hg hrg hsg hhr
      (by omega) hdom (Or.inl hgate) hJ hrval hsval hbc hcritical hnr)
  · exact Or.inr (diamond_root_sole_common G C hL hTop h g s r t c b hg hsg hrg hhs
      (by omega) hdom (Or.inr hgate) hJ hsval hrval hbc.symm
      (by simpa only [Diamond.pairInput_comm] using hcritical) hns)

lemma common_diamond_no_two_junk
    (firstRung : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (color : Fin n → Bool),
      (∀ u v, G.Adj u v → color u ≠ color v) → NoFourCycle G → IsLeastAO G C →
      (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v) (h4 : NoFourCycle G)
    (hL : IsLeastAO G C) (hTop : TopForm G C) (hcard : (junk G C).card = 2)
    (h g r s t : ℕ) (d b c : Fin n) (hgJ : g ∈ junk G C)
    (hrg : r < g) (hsg : s < g) (hhr : h < r) (hhs : h < s)
    (hr : gateAt C r = ⟨GateOp.or, [t, b.val]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, c.val]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hJ : ∀ j ∈ junk G C, j = g ∨ j = h)
    (hdom : ∀ x : Fin n → Bool, gateVal n C h x = true → wireVal n C t x = true)
    (hlower : ∀ x : Fin n → Bool, x d = true → wireVal n C t x = true) : False := by
  have hg : g < C.gates.length := (Absorption.mem_junk_iff G C g).mp hgJ |>.1
  have hbc : b ≠ c := (Absorption.diamond_edge G C r s g t b c hL hg hrg hsg hr hs hgate).ne
  apply SymmetricAbsorption.either_root_no_two_junk firstRung G C color hbip h4 hL hcard
    r s g t b c hgJ hrg hsg hr hs hgate
  exact common_diamond_root_choice G color hbip C hL hTop h g r s t d b c hg
    hrg hsg hhr hhs hbc hr hs hgate hJ hdom hlower

lemma wire_singleton_lower {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (t : ℕ) (d : Fin n) (ht : t < n + C.gates.length)
    (hunit : wireVal n C t (pairInput d d) = true) :
    ∀ x : Fin n → Bool, x d = true → wireVal n C t x = true := by
  intro x hxd
  apply wire_mono C hAO (pairInput d d) x ?_ t ht hunit
  intro i hi
  have hid : i = d := by simpa [pairInput] using hi
  simpa only [hid] using hxd

lemma or_context_diamond_no_two_junk
    (firstRung : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (color : Fin n → Bool),
      (∀ u v, G.Adj u v → color u ≠ color v) → NoFourCycle G → IsLeastAO G C →
      (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v) (h4 : NoFourCycle G)
    (hL : IsLeastAO G C) (hTop : TopForm G C) (hcard : (junk G C).card = 2)
    (h g r s t : ℕ) (d b c : Fin n) (hhJ : h ∈ junk G C) (hgJ : g ∈ junk G C)
    (hrg : r < g) (hsg : s < g)
    (hr : gateAt C r = ⟨GateOp.or, [t, b.val]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, c.val]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hpath : Relation.ReflTransGen (Trace.OrStep n C) t (n + h))
    (hraw : Relation.ReflTransGen (Trace.OrStep n C) t d.val) : False := by
  classical
  have hg : g < C.gates.length := (Absorption.mem_junk_iff G C g).mp hgJ |>.1
  have htr : t < n + r := hL.1.2.1 r (by omega) t (by rw [hr]; simp)
  have hts : t < n + s := hL.1.2.1 s (by omega) t (by rw [hs]; simp)
  have hht := Trace.orStep_le hpath
  have hhr : h < r := by omega
  have hhs : h < s := by omega
  have hgh : g ≠ h := by omega
  have hpair : ({g, h} : Finset ℕ) = junk G C := by
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact hgJ
      · exact hhJ
    · simp [hcard, hgh]
  have hJ : ∀ j ∈ junk G C, j = g ∨ j = h := by
    intro j hj
    rw [← hpair] at hj
    simpa using hj
  apply common_diamond_no_two_junk firstRung G C color hbip h4 hL hTop hcard
    h g r s t d b c hgJ hrg hsg hhr hhs hr hs hgate hJ
  · intro x hx
    exact Trace.orStep_up (n := n) (by simp) hpath hx
  · intro x hx
    exact Trace.reach_var_val x t d hraw hx

end PEqualNP.Outside.L_meta_5012.Frontier


namespace PEqualNP.Outside.L_meta_5012.PrivateMove

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Absorption

def fwd (r g j : ℕ) : ℕ :=
  if j = r then g - 1 else if r < j ∧ j < g then j - 1 else j

def back (r g j : ℕ) : ℕ :=
  if j = g - 1 then r else if r ≤ j ∧ j < g - 1 then j + 1 else j

lemma back_fwd (r g j : ℕ) (hrg : r < g) : back r g (fwd r g j) = j := by
  unfold fwd back
  split_ifs <;> omega

lemma fwd_back (r g j : ℕ) (hrg : r < g) : fwd r g (back r g j) = j := by
  unfold fwd back
  split_ifs <;> omega

lemma fwd_lt {r g m j : ℕ} (hrg : r < g) (hgm : g ≤ m) : fwd r g j < m ↔ j < m := by
  unfold fwd
  split_ifs <;> omega

lemma back_lt {r g m j : ℕ} (hrg : r < g) (hgm : g ≤ m) : back r g j < m ↔ j < m := by
  unfold back
  split_ifs <;> omega

lemma fwd_injective {r g : ℕ} (hrg : r < g) : Function.Injective (fwd r g) := by
  intro i j he
  have := congrArg (back r g) he
  simpa only [back_fwd r g i hrg, back_fwd r g j hrg] using this

def mapWire (n r g w : ℕ) : ℕ := if w < n then w else n + fwd r g (w - n)

lemma mapWire_input {n r g w : ℕ} (hw : w < n) : mapWire n r g w = w := by
  simp [mapWire, hw]

lemma mapWire_gate (n r g j : ℕ) : mapWire n r g (n + j) = n + fwd r g j := by
  simp [mapWire]

lemma mapWire_lt {n r g m w : ℕ} (hrg : r < g) (hgm : g ≤ m) :
    mapWire n r g w < n + m ↔ w < n + m := by
  by_cases hwn : w < n
  · rw [mapWire_input hwn]
  · have hw : w = n + (w - n) := by omega
    rw [hw, mapWire_gate]
    simpa only [Nat.add_lt_add_iff_left] using (fwd_lt (j := w - n) hrg hgm)

lemma mapWire_before {n r g j w : ℕ} (hrg : r < g)
    (hw : w < n + j) (hprivate : w = n + r → j = g) :
    mapWire n r g w < n + fwd r g j := by
  by_cases hwn : w < n
  · rw [mapWire_input hwn]
    omega
  · have hwrepr : w = n + (w - n) := by omega
    rw [hwrepr, mapWire_gate]
    have hkj : w - n < j := by omega
    have hkr : w - n = r → j = g := by intro h; apply hprivate; omega
    unfold fwd
    split_ifs <;> omega

def rename (n r g : ℕ) (q : Gate) : Gate :=
  ⟨q.op, q.inputs.map (mapWire n r g)⟩

def move (n : ℕ) (C : Circuit) (r g : ℕ) : Circuit :=
  ⟨List.ofFn (fun j : Fin C.gates.length => rename n r g (gateAt C (back r g j.val))),
    mapWire n r g C.output⟩

lemma move_length (n : ℕ) (C : Circuit) (r g : ℕ) :
    (move n C r g).gates.length = C.gates.length := by simp [move]

lemma move_size (n : ℕ) (C : Circuit) (r g : ℕ) :
    (move n C r g).size = C.size := by simp [Circuit.size, move_length]

lemma moved_gate (n : ℕ) (C : Circuit) (r g j : ℕ) (hj : j < C.gates.length) :
    gateAt (move n C r g) j = rename n r g (gateAt C (back r g j)) := by
  simp [gateAt, move, List.getD_eq_getElem?_getD, hj]

lemma moved_original_gate (n : ℕ) (C : Circuit) (r g j : ℕ)
    (hrg : r < g) (hg : g ≤ C.gates.length) (hj : j < C.gates.length) :
    gateAt (move n C r g) (fwd r g j) = rename n r g (gateAt C j) := by
  rw [moved_gate n C r g (fwd r g j) ((fwd_lt hrg hg).2 hj), back_fwd r g j hrg]

lemma move_ao {n : ℕ} (C : Circuit) (r g : ℕ) (hAO : IsAO2 n C)
    (hrg : r < g) (hg : g ≤ C.gates.length)
    (hread : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g) :
    IsAO2 n (move n C r g) := by
  have hidx : ∀ j < (move n C r g).gates.length,
      ((gateAt (move n C r g) j).op = GateOp.and ∨
        (gateAt (move n C r g) j).op = GateOp.or) ∧
      (gateAt (move n C r g) j).inputs.length = 2 ∧
      ∀ w ∈ (gateAt (move n C r g) j).inputs, w < n + j := by
    intro j hj
    have hj0 : j < C.gates.length := by simpa only [move_length] using hj
    have hjold : back r g j < C.gates.length := (back_lt hrg hg).2 hj0
    rw [moved_gate n C r g j hj0]
    refine ⟨?_, ?_, ?_⟩
    · simpa only [rename] using hAO.1 (gateAt C (back r g j)) (gateAt_mem hjold)
    · simpa [rename] using hAO.2.2 _ (gateAt_mem hjold)
    · intro w hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      have hlt := mapWire_before hrg (hAO.2.1 _ hjold v hv)
        (fun he => hread _ hjold (he ▸ hv))
      simpa only [fwd_back r g j hrg] using hlt
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    have hx := (hidx j hj).1
    rwa [gateAt_eq hj] at hx
  · intro j hj w hw
    exact (hidx j hj).2.2 w hw
  · intro q hq
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    have hx := (hidx j hj).2.1
    rwa [gateAt_eq hj] at hx

lemma moved_gate_values {n : ℕ} (C : Circuit) (r g : ℕ) (hAO : IsAO2 n C)
    (hrg : r < g) (hg : g ≤ C.gates.length)
    (hread : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g)
    (x : Fin n → Bool) : ∀ j < C.gates.length,
      val (move n C r g) (List.ofFn x) (n + j) =
        val C (List.ofFn x) (n + back r g j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    have hjold : back r g j < C.gates.length := (back_lt hrg hg).2 hj
    rw [val_gate (n := n) (by simp) (by simpa only [move_length] using hj),
      moved_gate n C r g j hj, val_gate (n := n) (by simp) hjold]
    simp only [rename, List.map_map]
    congr 1
    apply List.map_congr_left
    intro w hw
    have hwold := hAO.2.1 _ hjold w hw
    have hwnew : mapWire n r g w < n + j := by
      have hlt := mapWire_before hrg hwold (fun he => hread _ hjold (he ▸ hw))
      simpa only [fwd_back r g j hrg] using hlt
    simp only [ite_eq_left hwold, ite_eq_left hwnew, Function.comp_apply]
    by_cases hwn : w < n
    · rw [mapWire_input hwn, val_input (n := n) (by simp) hwn,
        val_input (n := n) (by simp) hwn]
    · have hwrepr : w = n + (w - n) := by omega
      rw [hwrepr, mapWire_gate]
      rw [hwrepr, mapWire_gate] at hwnew
      rw [ih (fwd r g (w - n)) (by omega) (by omega), back_fwd r g (w - n) hrg]

lemma moved_wire_values {n : ℕ} (C : Circuit) (r g : ℕ) (hAO : IsAO2 n C)
    (hrg : r < g) (hg : g ≤ C.gates.length)
    (hread : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g)
    (x : Fin n → Bool) (w : ℕ) :
    val (move n C r g) (List.ofFn x) (mapWire n r g w) = val C (List.ofFn x) w := by
  by_cases hwn : w < n
  · rw [mapWire_input hwn, val_input (n := n) (by simp) hwn,
      val_input (n := n) (by simp) hwn]
  by_cases hwC : w < n + C.gates.length
  · have hwrepr : w = n + (w - n) := by omega
    rw [hwrepr, mapWire_gate,
      moved_gate_values C r g hAO hrg hg hread x (fwd r g (w - n))
        ((fwd_lt hrg hg).2 (by omega)), back_fwd r g (w - n) hrg]
  · have hwm : n + (move n C r g).gates.length ≤ mapWire n r g w := by
      rw [move_length]
      have := (mapWire_lt (n := n) (w := w) hrg hg).not.mpr hwC
      omega
    rw [val_ge (n := n) (by simp) hwm, val_ge (n := n) (by simp) (by omega)]

lemma move_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r g : ℕ) (hL : IsLeastAO G C)
    (hrg : r < g) (hg : g ≤ C.gates.length)
    (hread : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g) :
    IsLeastAO G (move n C r g) := by
  refine ⟨move_ao C r g hL.1 hrg hg hread, ?_, ?_⟩
  · funext x
    change val (move n C r g) (List.ofFn x) (mapWire n r g C.output) = _
    rw [moved_wire_values C r g hL.1 hrg hg hread x C.output]
    exact congrFun hL.2.1 x
  · intro D hD hDF
    rw [move_size]
    exact hL.2.2 D hD hDF

lemma moved_junk_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r g : ℕ) (hAO : IsAO2 n C)
    (hrg : r < g) (hg : g ≤ C.gates.length)
    (hread : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g) (j : ℕ) :
    fwd r g j ∈ junk G (move n C r g) ↔ j ∈ junk G C := by
  by_cases hj : j < C.gates.length
  · have hvals : ∀ x : Fin n → Bool,
        gateVal n (move n C r g) (fwd r g j) x = gateVal n C j x := by
      intro x
      simpa only [mapWire_gate, gateVal_eq_val] using moved_wire_values C r g hAO hrg hg hread x (n + j)
    simp only [mem_junk_iff, move_length, fwd_lt hrg hg,
      moved_original_gate n C r g j hrg hg hj, rename, hvals]
  · simp only [mem_junk_iff, move_length, fwd_lt hrg hg, hj, false_and]

lemma moved_junk_image {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r g : ℕ) (hAO : IsAO2 n C)
    (hrg : r < g) (hg : g ≤ C.gates.length)
    (hread : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g) :
    junk G (move n C r g) = (junk G C).image (fwd r g) := by
  apply Finset.ext
  intro j
  constructor
  · intro hj
    apply Finset.mem_image.mpr
    refine ⟨back r g j, ?_, fwd_back r g j hrg⟩
    apply (moved_junk_iff G C r g hAO hrg hg hread (back r g j)).mp
    simpa only [fwd_back r g j hrg] using hj
  · intro hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    exact (moved_junk_iff G C r g hAO hrg hg hread k).mpr hk

lemma moved_junk_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r g : ℕ) (hAO : IsAO2 n C)
    (hrg : r < g) (hg : g ≤ C.gates.length)
    (hread : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g) :
    (junk G (move n C r g)).card = (junk G C).card := by
  rw [moved_junk_image G C r g hAO hrg hg hread,
    Finset.card_image_of_injective _ (fwd_injective hrg)]

lemma fwd_r (r g : ℕ) : fwd r g r = g - 1 := by simp [fwd]

lemma fwd_g (r g : ℕ) (hrg : r < g) : fwd r g g = g := by
  simp [fwd, Nat.ne_of_gt hrg]

lemma mapWire_eq_gate {n r g w j : ℕ} (hrg : r < g) :
    mapWire n r g w = n + fwd r g j ↔ w = n + j := by
  by_cases hwn : w < n
  · rw [mapWire_input hwn]
    constructor <;> intro he <;> omega
  · have hwrepr : w = n + (w - n) := by omega
    rw [hwrepr, mapWire_gate]
    constructor
    · intro he
      have hidx := fwd_injective hrg (Nat.add_left_cancel he)
      omega
    · intro he
      have : w - n = j := by omega
      rw [this]

lemma moved_readers {n : ℕ} (C : Circuit) (r g : ℕ)
    (hrg : r < g) (hg : g < C.gates.length)
    (hread : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g)
    (hrgmem : n + r ∈ (gateAt C g).inputs) :
    readers n (move n C r g) (fwd r g r) = {g} := by
  apply Finset.ext
  intro j
  simp only [readers, Finset.mem_filter, Finset.mem_range, move_length, Finset.mem_singleton]
  constructor
  · rintro ⟨hj, hw⟩
    rw [moved_gate n C r g j hj] at hw
    obtain ⟨w, hwold, he⟩ := List.mem_map.mp hw
    have hweq : w = n + r := (mapWire_eq_gate hrg).mp he
    have hjold : back r g j < C.gates.length := (back_lt hrg (by omega)).2 hj
    have hold := hread _ hjold (hweq ▸ hwold)
    have hh := congrArg (fwd r g) hold
    simpa only [fwd_back r g j hrg, fwd_g r g hrg] using hh
  · intro hjg
    subst j
    refine ⟨hg, ?_⟩
    have he := moved_original_gate n C r g g hrg (by omega) hg
    rw [fwd_g r g hrg] at he
    rw [he]
    apply List.mem_map.mpr
    exact ⟨n + r, hrgmem, mapWire_gate n r g r⟩

lemma mapWire_before_private {n r g w : ℕ} (hrg : r < g)
    (hw : w < n + g) (hwr : w ≠ n + r) :
    mapWire n r g w < n + fwd r g r := by
  rw [fwd_r]
  by_cases hwn : w < n
  · rw [mapWire_input hwn]
    omega
  · have hwrepr : w = n + (w - n) := by omega
    rw [hwrepr, mapWire_gate]
    have hne : w - n ≠ r := by omega
    unfold fwd
    split_ifs <;> omega

lemma absorption_without_order
    (firstRung : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (color : Fin n → Bool),
      (∀ u v, G.Adj u v → color u ≠ color v) → NoFourCycle G → IsLeastAO G C →
      (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v) (h4 : NoFourCycle G)
    (hL : IsLeastAO G C) (hcard : (junk G C).card = 2)
    (r s g t u v : ℕ) (hgJ : g ∈ junk G C) (hrg : r < g) (hsg : s < g)
    (hr : gateAt C r = ⟨GateOp.or, [t, u]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, v]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hread : readers n C r = {g})
    (hclean : ∀ x : Fin n → Bool, wireVal n C u x = true → wireVal n C v x = true →
      graphFun G ∅ x = true) : False := by
  have hg : g < C.gates.length := (mem_junk_iff G C g).mp hgJ |>.1
  have hread' : ∀ j < C.gates.length, n + r ∈ (gateAt C j).inputs → j = g := by
    intro j hj hw
    have hjmem : j ∈ readers n C r := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hw⟩
    simpa only [hread, Finset.mem_singleton] using hjmem
  have hML := move_least G C r g hL hrg (by omega) hread'
  have hMJ : (junk G (move n C r g)).card = 2 := by
    rw [moved_junk_card G C r g hL.1 hrg (by omega) hread', hcard]
  have hgMJ : g ∈ junk G (move n C r g) := by
    have hj := (moved_junk_iff G C r g hL.1 hrg (by omega) hread' g).mpr hgJ
    simpa only [fwd_g r g hrg] using hj
  have hrM : gateAt (move n C r g) (fwd r g r) =
      ⟨GateOp.or, [mapWire n r g t, mapWire n r g u]⟩ := by
    rw [moved_original_gate n C r g r hrg (by omega) (by omega), hr]
    rfl
  have hsM : gateAt (move n C r g) (fwd r g s) =
      ⟨GateOp.or, [mapWire n r g t, mapWire n r g v]⟩ := by
    rw [moved_original_gate n C r g s hrg (by omega) (by omega), hs]
    rfl
  have hgM : gateAt (move n C r g) g =
      ⟨GateOp.and, [n + fwd r g r, n + fwd r g s]⟩ := by
    have he := moved_original_gate n C r g g hrg (by omega) hg
    rw [fwd_g r g hrg] at he
    rw [he, hgate]
    simp [rename, mapWire_gate]
  have hvM : mapWire n r g v < n + fwd r g r := by
    apply mapWire_before_private hrg
    · have hv : v < n + s := hL.1.2.1 s (by omega) v (by rw [hs]; simp)
      omega
    · intro hv
      have hsg' := hread' s (by omega) (by rw [hs, hv]; simp)
      omega
  have hreadM : readers n (move n C r g) (fwd r g r) = {g} :=
    moved_readers C r g hrg hg hread' (by rw [hgate]; simp)
  apply WireAbsorption.absorption_contradiction firstRung G (move n C r g) color hbip h4 hML hMJ
    (fwd r g r) (fwd r g s) g (mapWire n r g t) (mapWire n r g u) (mapWire n r g v)
    hgMJ ((fwd_lt hrg le_rfl).2 hrg) ((fwd_lt hrg le_rfl).2 hsg)
    hvM hrM hsM hgM hreadM
  intro x huM hvM'
  change val (move n C r g) (List.ofFn x) (mapWire n r g u) = true at huM
  change val (move n C r g) (List.ofFn x) (mapWire n r g v) = true at hvM'
  rw [moved_wire_values C r g hL.1 hrg (by omega) hread' x u] at huM
  rw [moved_wire_values C r g hL.1 hrg (by omega) hread' x v] at hvM'
  exact hclean x huM hvM'

end PEqualNP.Outside.L_meta_5012.PrivateMove


namespace PEqualNP.Outside.L_meta_5012.AndSwap

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Absorption

def patch (C : Circuit) (g t h : ℕ) : Circuit :=
  ⟨C.gates.set g ⟨GateOp.and, [h, t]⟩, C.output⟩

lemma patch_length (C : Circuit) (g t h : ℕ) :
    (patch C g t h).gates.length = C.gates.length := by simp [patch]

lemma patch_size (C : Circuit) (g t h : ℕ) :
    (patch C g t h).size = C.size := by simp [patch, Circuit.size]

lemma patch_g (C : Circuit) (g t h : ℕ) (hg : g < C.gates.length) :
    gateAt (patch C g t h) g = ⟨GateOp.and, [h, t]⟩ := by
  simp [gateAt, patch, List.getD_eq_getElem?_getD, hg]

lemma patch_other (C : Circuit) (g t h j : ℕ) (hjg : j ≠ g) :
    gateAt (patch C g t h) j = gateAt C j := by
  simp [gateAt, patch, List.getD_eq_getElem?_getD, hjg.symm]

lemma patch_ao {n : ℕ} (C : Circuit) (g t h : ℕ)
    (hAO : IsAO2 n C) (ht : t < n + g) (hh : h < n + g) :
    IsAO2 n (patch C g t h) := by
  have hidx : ∀ j < (patch C g t h).gates.length,
      ((gateAt (patch C g t h) j).op = GateOp.and ∨
        (gateAt (patch C g t h) j).op = GateOp.or) ∧
      (gateAt (patch C g t h) j).inputs.length = 2 ∧
      ∀ w ∈ (gateAt (patch C g t h) j).inputs, w < n + j := by
    intro j hj
    have hj0 : j < C.gates.length := by simpa only [patch_length] using hj
    by_cases hjg : j = g
    · subst j
      rw [patch_g C g t h hj0]
      refine ⟨Or.inl rfl, rfl, ?_⟩
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> assumption
    rw [patch_other C g t h j hjg]
    exact ⟨hAO.1 _ (gateAt_mem hj0), hAO.2.2 _ (gateAt_mem hj0), hAO.2.1 j hj0⟩
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    have hx := (hidx j hj).1
    rwa [gateAt_eq hj] at hx
  · intro j hj w hw
    exact (hidx j hj).2.2 w hw
  · intro q hq
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    have hx := (hidx j hj).2.1
    rwa [gateAt_eq hj] at hx

lemma patched_gate_values {n : ℕ} (C : Circuit) (g t h : ℕ)
    (hAO : IsAO2 n C) (ht : t < n + g) (hh : h < n + g)
    (hgate : gateAt C g = ⟨GateOp.and, [t, h]⟩)
    (x : Fin n → Bool) : ∀ j < C.gates.length,
      val (patch C g t h) (List.ofFn x) (n + j) = val C (List.ofFn x) (n + j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    have earlier : ∀ w, w < n + j →
        val (patch C g t h) (List.ofFn x) w = val C (List.ofFn x) w := by
      intro w hw
      by_cases hwn : w < n
      · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
      · have hwrepr : w = n + (w - n) := by omega
        rw [hwrepr]
        exact ih (w - n) (by omega) (by omega)
    by_cases hjg : j = g
    · subst j
      rw [binary_eval _ g h t GateOp.and (by simpa only [patch_length] using hj)
        (patch_g C g t h hj) hh ht, earlier h hh, earlier t ht,
        binary_eval C g t h GateOp.and hj hgate ht hh]
      simp [GateOp.eval, Bool.and_comm]
    rw [val_gate (n := n) (by simp) (by simpa only [patch_length] using hj),
      val_gate (n := n) (by simp) hj, patch_other C g t h j hjg]
    congr 1
    apply List.map_congr_left
    intro w hw
    have hwl : w < n + j := hAO.2.1 j hj w hw
    simp only [ite_eq_left hwl]
    exact earlier w hwl

lemma patched_wire_values {n : ℕ} (C : Circuit) (g t h : ℕ)
    (hAO : IsAO2 n C) (ht : t < n + g) (hh : h < n + g)
    (hgate : gateAt C g = ⟨GateOp.and, [t, h]⟩)
    (x : Fin n → Bool) (w : ℕ) :
    val (patch C g t h) (List.ofFn x) w = val C (List.ofFn x) w := by
  by_cases hwn : w < n
  · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
  by_cases hwC : w < n + C.gates.length
  · have hwrepr : w = n + (w - n) := by omega
    rw [hwrepr]
    exact patched_gate_values C g t h hAO ht hh hgate x (w - n) (by omega)
  · rw [val_ge (n := n) (by simp) (by rw [patch_length]; omega),
      val_ge (n := n) (by simp) (by omega)]

lemma patch_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g t h : ℕ) (hL : IsLeastAO G C)
    (ht : t < n + g) (hh : h < n + g)
    (hgate : gateAt C g = ⟨GateOp.and, [t, h]⟩) :
    IsLeastAO G (patch C g t h) := by
  refine ⟨patch_ao C g t h hL.1 ht hh, ?_, ?_⟩
  · funext x
    change val (patch C g t h) (List.ofFn x) C.output = _
    rw [patched_wire_values C g t h hL.1 ht hh hgate x C.output]
    exact congrFun hL.2.1 x
  · intro D hD hcD
    rw [patch_size]
    exact hL.2.2 D hD hcD


lemma patch_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g t h : ℕ) (hAO : IsAO2 n C)
    (ht : t < n + g) (hh : h < n + g)
    (hgate : gateAt C g = ⟨GateOp.and, [t, h]⟩) :
    junk G (patch C g t h) = junk G C := by
  apply Finset.ext
  intro j
  by_cases hj : j < C.gates.length
  · have hvals : ∀ x : Fin n → Bool,
        gateVal n (patch C g t h) j x = gateVal n C j x := by
      intro x
      exact patched_wire_values C g t h hAO ht hh hgate x (n + j)
    have hop : (gateAt (patch C g t h) j).op = (gateAt C j).op := by
      by_cases hjg : j = g
      · subst j
        rw [patch_g C g t h hj, hgate]
      · rw [patch_other C g t h j hjg]
    simp only [mem_junk_iff, patch_length, hop, hvals]
  · simp only [mem_junk_iff, patch_length, hj, false_and]

lemma patch_readers {n : ℕ} (C : Circuit) (g t h k : ℕ)
    (hgate : gateAt C g = ⟨GateOp.and, [t, h]⟩) :
    readers n (patch C g t h) k = readers n C k := by
  apply Finset.ext
  intro j
  simp only [readers, Finset.mem_filter, Finset.mem_range, patch_length]
  by_cases hj : j < C.gates.length
  · simp only [hj, true_and]
    by_cases hjg : j = g
    · subst j
      rw [patch_g C g t h hj, hgate]
      simp [or_comm]
    · rw [patch_other C g t h j hjg]
  · simp [hj]

end PEqualNP.Outside.L_meta_5012.AndSwap

namespace PEqualNP.Outside.L_meta_5012.PrivateMove

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Absorption

lemma right_absorption_without_order
    (firstRung : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (color : Fin n → Bool),
      (∀ u v, G.Adj u v → color u ≠ color v) → NoFourCycle G → IsLeastAO G C →
      (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v) (h4 : NoFourCycle G)
    (hL : IsLeastAO G C) (hcard : (junk G C).card = 2)
    (r s g t u v : ℕ) (hgJ : g ∈ junk G C) (hrg : r < g) (hsg : s < g)
    (hr : gateAt C r = ⟨GateOp.or, [t, u]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, v]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hread : readers n C s = {g})
    (hclean : ∀ x : Fin n → Bool, wireVal n C u x = true → wireVal n C v x = true →
      graphFun G ∅ x = true) : False := by
  have hg : g < C.gates.length := (mem_junk_iff G C g).mp hgJ |>.1
  have hDL := AndSwap.patch_least G C g (n + r) (n + s) hL (by omega) (by omega) hgate
  have hDJ := AndSwap.patch_junk G C g (n + r) (n + s) hL.1 (by omega) (by omega) hgate
  have hrD : gateAt (AndSwap.patch C g (n + r) (n + s)) r = ⟨GateOp.or, [t, u]⟩ := by
    rw [AndSwap.patch_other C g (n + r) (n + s) r (by omega), hr]
  have hsD : gateAt (AndSwap.patch C g (n + r) (n + s)) s = ⟨GateOp.or, [t, v]⟩ := by
    rw [AndSwap.patch_other C g (n + r) (n + s) s (by omega), hs]
  have hgD := AndSwap.patch_g C g (n + r) (n + s) hg
  have hreadD : readers n (AndSwap.patch C g (n + r) (n + s)) s = {g} := by
    rw [AndSwap.patch_readers C g (n + r) (n + s) s hgate, hread]
  apply absorption_without_order firstRung G (AndSwap.patch C g (n + r) (n + s)) color
    hbip h4 hDL (by rw [hDJ]; exact hcard) s r g t v u (by rw [hDJ]; exact hgJ)
    hsg hrg hsD hrD hgD hreadD
  intro x hv hu
  change val (AndSwap.patch C g (n + r) (n + s)) (List.ofFn x) v = true at hv
  change val (AndSwap.patch C g (n + r) (n + s)) (List.ofFn x) u = true at hu
  rw [AndSwap.patched_wire_values C g (n + r) (n + s) hL.1 (by omega) (by omega) hgate x v] at hv
  rw [AndSwap.patched_wire_values C g (n + r) (n + s) hL.1 (by omega) (by omega) hgate x u] at hu
  exact hclean x hu hv

lemma either_absorption_without_order
    (firstRung : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (color : Fin n → Bool),
      (∀ u v, G.Adj u v → color u ≠ color v) → NoFourCycle G → IsLeastAO G C →
      (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v) (h4 : NoFourCycle G)
    (hL : IsLeastAO G C) (hcard : (junk G C).card = 2)
    (r s g t u v : ℕ) (hgJ : g ∈ junk G C) (hrg : r < g) (hsg : s < g)
    (hr : gateAt C r = ⟨GateOp.or, [t, u]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, v]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hread : readers n C r = {g} ∨ readers n C s = {g})
    (hclean : ∀ x : Fin n → Bool, wireVal n C u x = true → wireVal n C v x = true →
      graphFun G ∅ x = true) : False := by
  rcases hread with hread | hread
  · exact absorption_without_order firstRung G C color hbip h4 hL hcard
      r s g t u v hgJ hrg hsg hr hs hgate hread hclean
  · exact right_absorption_without_order firstRung G C color hbip h4 hL hcard
      r s g t u v hgJ hrg hsg hr hs hgate hread hclean

end PEqualNP.Outside.L_meta_5012.PrivateMove


namespace PEqualNP.Outside.L_meta_5012.Frontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma rawOr_singleton {n : ℕ} (B : Finset (Fin n)) (b : Fin n) :
    Overlap.rawOr B (pairInput b b) = decide (b ∈ B) := by
  simp [Overlap.rawOr, pairInput]

lemma clean_raw_cross {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B D : Finset (Fin n))
    (hclean : ∀ x : Fin n → Bool, Overlap.rawOr B x = true → Overlap.rawOr D x = true →
      graphFun G ∅ x = true) {b c : Fin n} (hb : b ∈ B) (hc : c ∈ D) : G.Adj b c := by
  apply (Overlap.graphFun_pair G b c).1
  apply hclean
  · exact Overlap.rawOr_true hb (by simp [pairInput])
  · exact Overlap.rawOr_true hc (by simp [pairInput])

lemma raw_residual_separation {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (g t : ℕ)
    (B D : Finset (Fin n)) (hg : g < C.gates.length) (ht : t < n + g)
    (heval : ∀ x : Fin n → Bool, gateVal n C g x =
      ((wireVal n C t x || Overlap.rawOr B x) && (wireVal n C t x || Overlap.rawOr D x)))
    (hclean : ∀ x : Fin n → Bool, Overlap.rawOr B x = true → Overlap.rawOr D x = true →
      graphFun G ∅ x = true) :
    ∃ b ∈ B, ∃ c ∈ D, G.Adj b c ∧ b ∉ D ∧ c ∉ B ∧
      wireVal n C t (pairInput b b) = false ∧ wireVal n C t (pairInput c c) = false := by
  have hsmall : ∀ x : Fin n → Bool, wireVal n C t x = true → gateVal n C g x = true := by
    intro x hx
    rw [heval, hx]
    rfl
  obtain ⟨p, q, hpq, hgval, htval⟩ :=
    CriticalEdge.least_edge_separates_earlier_wire G C hL g t ht hg hsmall
  rw [heval, htval] at hgval
  simp only [Bool.false_or, Bool.and_eq_true] at hgval
  obtain ⟨b, hb, hbpq⟩ : ∃ b ∈ B, pairInput p q b = true := by
    simpa only [Overlap.rawOr, decide_eq_true_eq] using hgval.1
  obtain ⟨c, hc, hcpq⟩ : ∃ c ∈ D, pairInput p q c = true := by
    simpa only [Overlap.rawOr, decide_eq_true_eq] using hgval.2
  have hsingleton (a : Fin n) (ha : pairInput p q a = true) :
      wireVal n C t (pairInput a a) = false := by
    cases hsingle : wireVal n C t (pairInput a a) with
    | false => rfl
    | true =>
      have hmono := wire_mono C hL.1 (pairInput a a) (pairInput p q)
        (by
          intro i hi
          have hia : i = a := by simpa [pairInput] using hi
          simpa only [hia] using ha) t (by omega) hsingle
      rw [htval] at hmono
      cases hmono
  refine ⟨b, hb, c, hc, clean_raw_cross G B D hclean hb hc, ?_, ?_, hsingleton b hbpq, hsingleton c hcpq⟩
  · intro hbd
    exact G.irrefl (clean_raw_cross G B D hclean hb hbd)
  · intro hcb
    exact G.irrefl (clean_raw_cross G B D hclean hcb hc)

lemma raw_diamond_root_sole {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hTop : TopForm G C)
    (h g r s t : ℕ) (B D : Finset (Fin n)) (b : Fin n)
    (hg : g < C.gates.length) (hrg : r < g) (hhr : h < r)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩ ∨
      gateAt C g = ⟨GateOp.and, [n + s, n + r]⟩)
    (hJ : ∀ j ∈ junk G C, j = g ∨ j = h)
    (hdom : ∀ x : Fin n → Bool, gateVal n C h x = true → wireVal n C t x = true)
    (hrval : ∀ x : Fin n → Bool, gateVal n C r x = (wireVal n C t x || Overlap.rawOr B x))
    (hsval : ∀ x : Fin n → Bool, gateVal n C s x = (wireVal n C t x || Overlap.rawOr D x))
    (hb : b ∈ B) (hbn : b ∉ D) (htsingle : wireVal n C t (pairInput b b) = false)
    (hnofilter : ¬ ∃ w, Diamond.RootFilter G (wireVal n C t) b w) :
    readers n C r = {g} := by
  have hrtrue : gateVal n C r (pairInput b b) = true := by
    rw [hrval, rawOr_singleton]
    simp [hb]
  have hsfalse : gateVal n C s (pairInput b b) = false := by
    rw [hsval, htsingle, rawOr_singleton]
    simp [hbn]
  apply sole_reader_of_dominated_junk G C hL hTop h g r s hg hrg hhr hgate hJ
  · intro j hj x hx
    rcases hJ j hj with hjg | hjh
    · subst j
      have hop : (gateAt C g).op = GateOp.and := by rcases hgate with he | he <;> rw [he]
      have hin : n + r ∈ (gateAt C g).inputs := by rcases hgate with he | he <;> rw [he] <;> simp
      exact ((Trace.val_and (n := n) (by simp) hg hop).1 hx (n + r) hin).2
    · subst j
      rw [hrval, hdom x hx]
      rfl
  · intro w hw
    apply hnofilter
    refine ⟨w, ?_⟩
    intro x hx hxw
    apply hw x ?_ hxw
    rw [hrval]
    simp only [Bool.or_eq_true] at hx ⊢
    rcases hx with ht | hbtrue
    · exact Or.inl ht
    · exact Or.inr (Overlap.rawOr_true hb hbtrue)
  · exact ⟨pairInput b b, hrtrue, Absorption.graphFun_singleton G b⟩
  · intro hp
    have hs := Trace.orStep_up (n := n) (by simp) hp hrtrue
    change gateVal n C s (pairInput b b) = true at hs
    rw [hsfalse] at hs
    cases hs

lemma raw_diamond_root_choice {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C) (hTop : TopForm G C)
    (h g r s t u v : ℕ) (B D : Finset (Fin n)) (d : Fin n)
    (hg : g < C.gates.length) (hrg : r < g) (hsg : s < g) (hhr : h < r) (hhs : h < s)
    (hr : gateAt C r = ⟨GateOp.or, [t, u]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, v]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hJ : ∀ j ∈ junk G C, j = g ∨ j = h)
    (hdom : ∀ x : Fin n → Bool, gateVal n C h x = true → wireVal n C t x = true)
    (hlower : ∀ x : Fin n → Bool, x d = true → wireVal n C t x = true)
    (huval : ∀ x : Fin n → Bool, wireVal n C u x = Overlap.rawOr B x)
    (hvval : ∀ x : Fin n → Bool, wireVal n C v x = Overlap.rawOr D x)
    (hclean : ∀ x : Fin n → Bool, wireVal n C u x = true → wireVal n C v x = true →
      graphFun G ∅ x = true) : readers n C r = {g} ∨ readers n C s = {g} := by
  have htr : t < n + r := hL.1.2.1 r (by omega) t (by rw [hr]; simp)
  have hts : t < n + s := hL.1.2.1 s (by omega) t (by rw [hs]; simp)
  have hur : u < n + r := hL.1.2.1 r (by omega) u (by rw [hr]; simp)
  have hvs : v < n + s := hL.1.2.1 s (by omega) v (by rw [hs]; simp)
  have hrval : ∀ x : Fin n → Bool, gateVal n C r x = (wireVal n C t x || Overlap.rawOr B x) := by
    intro x
    have he := WireAbsorption.or_wire_eval C r t u (by omega) hr htr hur x
    change gateVal n C r x = (wireVal n C t x || wireVal n C u x) at he
    simpa only [huval] using he
  have hsval : ∀ x : Fin n → Bool, gateVal n C s x = (wireVal n C t x || Overlap.rawOr D x) := by
    intro x
    have he := WireAbsorption.or_wire_eval C s t v (by omega) hs hts hvs x
    change gateVal n C s x = (wireVal n C t x || wireVal n C v x) at he
    simpa only [hvval] using he
  have heval : ∀ x : Fin n → Bool, gateVal n C g x =
      ((wireVal n C t x || Overlap.rawOr B x) && (wireVal n C t x || Overlap.rawOr D x)) := by
    intro x
    have he := WireAbsorption.original_g_eval C r s g t u v hg hrg hsg htr hts hur hvs hr hs hgate x
    change gateVal n C g x =
      ((wireVal n C t x || wireVal n C u x) && (wireVal n C t x || wireVal n C v x)) at he
    simpa only [huval, hvval] using he
  have hclean' : ∀ x : Fin n → Bool, Overlap.rawOr B x = true → Overlap.rawOr D x = true →
      graphFun G ∅ x = true := by
    intro x hx hy
    exact hclean x (by rw [huval]; exact hx) (by rw [hvval]; exact hy)
  obtain ⟨b, hb, c, hc, hbc, hbn, hcn, htb, htc⟩ :=
    raw_residual_separation G C hL g t B D hg (by omega) heval hclean'
  rcases Diamond.one_root_without_filters G color hbip (wireVal n C t) d b c hlower hbc with hnr | hns
  · exact Or.inl (raw_diamond_root_sole G C hL hTop h g r s t B D b hg hrg hhr
      (Or.inl hgate) hJ hdom hrval hsval hb hbn htb hnr)
  · exact Or.inr (raw_diamond_root_sole G C hL hTop h g s r t D B c hg hsg hhs
      (Or.inr hgate) hJ hdom hsval hrval hc hcn htc hns)

lemma raw_common_diamond_no_two_junk
    (firstRung : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (color : Fin n → Bool),
      (∀ u v, G.Adj u v → color u ≠ color v) → NoFourCycle G → IsLeastAO G C →
      (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v) (h4 : NoFourCycle G)
    (hL : IsLeastAO G C) (hTop : TopForm G C) (hcard : (junk G C).card = 2)
    (h g r s t u v : ℕ) (B D : Finset (Fin n)) (d : Fin n) (hgJ : g ∈ junk G C)
    (hrg : r < g) (hsg : s < g) (hhr : h < r) (hhs : h < s)
    (hr : gateAt C r = ⟨GateOp.or, [t, u]⟩)
    (hs : gateAt C s = ⟨GateOp.or, [t, v]⟩)
    (hgate : gateAt C g = ⟨GateOp.and, [n + r, n + s]⟩)
    (hJ : ∀ j ∈ junk G C, j = g ∨ j = h)
    (hdom : ∀ x : Fin n → Bool, gateVal n C h x = true → wireVal n C t x = true)
    (hlower : ∀ x : Fin n → Bool, x d = true → wireVal n C t x = true)
    (huval : ∀ x : Fin n → Bool, wireVal n C u x = Overlap.rawOr B x)
    (hvval : ∀ x : Fin n → Bool, wireVal n C v x = Overlap.rawOr D x)
    (hclean : ∀ x : Fin n → Bool, wireVal n C u x = true → wireVal n C v x = true →
      graphFun G ∅ x = true) : False := by
  have hg : g < C.gates.length := (Absorption.mem_junk_iff G C g).mp hgJ |>.1
  exact PrivateMove.either_absorption_without_order firstRung G C color hbip h4 hL hcard
    r s g t u v hgJ hrg hsg hr hs hgate
    (raw_diamond_root_choice G color hbip C hL hTop h g r s t u v B D d hg
      hrg hsg hhr hhs hr hs hgate hJ hdom hlower huval hvval hclean) hclean

end PEqualNP.Outside.L_meta_5012.Frontier


namespace PEqualNP.Outside.L_meta_5012.OrFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma or_frontier_of_live {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (hlive : ∀ q < C.gates.length,
      C.output = n + q ∨ ∃ j < C.gates.length, n + q ∈ (gateAt C j).inputs)
    (q : ℕ) (hq : q < C.gates.length) :
    Relation.ReflTransGen (Critical.Base.OrStep n C) C.output (n + q) ∨
      ∃ (a : ℕ) (b : Fin 2), a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
        Relation.ReflTransGen (Critical.Base.OrStep n C) (opnd C a b) (n + q) := by
  have aux : ∀ d q, C.gates.length - q = d → q < C.gates.length →
      Relation.ReflTransGen (Critical.Base.OrStep n C) C.output (n + q) ∨
        ∃ (a : ℕ) (b : Fin 2), a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
          Relation.ReflTransGen (Critical.Base.OrStep n C) (opnd C a b) (n + q) := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro q hd hq
      rcases hlive q hq with hout | ⟨j, hj, hread⟩
      · exact Or.inl (by rw [hout])
      · have hqj := Frontier.read_index_lt hAO hj hread
        rcases Frontier.gate_op_cases hAO hj with hand | hor
        · obtain ⟨_, hin, _, _, _⟩ := CriticalEdge.gate2 hAO hj
          have hread' : n + q = opnd C j 0 ∨ n + q = opnd C j 1 := by
            rw [hin] at hread
            simpa using hread
          rcases hread' with he | he
          · exact Or.inr ⟨j, 0, hj, hand, by rw [← he]⟩
          · exact Or.inr ⟨j, 1, hj, hand, by rw [← he]⟩
        · have hstep : Critical.Base.OrStep n C (n + j) (n + q) :=
            ⟨j, hj, rfl, hor, hread, by omega⟩
          rcases ih (C.gates.length - j) (by omega) j rfl hj with hout | ⟨a, b, ha, hand, hp⟩
          · exact Or.inl (hout.tail hstep)
          · exact Or.inr ⟨a, b, ha, hand, hp.tail hstep⟩
  exact aux _ q rfl hq

lemma least_or_frontier {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (q : ℕ) (hq : q < C.gates.length) :
    Relation.ReflTransGen (Critical.Base.OrStep n C) C.output (n + q) ∨
      ∃ (a : ℕ) (b : Fin 2), a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
        Relation.ReflTransGen (Critical.Base.OrStep n C) (opnd C a b) (n + q) :=
  or_frontier_of_live C hL.1 (Frontier.least_live G C hL) q hq

end PEqualNP.Outside.L_meta_5012.OrFrontier


namespace PEqualNP.Outside.L_meta_5012.OverlapCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo
open IndependentDescent CleanReplacement

lemma critical_overlap_cover {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (hF : circuitFun n C = graphFun G ∅) (hT : TopForm G C)
    {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
    (hjk : ¬ InCone n C j k) (hkj : ¬ InCone n C k j)
    (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k)
    (z : Fin n) (hW : wmax G C j = {z})
    (hzOut : z ∉ side (n := n) C j 0 ∪ side (n := n) C j 1)
    (u v : Fin n) (huv : G.Adj u v)
    (hLost : circuitFun n (patch C j off) (pairInput u v) = false) :
    pairInput u v z = true ∧
      ∃ i ∈ side (n := n) C j 0 ∩ side (n := n) C j 1,
        pairInput u v i = true := by
  let P := side (n := n) C j 0
  let Q := side (n := n) C j 1
  have heval (x : Fin n → Bool) : gateVal n C j x = product P Q x :=
    RawOperands.independent_product G C hAO hT j k hJ hjk hkj j (Or.inl rfl) x
  have hJ' : junk G C = {k,j} := by rw [hJ, Finset.pair_comm]
  obtain ⟨hjv, hFilter⟩ := Critical.critical_edge_useful hAO hF hT hJ'
    (Ne.symm hne) hjk hNoCommon u v huv hLost
  have hp : product P Q (pairInput u v) = true := (heval _).symm.trans hjv
  rcases hFilter with hu | hv
  · have hueq : u = z := by simpa [hW] using hu
    subst u
    have hvI := product_pair_overlap_of_outside P Q hzOut hp
    exact ⟨by simp [pairInput], v, hvI, by simp [pairInput]⟩
  · have hveq : v = z := by simpa [hW] using hv
    subst v
    have hSwap : pairInput u z = pairInput z u := by
      funext a
      simp [pairInput, or_comm]
    rw [hSwap] at hp
    have huI := product_pair_overlap_of_outside P Q hzOut hp
    exact ⟨by simp [pairInput], u, huI, by simp [pairInput]⟩

end PEqualNP.Outside.L_meta_5012.OverlapCase


namespace PEqualNP.Outside.L_meta_5012.OverlapCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

lemma both_large_overlap_no_opposite {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C)
    {j k : ℕ} (hJ : junk G C = {j,k})
    (hjk : ¬ InCone n C j k) (hkj : ¬ InCone n C k j) (h4 : NoFourCycle G)
    (hLargeJ : 2 ≤ (side (n := n) C j 0 ∩ side (n := n) C j 1).card)
    (hLargeK : 2 ≤ (side (n := n) C k 0 ∩ side (n := n) C k 1).card) :
    ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k := by
  intro a ha b hjr hkr
  have hevalJ (x : Fin n → Bool) : gateVal n C j x =
      IndependentDescent.product (side (n := n) C j 0) (side (n := n) C j 1) x :=
    RawOperands.independent_product G C hAO hT j k hJ hjk hkj j (Or.inl rfl) x
  have hevalK (x : Fin n → Bool) : gateVal n C k x =
      IndependentDescent.product (side (n := n) C k 0) (side (n := n) C k 1) x :=
    RawOperands.independent_product G C hAO hT j k hJ hjk hkj k (Or.inr rfl) x
  have hClean : Overlap.CleanMutual G (side (n := n) C j 0) (side (n := n) C j 1)
      (side (n := n) C k 0) (side (n := n) C k 1) := by
    intro x hx
    have hv : Overlap.product (side (n := n) C j 0) (side (n := n) C j 1) x = true ∧
        Overlap.product (side (n := n) C k 0) (side (n := n) C k 1) x = true := by
      simpa only [Bool.and_eq_true] using hx
    have hjv : gateVal n C j x = true := by rw [hevalJ]; exact hv.1
    have hkv : gateVal n C k x = true := by rw [hevalK]; exact hv.2
    obtain ⟨haLen, haAnd, haBelow⟩ := Critical.Base.topData ha
    apply haBelow x
    apply (Critical.Base.andValOperands hAO haLen haAnd x).mpr
    intro c
    rcases Critical.Base.eitherOperand b c with rfl | rfl
    · exact Critical.Base.reachVal hjr hjv
    · exact Critical.Base.reachVal hkr hkv
  rcases Overlap.cleanMutual_small_overlap G _ _ _ _ h4 hClean with hSmall | hSmall <;>
    omega

end PEqualNP.Outside.L_meta_5012.OverlapCase


namespace PEqualNP.Outside.L_meta_5012.OrProjection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm
open Absorption

def internal (n : ℕ) (J : Finset ℕ) (w : ℕ) : Prop := n ≤ w ∧ w - n ∈ J

def rewire (n : ℕ) (J : Finset ℕ) (proxy : ℕ → ℕ) (w : ℕ) : ℕ :=
  if n ≤ w ∧ w - n ∈ J then w else proxy w

def project (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ) : Circuit :=
  ⟨C.gates.mapIdx (fun j gate =>
    if j ∈ J then ⟨GateOp.or, gate.inputs.map (rewire n J proxy)⟩ else gate), C.output⟩

lemma project_length (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ) :
    (project n C J proxy).gates.length = C.gates.length := by simp [project]

lemma project_size (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ) :
    (project n C J proxy).size = C.size := by simp [project, Circuit.size]

lemma project_gate (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (j : ℕ) (hj : j < C.gates.length) :
    gateAt (project n C J proxy) j =
      if j ∈ J then ⟨GateOp.or, (gateAt C j).inputs.map (rewire n J proxy)⟩ else gateAt C j := by
  rw [gateAt_eq (by simpa only [project_length] using hj), gateAt_eq hj]
  simp [project]

lemma project_ao (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (hAO : IsAO2 n C)
    (hback : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, rewire n J proxy w < n + j) :
    IsAO2 n (project n C J proxy) := by
  have hdata : ∀ j < (project n C J proxy).gates.length,
      ((gateAt (project n C J proxy) j).op = GateOp.and ∨
        (gateAt (project n C J proxy) j).op = GateOp.or) ∧
      (gateAt (project n C J proxy) j).inputs.length = 2 ∧
      ∀ w ∈ (gateAt (project n C J proxy) j).inputs, w < n + j := by
    intro j hj
    have hjC : j < C.gates.length := by simpa only [project_length] using hj
    rw [project_gate n C J proxy j hjC]
    split_ifs with hjJ
    · refine ⟨Or.inr rfl, ?_, ?_⟩
      · simpa using hAO.2.2 _ (gateAt_mem hjC)
      · intro w hw
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
        exact hback j hjJ u hu
    · exact ⟨hAO.1 _ (gateAt_mem hjC), hAO.2.2 _ (gateAt_mem hjC), hAO.2.1 j hjC⟩
  refine ⟨?_, ?_, ?_⟩
  · intro gate hgate
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hgate
    have h := (hdata j hj).1
    rwa [gateAt_eq hj] at h
  · intro j hj w hw
    exact (hdata j hj).2.2 w hw
  · intro gate hgate
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hgate
    have h := (hdata j hj).2.1
    rwa [gateAt_eq hj] at h

lemma project_protected_values (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (hAO : IsAO2 n C) (E : Finset ℕ) (hdis : Disjoint E J)
    (hclosed : ∀ j ∈ E, ∀ w ∈ (gateAt C j).inputs, n ≤ w → w - n ∈ E)
    (x : Fin n → Bool) :
    ∀ j < C.gates.length, j ∈ E →
      val (project n C J proxy) (List.ofFn x) (n + j) = val C (List.ofFn x) (n + j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hjE
    have hjJ : j ∉ J := fun hjJ => Finset.disjoint_left.mp hdis hjE hjJ
    have earlier : ∀ w ∈ (gateAt C j).inputs,
        val (project n C J proxy) (List.ofFn x) w = val C (List.ofFn x) w := by
      intro w hw
      by_cases hwn : w < n
      · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
      · have hwj := hAO.2.1 j hj w hw
        have hwrepr : w = n + (w - n) := by omega
        rw [hwrepr]
        exact ih (w - n) (by omega) (by omega) (hclosed j hjE w hw (by omega))
    rw [val_gate (n := n) (by simp) (by simpa only [project_length] using hj),
      val_gate (n := n) (by simp) hj, project_gate n C J proxy j hj, ite_eq_right hjJ]
    congr 1
    apply List.map_congr_left
    intro w hw
    have hwj := hAO.2.1 j hj w hw
    simp only [ite_eq_left hwj]
    exact earlier w hw

lemma project_protected_wire (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (hAO : IsAO2 n C) (E : Finset ℕ) (hdis : Disjoint E J)
    (hclosed : ∀ j ∈ E, ∀ w ∈ (gateAt C j).inputs, n ≤ w → w - n ∈ E)
    (x : Fin n → Bool) (w : ℕ) (hwE : n ≤ w → w - n ∈ E) :
    val (project n C J proxy) (List.ofFn x) w = val C (List.ofFn x) w := by
  by_cases hwn : w < n
  · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
  by_cases hwC : w < n + C.gates.length
  · have hwrepr : w = n + (w - n) := by omega
    rw [hwrepr]
    exact project_protected_values n C J proxy hAO E hdis hclosed x (w-n) (by omega) (hwE (by omega))
  · rw [val_ge (n := n) (by simp) (by rw [project_length]; omega),
      val_ge (n := n) (by simp) (by omega)]

def support (n : ℕ) (C : Circuit) (J : Finset ℕ) (boundary : ℕ → Finset (Fin n))
    (w : ℕ) : Finset (Fin n) :=
  if n ≤ w ∧ w - n ∈ J then
    (gateAt C (w-n)).inputs.foldr
      (fun u S => (if _hu : u < w then support n C J boundary u else ∅) ∪ S) ∅
  else boundary w
termination_by w

def rawOr {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ S, x a = true)

lemma rawOr_union {n : ℕ} (A B : Finset (Fin n)) (x : Fin n → Bool) :
    rawOr (A ∪ B) x = (rawOr A x || rawOr B x) := by
  simp [rawOr, Finset.mem_union, or_and_right, exists_or]

lemma support_outside (n : ℕ) (C : Circuit) (J : Finset ℕ) (boundary : ℕ → Finset (Fin n))
    (w : ℕ) (hw : ¬ internal n J w) : support n C J boundary w = boundary w := by
  change ¬ (n ≤ w ∧ w - n ∈ J) at hw
  rw [support, ite_eq_right hw]

lemma support_gate (n : ℕ) (C : Circuit) (J : Finset ℕ) (boundary : ℕ → Finset (Fin n))
    (j a b : ℕ) (hj : j ∈ J) (hinputs : (gateAt C j).inputs = [a,b])
    (ha : a < n+j) (hb : b < n+j) :
    support n C J boundary (n+j) =
      support n C J boundary a ∪ support n C J boundary b := by
  rw [support]
  simp only [Nat.le_add_right, Nat.add_sub_cancel_left, hj, and_self, ite_true, hinputs,
    List.foldr_cons, List.foldr_nil, dite_eq_left ha, dite_eq_left hb, Finset.union_empty]

lemma support_subset (n : ℕ) (C : Circuit) (J : Finset ℕ) (boundary : ℕ → Finset (Fin n))
    (hAO : IsAO2 n C) (hreal : ∀ j ∈ J, j < C.gates.length)
    (N : Finset (Fin n)) (hboundary : ∀ w, boundary w ⊆ N) :
    ∀ w, support n C J boundary w ⊆ N := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : internal n J w
    · have hj : w-n ∈ J := hw.2
      have hjr := hreal (w-n) hj
      have hwrep : w = n+(w-n) := by have := hw.1; omega
      obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem hjr))
      have ha : a < w := by
        have h := hAO.2.1 (w-n) hjr a (by rw [hab]; simp)
        omega
      have hb : b < w := by
        have h := hAO.2.1 (w-n) hjr b (by rw [hab]; simp)
        omega
      have hgate := support_gate n C J boundary (w-n) a b hj hab (by omega) (by omega)
      rw [← hwrep] at hgate
      rw [hgate]
      exact Finset.union_subset (ih a ha) (ih b hb)
    · rw [support_outside n C J boundary w hw]
      exact hboundary w

lemma support_covers (n : ℕ) (C : Circuit) (J : Finset ℕ) (boundary S : ℕ → Finset (Fin n))
    (hAO : IsAO2 n C) (hreal : ∀ j ∈ J, j < C.gates.length)
    (I : Finset (Fin n))
    (hboundary : ∀ w, S w ∩ I ⊆ boundary w)
    (hS : ∀ j ∈ J, ∀ a b, (gateAt C j).inputs = [a,b] → S (n+j) = S a ∪ S b) :
    ∀ w, S w ∩ I ⊆ support n C J boundary w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : internal n J w
    · have hj : w-n ∈ J := hw.2
      have hjr := hreal (w-n) hj
      have hwrep : w = n+(w-n) := by have := hw.1; omega
      obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem hjr))
      have ha : a < w := by
        have h := hAO.2.1 (w-n) hjr a (by rw [hab]; simp)
        omega
      have hb : b < w := by
        have h := hAO.2.1 (w-n) hjr b (by rw [hab]; simp)
        omega
      have hgate := support_gate n C J boundary (w-n) a b hj hab (by omega) (by omega)
      have hSgate := hS (w-n) hj a b hab
      rw [← hwrep] at hgate hSgate
      rw [hgate, hSgate]
      intro v hv
      have hvI := (Finset.mem_inter.mp hv).2
      rcases Finset.mem_union.mp (Finset.mem_inter.mp hv).1 with hva | hvb
      · exact Finset.mem_union_left _ (ih a ha (Finset.mem_inter.mpr ⟨hva,hvI⟩))
      · exact Finset.mem_union_right _ (ih b hb (Finset.mem_inter.mpr ⟨hvb,hvI⟩))
    · rw [support_outside n C J boundary w hw]
      exact hboundary w

lemma project_internal_values (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (boundary : ℕ → Finset (Fin n)) (hAO : IsAO2 n C)
    (hreal : ∀ j ∈ J, j < C.gates.length)
    (hback : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, rewire n J proxy w < n + j)
    (hBoundary : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w →
      ∀ x : Fin n → Bool,
        val (project n C J proxy) (List.ofFn x) (proxy w) = rawOr (boundary w) x)
    (x : Fin n → Bool) :
    ∀ j ∈ J, val (project n C J proxy) (List.ofFn x) (n+j) =
      rawOr (support n C J boundary (n+j)) x := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    have hjr := hreal j hj
    obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem hjr))
    have ha := hAO.2.1 j hjr a (by rw [hab]; simp)
    have hb := hAO.2.1 j hjr b (by rw [hab]; simp)
    have hgate : gateAt (project n C J proxy) j =
        ⟨GateOp.or, [rewire n J proxy a, rewire n J proxy b]⟩ := by
      rw [project_gate n C J proxy j hjr, ite_eq_left hj, hab]
      rfl
    have hinput (w : ℕ) (hw : w ∈ (gateAt C j).inputs) :
        val (project n C J proxy) (List.ofFn x) (rewire n J proxy w) =
          rawOr (support n C J boundary w) x := by
      by_cases hwI : internal n J w
      · have hwn := hwI.1
        have hwj := hAO.2.1 j hjr w hw
        have hwrep : w = n+(w-n) := by omega
        have hcond : n ≤ w ∧ w - n ∈ J := hwI
        rw [rewire, ite_eq_left hcond, hwrep]
        exact ih (w-n) (by omega) hwI.2
      · have hcond : ¬ (n ≤ w ∧ w - n ∈ J) := hwI
        rw [rewire, ite_eq_right hcond, support_outside n C J boundary w hwI]
        exact hBoundary j hj w hw hwI x
    rw [binary_eval _ j _ _ GateOp.or (by simpa only [project_length] using hjr) hgate
      (hback j hj a (by rw [hab]; simp)) (hback j hj b (by rw [hab]; simp)),
      hinput a (by rw [hab]; simp), hinput b (by rw [hab]; simp),
      support_gate n C J boundary j a b hj hab ha hb, rawOr_union]
    simp [GateOp.eval]

lemma binary_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b c d : Bool) (hac : a = true → c = true) (hbd : b = true → d = true) :
    op.eval [a,b] = true → op.eval [c,d] = true := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [GateOp.eval]

lemma private_patch_mono (n : ℕ) (C D E : Circuit) (J : Finset ℕ) (g : ℕ)
    (hAO : IsAO2 n C) (hDlen : D.gates.length = C.gates.length)
    (hElen : E.gates.length = C.gates.length)
    (hDsame : ∀ j < C.gates.length, j ∉ J → j ≠ g → gateAt D j = gateAt C j)
    (hEsame : ∀ j < C.gates.length, j ∉ J → j ≠ g → gateAt E j = gateAt C j)
    (hprivate : ∀ i ∈ J, ∀ j < C.gates.length,
      n+i ∈ (gateAt C j).inputs → j ∈ J ∨ j = g)
    (x : Fin n → Bool)
    (hg : val D (List.ofFn x) (n+g) = true → val E (List.ofFn x) (n+g) = true) :
    ∀ j < C.gates.length, j ∉ J →
      val D (List.ofFn x) (n+j) = true → val E (List.ofFn x) (n+j) = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hjJ
    by_cases hjg : j = g
    · subst j; exact hg
    obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem hj))
    have hshape : gateAt C j = ⟨(gateAt C j).op,[a,b]⟩ := by rw [← hab]
    have ha := hAO.2.1 j hj a (by rw [hab]; simp)
    have hb := hAO.2.1 j hj b (by rw [hab]; simp)
    have hinput (w : ℕ) (hw : w ∈ (gateAt C j).inputs) :
        val D (List.ofFn x) w = true → val E (List.ofFn x) w = true := by
      by_cases hwn : w < n
      · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
        exact id
      · have hwj := hAO.2.1 j hj w hw
        have hwrep : w = n+(w-n) := by omega
        have hwJ : w-n ∉ J := by
          intro hmem
          have hread : n+(w-n) ∈ (gateAt C j).inputs := by rwa [← hwrep]
          rcases hprivate (w-n) hmem j hj hread with hJ | hG
          · exact hjJ hJ
          · exact hjg hG
        rw [hwrep]
        exact ih (w-n) (by omega) (by omega) hwJ
    rw [binary_eval D j a b _ (by omega) ((hDsame j hj hjJ hjg).trans hshape) ha hb,
      binary_eval E j a b _ (by omega) ((hEsame j hj hjJ hjg).trans hshape) ha hb]
    exact binary_mono _ (hAO.1 _ (gateAt_mem hj)) _ _ _ _
      (hinput a (by rw [hab]; simp)) (hinput b (by rw [hab]; simp))

lemma private_patch_wire_mono (n : ℕ) (C D E : Circuit) (J : Finset ℕ) (g : ℕ)
    (hAO : IsAO2 n C) (hDlen : D.gates.length = C.gates.length)
    (hElen : E.gates.length = C.gates.length)
    (hDsame : ∀ j < C.gates.length, j ∉ J → j ≠ g → gateAt D j = gateAt C j)
    (hEsame : ∀ j < C.gates.length, j ∉ J → j ≠ g → gateAt E j = gateAt C j)
    (hprivate : ∀ i ∈ J, ∀ j < C.gates.length,
      n+i ∈ (gateAt C j).inputs → j ∈ J ∨ j = g)
    (x : Fin n → Bool)
    (hg : val D (List.ofFn x) (n+g) = true → val E (List.ofFn x) (n+g) = true)
    (w : ℕ) (hw : ¬ internal n J w) :
    val D (List.ofFn x) w = true → val E (List.ofFn x) w = true := by
  by_cases hwn : w < n
  · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
    exact id
  by_cases hwC : w < n+C.gates.length
  · have hwrep : w = n+(w-n) := by omega
    have hwJ : w-n ∉ J := fun hJ => hw ⟨by omega,hJ⟩
    rw [hwrep]
    exact private_patch_mono n C D E J g hAO hDlen hElen hDsame hEsame hprivate x hg
      (w-n) (by omega) hwJ
  · rw [val_ge (n := n) (by simp) (by omega), val_ge (n := n) (by simp) (by omega)]
    exact id

def finish (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (g center root : ℕ) : Circuit :=
  ⟨(project n C J proxy).gates.set g ⟨GateOp.and,[center,root]⟩, C.output⟩

lemma finish_length (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (g center root : ℕ) :
    (finish n C J proxy g center root).gates.length = C.gates.length := by
  simp [finish, project_length]

lemma finish_size (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (g center root : ℕ) : (finish n C J proxy g center root).size = C.size := by
  exact finish_length n C J proxy g center root

lemma finish_gate (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (g center root j : ℕ) (hj : j < C.gates.length) :
    gateAt (finish n C J proxy g center root) j =
      if j = g then ⟨GateOp.and,[center,root]⟩ else gateAt (project n C J proxy) j := by
  rw [gateAt_eq (by simpa only [finish_length] using hj),
    gateAt_eq (by simpa only [project_length] using hj)]
  simp [finish, List.getElem_set, eq_comm]

lemma finish_same (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (g center root j : ℕ) (hj : j < C.gates.length) (hjJ : j ∉ J) (hjg : j ≠ g) :
    gateAt (finish n C J proxy g center root) j = gateAt C j := by
  rw [finish_gate n C J proxy g center root j hj, ite_eq_right hjg,
    project_gate n C J proxy j hj, ite_eq_right hjJ]

lemma finish_ao (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (g center root : ℕ) (hAO : IsAO2 n C)
    (hback : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, rewire n J proxy w < n+j)
    (hcenter : center < n+g) (hroot : root < n+g) :
    IsAO2 n (finish n C J proxy g center root) := by
  have hP := project_ao n C J proxy hAO hback
  have hdata : ∀ j < (finish n C J proxy g center root).gates.length,
      ((gateAt (finish n C J proxy g center root) j).op = GateOp.and ∨
        (gateAt (finish n C J proxy g center root) j).op = GateOp.or) ∧
      (gateAt (finish n C J proxy g center root) j).inputs.length = 2 ∧
      ∀ w ∈ (gateAt (finish n C J proxy g center root) j).inputs, w < n+j := by
    intro j hj
    have hjC : j < C.gates.length := by simpa only [finish_length] using hj
    rw [finish_gate n C J proxy g center root j hjC]
    split_ifs with hjg
    · subst j
      refine ⟨Or.inl rfl,rfl,?_⟩
      intro w hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl | rfl
      · exact hcenter
      · exact hroot
    · have hjP : j < (project n C J proxy).gates.length := by simpa only [project_length] using hjC
      exact ⟨hP.1 _ (gateAt_mem hjP), hP.2.2 _ (gateAt_mem hjP), hP.2.1 j hjP⟩
  refine ⟨?_,?_,?_⟩
  · intro gate hgate
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hgate
    have h := (hdata j hj).1
    rwa [gateAt_eq hj] at h
  · intro j hj w hw
    exact (hdata j hj).2.2 w hw
  · intro gate hgate
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hgate
    have h := (hdata j hj).2.1
    rwa [gateAt_eq hj] at h

lemma same_before_values (n : ℕ) (C D : Circuit) (cut : ℕ)
    (hAO : IsAO2 n C) (hlen : D.gates.length = C.gates.length)
    (hsame : ∀ j < C.gates.length, j < cut → gateAt D j = gateAt C j)
    (x : Fin n → Bool) : ∀ j < C.gates.length, j < cut →
      val D (List.ofFn x) (n+j) = val C (List.ofFn x) (n+j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hjcut
    have earlier (w : ℕ) (hw : w ∈ (gateAt C j).inputs) :
        val D (List.ofFn x) w = val C (List.ofFn x) w := by
      by_cases hwn : w < n
      · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
      · have hwj := hAO.2.1 j hj w hw
        have hwrep : w = n+(w-n) := by omega
        rw [hwrep]
        exact ih (w-n) (by omega) (by omega) (by omega)
    rw [val_gate (n := n) (by simp) (by omega), val_gate (n := n) (by simp) hj,
      hsame j hj hjcut]
    congr 1
    apply List.map_congr_left
    intro w hw
    have hwj := hAO.2.1 j hj w hw
    simp only [ite_eq_left hwj]
    exact earlier w hw

lemma same_before_wire (n : ℕ) (C D : Circuit) (cut : ℕ)
    (hAO : IsAO2 n C) (hlen : D.gates.length = C.gates.length)
    (hsame : ∀ j < C.gates.length, j < cut → gateAt D j = gateAt C j)
    (x : Fin n → Bool) (w : ℕ) (hw : w < n+cut) :
    val D (List.ofFn x) w = val C (List.ofFn x) w := by
  by_cases hwn : w < n
  · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
  by_cases hwC : w < n+C.gates.length
  · have hwrep : w = n+(w-n) := by omega
    rw [hwrep]
    exact same_before_values n C D cut hAO hlen hsame x (w-n) (by omega) (by omega)
  · rw [val_ge (n := n) (by simp) (by omega), val_ge (n := n) (by simp) (by omega)]

lemma finish_before_wire (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (g center root : ℕ) (hAO : IsAO2 n C)
    (hback : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, rewire n J proxy w < n+j)
    (x : Fin n → Bool) (w : ℕ) (hw : w < n+g) :
    val (finish n C J proxy g center root) (List.ofFn x) w =
      val (project n C J proxy) (List.ofFn x) w := by
  apply same_before_wire n (project n C J proxy) (finish n C J proxy g center root) g
    (project_ao n C J proxy hAO hback)
    (by rw [finish_length, project_length]) _ x w hw
  intro j hj hjg
  have hjC : j < C.gates.length := by simpa only [project_length] using hj
  rw [finish_gate n C J proxy g center root j hjC, ite_eq_right (Nat.ne_of_lt hjg)]

lemma finish_g_value (n : ℕ) (C : Circuit) (J : Finset ℕ) (proxy : ℕ → ℕ)
    (boundary : ℕ → Finset (Fin n)) (g r : ℕ) (center : Fin n)
    (hAO : IsAO2 n C) (hreal : ∀ j ∈ J, j < C.gates.length)
    (hback : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, rewire n J proxy w < n+j)
    (hBoundary : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w →
      ∀ x : Fin n → Bool,
        val (project n C J proxy) (List.ofFn x) (proxy w) = rawOr (boundary w) x)
    (hg : g < C.gates.length) (hr : r ∈ J) (hrg : r < g) (x : Fin n → Bool) :
    gateVal n (finish n C J proxy g center.val (n+r)) g x =
      (x center && rawOr (support n C J boundary (n+r)) x) := by
  have hgate : gateAt (finish n C J proxy g center.val (n+r)) g =
      ⟨GateOp.and,[center.val,n+r]⟩ := by
    rw [finish_gate n C J proxy g center.val (n+r) g hg, ite_eq_left rfl]
  rw [gateVal_eq_val,
    binary_eval _ g center.val (n+r) GateOp.and (by simpa only [finish_length] using hg)
      hgate (by have := center.isLt; omega) (by omega),
    val_ofFn _ x center,
    finish_before_wire n C J proxy g center.val (n+r) hAO hback x (n+r) (by omega),
    project_internal_values n C J proxy boundary hAO hreal hback hBoundary x r hr]
  simp [GateOp.eval]

lemma project_boundary_from_protected (n : ℕ) (C : Circuit) (J E : Finset ℕ)
    (proxy : ℕ → ℕ) (boundary : ℕ → Finset (Fin n))
    (hAO : IsAO2 n C) (hdis : Disjoint E J)
    (hclosed : ∀ j ∈ E, ∀ w ∈ (gateAt C j).inputs, n ≤ w → w-n ∈ E)
    (hproxy : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w →
      n ≤ proxy w → proxy w-n ∈ E)
    (hBoundary : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w →
      ∀ x : Fin n → Bool, val C (List.ofFn x) (proxy w) = rawOr (boundary w) x) :
    ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w →
      ∀ x : Fin n → Bool,
        val (project n C J proxy) (List.ofFn x) (proxy w) = rawOr (boundary w) x := by
  intro j hj w hw hwI x
  rw [project_protected_wire n C J proxy hAO E hdis hclosed x (proxy w) (hproxy j hj w hw hwI)]
  exact hBoundary j hj w hw hwI x

def cut (C : Circuit) (g : ℕ) : Circuit :=
  ⟨C.gates.set g ⟨GateOp.or,[]⟩,C.output⟩

lemma cut_length (C : Circuit) (g : ℕ) : (cut C g).gates.length = C.gates.length := by
  simp [cut]

lemma cut_gate (C : Circuit) (g j : ℕ) (hj : j < C.gates.length) :
    gateAt (cut C g) j = if j = g then ⟨GateOp.or,[]⟩ else gateAt C j := by
  rw [gateAt_eq (by simpa only [cut_length] using hj), gateAt_eq hj]
  simp [cut,List.getElem_set,eq_comm]

lemma cut_g_false (n : ℕ) (C : Circuit) (g : ℕ) (hg : g < C.gates.length)
    (x : Fin n → Bool) : val (cut C g) (List.ofFn x) (n+g) = false := by
  rw [val_gate (n := n) (by simp) (by simpa only [cut_length] using hg),
    cut_gate C g g hg, ite_eq_left rfl]
  rfl

lemma wire_input_mono (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) :
    ∀ j < C.gates.length,
      val C (List.ofFn x) (n+j) = true → val C (List.ofFn y) (n+j) = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem hj))
    have hshape : gateAt C j = ⟨(gateAt C j).op,[a,b]⟩ := by rw [←hab]
    have ha := hAO.2.1 j hj a (by rw [hab]; simp)
    have hb := hAO.2.1 j hj b (by rw [hab]; simp)
    have hi (w : ℕ) (hw : w < n+j) :
        val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
      by_cases hwn : w < n
      · have heq : w = (⟨w,hwn⟩ : Fin n).val := rfl
        rw [heq, val_ofFn C x ⟨w,hwn⟩, val_ofFn C y ⟨w,hwn⟩]
        exact hxy ⟨w,hwn⟩
      · have hwrep : w = n+(w-n) := by omega
        rw [hwrep]
        exact ih (w-n) (by omega) (by omega)
    rw [binary_eval C j a b _ hj hshape ha hb, binary_eval C j a b _ hj hshape ha hb]
    exact binary_mono _ (hAO.1 _ (gateAt_mem hj)) _ _ _ _ (hi a ha) (hi b hb)

lemma circuit_input_mono (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) :
    circuitFun n C x = true → circuitFun n C y = true := by
  change val C (List.ofFn x) C.output = true → val C (List.ofFn y) C.output = true
  by_cases hwn : C.output < n
  · have heq : C.output = (⟨C.output,hwn⟩ : Fin n).val := rfl
    rw [heq, val_ofFn C x ⟨C.output,hwn⟩, val_ofFn C y ⟨C.output,hwn⟩]
    exact hxy ⟨C.output,hwn⟩
  by_cases hwC : C.output < n+C.gates.length
  · have hwrep : C.output = n+(C.output-n) := by omega
    rw [hwrep]
    exact wire_input_mono n C hAO x y hxy (C.output-n) (by omega)
  · rw [val_ge (n := n) (by simp) (by omega)]
    simp

lemma computes_of_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (hD : IsAO2 n D)
    (hnegative : ∀ x, graphFun G ∅ x = false → circuitFun n D x = false)
    (hedge : ∀ u v, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hDx
    by_contra hF
    have hfalse : graphFun G ∅ x = false := by cases h : graphFun G ∅ x <;> simp_all
    rw [hnegative x hfalse] at hDx
    cases hDx
  · intro hF
    have hpair : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
      simpa [graphFun] using hF
    obtain ⟨u,v,huv,hu,hv⟩ := hpair
    apply circuit_input_mono n D hD (pairInput u v) x _ (hedge u v huv)
    intro a ha
    have ha' : a = u ∨ a = v := by simpa [pairInput] using ha
    rcases ha' with rfl | rfl
    · exact hu
    · exact hv

lemma private_patch_computes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (J : Finset ℕ) (g : ℕ)
    (hAO : IsAO2 n C) (hD : IsAO2 n D) (hDlen : D.gates.length = C.gates.length)
    (hg : g < C.gates.length) (hDout : D.output = C.output)
    (hDsame : ∀ j < C.gates.length, j ∉ J → j ≠ g → gateAt D j = gateAt C j)
    (hprivate : ∀ i ∈ J, ∀ j < C.gates.length,
      n+i ∈ (gateAt C j).inputs → j ∈ J ∨ j = g)
    (hout : ¬ internal n J C.output) (hCF : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x, gateVal n D g x = true → graphFun G ∅ x = true)
    (hcritical : ∀ u v, G.Adj u v → circuitFun n (cut C g) (pairInput u v) = false →
      gateVal n D g (pairInput u v) = true) :
    circuitFun n D = graphFun G ∅ := by
  apply computes_of_edges G D hD
  · intro x hF
    by_contra hDx
    have hDt : circuitFun n D x = true := by cases h : circuitFun n D x <;> simp_all
    have hG : val D (List.ofFn x) (n+g) = true → val C (List.ofFn x) (n+g) = true := by
      intro h
      have hc := hclean x h
      rw [hF] at hc
      cases hc
    have hmono := private_patch_wire_mono n C D C J g hAO hDlen rfl hDsame
      (fun _ _ _ _ => rfl) hprivate x hG C.output hout
    change val D (List.ofFn x) D.output = true at hDt
    rw [hDout] at hDt
    have hCt : circuitFun n C x = true := hmono hDt
    rw [hCF,hF] at hCt
    cases hCt
  · intro u v huv
    let x := pairInput u v
    have hCt : circuitFun n C x = true := by
      rw [hCF]
      simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]
      right
      exact ⟨u,v,huv,by simp [x,pairInput],by simp [x,pairInput]⟩
    change val D (List.ofFn x) D.output = true
    rw [hDout]
    by_cases hG : gateVal n D g x = true
    · apply private_patch_wire_mono n C C D J g hAO rfl hDlen
        (fun _ _ _ _ => rfl) hDsame hprivate x (fun _ => hG) C.output hout
      exact hCt
    · have hcut : circuitFun n (cut C g) x = true := by
        by_contra hcut
        have hcutf : circuitFun n (cut C g) x = false := by
          cases h : circuitFun n (cut C g) x <;> simp_all
        exact hG (hcritical u v huv hcutf)
      apply private_patch_wire_mono n C (cut C g) D J g hAO (cut_length C g) hDlen
        (fun j hj _ hjg => by rw [cut_gate C g j hj, ite_eq_right hjg])
        hDsame hprivate x _ C.output hout hcut
      intro hgtrue
      rw [cut_g_false n C g hg x] at hgtrue
      cases hgtrue

lemma private_patch_junk_subset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (J : Finset ℕ) (g : ℕ)
    (hAO : IsAO2 n C) (hDlen : D.gates.length = C.gates.length)
    (hDsame : ∀ j < C.gates.length, j ∉ J → j ≠ g → gateAt D j = gateAt C j)
    (hDor : ∀ j ∈ J, (gateAt D j).op = GateOp.or)
    (hprivate : ∀ i ∈ J, ∀ j < C.gates.length,
      n+i ∈ (gateAt C j).inputs → j ∈ J ∨ j = g)
    (hclean : ∀ x, gateVal n D g x = true → graphFun G ∅ x = true) :
    junk G D ⊆ (junk G C).erase g := by
  intro j hjD
  obtain ⟨hj,hop,x,hjx,hF⟩ := (mem_junk_iff G D j).mp hjD
  have hjC : j < C.gates.length := by omega
  have hjJ : j ∉ J := by
    intro hjJ
    rw [hDor j hjJ] at hop
    cases hop
  have hjg : j ≠ g := by
    intro heq
    subst j
    have h := hclean x hjx
    rw [hF] at h
    cases h
  refine Finset.mem_erase.mpr ⟨hjg, (mem_junk_iff G C j).mpr ⟨hjC,?_,x,?_,hF⟩⟩
  · rw [← hDsame j hjC hjJ hjg]
    exact hop
  · apply private_patch_mono n C D C J g hAO hDlen rfl hDsame
      (fun _ _ _ _ => rfl) hprivate x _ j hjC hjJ hjx
    intro hgtrue
    have h := hclean x hgtrue
    rw [hF] at h
    cases h

lemma same_domain_values (n : ℕ) (C D : Circuit) (E : Finset ℕ)
    (hAO : IsAO2 n C) (hlen : D.gates.length = C.gates.length)
    (hsame : ∀ j < C.gates.length, j ∈ E → gateAt D j = gateAt C j)
    (hclosed : ∀ j ∈ E, ∀ w ∈ (gateAt C j).inputs, n ≤ w → w-n ∈ E)
    (x : Fin n → Bool) : ∀ j < C.gates.length, j ∈ E →
      val D (List.ofFn x) (n+j) = val C (List.ofFn x) (n+j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hjE
    have earlier (w : ℕ) (hw : w ∈ (gateAt C j).inputs) :
        val D (List.ofFn x) w = val C (List.ofFn x) w := by
      by_cases hwn : w < n
      · rw [val_input (n := n) (by simp) hwn, val_input (n := n) (by simp) hwn]
      · have hwj := hAO.2.1 j hj w hw
        have hwrep : w = n+(w-n) := by omega
        rw [hwrep]
        exact ih (w-n) (by omega) (by omega) (hclosed j hjE w hw (by omega))
    rw [val_gate (n := n) (by simp) (by omega), val_gate (n := n) (by simp) hj,
      hsame j hj hjE]
    congr 1
    apply List.map_congr_left
    intro w hw
    have hwj := hAO.2.1 j hj w hw
    simp only [ite_eq_left hwj]
    exact earlier w hw

lemma same_domain_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (E : Finset ℕ) (hAO : IsAO2 n C)
    (hlen : D.gates.length = C.gates.length)
    (hsame : ∀ j < C.gates.length, j ∈ E → gateAt D j = gateAt C j)
    (hclosed : ∀ j ∈ E, ∀ w ∈ (gateAt C j).inputs, n ≤ w → w-n ∈ E)
    (j : ℕ) (hjE : j ∈ E) (hj : j ∈ junk G C) : j ∈ junk G D := by
  obtain ⟨hjr,hop,x,hjx,hF⟩ := (mem_junk_iff G C j).mp hj
  apply (mem_junk_iff G D j).mpr
  refine ⟨by omega,?_,x,?_,hF⟩
  · rw [hsame j hjr hjE]
    exact hop
  · change val D (List.ofFn x) (n+j) = true
    rw [same_domain_values n C D E hAO hlen hsame hclosed x j hjr hjE]
    exact hjx

lemma cleaning_contradiction {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hL : IsLeastAO G C)
    (hOne : ∀ E : Circuit, IsLeastAO G E → (junk G E).card ≠ 1)
    (hTwo : (junk G C).card = 2) (g : ℕ) (hg : g ∈ junk G C)
    (hD : IsAO2 n D) (hsize : D.size = C.size) (hDF : circuitFun n D = graphFun G ∅)
    (hsub : junk G D ⊆ (junk G C).erase g) (hSurvive : (junk G D).Nonempty) : False := by
  have hcard : (junk G D).card = 1 := by
    have hle := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hg,hTwo] at hle
    have hpos := Finset.card_pos.mpr hSurvive
    omega
  have hDL : IsLeastAO G D := by
    refine ⟨hD,hDF,?_⟩
    intro E hE hEF
    rw [hsize]
    exact hL.2.2 E hE hEF
  exact hOne D hDL hcard

lemma projection_contradiction {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hTwo : (junk G C).card = 2) (g h r : ℕ) (center : Fin n)
    (hgJ : g ∈ junk G C) (hhJ : h ∈ junk G C)
    (J E A : Finset ℕ) (proxy : ℕ → ℕ) (boundary S : ℕ → Finset (Fin n))
    (I : Finset (Fin n))
    (hbefore : ∀ j ∈ J, j < g) (hr : r ∈ J)
    (hback : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, rewire n J proxy w < n+j)
    (hEdis : Disjoint E J)
    (hEclosed : ∀ j ∈ E, ∀ w ∈ (gateAt C j).inputs, n ≤ w → w-n ∈ E)
    (hproxy : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w →
      n ≤ proxy w → proxy w-n ∈ E)
    (hBoundary : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w →
      ∀ x : Fin n → Bool, val C (List.ofFn x) (proxy w) = rawOr (boundary w) x)
    (hBoundaryClean : ∀ w, ∀ v ∈ boundary w, G.Adj center v)
    (hBoundaryCover : ∀ w, S w ∩ I ⊆ boundary w)
    (hS : ∀ j ∈ J, ∀ a b, (gateAt C j).inputs = [a,b] → S (n+j) = S a ∪ S b)
    (hIroot : I ⊆ S (n+r))
    (hprivate : ∀ i ∈ J, ∀ j < C.gates.length,
      n+i ∈ (gateAt C j).inputs → j ∈ J ∨ j = g)
    (hout : ¬ internal n J C.output)
    (hCritical : ∀ u v, G.Adj u v → circuitFun n (cut C g) (pairInput u v) = false →
      pairInput u v center = true ∧ ∃ i ∈ I, pairInput u v i = true)
    (hhA : h ∈ A)
    (hAclean : ∀ j ∈ A, j ∉ J ∧ j ≠ g)
    (hAclosed : ∀ j ∈ A, ∀ w ∈ (gateAt C j).inputs, n ≤ w → w-n ∈ A) : False := by
  let D := finish n C J proxy g center.val (n+r)
  have hg : g < C.gates.length := (mem_junk_iff G C g).mp hgJ |>.1
  have hreal : ∀ j ∈ J, j < C.gates.length := fun j hj => lt_trans (hbefore j hj) hg
  have hrg := hbefore r hr
  have hDlen : D.gates.length = C.gates.length := finish_length n C J proxy g center.val (n+r)
  have hDsize : D.size = C.size := finish_size n C J proxy g center.val (n+r)
  have hD : IsAO2 n D := finish_ao n C J proxy g center.val (n+r) hL.1 hback
    (by have := center.isLt; omega) (by omega)
  have hDsame : ∀ j < C.gates.length, j ∉ J → j ≠ g → gateAt D j = gateAt C j :=
    finish_same n C J proxy g center.val (n+r)
  have hBoundaryP := project_boundary_from_protected n C J E proxy boundary hL.1
    hEdis hEclosed hproxy hBoundary
  have hvalue (x : Fin n → Bool) : gateVal n D g x =
      (x center && rawOr (support n C J boundary (n+r)) x) :=
    finish_g_value n C J proxy boundary g r center hL.1 hreal hback hBoundaryP hg hr hrg x
  have hsubset : support n C J boundary (n+r) ⊆
      Finset.univ.filter (fun v => G.Adj center v) := by
    apply support_subset n C J boundary hL.1 hreal _ _ (n+r)
    intro w v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hBoundaryClean w v hv⟩
  have hcover : I ⊆ support n C J boundary (n+r) := by
    intro i hi
    exact support_covers n C J boundary S hL.1 hreal I hBoundaryCover hS (n+r)
      (Finset.mem_inter.mpr ⟨hIroot hi,hi⟩)
  have hclean : ∀ x, gateVal n D g x = true → graphFun G ∅ x = true := by
    intro x hx
    rw [hvalue x] at hx
    have hx' : x center = true ∧ ∃ v ∈ support n C J boundary (n+r), x v = true := by
      simpa [rawOr] using hx
    obtain ⟨hc,v,hv,hvx⟩ := hx'
    have hcv : G.Adj center v := (Finset.mem_filter.mp (hsubset hv)).2
    simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
    exact Or.inr ⟨center,v,hcv,hc,hvx⟩
  have hcrit : ∀ u v, G.Adj u v → circuitFun n (cut C g) (pairInput u v) = false →
      gateVal n D g (pairInput u v) = true := by
    intro u v huv hcut
    obtain ⟨hc,i,hi,hix⟩ := hCritical u v huv hcut
    rw [hvalue]
    have hraw : rawOr (support n C J boundary (n+r)) (pairInput u v) = true :=
      decide_eq_true ⟨i,hcover hi,hix⟩
    simp [hc,hraw]
  have hDF : circuitFun n D = graphFun G ∅ := private_patch_computes G C D J g hL.1 hD
    hDlen hg rfl hDsame hprivate hout hL.2.1 hclean hcrit
  have hDor : ∀ j ∈ J, (gateAt D j).op = GateOp.or := by
    intro j hj
    have hjr := hreal j hj
    have hjg : j ≠ g := Nat.ne_of_lt (hbefore j hj)
    change (gateAt (finish n C J proxy g center.val (n+r)) j).op = _
    rw [finish_gate n C J proxy g center.val (n+r) j hjr, ite_eq_right hjg,
      project_gate n C J proxy j hjr, ite_eq_left hj]
  have hsub := private_patch_junk_subset G C D J g hL.1 hDlen hDsame hDor hprivate hclean
  have hsurv : h ∈ junk G D := same_domain_junk G C D A hL.1 hDlen
    (fun j hj hjA => hDsame j hj (hAclean j hjA).1 (hAclean j hjA).2) hAclosed h hhA hhJ
  exact cleaning_contradiction G C D hL hOne hTwo g hgJ hD hDsize hDF hsub ⟨h,hsurv⟩

end PEqualNP.Outside.L_meta_5012.OrProjection


namespace PEqualNP.Outside.L_meta_5012.OrProjection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm
open Absorption

noncomputable def pickOr {n : ℕ} (T : Finset (Fin n)) (d : Fin n) : Fin n :=
  if h : T.Nonempty then Classical.choose h else d

lemma pickOr_mem {n : ℕ} (T : Finset (Fin n)) (d : Fin n) (h : T.Nonempty) :
    pickOr T d ∈ T := by
  simp only [pickOr,dite_eq_left h]
  exact Classical.choose_spec h

noncomputable def boundaryProxy {n : ℕ} (N I : Finset (Fin n)) (d : Fin n)
    (S : ℕ → Finset (Fin n)) (w : ℕ) : ℕ :=
  if S w ⊆ N then w else (pickOr (S w ∩ I) d).val

def boundarySupport {n : ℕ} (N I : Finset (Fin n)) (d : Fin n)
    (S : ℕ → Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  if S w ⊆ N then S w else if (S w ∩ I).Nonempty then S w ∩ I else {d}

lemma boundaryProxy_eq_or_raw {n : ℕ} (N I : Finset (Fin n)) (d : Fin n)
    (S : ℕ → Finset (Fin n)) (w : ℕ) :
    boundaryProxy N I d S w = w ∨ boundaryProxy N I d S w < n := by
  by_cases h : S w ⊆ N
  · exact Or.inl (by simp [boundaryProxy,h])
  · right
    simp only [boundaryProxy,ite_eq_right h]
    exact (pickOr (S w ∩ I) d).isLt

lemma boundarySupport_subset {n : ℕ} (N I : Finset (Fin n)) (d : Fin n)
    (S : ℕ → Finset (Fin n)) (hI : I ⊆ N) (hd : d ∈ I) (w : ℕ) :
    boundarySupport N I d S w ⊆ N := by
  unfold boundarySupport
  split_ifs with hgood hnonempty
  · exact hgood
  · exact (Finset.inter_subset_right).trans hI
  · intro v hv
    have hvd : v = d := Finset.mem_singleton.mp hv
    subst v
    exact hI hd

lemma boundarySupport_covers {n : ℕ} (N I : Finset (Fin n)) (d : Fin n)
    (S : ℕ → Finset (Fin n)) (w : ℕ) :
    S w ∩ I ⊆ boundarySupport N I d S w := by
  unfold boundarySupport
  split_ifs with hgood hnonempty
  · exact Finset.inter_subset_left
  · exact Finset.Subset.refl _
  · intro v hv
    exact False.elim (hnonempty ⟨v,hv⟩)

lemma boundaryProxy_back {n : ℕ} (C : Circuit) (J : Finset ℕ)
    (N I : Finset (Fin n)) (d : Fin n) (S : ℕ → Finset (Fin n))
    (hAO : IsAO2 n C) (hreal : ∀ j ∈ J, j < C.gates.length) :
    ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs,
      rewire n J (boundaryProxy N I d S) w < n+j := by
  intro j hj w hw
  have hbound := hAO.2.1 j (hreal j hj) w hw
  unfold rewire
  split_ifs with hI
  · exact hbound
  · rcases boundaryProxy_eq_or_raw N I d S w with heq | hraw
    · rw [heq]
      exact hbound
    · omega

lemma boundaryProxy_protected {n : ℕ} (C : Circuit) (J E : Finset ℕ)
    (N I : Finset (Fin n)) (d : Fin n) (S : ℕ → Finset (Fin n))
    (hE : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w → n ≤ w → w-n ∈ E) :
    ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w →
      n ≤ boundaryProxy N I d S w → boundaryProxy N I d S w-n ∈ E := by
  intro j hj w hw hwI hn
  rcases boundaryProxy_eq_or_raw N I d S w with heq | hraw
  · rw [heq] at hn ⊢
    exact hE j hj w hw hwI hn
  · omega

lemma boundaryProxy_value {n : ℕ} (C : Circuit)
    (N I : Finset (Fin n)) (d : Fin n) (S : ℕ → Finset (Fin n))
    (w : ℕ) (hprotected : S w ⊆ N ∨ (S w ∩ I).card ≤ 1)
    (hraw : ∀ x : Fin n → Bool, val C (List.ofFn x) w = rawOr (S w) x)
    (x : Fin n → Bool) :
    val C (List.ofFn x) (boundaryProxy N I d S w) =
      rawOr (boundarySupport N I d S w) x := by
  by_cases hgood : S w ⊆ N
  · simp only [boundaryProxy,boundarySupport,ite_eq_left hgood]
    exact hraw x
  · have hsmall : (S w ∩ I).card ≤ 1 := hprotected.resolve_left hgood
    simp only [boundaryProxy,boundarySupport,ite_eq_right hgood]
    by_cases hnonempty : (S w ∩ I).Nonempty
    · rw [ite_eq_left hnonempty, val_ofFn C x (pickOr (S w ∩ I) d)]
      have hpick := pickOr_mem (S w ∩ I) d hnonempty
      have heq : S w ∩ I = {pickOr (S w ∩ I) d} := by
        ext v
        simp only [Finset.mem_singleton]
        constructor
        · intro hv
          exact Finset.card_le_one.mp hsmall v hv _ hpick
        · intro hv
          simpa [hv] using hpick
      conv_rhs => rw [heq]
      simp [rawOr]
    · rw [ite_eq_right hnonempty]
      simp only [pickOr,dite_eq_right hnonempty]
      rw [val_ofFn C x d]
      simp [rawOr]

lemma projection_contradiction_of_boundaries {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hTwo : (junk G C).card = 2) (g h r : ℕ) (center d : Fin n)
    (hgJ : g ∈ junk G C) (hhJ : h ∈ junk G C)
    (J E A : Finset ℕ) (S : ℕ → Finset (Fin n)) (I : Finset (Fin n))
    (hd : d ∈ I) (hI : ∀ i ∈ I, G.Adj center i)
    (hbefore : ∀ j ∈ J, j < g) (hr : r ∈ J)
    (hEdis : Disjoint E J)
    (hEclosed : ∀ j ∈ E, ∀ w ∈ (gateAt C j).inputs, n ≤ w → w-n ∈ E)
    (hEboundary : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w →
      n ≤ w → w-n ∈ E)
    (hBoundaryProtected : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w →
      (∀ v ∈ S w, G.Adj center v) ∨ (S w ∩ I).card ≤ 1)
    (hBoundaryRaw : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs, ¬ internal n J w →
      ∀ x : Fin n → Bool, val C (List.ofFn x) w = rawOr (S w) x)
    (hS : ∀ j ∈ J, ∀ a b, (gateAt C j).inputs = [a,b] → S (n+j) = S a ∪ S b)
    (hIroot : I ⊆ S (n+r))
    (hprivate : ∀ i ∈ J, ∀ j < C.gates.length,
      n+i ∈ (gateAt C j).inputs → j ∈ J ∨ j = g)
    (hout : ¬ internal n J C.output)
    (hCritical : ∀ u v, G.Adj u v → circuitFun n (cut C g) (pairInput u v) = false →
      pairInput u v center = true ∧ ∃ i ∈ I, pairInput u v i = true)
    (hhA : h ∈ A)
    (hAclean : ∀ j ∈ A, j ∉ J ∧ j ≠ g)
    (hAclosed : ∀ j ∈ A, ∀ w ∈ (gateAt C j).inputs, n ≤ w → w-n ∈ A) : False := by
  let N : Finset (Fin n) := Finset.univ.filter (fun v => G.Adj center v)
  let proxy := boundaryProxy N I d S
  let boundary := boundarySupport N I d S
  have hg : g < C.gates.length := (mem_junk_iff G C g).mp hgJ |>.1
  have hreal : ∀ j ∈ J, j < C.gates.length := fun j hj => lt_trans (hbefore j hj) hg
  have hIN : I ⊆ N := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hI i hi⟩
  apply projection_contradiction G C hL hOne hTwo g h r center hgJ hhJ J E A proxy boundary S I
    hbefore hr (boundaryProxy_back C J N I d S hL.1 hreal) hEdis hEclosed
    (boundaryProxy_protected C J E N I d S hEboundary) _ _
    (boundarySupport_covers N I d S) hS hIroot hprivate hout hCritical hhA hAclean hAclosed
  · intro j hj w hw hwI x
    apply boundaryProxy_value C N I d S w _ (hBoundaryRaw j hj w hw hwI) x
    rcases hBoundaryProtected j hj w hw hwI with hgood | hsmall
    · left
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hgood v hv⟩
    · exact Or.inr hsmall
  · intro w v hv
    have hvN := boundarySupport_subset N I d S hIN hd w hv
    exact (Finset.mem_filter.mp hvN).2

end PEqualNP.Outside.L_meta_5012.OrProjection


namespace PEqualNP.Outside.L_meta_5012

namespace Colors

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.IndependentDescent

lemma safe_triple {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) {w : Fin n} (hs : Safe G P Q w)
    {p q : Fin n} (hp : p ∈ P) (hq : q ∈ Q) :
    G.Adj p q ∨ G.Adj p w ∨ G.Adj q w := by
  let x : Fin n → Bool := fun v => decide (v = p ∨ v = q ∨ v = w)
  have hprod : product P Q x = true :=
    (product_true P Q x).mpr ⟨⟨p, hp, by simp [x]⟩, q, hq, by simp [x]⟩
  have hF := hs x hprod (by simp [x])
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, x] at hF
  obtain ⟨a, b, hab, ha, hb⟩ := hF
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact (G.irrefl hab).elim
  · exact Or.inl hab
  · exact Or.inr (Or.inl hab)
  · exact Or.inl hab.symm
  · exact (G.irrefl hab).elim
  · exact Or.inr (Or.inr hab)
  · exact Or.inr (Or.inl hab.symm)
  · exact Or.inr (Or.inr hab.symm)
  · exact (G.irrefl hab).elim

lemma safe_bad_adjacent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) {w : Fin n} (hs : Safe G P Q w)
    {p q : Fin n} (hp : p ∈ P) (hq : q ∈ Q)
    (hpw : ¬ G.Adj p w) (hqw : ¬ G.Adj q w) : G.Adj p q := by
  rcases safe_triple G P Q hs hp hq with hpq | hpw' | hqw'
  · exact hpq
  · exact (hpw hpw').elim
  · exact (hqw hqw').elim

lemma bool_eq_of_common_ne {a b c : Bool} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

lemma safe_bad_colors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (P Q : Finset (Fin n)) {w p0 q0 : Fin n} (hs : Safe G P Q w)
    (hp0 : p0 ∈ P) (hq0 : q0 ∈ Q) (hpw : ¬ G.Adj p0 w) (hqw : ¬ G.Adj q0 w) :
    G.Adj p0 q0 ∧
      (∀ p ∈ P, ¬ G.Adj p w → s p = s p0) ∧
      (∀ q ∈ Q, ¬ G.Adj q w → s q = s q0) := by
  have hpq := safe_bad_adjacent G P Q hs hp0 hq0 hpw hqw
  refine ⟨hpq, ?_, ?_⟩
  · intro p hp hnp
    have hadj := safe_bad_adjacent G P Q hs hp hq0 hnp hqw
    exact bool_eq_of_common_ne (hbip p q0 hadj) (hbip p0 q0 hpq)
  · intro q hq hnq
    have hadj := safe_bad_adjacent G P Q hs hp0 hq hpw hnq
    exact bool_eq_of_common_ne (Ne.symm (hbip p0 q hadj)) (Ne.symm (hbip p0 q0 hpq))

lemma safe_oriented_bad_factors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (P Q : Finset (Fin n)) {w p0 q0 : Fin n} (hs : Safe G P Q w)
    (hp0 : p0 ∈ P) (hq0 : q0 ∈ Q) (hpw : ¬ G.Adj p0 w) (hqw : ¬ G.Adj q0 w) :
    ((∀ p ∈ P, ¬ G.Adj p w → s p = s w) ∧ (∀ q ∈ Q, s q ≠ s w)) ∨
      ((∀ q ∈ Q, ¬ G.Adj q w → s q = s w) ∧ (∀ p ∈ P, s p ≠ s w)) := by
  obtain ⟨hpq, hP, hQ⟩ := safe_bad_colors G s hbip P Q hs hp0 hq0 hpw hqw
  have hpqColor := hbip p0 q0 hpq
  by_cases hpColor : s p0 = s w
  · left
    constructor
    · intro p hp hn
      exact (hP p hp hn).trans hpColor
    · intro q hq hqwColor
      have hnq : ¬ G.Adj q w := fun hadj => hbip q w hadj hqwColor
      have hqColor := hQ q hq hnq
      exact hpqColor (hpColor.trans (hqwColor.symm.trans hqColor))
  · right
    have hqColor : s q0 = s w :=
      bool_eq_of_common_ne (Ne.symm hpqColor) (Ne.symm hpColor)
    constructor
    · intro q hq hn
      exact (hQ q hq hn).trans hqColor
    · intro p hp hpwColor
      have hnp : ¬ G.Adj p w := fun hadj => hbip p w hadj hpwColor
      have hpColor' := hP p hp hnp
      exact hpqColor (hpColor'.symm.trans (hpwColor.trans hqColor.symm))

lemma safe_iff_triples {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (w : Fin n) :
    Safe G P Q w ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w := by
  constructor
  · intro hs p hp q hq
    exact safe_triple G P Q hs hp hq
  · intro h x hprod hxw
    obtain ⟨⟨p, hp, hxp⟩, q, hq, hxq⟩ := (product_true P Q x).mp hprod
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    rcases h p hp q hq with hpq | hpw | hqw
    · exact ⟨p, q, hpq, hxp, hxq⟩
    · exact ⟨p, w, hpw, hxp, hxw⟩
    · exact ⟨q, w, hqw, hxq, hxw⟩

lemma safe_swap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (w : Fin n) : Safe G P Q w ↔ Safe G Q P w := by
  constructor <;> intro hs x hx hw <;> apply hs x _ hw <;>
    simpa only [product, Bool.and_comm] using hx

end Colors

namespace Sharing

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.IndependentDescent
  PEqualNP.Outside.L_meta_5012.Colors

lemma safe_swap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) {w : Fin n} (hs : Safe G P Q w) : Safe G Q P w := by
  intro x hx hxw
  apply hs x _ hxw
  simpa only [product, Bool.and_comm] using hx

lemma common_neighbor_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (I : Finset (Fin n)) (hI : 2 ≤ I.card)
    {w z : Fin n} (hw : ∀ i ∈ I, G.Adj w i) (hz : ∀ i ∈ I, G.Adj z i) : z = w := by
  by_contra hne
  have hsub : I ⊆ Finset.univ.filter fun i => G.Adj z i ∧ G.Adj w i := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz i hi, hw i hi⟩
  have hc := (Finset.card_le_card hsub).trans (h4 z w hne)
  omega

lemma shared_mixed_forces_same_center {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (I T R S : Finset (Fin n)) (hI : 2 ≤ I.card)
    {w z p : Fin n} (hIw : ∀ i ∈ I, G.Adj w i) (hIT : I ⊆ T) (hTR : T ⊆ R)
    (hpT : p ∈ T) (hpColor : s p = s w) (hzColor : s z = s w)
    (hSafe : Safe G R S z) (hBad : ∃ q ∈ S, ¬ G.Adj q z) : z = w := by
  obtain ⟨q, hqS, hqBad⟩ := hBad
  have hpBad : ¬ G.Adj p z := by
    intro hpz
    exact hbip p z hpz (hpColor.trans hzColor.symm)
  have hpq := safe_bad_adjacent G R S hSafe (hTR hpT) hqS hpBad hqBad
  have hqColor : s q ≠ s w := by
    intro he
    exact hbip p q hpq (hpColor.trans he.symm)
  apply common_neighbor_unique G h4 I hI hIw
  intro i hi
  have hiColor : s i ≠ s w := Ne.symm (hbip w i (hIw i hi))
  have hiq : s i = s q := bool_eq_of_common_ne hiColor hqColor
  rcases safe_triple G R S hSafe (hTR (hIT hi)) hqS with hiqAdj | hizAdj | hqzAdj
  · exact False.elim (hbip i q hiqAdj hiq)
  · exact hizAdj.symm
  · exact False.elim (hqBad hqzAdj)

lemma shared_mono_forces_neighbors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (I T R S : Finset (Fin n)) (hI : 2 ≤ I.card)
    {w z : Fin n} (hIw : ∀ i ∈ I, G.Adj w i) (hIT : I ⊆ T) (hTR : T ⊆ R)
    (hColor : ∀ t ∈ T, s t = s z) (hSafe : Safe G R S z)
    (hBad : ∃ q ∈ S, ¬ G.Adj q z) : ∀ t ∈ T, G.Adj w t := by
  obtain ⟨q, hqS, hqBad⟩ := hBad
  have hqt : ∀ t ∈ T, G.Adj q t := by
    intro t ht
    have htBad : ¬ G.Adj t z := fun htz => hbip t z htz (hColor t ht)
    exact (safe_bad_adjacent G R S hSafe (hTR ht) hqS htBad hqBad).symm
  have hqw : q = w := common_neighbor_unique G h4 I hI hIw (fun i hi => hqt i (hIT hi))
  simpa only [hqw] using hqt

lemma mixed_shared_subset_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (I T R S : Finset (Fin n)) {w z : Fin n}
    (hIw : ∀ i ∈ I, G.Adj w i) (hzColor : s z = s w) (hzw : z ≠ w)
    (hColor : ∀ t ∈ T, ¬ G.Adj t w → s t = s w)
    (hSafe : Safe G R S z) (hRBad : ∃ p ∈ R, ¬ G.Adj p z)
    (hSBad : ∃ q ∈ S, ¬ G.Adj q z) (hShared : T ⊆ R ∨ T ⊆ S) :
    (∀ t ∈ T, G.Adj w t) ∨ (T ∩ I).card ≤ 1 := by
  classical
  by_cases hGood : ∀ t ∈ T, G.Adj w t
  · exact Or.inl hGood
  · right
    by_contra hCard
    have hI : 2 ≤ (T ∩ I).card := by omega
    push Not at hGood
    obtain ⟨p, hpT, hpBad⟩ := hGood
    have hpBad' : ¬ G.Adj p w := fun hpw => hpBad hpw.symm
    have hpColor := hColor p hpT hpBad'
    have hIntw : ∀ i ∈ T ∩ I, G.Adj w i := fun i hi => hIw i (Finset.mem_inter.mp hi).2
    rcases hShared with hTR | hTS
    · exact hzw (shared_mixed_forces_same_center G s hbip h4 (T ∩ I) T R S hI
        hIntw Finset.inter_subset_left hTR hpT hpColor hzColor hSafe hSBad)
    · exact hzw (shared_mixed_forces_same_center G s hbip h4 (T ∩ I) T S R hI
        hIntw Finset.inter_subset_left hTS hpT hpColor hzColor (safe_swap G R S hSafe) hRBad)

lemma mono_shared_subset_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (I T R S : Finset (Fin n)) {w z : Fin n}
    (hIw : ∀ i ∈ I, G.Adj w i) (hzColor : s z ≠ s w)
    (hColor : ∀ t ∈ T, s t ≠ s w)
    (hSafe : Safe G R S z) (hRBad : ∃ p ∈ R, ¬ G.Adj p z)
    (hSBad : ∃ q ∈ S, ¬ G.Adj q z) (hShared : T ⊆ R ∨ T ⊆ S) :
    (∀ t ∈ T, G.Adj w t) ∨ (T ∩ I).card ≤ 1 := by
  classical
  by_cases hCard : (T ∩ I).card ≤ 1
  · exact Or.inr hCard
  · left
    have hI : 2 ≤ (T ∩ I).card := by omega
    have hColor' : ∀ t ∈ T, s t = s z := fun t ht => bool_eq_of_common_ne (hColor t ht) hzColor
    have hIntw : ∀ i ∈ T ∩ I, G.Adj w i := fun i hi => hIw i (Finset.mem_inter.mp hi).2
    rcases hShared with hTR | hTS
    · exact shared_mono_forces_neighbors G s hbip h4 (T ∩ I) T R S hI hIntw
        Finset.inter_subset_left hTR hColor' hSafe hSBad
    · exact shared_mono_forces_neighbors G s hbip h4 (T ∩ I) T S R hI hIntw
        Finset.inter_subset_left hTS hColor' (safe_swap G R S hSafe) hRBad

lemma distinct_safe_centers_protected_factor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (P Q R S : Finset (Fin n)) {w z : Fin n}
    (hSafe : Safe G P Q w) (hSafe' : Safe G R S z) (hzw : z ≠ w)
    (hPBad : ∃ p ∈ P, ¬ G.Adj p w) (hQBad : ∃ q ∈ Q, ¬ G.Adj q w)
    (hRBad : ∃ p ∈ R, ¬ G.Adj p z) (hSBad : ∃ q ∈ S, ¬ G.Adj q z) :
    ∃ U : Finset (Fin n), (U = P ∨ U = Q) ∧ ∀ T ⊆ U, (T ⊆ R ∨ T ⊆ S) →
      (∀ t ∈ T, G.Adj w t) ∨ (T ∩ (P ∩ Q)).card ≤ 1 := by
  obtain ⟨p, hp, hpBad⟩ := hPBad
  obtain ⟨q, hq, hqBad⟩ := hQBad
  have hIw : ∀ i ∈ P ∩ Q, G.Adj w i :=
    fun _ hi => OverlapCase.safe_adj_overlap G P Q hSafe hi
  rcases safe_oriented_bad_factors G s hbip P Q hSafe hp hq hpBad hqBad with hPQ | hQP
  · by_cases hzColor : s z = s w
    · refine ⟨P, Or.inl rfl, ?_⟩
      intro T hTP hShared
      exact mixed_shared_subset_bound G s hbip h4 (P ∩ Q) T R S hIw hzColor hzw
        (fun t ht hBad => hPQ.1 t (hTP ht) hBad) hSafe' hRBad hSBad hShared
    · refine ⟨Q, Or.inr rfl, ?_⟩
      intro T hTQ hShared
      exact mono_shared_subset_bound G s hbip h4 (P ∩ Q) T R S hIw hzColor
        (fun t ht => hPQ.2 t (hTQ ht)) hSafe' hRBad hSBad hShared
  · by_cases hzColor : s z = s w
    · refine ⟨Q, Or.inr rfl, ?_⟩
      intro T hTQ hShared
      exact mixed_shared_subset_bound G s hbip h4 (P ∩ Q) T R S hIw hzColor hzw
        (fun t ht hBad => hQP.1 t (hTQ ht) hBad) hSafe' hRBad hSBad hShared
    · refine ⟨P, Or.inl rfl, ?_⟩
      intro T hTP hShared
      exact mono_shared_subset_bound G s hbip h4 (P ∩ Q) T R S hIw hzColor
        (fun t ht => hQP.2 t (hTP ht)) hSafe' hRBad hSBad hShared

end Sharing

end PEqualNP.Outside.L_meta_5012


namespace PEqualNP.Outside.L_meta_5012.PrivateRegion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

def overlap (n : ℕ) (C : Circuit) (g : ℕ) : Finset (Fin n) :=
  side (n := n) C g 0 ∩ side (n := n) C g 1

def Bad {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n)
    (I T : Finset (Fin n)) : Prop :=
  (¬ ∀ t ∈ T, G.Adj w t) ∧ 2 ≤ (T ∩ I).card

noncomputable def nodes {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (g : ℕ) (b : Fin 2) (w : Fin n) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun q =>
    (gateAt C q).op = GateOp.or ∧ OrReaches n C (opnd C g b) q ∧
      Bad G w (overlap n C g) (orIn n C (n+q))

lemma mem_nodes {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (g : ℕ) (b : Fin 2) (w : Fin n) (q : ℕ) :
    q ∈ nodes G C g b w ↔ q < C.gates.length ∧
      (gateAt C q).op = GateOp.or ∧ OrReaches n C (opnd C g b) q ∧
        Bad G w (overlap n C g) (orIn n C (n+q)) := by
  classical
  simp only [nodes, Finset.mem_filter, Finset.mem_range]

lemma bad_mono {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n)
    (I S T : Finset (Fin n)) (hST : S ⊆ T) (hBad : Bad G w I S) : Bad G w I T := by
  refine ⟨fun hGood => hBad.1 (fun t ht => hGood t (hST ht)), ?_⟩
  have hSub : S ∩ I ⊆ T ∩ I := by
    intro t ht
    exact Finset.mem_inter.mpr ⟨hST (Finset.mem_inter.mp ht).1, (Finset.mem_inter.mp ht).2⟩
  exact hBad.2.trans (Finset.card_le_card hSub)

lemma bad_excludes_protected {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n)
    (I T : Finset (Fin n)) (hBad : Bad G w I T)
    (hProtect : (∀ t ∈ T, G.Adj w t) ∨ (T ∩ I).card ≤ 1) : False := by
  rcases hProtect with hGood | hSmall
  · exact hBad.1 hGood
  · have := hBad.2
    omega

lemma nodes_before_junk {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hAO : IsAO2 n C) {g : ℕ} (hg : g < C.gates.length) (b : Fin 2) (w : Fin n)
    {q : ℕ} (hq : q ∈ nodes G C g b w) : q < g := by
  have hr := ((mem_nodes G C g b w q).mp hq).2.2.1
  have hle := Critical.Base.orStep_le (Critical.Base.orReaches_reach q _ hr).1
  have hback := Lift.opnd_lt hAO hg b
  omega

lemma bad_terminal_is_chosen {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTF : TopForm G C)
    {g h : ℕ} (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (b : Fin 2) (w : Fin n) (hW : wmax G C g = {w}) (h4 : NoFourCycle G)
    (hOtherOverlap : (overlap n C h).Nonempty)
    (hIw : ∀ i ∈ overlap n C g, G.Adj w i)
    (hProtected : ∀ T ⊆ side (n := n) C g b,
      (T ⊆ side (n := n) C h 0 ∨ T ⊆ side (n := n) C h 1) →
      (∀ t ∈ T, G.Adj w t) ∨ (T ∩ overlap n C g).card ≤ 1)
    (T : Finset (Fin n)) (hT : T ⊆ side (n := n) C g b)
    (hBad : Bad G w (overlap n C g) T)
    {a : ℕ} (ha : a < C.gates.length) (haAnd : (gateAt C a).op = GateOp.and)
    (c : Fin 2) (hTa : T ⊆ side (n := n) C a c) : a = g ∧ c = b := by
  classical
  by_cases hag : a = g
  · subst a
    refine ⟨rfl, ?_⟩
    rcases Critical.Base.eitherOperand b c with hcb | hcb
    · exact hcb
    · exfalso
      apply hBad.1
      intro t ht
      apply hIw
      have ht0 := hT ht
      have ht1 := hTa ht
      rw [hcb] at ht1
      fin_cases b
      · exact Finset.mem_inter.mpr ⟨ht0, ht1⟩
      · exact Finset.mem_inter.mpr ⟨ht1, ht0⟩
  · by_cases hah : a = h
    · subst a
      have hShared : T ⊆ side (n := n) C h 0 ∨ T ⊆ side (n := n) C h 1 := by
        fin_cases c
        · exact Or.inl hTa
        · exact Or.inr hTa
      exact (bad_excludes_protected G w _ T hBad (hProtected T hT hShared)).elim
    · have hNotJ : a ∉ junk G C := by
        intro haJ
        exact (Critical.Base.memJunkPair hJ haJ).elim hag hah
      have hBelow : BelowF G C a := by
        intro x hx
        by_contra hf
        exact hNotJ (CleanReplacement.mem_junk.mpr
          ⟨ha, haAnd, ha, x, hx, Bool.eq_false_iff.mpr hf⟩)
      have haTop : a ∈ tops G C := by
        simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
          And.intro ha (And.intro haAnd hBelow)
      have hProtect := OverlapCase.top_raw_boundary_protected G C hAO hTF hJ hgh hhg
        hW h4 hOtherOverlap (overlap n C g) T hIw haTop c hTa
      exact (bad_excludes_protected G w _ T hBad hProtect).elim

lemma private_readers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hTF : TopForm G C)
    {g h : ℕ} (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (b : Fin 2) (w : Fin n) (hW : wmax G C g = {w}) (h4 : NoFourCycle G)
    (hOtherOverlap : (overlap n C h).Nonempty)
    (hIw : ∀ i ∈ overlap n C g, G.Adj w i)
    (hProtected : ∀ T ⊆ side (n := n) C g b,
      (T ⊆ side (n := n) C h 0 ∨ T ⊆ side (n := n) C h 1) →
      (∀ t ∈ T, G.Adj w t) ∨ (T ∩ overlap n C g).card ≤ 1) :
    ∀ q ∈ nodes G C g b w, ∀ r < C.gates.length,
      n + q ∈ (gateAt C r).inputs → r ∈ nodes G C g b w ∨ r = g := by
  intro q hq r hr hread
  obtain ⟨hqLen, _, hqReach, hqBad⟩ := (mem_nodes G C g b w q).mp hq
  let T := orIn n C (n+q)
  have hT : T ⊆ side (n := n) C g b :=
    Critical.Base.orInTrans (Critical.Base.orReaches_reach q _ hqReach).1
  have hNoOutput (hp : Relation.ReflTransGen (Critical.Base.OrStep n C) C.output (n+q)) : False := by
    have hCard : 2 ≤ (T ∩ overlap n C g).card := hqBad.2
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < (T ∩ overlap n C g).card)
    have hiOut := Critical.Base.orInTrans hp (Finset.mem_inter.mp hi).1
    rw [OverlapCase.output_raw_frontier_empty G C hL.2.1] at hiOut
    exact Finset.notMem_empty i hiOut
  rcases hL.1.1 _ (Lift.gateAt_mem hr) with hrAnd | hrOr
  · obtain ⟨c, hc⟩ := Critical.Base.inputsAsOpnd hL.1 hr hread
    have hTa : T ⊆ side (n := n) C r c := by
      change orIn n C (n+q) ⊆ orIn n C (opnd C r c)
      rw [← hc]
    exact Or.inr (bad_terminal_is_chosen G C hL.1 hTF hJ hgh hhg b w hW h4
      hOtherOverlap hIw hProtected T hT hqBad hr hrAnd c hTa).1
  · have hStep : Critical.Base.OrStep n C (n+r) (n+q) :=
      ⟨r, hr, rfl, hrOr, hread, hL.1.2.1 r hr _ hread⟩
    have hQR : T ⊆ orIn n C (n+r) :=
      Critical.Base.orInTrans (Relation.ReflTransGen.single hStep)
    have hrBad := bad_mono G w (overlap n C g) T _ hQR hqBad
    have hrReach : OrReaches n C (opnd C g b) r := by
      rcases OrFrontier.least_or_frontier G C hL r hr with hpOut | ⟨a, c, ha, haAnd, hp⟩
      · exact (hNoOutput (hpOut.tail hStep)).elim
      · have hTa : T ⊆ side (n := n) C a c := Critical.Base.orInTrans (hp.tail hStep)
        obtain ⟨hag, hcb⟩ := bad_terminal_is_chosen G C hL.1 hTF hJ hgh hhg b w hW h4
          hOtherOverlap hIw hProtected T hT hqBad ha haAnd c hTa
        subst a
        subst c
        exact Critical.Base.reach_orReaches hp r rfl hr
    exact Or.inl ((mem_nodes G C g b w r).mpr ⟨hr, hrOr, hrReach, hrBad⟩)

lemma or_of_operand_path {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTF : TopForm G C)
    {g h : ℕ} (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (b : Fin 2) {q : ℕ} (hq : q < C.gates.length)
    (hp : Relation.ReflTransGen (Critical.Base.OrStep n C) (opnd C g b) (n+q)) :
    (gateAt C q).op = GateOp.or := by
  rcases hAO.1 _ (Lift.gateAt_mem hq) with hAnd | hOr
  · have hgJ : g ∈ junk G C := by rw [hJ]; simp
    obtain ⟨hg, hgAnd⟩ := RawOperands.junk_data G C g hgJ
    have hReach := Critical.Base.reach_orReaches hp q rfl hq
    have hqJ := Critical.Base.operandOrAndJunk hAO hTF hg hgAnd hReach hAnd
    have hCone := Critical.Base.operandReachCone hAO hg hReach
    exact (RawOperands.independent_no_junk_ancestors G C g h hJ hgh hhg g
      (Or.inl rfl) q hqJ hCone).elim
  · exact hOr

lemma raw_of_operand_path {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTF : TopForm G C)
    {g h : ℕ} (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (b : Fin 2) (u : ℕ)
    (hp : Relation.ReflTransGen (Critical.Base.OrStep n C) (opnd C g b) u)
    (x : Fin n → Bool) :
    wval C x u = decide (∃ i ∈ orIn n C u, x i = true) := by
  have hForward : wval C x u = true → ∃ i ∈ orIn n C u, x i = true := by
    intro hu
    rcases RawOperands.down n C x (fun q hq => hAO.1 _ (Lift.gateAt_mem hq)) u hu with
      hRaw | ⟨q, hq, hReach, hAnd, _⟩
    · exact hRaw
    · have hOr := or_of_operand_path G C hAO hTF hJ hgh hhg b hq
        (hp.trans (Critical.Base.orReaches_reach q _ hReach).1)
      rw [hOr] at hAnd
      cases hAnd
  have hBackward : (∃ i ∈ orIn n C u, x i = true) → wval C x u = true := by
    rintro ⟨i, hi, hxi⟩
    exact Critical.Base.reach_var_val x u i (Critical.Base.mem_orIn_reach i hi) hxi
  by_cases hu : wval C x u = true
  · simp [hu, hForward hu]
  · have hn : ¬ ∃ i ∈ orIn n C u, x i = true := fun hh => hu (hBackward hh)
    simp [Bool.eq_false_iff.mpr hu, hn]

lemma input_raw_card {n : ℕ} (C : Circuit) (u : ℕ) (hu : u < n) :
    (orIn n C u).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi t ht
  have hiu : i.val = u := by
    rcases (RawOperands.orIn_mem n C u i).mp hi with hh | ⟨q, _, hReach, _, _⟩
    · exact hh
    · have := hReach.1
      omega
  have htu : t.val = u := by
    rcases (RawOperands.orIn_mem n C u t).mp ht with hh | ⟨q, _, hReach, _, _⟩
    · exact hh
    · have := hReach.1
      omega
  exact Fin.ext (hiu.trans htu.symm)

lemma node_input_path {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hAO : IsAO2 n C) (g : ℕ) (b : Fin 2) (w : Fin n)
    {q u : ℕ} (hq : q ∈ nodes G C g b w) (hu : u ∈ (gateAt C q).inputs) :
    Relation.ReflTransGen (Critical.Base.OrStep n C) (opnd C g b) u := by
  obtain ⟨hqLen, hqOr, hqReach, _⟩ := (mem_nodes G C g b w q).mp hq
  exact ((Critical.Base.orReaches_reach q _ hqReach).1).tail
    ⟨q, hqLen, rfl, hqOr, hu, hAO.2.1 q hqLen u hu⟩

lemma boundary_protected {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTF : TopForm G C)
    {g h : ℕ} (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (b : Fin 2) (w : Fin n) {q u : ℕ}
    (hq : q ∈ nodes G C g b w) (hu : u ∈ (gateAt C q).inputs)
    (hExternal : ¬ (n ≤ u ∧ u - n ∈ nodes G C g b w)) :
    (∀ i ∈ orIn n C u, G.Adj w i) ∨ (orIn n C u ∩ overlap n C g).card ≤ 1 := by
  by_cases hun : u < n
  · exact Or.inr ((Finset.card_le_card Finset.inter_subset_left).trans (input_raw_card C u hun))
  · have hnu : n ≤ u := by omega
    have hqLen := ((mem_nodes G C g b w q).mp hq).1
    have hub := hAO.2.1 q hqLen u hu
    have huLen : u - n < C.gates.length := by omega
    have hRep : n + (u - n) = u := by omega
    have hp := node_input_path G C hAO g b w hq hu
    have huOr := or_of_operand_path G C hAO hTF hJ hgh hhg b huLen (by rwa [hRep])
    have huReach := Critical.Base.reach_orReaches hp (u-n) hRep.symm huLen
    by_cases hGood : ∀ i ∈ orIn n C u, G.Adj w i
    · exact Or.inl hGood
    · right
      by_contra hSmall
      have hBad : Bad G w (overlap n C g) (orIn n C (n+(u-n))) := by
        rw [hRep]
        exact ⟨hGood, by omega⟩
      exact hExternal ⟨hnu, (mem_nodes G C g b w (u-n)).mpr ⟨huLen, huOr, huReach, hBad⟩⟩

lemma root_mem_nodes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTF : TopForm G C)
    {g h : ℕ} (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (b : Fin 2) (w : Fin n) (hI : 2 ≤ (overlap n C g).card)
    (hBad : ¬ ∀ t ∈ side (n := n) C g b, G.Adj w t) :
    ∃ q ∈ nodes G C g b w, opnd C g b = n + q := by
  have hgJ : g ∈ junk G C := by rw [hJ]; simp
  have hg := (RawOperands.junk_data G C g hgJ).1
  have hIu : overlap n C g ⊆ side (n := n) C g b := by
    fin_cases b
    · exact Finset.inter_subset_left
    · exact Finset.inter_subset_right
  have hCard : 2 ≤ (side (n := n) C g b).card := hI.trans (Finset.card_le_card hIu)
  have hun : n ≤ opnd C g b := by
    by_contra hn
    have hc := input_raw_card (n := n) C (opnd C g b) (by omega)
    change (side (n := n) C g b).card ≤ 1 at hc
    omega
  have hRep : opnd C g b = n + (opnd C g b - n) := by omega
  have huBack := Lift.opnd_lt hAO hg b
  have hq : opnd C g b - n < C.gates.length := by omega
  have hp : Relation.ReflTransGen (Critical.Base.OrStep n C)
      (opnd C g b) (n + (opnd C g b - n)) := by rw [← hRep]
  have hOr := or_of_operand_path G C hAO hTF hJ hgh hhg b hq hp
  have hReach := Critical.Base.reach_orReaches hp (opnd C g b - n) rfl hq
  have hBad' : Bad G w (overlap n C g) (orIn n C (n + (opnd C g b - n))) := by
    rw [← hRep]
    refine ⟨hBad, ?_⟩
    change 2 ≤ (side (n := n) C g b ∩ overlap n C g).card
    rw [Finset.inter_eq_right.mpr hIu]
    exact hI
  exact ⟨_, (mem_nodes G C g b w _).mpr ⟨hq, hOr, hReach, hBad'⟩, hRep⟩

end PEqualNP.Outside.L_meta_5012.PrivateRegion


namespace PEqualNP.Outside.L_meta_5012.PrivateRegion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

noncomputable def protectedNodes {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (g : ℕ) (b : Fin 2) (w : Fin n) : Finset ℕ :=
  Finset.range g \ nodes G C g b w

lemma mem_protectedNodes {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (g : ℕ) (b : Fin 2) (w : Fin n) (q : ℕ) :
    q ∈ protectedNodes G C g b w ↔ q < g ∧ q ∉ nodes G C g b w := by
  simp only [protectedNodes, Finset.mem_sdiff, Finset.mem_range]

lemma protected_disjoint {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (g : ℕ) (b : Fin 2) (w : Fin n) :
    Disjoint (protectedNodes G C g b w) (nodes G C g b w) := by
  exact Finset.disjoint_left.mpr fun q hq hqJ => ((mem_protectedNodes G C g b w q).mp hq).2 hqJ

lemma protected_closed_of_private {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (hAO : IsAO2 n C) (g : ℕ) (hg : g < C.gates.length)
    (b : Fin 2) (w : Fin n)
    (hPrivate : ∀ q ∈ nodes G C g b w, ∀ r < C.gates.length,
      n + q ∈ (gateAt C r).inputs → r ∈ nodes G C g b w ∨ r = g) :
    ∀ q ∈ protectedNodes G C g b w, ∀ u ∈ (gateAt C q).inputs,
      n ≤ u → u - n ∈ protectedNodes G C g b w := by
  intro q hq u hu hnu
  obtain ⟨hqg, hqNot⟩ := (mem_protectedNodes G C g b w q).mp hq
  have hqLen : q < C.gates.length := by omega
  have hub := hAO.2.1 q hqLen u hu
  apply (mem_protectedNodes G C g b w (u-n)).mpr
  refine ⟨by omega, ?_⟩
  intro huJ
  have hRep : n + (u-n) = u := by omega
  rcases hPrivate (u-n) huJ q hqLen (by rwa [hRep]) with hqJ | hqEq
  · exact hqNot hqJ
  · omega

lemma boundary_mem_protected {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (hAO : IsAO2 n C) (g : ℕ) (hg : g < C.gates.length)
    (b : Fin 2) (w : Fin n) {q u : ℕ}
    (hq : q ∈ nodes G C g b w) (hu : u ∈ (gateAt C q).inputs)
    (hExternal : ¬ (n ≤ u ∧ u - n ∈ nodes G C g b w)) (hnu : n ≤ u) :
    u - n ∈ protectedNodes G C g b w := by
  have hqLen := ((mem_nodes G C g b w q).mp hq).1
  have hqg := nodes_before_junk G C hAO hg b w hq
  have hub := hAO.2.1 q hqLen u hu
  exact (mem_protectedNodes G C g b w (u-n)).mpr
    ⟨by omega, fun huJ => hExternal ⟨hnu, huJ⟩⟩

lemma nodes_not_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hF : circuitFun n C = graphFun G ∅)
    (g : ℕ) (b : Fin 2) (w : Fin n) {q : ℕ} (hq : q ∈ nodes G C g b w) :
    C.output ≠ n + q := by
  intro hOut
  have hBad := ((mem_nodes G C g b w q).mp hq).2.2.2
  have hEmpty := OverlapCase.output_raw_frontier_empty G C hF
  rw [hOut] at hEmpty
  have hCard := hBad.2
  rw [hEmpty] at hCard
  simp at hCard

end PEqualNP.Outside.L_meta_5012.PrivateRegion


namespace PEqualNP.Outside.L_meta_5012.PrivateRegion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

lemma distinct_filters_choose_private_factor {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hTF : TopForm G C) {g h : ℕ} (hne : g ≠ h) (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) g → ¬ OrReaches n C (opnd C a (1-b)) h)
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (w z : Fin n)
    (hW : wmax G C g = {w}) (hZ : wmax G C h = {z}) (hzw : z ≠ w)
    (hI : 2 ≤ (overlap n C g).card) (hH : (overlap n C h).Nonempty) :
    ∃ b : Fin 2,
      (∃ q ∈ nodes G C g b w, opnd C g b = n + q) ∧
      (∀ q ∈ nodes G C g b w, ∀ r < C.gates.length,
        n + q ∈ (gateAt C r).inputs → r ∈ nodes G C g b w ∨ r = g) := by
  classical
  have hJ' : junk G C = {h,g} := by rw [hJ, Finset.pair_comm]
  have hNoCommon' : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) h → ¬ OrReaches n C (opnd C a (1-b)) g := by
    intro a ha b hh hg
    have hFlip : 1 - (1 - b) = b := by fin_cases b <;> decide
    exact hNoCommon a ha (1-b) hg (by simpa only [hFlip] using hh)
  have hBadG (b : Fin 2) : ∃ p ∈ side (n := n) C g b, ¬ G.Adj p w := by
    by_contra hn
    push_neg at hn
    exact OverlapCase.no_independent_unique_filter_neighbor_factor G C hL hOne hTF hne hJ
      hgh hhg hNoCommon hW b (fun p hp => (hn p hp).symm)
  have hBadH (b : Fin 2) : ∃ p ∈ side (n := n) C h b, ¬ G.Adj p z := by
    by_contra hn
    push_neg at hn
    exact OverlapCase.no_independent_unique_filter_neighbor_factor G C hL hOne hTF
      (Ne.symm hne) hJ' hhg hgh hNoCommon' hZ b (fun p hp => (hn p hp).symm)
  have hEvalG (x : Fin n → Bool) : gateVal n C g x = IndependentDescent.product
      (side (n := n) C g 0) (side (n := n) C g 1) x :=
    RawOperands.independent_product G C hL.1 hTF g h hJ hgh hhg g (Or.inl rfl) x
  have hEvalH (x : Fin n → Bool) : gateVal n C h x = IndependentDescent.product
      (side (n := n) C h 0) (side (n := n) C h 1) x :=
    RawOperands.independent_product G C hL.1 hTF g h hJ hgh hhg h (Or.inr rfl) x
  have hSafeG := (IndependentDescent.wmax_iff G C g _ _ hEvalG w).mp (by rw [hW]; simp)
  have hSafeH := (IndependentDescent.wmax_iff G C h _ _ hEvalH z).mp (by rw [hZ]; simp)
  have hIw : ∀ i ∈ overlap n C g, G.Adj w i := fun i hi =>
    OverlapCase.safe_adj_overlap G _ _ hSafeG hi
  obtain ⟨U, hU, hProtect⟩ := Sharing.distinct_safe_centers_protected_factor G s hbip h4
    (side (n := n) C g 0) (side (n := n) C g 1)
    (side (n := n) C h 0) (side (n := n) C h 1) hSafeG hSafeH hzw
    (hBadG 0) (hBadG 1) (hBadH 0) (hBadH 1)
  have hFinish (b : Fin 2) (hUb : U = side (n := n) C g b) :
      (∃ q ∈ nodes G C g b w, opnd C g b = n + q) ∧
      (∀ q ∈ nodes G C g b w, ∀ r < C.gates.length,
        n + q ∈ (gateAt C r).inputs → r ∈ nodes G C g b w ∨ r = g) := by
    have hBad : ¬ ∀ t ∈ side (n := n) C g b, G.Adj w t := by
      intro hGood
      obtain ⟨t, ht, htBad⟩ := hBadG b
      exact htBad (hGood t ht).symm
    refine ⟨root_mem_nodes G C hL.1 hTF hJ hgh hhg b w hI hBad, ?_⟩
    apply private_readers G C hL hTF hJ hgh hhg b w hW h4 hH hIw
    intro T hT hShared
    exact hProtect T (by simpa only [hUb] using hT) hShared
  rcases hU with hU | hU
  · exact ⟨0, hFinish 0 hU⟩
  · exact ⟨1, hFinish 1 hU⟩

end PEqualNP.Outside.L_meta_5012.PrivateRegion


namespace PEqualNP.Outside.L_meta_5012.PrivateRegion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

noncomputable def independentProtected {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (g : ℕ) (b : Fin 2) (w : Fin n) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun q =>
    q ∉ nodes G C g b w ∧ q ≠ g ∧ ¬ InCone n C g q

lemma mem_independentProtected {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (g : ℕ) (b : Fin 2) (w : Fin n) (q : ℕ) :
    q ∈ independentProtected G C g b w ↔ q < C.gates.length ∧
      q ∉ nodes G C g b w ∧ q ≠ g ∧ ¬ InCone n C g q := by
  classical
  simp only [independentProtected, Finset.mem_filter, Finset.mem_range]

lemma independentProtected_closed {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (hAO : IsAO2 n C) (g : ℕ) (b : Fin 2) (w : Fin n)
    (hPrivate : ∀ q ∈ nodes G C g b w, ∀ r < C.gates.length,
      n + q ∈ (gateAt C r).inputs → r ∈ nodes G C g b w ∨ r = g) :
    ∀ q ∈ independentProtected G C g b w, ∀ u ∈ (gateAt C q).inputs,
      n ≤ u → u - n ∈ independentProtected G C g b w := by
  intro q hq u hu hnu
  obtain ⟨hqLen, hqNot, hqNe, hqCone⟩ := (mem_independentProtected G C g b w q).mp hq
  have hub := hAO.2.1 q hqLen u hu
  have hRep : n + (u-n) = u := by omega
  have hDirect : InCone n C (u-n) q :=
    (Lift.inCone_iff hqLen).mpr ⟨u, hu, hnu, hub, Or.inl rfl⟩
  apply (mem_independentProtected G C g b w (u-n)).mpr
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro huJ
    rcases hPrivate (u-n) huJ q hqLen (by rwa [hRep]) with hqJ | hqEq
    · exact hqNot hqJ
    · exact hqNe hqEq
  · intro he
    exact hqCone (he ▸ hDirect)
  · intro hCone
    exact hqCone (Lift.inCone_trans hCone hDirect)

lemma other_mem_independentProtected {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) {g h : ℕ} (hne : g ≠ h) (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (b : Fin 2) (w : Fin n) :
    h ∈ independentProtected G C g b w := by
  have hhJ : h ∈ junk G C := by rw [hJ]; simp
  obtain ⟨hh, hhAnd⟩ := RawOperands.junk_data G C h hhJ
  apply (mem_independentProtected G C g b w h).mpr
  refine ⟨hh, ?_, Ne.symm hne, hgh⟩
  intro hhNodes
  have hhOr := ((mem_nodes G C g b w h).mp hhNodes).2.1
  rw [hhAnd] at hhOr
  cases hhOr

end PEqualNP.Outside.L_meta_5012.PrivateRegion


namespace PEqualNP.Outside.L_meta_5012.PrivateRegion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

lemma nodes_support_union {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTF : TopForm G C)
    {g h : ℕ} (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (b : Fin 2) (w : Fin n) {q : ℕ} (hq : q ∈ nodes G C g b w)
    (a c : ℕ) (hInputs : (gateAt C q).inputs = [a,c]) :
    orIn n C (n+q) = orIn n C a ∪ orIn n C c := by
  obtain ⟨hqLen, hqOr, hqReach, _⟩ := (mem_nodes G C g b w q).mp hq
  have ha : a ∈ (gateAt C q).inputs := by rw [hInputs]; simp
  have hc : c ∈ (gateAt C q).inputs := by rw [hInputs]; simp
  have hp := (Critical.Base.orReaches_reach q _ hqReach).1
  have hpa := node_input_path G C hAO g b w hq ha
  have hpc := node_input_path G C hAO g b w hq hc
  apply Finset.ext
  intro i
  let x : Fin n → Bool := fun t => decide (t = i)
  have hRawQ := raw_of_operand_path G C hAO hTF hJ hgh hhg b (n+q) hp x
  have hRawA := raw_of_operand_path G C hAO hTF hJ hgh hhg b a hpa x
  have hRawC := raw_of_operand_path G C hAO hTF hJ hgh hhg b c hpc x
  have hEval := Lift.wval_gate_or hAO x hqLen hqOr
  have hOpA : opnd C q 0 = a := by simp [opnd, hInputs]
  have hOpC : opnd C q 1 = c := by simp [opnd, hInputs]
  rw [hOpA, hOpC, hRawQ, hRawA, hRawC] at hEval
  have hEq : decide (i ∈ orIn n C (n+q)) =
      (decide (i ∈ orIn n C a) || decide (i ∈ orIn n C c)) := by
    simpa [x] using hEval
  have hTrue : decide (i ∈ orIn n C (n+q)) = true ↔
      (decide (i ∈ orIn n C a) || decide (i ∈ orIn n C c)) = true := by rw [hEq]
  simpa only [decide_eq_true_eq, Bool.or_eq_true, Finset.mem_union] using hTrue

end PEqualNP.Outside.L_meta_5012.PrivateRegion


namespace PEqualNP.Outside.L_meta_5012.OverlapCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

lemma independent_large_overlaps_distinct_filters_impossible {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hT : TopForm G C) {g h : ℕ} (hne : g ≠ h) (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G)
    (hLargeG : 2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card)
    (hLargeH : 2 ≤ (side (n := n) C h 0 ∩ side (n := n) C h 1).card)
    (w z : Fin n) (hW : wmax G C g = {w}) (hZ : wmax G C h = {z})
    (hwz : w ≠ z) : False := by
  classical
  have hNoCommon := both_large_overlap_no_opposite G C hL.1 hT hJ hgh hhg h4 hLargeG hLargeH
  have hgJ : g ∈ junk G C := by rw [hJ]; simp
  have hhJ : h ∈ junk G C := by rw [hJ]; simp
  have hg := (RawOperands.junk_data G C g hgJ).1
  have hTwo : (junk G C).card = 2 := by simp [hJ,hne]
  have hH : (PrivateRegion.overlap n C h).Nonempty := by
    apply Finset.card_pos.mp
    change 0 < (side (n := n) C h 0 ∩ side (n := n) C h 1).card
    omega
  obtain ⟨b,⟨r,hr,hroot⟩,hprivate⟩ :=
    PrivateRegion.distinct_filters_choose_private_factor G C hL hOne hT hne hJ hgh hhg
      hNoCommon s hbip h4 w z hW hZ (Ne.symm hwz) hLargeG hH
  obtain ⟨d,hd⟩ : (PrivateRegion.overlap n C g).Nonempty := by
    apply Finset.card_pos.mp
    change 0 < (side (n := n) C g 0 ∩ side (n := n) C g 1).card
    omega
  have hWmem : w ∈ wmax G C g := by rw [hW]; simp
  have hwOut : w ∉ side (n := n) C g 0 ∪ side (n := n) C g 1 := by
    intro hin
    exact no_independent_overlap_filter_inside G C hL hOne hT hne hJ hgh hhg
      hNoCommon h4 hLargeG hWmem hin
  have hEval (x : Fin n → Bool) : gateVal n C g x = IndependentDescent.product
      (side (n := n) C g 0) (side (n := n) C g 1) x :=
    RawOperands.independent_product G C hL.1 hT g h hJ hgh hhg g (Or.inl rfl) x
  have hSafe := (IndependentDescent.wmax_iff G C g _ _ hEval w).mp hWmem
  have hIw : ∀ i ∈ PrivateRegion.overlap n C g, G.Adj w i := fun i hi =>
    safe_adj_overlap G _ _ hSafe hi
  have hIroot : PrivateRegion.overlap n C g ⊆ orIn n C (n+r) := by
    rw [← hroot]
    change PrivateRegion.overlap n C g ⊆ side (n := n) C g b
    fin_cases b
    · exact Finset.inter_subset_left
    · exact Finset.inter_subset_right
  apply OrProjection.projection_contradiction_of_boundaries G C hL hOne hTwo g h r w d
    hgJ hhJ (PrivateRegion.nodes G C g b w) (PrivateRegion.protectedNodes G C g b w)
    (PrivateRegion.independentProtected G C g b w) (orIn n C) (PrivateRegion.overlap n C g)
    hd hIw
    (fun j hj => PrivateRegion.nodes_before_junk G C hL.1 hg b w hj) hr
    (PrivateRegion.protected_disjoint G C g b w)
    (PrivateRegion.protected_closed_of_private G C hL.1 g hg b w hprivate)
    _ _ _ _ hIroot hprivate _ _
    (PrivateRegion.other_mem_independentProtected G C hne hJ hgh b w) _
    (PrivateRegion.independentProtected_closed G C hL.1 g b w hprivate)
  · intro j hj u hu huJ hnu
    exact PrivateRegion.boundary_mem_protected G C hL.1 g hg b w hj hu huJ hnu
  · intro j hj u hu huJ
    exact PrivateRegion.boundary_protected G C hL.1 hT hJ hgh hhg b w hj hu huJ
  · intro j hj u hu _ x
    exact PrivateRegion.raw_of_operand_path G C hL.1 hT hJ hgh hhg b u
      (PrivateRegion.node_input_path G C hL.1 g b w hj hu) x
  · intro j hj a c hinputs
    exact PrivateRegion.nodes_support_union G C hL.1 hT hJ hgh hhg b w hj a c hinputs
  · intro hOutput
    have hrep : C.output = n+(C.output-n) := by have := hOutput.1; omega
    exact PrivateRegion.nodes_not_output G C hL.2.1 g b w hOutput.2 hrep
  · intro u v huv hcut
    exact critical_overlap_cover G C hL.1 hL.2.1 hT hne hJ hgh hhg hNoCommon
      w hW hwOut u v huv hcut
  · intro j hj
    have hmem := (PrivateRegion.mem_independentProtected G C g b w j).mp hj
    exact ⟨hmem.2.1,hmem.2.2.1⟩

lemma independent_large_overlaps_same_filters {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hT : TopForm G C) {g h : ℕ} (hne : g ≠ h) (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G)
    (hLargeG : 2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card)
    (hLargeH : 2 ≤ (side (n := n) C h 0 ∩ side (n := n) C h 1).card) :
    wmax G C g = wmax G C h := by
  have hNoCommon := both_large_overlap_no_opposite G C hL.1 hT hJ hgh hhg h4 hLargeG hLargeH
  have hJ' : junk G C = {h,g} := by rw [hJ,Finset.pair_comm]
  have hNoCommon' := both_large_overlap_no_opposite G C hL.1 hT hJ' hhg hgh h4 hLargeH hLargeG
  obtain ⟨w,hW,_⟩ := independent_overlap_unique_outside G C hL hOne hT hne hJ hgh hhg
    hNoCommon h4 hLargeG
  obtain ⟨z,hZ,_⟩ := independent_overlap_unique_outside G C hL hOne hT (Ne.symm hne) hJ' hhg hgh
    hNoCommon' h4 hLargeH
  by_cases hwz : w = z
  · rw [hW,hZ,hwz]
  · exact False.elim (independent_large_overlaps_distinct_filters_impossible G C hL hOne hT
      hne hJ hgh hhg s hbip h4 hLargeG hLargeH w z hW hZ hwz)

end PEqualNP.Outside.L_meta_5012.OverlapCase
