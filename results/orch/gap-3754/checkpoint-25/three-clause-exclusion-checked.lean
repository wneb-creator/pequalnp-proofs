import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3754.ThreeClause
open PEqualNP.TopForm

def PairSpec {n : ℕ} (G : SimpleGraph (Fin n)) (U V B : Finset (Fin n)) : Prop :=
  ∀ u v,G.Adj u v ↔ (u∈U ∨ v∈U) ∧ (u∈V ∨ v∈V) ∧ (u∈B ∨ v∈B)

def TripleSpec {n : ℕ} (G : SimpleGraph (Fin n)) (U V B : Finset (Fin n)) : Prop :=
  ∀ u∈U,∀ v∈V,∀ b∈B,G.Adj u v ∨ G.Adj u b ∨ G.Adj v b

lemma not_subset_witness {α : Type} [DecidableEq α] (A B : Finset α) (h : ¬A⊆B) :
    ∃ x,x∈A ∧ x∉B := by
  classical
  by_contra! hc
  exact h (fun x hx => hc x hx)

lemma not_disjoint_witness {α : Type} [DecidableEq α] (A B : Finset α) (h : ¬Disjoint A B) :
    ∃ x,x∈A ∧ x∈B := by
  classical
  by_contra! hc
  exact h (Finset.disjoint_left.mpr (fun x hx hxb => hc x hx hxb))

lemma some_disjoint_pair {n : ℕ} (G : SimpleGraph (Fin n)) (U V B : Finset (Fin n))
    (s : Fin n → Bool) (hcolor : ∀ u v,G.Adj u v → s u≠s v)
    (hp : PairSpec G U V B) : Disjoint U V ∨ Disjoint V B ∨ Disjoint B U := by
  classical
  by_cases huv : Disjoint U V
  · exact Or.inl huv
  by_cases hvb : Disjoint V B
  · exact Or.inr (Or.inl hvb)
  by_cases hbu : Disjoint B U
  · exact Or.inr (Or.inr hbu)
  obtain ⟨a,haU,haV⟩ := not_disjoint_witness U V huv
  obtain ⟨b,hbV,hbB⟩ := not_disjoint_witness V B hvb
  obtain ⟨c,hcB,hcU⟩ := not_disjoint_witness B U hbu
  have hab := hcolor a b ((hp a b).mpr ⟨Or.inl haU,Or.inl haV,Or.inr hbB⟩)
  have hbc := hcolor b c ((hp b c).mpr ⟨Or.inr hcU,Or.inl hbV,Or.inl hbB⟩)
  have hca := hcolor c a ((hp c a).mpr ⟨Or.inl hcU,Or.inr haV,Or.inl hcB⟩)
  cases hsa : s a <;> cases hsb : s b <;> cases hsc : s c <;> simp_all

lemma common_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (x y a b : Fin n) (hxy : x≠y)
    (hxa : G.Adj x a) (hya : G.Adj y a) (hxb : G.Adj x b) (hyb : G.Adj y b) : a=b := by
  exact Finset.card_le_one.mp (h4 x y hxy) a (by simp [hxa,hya]) b (by simp [hxb,hyb])

lemma oriented_double_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (U V B : Finset (Fin n)) (h4 : NoFourCycle G)
    (hp : PairSpec G U V B) (ht : TripleSpec G U V B) (hd : Disjoint U V)
    (hUB : ¬U⊆B) (hVB : ¬V⊆B) (hBU : ¬B⊆U) (hBV : ¬B⊆V) :
    ∃ e h,e∈U ∧ h∈V ∧ U∩B={e} ∧ V∩B={h} ∧ B={e,h} ∧ 2≤U.card ∧ 2≤V.card := by
  classical
  obtain ⟨u,hu,hunB⟩ := not_subset_witness U B hUB
  obtain ⟨v,hv,hvnB⟩ := not_subset_witness V B hVB
  have hunV : u∉V := fun hh => Finset.disjoint_left.mp hd hu hh
  have hvnU : v∉U := fun hh => Finset.disjoint_left.mp hd hh hv
  have hsub : B⊆U∪V := by
    intro b hb
    by_contra hbu
    have hbU : b∉U := fun hh => hbu (Finset.mem_union_left V hh)
    have hbV : b∉V := fun hh => hbu (Finset.mem_union_right U hh)
    rcases ht u hu v hv b hb with huv | hub | hvb
    · exact ((hp u v).mp huv).2.2.elim hunB hvnB
    · exact ((hp u b).mp hub).2.1.elim hunV hbV
    · exact ((hp v b).mp hvb).1.elim hvnU hbU
  obtain ⟨e,heB,henV⟩ := not_subset_witness B V hBV
  obtain ⟨h,hhB,hhnU⟩ := not_subset_witness B U hBU
  have heU : e∈U := (Finset.mem_union.mp (hsub heB)).resolve_right henV
  have hhV : h∈V := (Finset.mem_union.mp (hsub hhB)).resolve_left hhnU
  have cross (a b : Fin n) (ha : a∈U) (hb : b∈V) (hB : a∈B ∨ b∈B) : G.Adj a b :=
    (hp a b).mpr ⟨Or.inl ha,Or.inr hb,hB⟩
  have hE : ∀ z,z∈U → z∈B → z=e := by
    intro z hzU hzB
    by_contra hze
    have hhv := common_eq G h4 z e h v hze
      (cross z h hzU hhV (Or.inl hzB)) (cross e h heU hhV (Or.inl heB))
      (cross z v hzU hv (Or.inl hzB)) (cross e v heU hv (Or.inl heB))
    exact hvnB (hhv ▸ hhB)
  have hH : ∀ z,z∈V → z∈B → z=h := by
    intro z hzV hzB
    by_contra hzh
    have heu := common_eq G h4 z h e u hzh
      (cross e z heU hzV (Or.inr hzB)).symm (cross e h heU hhV (Or.inr hhB)).symm
      (cross u z hu hzV (Or.inr hzB)).symm (cross u h hu hhV (Or.inr hhB)).symm
    exact hunB (heu ▸ heB)
  refine ⟨e,h,heU,hhV,?_,?_,?_,?_,?_⟩
  · ext z
    simp only [Finset.mem_inter,Finset.mem_singleton]
    exact ⟨fun hz => hE z hz.1 hz.2,fun hz => hz.symm ▸ ⟨heU,heB⟩⟩
  · ext z
    simp only [Finset.mem_inter,Finset.mem_singleton]
    exact ⟨fun hz => hH z hz.1 hz.2,fun hz => hz.symm ▸ ⟨hhV,hhB⟩⟩
  · ext z
    constructor
    · intro hz
      rcases Finset.mem_union.mp (hsub hz) with hzU | hzV
      · simp [hE z hzU hz]
      · simp [hH z hzV hz]
    · intro hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      exact hz.elim (fun hz => hz.symm ▸ heB) (fun hz => hz.symm ▸ hhB)
  · by_contra hn
    have hc : U.card≤1 := by omega
    have heu := Finset.card_le_one.mp hc e heU u hu
    exact hunB (heu ▸ heB)
  · by_contra hn
    have hc : V.card≤1 := by omega
    have hhv := Finset.card_le_one.mp hc h hhV v hv
    exact hvnB (hhv ▸ hhB)


open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def orQ {n : ℕ} (Q : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ u∈Q,x u=true)

lemma graphFun_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x=true ↔ ∃ u v : Fin n,G.Adj u v ∧ x u=true ∧ x v=true := by
  unfold graphFun
  simp

lemma graphFun_pair_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v)=true ↔ G.Adj u v := by
  rw [graphFun_iff]
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    unfold pairInput at ha hb
    simp only [decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd hab (G.loopless.irrefl _)
    · exact hab
    · exact hab.symm
    · exact absurd hab (G.loopless.irrefl _)
  · intro huv
    exact ⟨u,v,huv,by simp [pairInput],by simp [pairInput]⟩

lemma orQ_pair {n : ℕ} (Q : Finset (Fin n)) (u v : Fin n) :
    orQ Q (pairInput u v)=true ↔ u∈Q ∨ v∈Q := by
  simp only [orQ,pairInput,decide_eq_true_eq]
  constructor
  · rintro ⟨w,hw,hwu | hwv⟩
    · exact Or.inl (hwu ▸ hw)
    · exact Or.inr (hwv ▸ hw)
  · rintro (hu | hv)
    · exact ⟨u,hu,Or.inl rfl⟩
    · exact ⟨v,hv,Or.inr rfl⟩

lemma product_specs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (U V B : Finset (Fin n))
    (hf : ∀ x : Fin n → Bool,graphFun G ∅ x=(orQ U x && orQ V x && orQ B x)) :
    PairSpec G U V B ∧ TripleSpec G U V B := by
  constructor
  · intro u v
    rw [←graphFun_pair_iff u v,hf]
    simp only [Bool.and_eq_true,orQ_pair,and_assoc]
  · intro u hu v hv b hb
    let x : Fin n → Bool := fun w => decide (w=u ∨ w=v ∨ w=b)
    have hU : orQ U x=true := decide_eq_true ⟨u,hu,by simp [x]⟩
    have hV : orQ V x=true := decide_eq_true ⟨v,hv,by simp [x]⟩
    have hB : orQ B x=true := decide_eq_true ⟨b,hb,by simp [x]⟩
    have hF : graphFun G ∅ x=true := by rw [hf,hU,hV,hB];rfl
    obtain ⟨a,c,hac,ha,hc⟩ := (graphFun_iff x).mp hF
    simp only [x,decide_eq_true_eq] at ha hc
    rcases ha with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl
    all_goals first
      | exact (G.loopless.irrefl _ hac).elim
      | exact Or.inl hac
      | exact Or.inl hac.symm
      | exact Or.inr (Or.inl hac)
      | exact Or.inr (Or.inl hac.symm)
      | exact Or.inr (Or.inr hac)
      | exact Or.inr (Or.inr hac.symm)

def DoubleStar {n : ℕ} (U V B : Finset (Fin n)) : Prop :=
  Disjoint U V ∧ ∃ e h,e∈U ∧ h∈V ∧ U∩B={e} ∧ V∩B={h} ∧ B={e,h} ∧ 2≤U.card ∧ 2≤V.card

lemma cyclic_specs {n : ℕ} (G : SimpleGraph (Fin n)) (U V B : Finset (Fin n))
    (hp : PairSpec G U V B) (ht : TripleSpec G U V B) :
    PairSpec G V B U ∧ TripleSpec G V B U := by
  constructor
  · intro u v
    constructor
    · intro h
      have h := (hp u v).mp h
      exact ⟨h.2.1,h.2.2,h.1⟩
    · rintro ⟨hV,hB,hU⟩
      exact (hp u v).mpr ⟨hU,hV,hB⟩
  · intro v hv b hb u hu
    rcases ht u hu v hv b hb with huv | hub | hvb
    · exact Or.inr (Or.inl huv.symm)
    · exact Or.inr (Or.inr hub.symm)
    · exact Or.inl hvb

lemma irredundant_product_double_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (U V B : Finset (Fin n)) (s : Fin n → Bool)
    (hcolor : ∀ u v,G.Adj u v → s u≠s v) (h4 : NoFourCycle G)
    (hf : ∀ x : Fin n → Bool,graphFun G ∅ x=(orQ U x && orQ V x && orQ B x))
    (hUV : ¬U⊆V) (hVU : ¬V⊆U) (hUB : ¬U⊆B) (hBU : ¬B⊆U)
    (hVB : ¬V⊆B) (hBV : ¬B⊆V) :
    DoubleStar U V B ∨ DoubleStar V B U ∨ DoubleStar B U V := by
  obtain ⟨hp,ht⟩ := product_specs G U V B hf
  rcases some_disjoint_pair G U V B s hcolor hp with hd | hd | hd
  · exact Or.inl ⟨hd,oriented_double_star G U V B h4 hp ht hd hUB hVB hBU hBV⟩
  · obtain ⟨hp',ht'⟩ := cyclic_specs G U V B hp ht
    exact Or.inr (Or.inl ⟨hd,oriented_double_star G V B U h4 hp' ht' hd hVU hBU hUV hUB⟩)
  · obtain ⟨hp',ht'⟩ := cyclic_specs G U V B hp ht
    obtain ⟨hp'',ht''⟩ := cyclic_specs G V B U hp' ht'
    exact Or.inr (Or.inr ⟨hd,oriented_double_star G B U V h4 hp'' ht'' hd hBV hUV hVB hVU⟩)

end PEqualNP.Outside.L_meta_3754.ThreeClause

-- The OR family bound below is reused from the checked semantic proof library.

namespace PEqualNP.Outside.L_meta_3754.ClauseCost

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

theorem val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem gate_cases {X : Type} (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (f : X → ℕ → Bool) (z : X) :
    (∀ y, g.op.eval (g.inputs.map (f y)) = false) ∨
    ∃ a b, g.op.eval (g.inputs.map (f z)) = false →
      (f z a = false ∧ f z b = false ∧
        ∀ y, g.op.eval (g.inputs.map (f y)) = true → f y a = true ∨ f y b = true) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · right
      exact ⟨0, 0, by simp [GateOp.eval]⟩
    · left
      simp [GateOp.eval]
  | [a], _ =>
    right
    refine ⟨a, a, ?_⟩
    rcases hop with rfl | rfl <;> simp [GateOp.eval]
  | [a, b], _ =>
    rcases hop with rfl | rfl
    · right
      by_cases h : f z a = false
      · refine ⟨a, a, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro _
        exact ⟨h, h, fun y hy => Or.inl hy.1⟩
      · refine ⟨b, b, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro hz
        have hb : f z b = false := by
          cases ha : f z a <;> cases hb : f z b <;> simp_all
        exact ⟨hb, hb, fun y hy => Or.inl hy.2⟩
    · right
      refine ⟨a, b, ?_⟩
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id_eq, Bool.or_eq_true, Bool.or_eq_false_iff]
      intro hz
      exact ⟨hz.1, hz.2, fun y hy => hy⟩
  | _ :: _ :: _ :: _, h => simp at h

def Zof {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun c => decide (c ∉ S)

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def Inv {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, val gs (Zof S) i = false → val gs (eof u) i = true → val gs (eof v) i = true →
    u ∈ S ∧ l u = l v

def Cnt {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Prop :=
  val gs (Zof S) i = false ∧
    ∃ u v : Fin n, u ≠ v ∧ val gs (eof u) i = true ∧ val gs (eof v) i = true

open Classical in
noncomputable def D {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i =>
    Cnt S gs i ∧ (gs[i - n]?).map Gate.op = some GateOp.or

open Classical in
noncomputable def orGates (n : ℕ) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i =>
    (gs[i - n]?).map Gate.op = some GateOp.or

theorem D_mono {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    D S gs ⊆ D S (gs ++ [g]) := by
  classical
  intro i hi
  simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨⟨hz, u, v, huv, hu, hv⟩, hop⟩ := hi.2
  constructor
  · refine ⟨?_, u, v, huv, ?_, ?_⟩
    · rw [val_snoc, ite_eq_right hne]; exact hz
    · rw [val_snoc, ite_eq_right hne]; exact hu
    · rw [val_snoc, ite_eq_right hne]; exact hv
  · rw [List.getElem?_append_left (by omega)]
    exact hop

lemma merging_is_or {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (l : Fin n → Fin n) (hinv : Inv S gs l) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hz : g.op.eval (g.inputs.map fun j => val gs (Zof S) j) = false)
    {u v : Fin n}
    (hu : g.op.eval (g.inputs.map fun j => val gs (eof u) j) = true)
    (hv : g.op.eval (g.inputs.map fun j => val gs (eof v) j) = true)
    (hne : l u ≠ l v) : g.op = GateOp.or := by
  rcases hop with hop | hop
  · exfalso
    rw [hop] at hz hu hv
    simp only [GateOp.eval, List.all_map, Function.comp_def, id_eq,
      List.all_eq_true] at hu hv
    have hnot : ¬ ∀ i ∈ g.inputs, val gs (Zof S) i = true := by
      intro hall
      have htrue : GateOp.and.eval (g.inputs.map fun j => val gs (Zof S) j) = true := by
        simp only [GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true]
        exact hall
      simp_all
    push Not at hnot
    obtain ⟨i, hi, hfalse⟩ := hnot
    have hz' : val gs (Zof S) i = false := by
      cases h : val gs (Zof S) i <;> simp_all
    exact hne (hinv i u v hz' (hu i hi) (hv i hi)).2
  · exact hop

theorem main_inv {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ l : Fin n → Fin n, Inv S gs l ∧ S.card ≤ (S.image l).card + (D S gs).card := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, by simp⟩
    intro i u v hz hu hv
    rw [val_nil] at hz hu hv
    by_cases h : i < n
    · simp only [h, dite_true, Zof, eof, decide_eq_false_iff_not, not_not,
        decide_eq_true_eq] at hz hu hv
      subst hu
      subst hv
      exact ⟨hz, rfl⟩
    · simp [h] at hu
  | append_singleton gs g ih =>
    obtain ⟨l, hinv, hcard⟩ := ih (fun g' hg' => hg g' (by simp [hg']))
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    set N := n + gs.length with hN
    set P : (Fin n → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun j => val gs x j)
      with hP
    have hnew : ∀ x : Fin n → Bool, val (gs ++ [g]) x N = P x := by
      intro x
      rw [val_snoc, ite_eq_left hN]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → val (gs ++ [g]) x i = val gs x i := by
      intro x i hi
      rw [val_snoc, ite_eq_right hi]
    -- facts about the new wire from the old invariant
    have key : P (Zof S) = false → ∀ u, P (eof u) = true →
        u ∈ S ∧ ∃ A B : Fin n → Prop, (∀ w, P (eof w) = true → A w ∨ B w) ∧
          (∀ w w', A w → A w' → l w = l w') ∧ (∀ w w', B w → B w' → l w = l w') := by
      intro hz u hu
      rcases gate_cases g hop hlen (fun x j => val gs x j) (Zof S) with hall | ⟨a, b, hab⟩
      · have := hall (eof u)
        simp only [hP] at hu
        rw [this] at hu
        exact absurd hu (by simp)
      · obtain ⟨ha, hb, hy⟩ := hab hz
        refine ⟨?_, fun w => val gs (eof w) a = true, fun w => val gs (eof w) b = true,
          fun w hw => hy (eof w) hw, fun w w' hw hw' => (hinv a w w' ha hw hw').2,
          fun w w' hw hw' => (hinv b w w' hb hw hw').2⟩
        rcases hy (eof u) hu with h | h
        · exact (hinv a u u ha h h).1
        · exact (hinv b u u hb h h).1
    by_cases hm : P (Zof S) = false ∧ ∃ u v, P (eof u) = true ∧ P (eof v) = true ∧ l u ≠ l v
    · obtain ⟨hz, u0, v0, hu0, hv0, hne⟩ := hm
      have hgor : g.op = GateOp.or := merging_is_or S gs l hinv g hop hz hu0 hv0 hne
      refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, A, B, hAB, hA, hB⟩ := key hiz u hiu
          refine ⟨huS, ?_⟩
          have two : ∀ w, P (eof w) = true → l w = l u0 ∨ l w = l v0 := by
            intro w hw
            rcases hAB w hw with h | h <;> rcases hAB u0 hu0 with h0 | h0 <;>
              rcases hAB v0 hv0 with h1 | h1
            · exact Or.inl (hA w u0 h h0)
            · exact Or.inl (hA w u0 h h0)
            · exact Or.inr (hA w v0 h h1)
            · exact absurd (hB u0 v0 h0 h1) hne
            · exact absurd (hA u0 v0 h0 h1) hne
            · exact Or.inr (hB w v0 h h1)
            · exact Or.inl (hB w u0 h h0)
            · exact Or.inl (hB w u0 h h0)
          have red : ∀ w, P (eof w) = true → (if l w = l v0 then l u0 else l w) = l u0 := by
            intro w hw
            rcases two w hw with h | h
            · rw [h]; split_ifs <;> rfl
            · rw [ite_eq_left h]
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [red u hiu, red v hiv]
        · rw [hold _ _ hi] at hiz hiu hiv
          obtain ⟨huS, hl⟩ := hinv i u v hiz hiu hiv
          refine ⟨huS, ?_⟩
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [hl]
      · have himg : S.image l ⊆
            insert (l v0) (S.image fun w => if l w = l v0 then l u0 else l w) := by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
          by_cases h : l w = l v0
          · rw [h]; exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
            rw [ite_eq_right h]
        have h1 : (S.image l).card ≤
            (S.image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
          (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
        have hNin : N ∈ D S (gs ++ [g]) := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append,
            List.length_cons, List.length_nil]
          refine ⟨⟨by omega, by omega⟩, ⟨?_, u0, v0, ?_, ?_, ?_⟩, ?_⟩
          · rw [hnew]; exact hz
          · intro h; exact hne (by rw [h])
          · rw [hnew]; exact hu0
          · rw [hnew]; exact hv0
          · simp [hN, hgor]
        have hNnot : N ∉ D S gs := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico]
          intro h
          omega
        have h2 : (D S gs).card + 1 ≤ (D S (gs ++ [g])).card := by
          rw [← Finset.card_insert_of_notMem hNnot]
          apply Finset.card_le_card
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hNin
          · exact D_mono S gs g hi
        omega
    · refine ⟨l, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, -⟩ := key hiz u hiu
          refine ⟨huS, ?_⟩
          by_contra hne
          exact hm ⟨hiz, u, v, hiu, hiv, hne⟩
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i u v hiz hiu hiv
      · have := Finset.card_le_card (D_mono S gs g)
        omega

lemma or_outputs_bound : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ (orGates n gates).card := by
  classical
  intro n m S hS gates out hg hev
  have hval : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true) := fun w x => hev w x
  have hZ : ∀ w, val gates (Zof (S w)) (out w) = false := by
    intro w
    rw [hval]
    simp [Zof]
  have hE : ∀ w, ∀ u ∈ S w, val gates (eof u) (out w) = true := by
    intro w u hu
    rw [hval]
    simp only [decide_eq_true_eq]
    exact ⟨u, hu, by simp [eof]⟩
  choose l hinv hcard using fun w => main_inv (S w) gates hg
  have hbound : ∀ w, (S w).card - 1 ≤ (D (S w) gates).card := by
    intro w
    have h1 : ((S w).image (l w)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      exact (hinv w (out w) u v (hZ w) (hE w u hu) (hE w v hv)).2
    have := hcard w
    omega
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (D (S a) gates) (D (S b) gates) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro i hia hib
    simp only [D, Finset.mem_filter, Finset.mem_Ico] at hia hib
    obtain ⟨-, ⟨hza, u, v, huv, hu, hv⟩, -⟩ := hia
    obtain ⟨-, ⟨hzb, -⟩, -⟩ := hib
    have hua := (hinv a i u u hza hu hu).1
    have hva := (hinv a i v v hza hv hv).1
    have hub := (hinv b i u u hzb hu hu).1
    have hvb := (hinv b i v v hzb hv hv).1
    have hsub : ({u, v} : Finset (Fin n)) ⊆ S a ∩ S b := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hua, hub⟩
      · exact Finset.mem_inter.mpr ⟨hva, hvb⟩
    have h2 : ({u, v} : Finset (Fin n)).card = 2 := Finset.card_pair huv
    have := Finset.card_le_card hsub
    have := hS a b hab
    omega
  calc ∑ w, ((S w).card - 1) ≤ ∑ w, (D (S w) gates).card :=
        Finset.sum_le_sum fun w _ => hbound w
    _ = (Finset.univ.biUnion fun w => D (S w) gates).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (orGates n gates).card := by
        apply Finset.card_le_card
        intro i hi
        obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hi
        simp only [D, Finset.mem_filter] at hw
        exact Finset.mem_filter.mpr ⟨hw.1, hw.2.2⟩



open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

lemma gateAt_option (C : Circuit) (k : ℕ) (hk : k<C.gates.length) :
    (C.gates[k]?).map Gate.op=some (gateAt C k).op := by
  have hg : gateAt C k=C.gates[k] := List.getD_eq_getElem _ _ hk
  rw [hg,List.getElem?_eq_getElem hk]
  rfl

lemma two_and_room (n : ℕ) (C : Circuit) (a b : ℕ) (ha : a<C.gates.length)
    (hb : b<C.gates.length) (hab : a≠b)
    (haop : (gateAt C a).op=GateOp.and) (hbop : (gateAt C b).op=GateOp.and) :
    (orGates n C.gates).card+2≤C.size := by
  classical
  have hna : n+a∉orGates n C.gates := by
    intro hi
    have hh := (Finset.mem_filter.mp hi).2
    rw [Nat.add_sub_cancel_left,gateAt_option C a ha,haop] at hh
    cases hh
  have hnb : n+b∉orGates n C.gates := by
    intro hi
    have hh := (Finset.mem_filter.mp hi).2
    rw [Nat.add_sub_cancel_left,gateAt_option C b hb,hbop] at hh
    cases hh
  have hsub : insert (n+a) (insert (n+b) (orGates n C.gates))⊆Finset.Ico n (n+C.gates.length) := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simp only [Finset.mem_Ico];omega
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simp only [Finset.mem_Ico];omega
    · exact (Finset.mem_filter.mp hi).1
  have hc := Finset.card_le_card hsub
  have hneq : n+a≠n+b := by omega
  have hna' : n+a∉insert (n+b) (orGates n C.gates) := by simp [hab,hna]
  rw [Finset.card_insert_of_notMem hna',Finset.card_insert_of_notMem hnb] at hc
  have hc' : (orGates n C.gates).card+1+1≤C.gates.length := by
    simpa using hc
  change (orGates n C.gates).card+2≤C.gates.length
  omega

def three {n : ℕ} (U V B : Finset (Fin n)) : Fin 3 → Finset (Fin n) :=
  fun i => if i=0 then U else if i=1 then V else B

lemma double_star_cost {n : ℕ} (U V B : Finset (Fin n))
    (hd : PEqualNP.Outside.L_meta_3754.ThreeClause.DoubleStar U V B)
    (C : Circuit) (hAO : IsAO2 n C) (out : Fin 3 → ℕ)
    (hout : ∀ (i : Fin 3) (x : Fin n → Bool),
      Circuit.eval ⟨C.gates,out i⟩ (List.ofFn x)=
        PEqualNP.Outside.L_meta_3754.ThreeClause.orQ (three U V B i) x)
    (a b : ℕ) (ha : a<C.gates.length) (hb : b<C.gates.length) (hab : a≠b)
    (haop : (gateAt C a).op=GateOp.and) (hbop : (gateAt C b).op=GateOp.and) :
    U.card+V.card+1≤C.size := by
  classical
  obtain ⟨hdis,e,h,heU,hhV,hUB,hVB,hB,hU,hV⟩ := hd
  have hUV : U∩V=∅ := by
    ext z
    constructor
    · intro hz
      exact (Finset.disjoint_left.mp hdis (Finset.mem_inter.mp hz).1 (Finset.mem_inter.mp hz).2).elim
    · simp
  have hVU : V∩U=∅ := by rw [Finset.inter_comm,hUV]
  have hBU : B∩U={e} := by rw [Finset.inter_comm,hUB]
  have hBV : B∩V={h} := by rw [Finset.inter_comm,hVB]
  have hEh : e≠h := by
    intro heq
    exact Finset.disjoint_left.mp hdis (heq ▸ heU) hhV
  have hBcard : B.card=2 := by rw [hB,Finset.card_pair hEh]
  have hp : ∀ i j : Fin 3,i≠j → (three U V B i∩three U V B j).card≤1 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [three,hUV,hVU,hUB,hBU,hVB,hBV] at hij ⊢
  have hlegal : ∀ g∈C.gates,(g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2 := by
    intro g hg
    exact ⟨hAO.1 g hg,(hAO.2.2 g hg).le⟩
  have hOr := or_outputs_bound n 3 (three U V B) hp C.gates out hlegal hout
  have hRoom := two_and_room n C a b ha hb hab haop hbop
  simp [Fin.sum_univ_succ,three,hBcard] at hOr
  omega

end PEqualNP.Outside.L_meta_3754.ClauseCost

-- Compositional builder adapted from EdgeUpper and EdgeUpperMono (Apache-2.0).
namespace PEqualNP.Outside.L_meta_3754.Upper
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def Ready (m : Nat) (gs : List Gate) : Prop :=
  ∀ i (hi : i<gs.length),
    ((gs[i]).op=GateOp.and ∨ (gs[i]).op=GateOp.or) ∧
    (gs[i]).inputs.length=2 ∧ ∀ v∈(gs[i]).inputs,v<m+i

lemma ready_append {m : Nat} {xs ys : List Gate}
    (hx : Ready m xs) (hy : Ready (m+xs.length) ys) : Ready m (xs++ys) := by
  intro i hi
  by_cases hix : i<xs.length
  · simpa only [List.getElem_append_left hix] using hx i hix
  · have hiy : i-xs.length<ys.length := by simp only [List.length_append] at hi;omega
    have h := hy (i-xs.length) hiy
    have hil : xs.length ≤ i := by omega
    simp only [List.getElem_append_right hil]
    refine ⟨h.1,h.2.1,?_⟩
    intro v hv
    have hh:=h.2.2 v hv
    omega

lemma ready_single (op : GateOp) (hop : op=GateOp.and ∨ op=GateOp.or)
    {m a b : Nat} (ha : a<m) (hb : b<m) : Ready m [⟨op,[a,b]⟩] := by
  intro i hi
  have he : i=0 := by simpa using hi
  subst i
  refine ⟨hop,rfl,?_⟩
  intro v hv
  simp only [List.getElem_cons_zero,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl
  · simpa using ha
  · simpa using hb

lemma ready_isAO2 {m : Nat} {gs : List Gate} (h : Ready m gs) {out : Nat} :
    PEqualNP.TopForm.IsAO2 m ⟨gs,out⟩ := by
  refine ⟨?_,?_,?_⟩
  · intro g hg
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hg
    exact (h i hi).1
  · intro i hi v hv
    have he : gateAt ⟨gs,out⟩ i=gs[i] := by
      simp [gateAt,List.getD_eq_getElem?_getD,hi]
    rw [he] at hv
    exact (h i hi).2.2 v hv
  · intro g hg
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hg
    exact (h i hi).2.1

def step (w : List Bool) (g : Gate) : List Bool :=
  w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w
lemma wiresFrom_append (xs ys : List Gate) (w : List Bool) :
    wiresFrom (xs++ys) w=wiresFrom ys (wiresFrom xs w) := by simp [wiresFrom,List.foldl_append]
lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length=w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    change (wiresFrom gs (step w g)).length=_
    rw [ih]
    simp [step]
    omega
lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : Nat) (hi : i<w.length) :
    (wiresFrom gs w).getD i false=w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (wiresFrom gs (step w g)).getD i false=_
    rw [ih (step w g) (by simp [step];omega)]
    simp [step,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
lemma getD_snoc_eq (w : List Bool) (v d : Bool) : (w++[v]).getD w.length d=v := by simp

def Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), Ready m gs ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

theorem bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
    Bld n F s' := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, le_trans len hs, ho, ev⟩

theorem bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
    (e : ∀ x, F x = H x) : Bld n H s := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, len, ho, fun w hw => by rw [ev w hw, e]⟩

theorem bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by intro j hj; simp at hj, le_rfl, by simp; omega, ?_⟩
  intro w _
  simp [wiresFrom]

theorem bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2) :
    Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_⟩
  · apply ready_append (ready_append ok1 ok2)
    apply ready_single op hop
    · simp only [List.length_append]
      omega
    · simp only [List.length_append]
      omega
  · simp; omega
  · simp; omega
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have step : wiresFrom [⟨op, [o1, o2]⟩] u
        = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step, ← lu, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv]
      congr 1
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
    rw [e1, e2]

theorem bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_circuit {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ}
    (h : Bld n F s) : ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
      PEqualNP.MetaComplexity.circuitFun n D=F ∧ D.size≤s := by
  obtain ⟨gs,out,ok,len,_,ev⟩ := h n le_rfl
  refine ⟨⟨gs,out⟩,ready_isAO2 ok,?_,len⟩
  funext x
  have h := ev (List.ofFn x) (by simp)
  change (wiresFrom gs (List.ofFn x)).getD out false = F x
  rw [h]
  congr 1
  funext i
  simp

/-- The OR of the inputs in a nonempty list. -/
theorem bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp

/-- The OR of the inputs in a nonempty finset `S`, with `|S| - 1` gates. -/
theorem bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp


lemma double_star_upper {n : Nat} (U V : Finset (Fin n)) (e h : Fin n)
    (he : e∈U) (hU : 2≤U.card) (hV : V.Nonempty) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
      PEqualNP.MetaComplexity.circuitFun n D=(fun x=>
        (x e && decide (∃ v∈V,x v=true)) ||
        (x h && decide (∃ u∈U.erase e,x u=true))) ∧ D.size≤U.card+V.card := by
  have hc : (U.erase e).card=U.card-1 := Finset.card_erase_of_mem he
  have hE : (U.erase e).Nonempty := Finset.card_pos.mp (by omega)
  have hVc : 1≤V.card := Finset.card_pos.mpr hV
  have b1 := bld_and (bld_var e) (bld_anyFinset V hV)
  have b2 := bld_and (bld_var h) (bld_anyFinset (U.erase e) hE)
  apply bld_circuit
  exact bld_mono (bld_or b1 b2) (by omega)

end PEqualNP.Outside.L_meta_3754.Upper

namespace PEqualNP.Outside.L_meta_3754.ClauseCost
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_3754.ThreeClause

lemma orQ_insert {n : ℕ} (Q : Finset (Fin n)) (u : Fin n) (x : Fin n → Bool) :
    orQ (insert u Q) x=(x u || orQ Q x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [orQ,decide_eq_true_eq,Bool.or_eq_true]
  constructor
  · rintro ⟨v,hv,hvx⟩
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Or.inl hvx
    · exact Or.inr ⟨v,hv,hvx⟩
  · rintro (hux | ⟨v,hv,hvx⟩)
    · exact ⟨u,by simp,hux⟩
    · exact ⟨v,Finset.mem_insert_of_mem hv,hvx⟩

lemma double_star_product {n : ℕ} (U V B : Finset (Fin n)) (e h : Fin n)
    (heU : e∈U) (hhV : h∈V) (hB : B={e,h}) (x : Fin n → Bool) :
    (orQ U x && orQ V x && orQ B x)=
      ((x e && orQ V x) || (x h && orQ (U.erase e) x)) := by
  have hUeq : orQ U x=(x e || orQ (U.erase e) x) := by
    conv_lhs => rw [←Finset.insert_erase heU]
    exact orQ_insert _ _ _
  have hsingle : orQ ({h} : Finset (Fin n)) x=x h := by simp [orQ]
  have hVtrue : x h=true → orQ V x=true := fun hx => decide_eq_true ⟨h,hhV,hx⟩
  rw [hUeq,hB,orQ_insert,hsingle]
  cases hxe : x e <;> cases hxh : x h <;> cases hu : orQ (U.erase e) x <;>
    cases hv : orQ V x <;> simp_all

lemma no_least_double_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (U V B : Finset (Fin n)) (hd : DoubleStar U V B)
    (hf : ∀ x : Fin n → Bool,graphFun G ∅ x=(orQ U x && orQ V x && orQ B x))
    (C : Circuit) (hL : IsLeastAO G C) (out : Fin 3 → ℕ)
    (hout : ∀ (i : Fin 3) (x : Fin n → Bool),
      Circuit.eval ⟨C.gates,out i⟩ (List.ofFn x)=orQ (three U V B i) x)
    (a b : ℕ) (ha : a<C.gates.length) (hb : b<C.gates.length) (hab : a≠b)
    (haop : (gateAt C a).op=GateOp.and) (hbop : (gateAt C b).op=GateOp.and) : False := by
  have hcost := double_star_cost U V B hd C hL.1 out hout a b ha hb hab haop hbop
  obtain ⟨_,e,h,heU,hhV,_,_,hB,hU,hV⟩ := hd
  have hVne : V.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨D,hDA,hDF,hDS⟩ := PEqualNP.Outside.L_meta_3754.Upper.double_star_upper U V e h heU hU hVne
  have hDfun : circuitFun n D=graphFun G ∅ := by
    funext x
    rw [hDF]
    exact ((hf x).trans (double_star_product U V B e h heU hhV hB x)).symm
  have hmin := hL.2.2 D hDA hDfun
  omega

end PEqualNP.Outside.L_meta_3754.ClauseCost
