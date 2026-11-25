import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3566

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def CutWitness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) (C : Circuit) : Prop :=
  ∃ D : Circuit, IsAO2 n D ∧
    circuitFun n D = (fun y : Fin n → Bool =>
      @decide (∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b ∧
        y a = true ∧ y b = true) (Classical.propDecidable _)) ∧
    D.size + G.degree z ≤ C.size ∧
    ((∃ S : Finset (Fin n),
      CoverPromise.IsVertexCover (G.deleteEdges (G.incidenceSet z)) S ∧
      ∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T → S.card < T.card) →
      D.size + G.degree z + 1 ≤ C.size)

lemma cutWitness_mono {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) (C C' : Circuit) (hsize : C.size ≤ C'.size)
    (h : CutWitness G z C) : CutWitness G z C' := by
  obtain ⟨D, hAO, hfun, hsizeD, hbonus⟩ := h
  exact ⟨D, hAO, hfun, hsizeD.trans hsize, fun hdrop => (hbonus hdrop).trans hsize⟩

lemma exists_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C)
    (hfun : circuitFun n C = NestedCover.graphFun G ∅) :
    ∃ D : Circuit, IsLeastAO G D ∧ D.size ≤ C.size := by
  classical
  let P : ℕ → Prop := fun k => ∃ D : Circuit,
    IsAO2 n D ∧ circuitFun n D = NestedCover.graphFun G ∅ ∧ D.size = k
  have hex : ∃ k, P k := ⟨C.size, C, hAO, hfun, rfl⟩
  obtain ⟨D, hD, hfunD, hsizeD⟩ := Nat.find_spec hex
  have hmin : ∀ E : Circuit, IsAO2 n E →
      circuitFun n E = NestedCover.graphFun G ∅ → D.size ≤ E.size := by
    intro E hE hfunE
    rw [hsizeD]
    exact Nat.find_min' hex ⟨E, hE, hfunE, rfl⟩
  exact ⟨D, ⟨hD, hfunD, hmin⟩, hmin C hAO hfun⟩

lemma peel_of_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hpos : ∃ z : Fin n, 0 < G.degree z)
    (h : ∀ C : Circuit, IsLeastAO G C →
      ∃ z : Fin n, 0 < G.degree z ∧ CutWitness G z C) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = NestedCover.graphFun G ∅ → CutWitness G z C := by
  classical
  by_cases hex : ∃ C : Circuit,
      IsAO2 n C ∧ circuitFun n C = NestedCover.graphFun G ∅
  · obtain ⟨C, hAO, hfun⟩ := hex
    obtain ⟨D, hD, _⟩ := exists_least G C hAO hfun
    obtain ⟨z, hz, hcut⟩ := h D hD
    exact ⟨z, hz, fun E hE hfunE =>
      cutWitness_mono G z D E (hD.2.2 E hE hfunE) hcut⟩
  · obtain ⟨z, hz⟩ := hpos
    exact ⟨z, hz, fun C hAO hfun => (hex ⟨C, hAO, hfun⟩).elim⟩

lemma cut_adj_iff {n : ℕ} (G : SimpleGraph (Fin n)) (z a b : Fin n) :
    (G.deleteEdges (G.incidenceSet z)).Adj a b ↔ G.Adj a b ∧ a ≠ z ∧ b ≠ z := by
  rw [SimpleGraph.deleteEdges_adj, SimpleGraph.mk'_mem_incidenceSet_iff]
  tauto

lemma twin_leaves_no_cover_drop {n : ℕ} (G : SimpleGraph (Fin n))
    (u v w : Fin n) (huv : u ≠ v) (huw : G.Adj u w) (hvw : G.Adj v w)
    (hu : ∀ t : Fin n, G.Adj u t → t = w)
    (hv : ∀ t : Fin n, G.Adj v t → t = w) :
    ¬ ∃ S : Finset (Fin n),
      CoverPromise.IsVertexCover (G.deleteEdges (G.incidenceSet u)) S ∧
      ∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T → S.card < T.card := by
  rintro ⟨S, hS, hsmall⟩
  let T := insert w (S.erase v)
  have hT : CoverPromise.IsVertexCover G T := by
    intro a b hab
    by_cases hau : a = u
    · subst a
      have hbw := hu b hab
      right
      simp [T, hbw]
    by_cases hbu : b = u
    · subst b
      have haw := hu a hab.symm
      left
      simp [T, haw]
    by_cases hav : a = v
    · subst a
      have hbw := hv b hab
      right
      simp [T, hbw]
    by_cases hbv : b = v
    · subst b
      have haw := hv a hab.symm
      left
      simp [T, haw]
    obtain ha | hb := hS a b ((cut_adj_iff G u a b).mpr ⟨hab, hau, hbu⟩)
    · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hav, ha⟩))
    · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hbv, hb⟩))
  have hcard : T.card ≤ S.card := by
    obtain hvS | hwS := hS v w
      ((cut_adj_iff G u v w).mpr ⟨hvw, huv.symm, huw.ne.symm⟩)
    · have h1 := Finset.card_insert_le w (S.erase v)
      have h2 := Finset.card_erase_of_mem hvS
      have h3 : 0 < S.card := Finset.card_pos.mpr ⟨v, hvS⟩
      dsimp [T]
      omega
    · have hw : w ∈ S.erase v := Finset.mem_erase.mpr ⟨hvw.ne.symm, hwS⟩
      dsimp [T]
      rw [Finset.card_insert_of_mem hw]
      exact Finset.card_le_card (Finset.erase_subset _ _)
  exact (Nat.not_lt_of_ge hcard) (hsmall T hT)

lemma cutWitness_of_twin_leaves {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v w : Fin n) (huv : u ≠ v) (huw : G.Adj u w) (hvw : G.Adj v w)
    (hu : ∀ t : Fin n, G.Adj u t → t = w)
    (hv : ∀ t : Fin n, G.Adj v t → t = w)
    (C D : Circuit) (hAO : IsAO2 n D)
    (hfun : circuitFun n D = (fun y : Fin n → Bool =>
      @decide (∃ a b : Fin n, (G.deleteEdges (G.incidenceSet u)).Adj a b ∧
        y a = true ∧ y b = true) (Classical.propDecidable _)))
    (hsize : D.size + 1 ≤ C.size) : CutWitness G u C := by
  have hdeg : G.degree u = 1 :=
    SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr ⟨w, huw, hu⟩
  refine ⟨D, hAO, hfun, by simpa [hdeg] using hsize, ?_⟩
  intro hdrop
  exact (twin_leaves_no_cover_drop G u v w huv huw hvw hu hv hdrop).elim


namespace TwinLeaf

namespace Basic

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]


lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

lemma getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp

def Good : ℕ → List Gate → Prop
  | _, [] => True
  | m, g :: gs =>
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧
        ∀ i ∈ g.inputs, i < m) ∧ Good (m + 1) gs

lemma good_append (gs hs : List Gate) (m : ℕ) :
    Good m gs → Good (m + gs.length) hs → Good m (gs ++ hs) := by
  induction gs generalizing m with
  | nil => simp [Good]
  | cons g gs ih =>
    rintro ⟨hg, hgs⟩ hhs
    refine ⟨hg, ih (m + 1) hgs ?_⟩
    simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hhs

lemma good_mem (gs : List Gate) (m : ℕ) (h : Good m gs) :
    ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  induction gs generalizing m with
  | nil => simp
  | cons g gs ih =>
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨h.1.1, h.1.2.1⟩
    · exact ih (m + 1) h.2 a ha

lemma good_back (gs : List Gate) (m : ℕ) (h : Good m gs) :
    ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < m + j := by
  induction gs generalizing m with
  | nil => simp
  | cons g gs ih =>
    intro j hj i hi
    cases j with
    | zero =>
      simpa using h.1.2.2 i (by simpa using hi)
    | succ j =>
      have hlt : j < gs.length := by simpa using hj
      have him : i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs := by simpa using hi
      have := ih (m + 1) h.2 j hlt i him
      omega

lemma good_ao2 (m : ℕ) (gs : List Gate) (out : ℕ) (h : Good m gs) :
    IsAO2 m ⟨gs, out⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    exact (good_mem gs m h g hg).1
  · exact good_back gs m h
  · intro g hg
    exact (good_mem gs m h g hg).2

end Basic

namespace Restrict

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3566.TwinLeaf.Basic

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

def readOption (a : Option ℕ) (w : List Bool) : Bool :=
  a.elim false (fun i => w.getD i false)

def Bound (m : ℕ) (a : Option ℕ) : Prop :=
  ∀ i, a = some i → i < m

def reduceGate (m : ℕ) (op : GateOp) : Option ℕ → Option ℕ → List Gate × Option ℕ
  | some a, some b => ([⟨op, [a, b]⟩], some m)
  | none, none => ([], none)
  | some a, none => ([], match op with | .or => some a | _ => none)
  | none, some b => ([], match op with | .or => some b | _ => none)

lemma reduce_good (m : ℕ) (op : GateOp) (a b : Option ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or) (ha : Bound m a) (hb : Bound m b) :
    Good m (reduceGate m op a b).1 := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp_all [reduceGate, Good, Bound]

lemma reduce_bound (m : ℕ) (op : GateOp) (a b : Option ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or) (ha : Bound m a) (hb : Bound m b) :
    Bound (m + (reduceGate m op a b).1.length) (reduceGate m op a b).2 := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp_all [reduceGate, Bound]

lemma reduce_size (m : ℕ) (op : GateOp) (a b : Option ℕ) :
    (reduceGate m op a b).1.length + (if a.isNone || b.isNone then 1 else 0) = 1 := by
  cases a <;> cases b <;> simp [reduceGate]

lemma reduce_eval (w : List Bool) (op : GateOp) (a b : Option ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or) :
    readOption (reduceGate w.length op a b).2 (wiresFrom (reduceGate w.length op a b).1 w) =
      op.eval [readOption a w, readOption b w] := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp [reduceGate, readOption, wiresFrom, GateOp.eval]

lemma readOption_preserved (a : Option ℕ) (w : List Bool) (gs : List Gate)
    (ha : Bound w.length a) : readOption a (wiresFrom gs w) = readOption a w := by
  cases a with
  | none => rfl
  | some i => exact getD_wiresFrom gs w i (ha i rfl)

def MapRel (σ : List (Option ℕ)) (s t : List Bool) : Prop :=
  σ.length = s.length ∧ (∀ i, Bound t.length (σ.getD i none)) ∧
    ∀ i, s.getD i false = readOption (σ.getD i none) t

def emit (m : ℕ) (σ : List (Option ℕ)) (g : Gate) : List Gate × Option ℕ :=
  reduceGate m g.op (σ.getD (g.inputs.getD 0 0) none) (σ.getD (g.inputs.getD 1 0) none)

lemma mapRel_step (σ : List (Option ℕ)) (s t : List Bool) (g : Gate)
    (h : MapRel σ s t) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length = 2) :
    MapRel (σ ++ [(emit t.length σ g).2])
      (s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)])
      (wiresFrom (emit t.length σ g).1 t) := by
  have hev : readOption (emit t.length σ g).2 (wiresFrom (emit t.length σ g).1 t) =
      g.op.eval (g.inputs.map fun i => s.getD i false) := by
    obtain ⟨a, b, hg⟩ := List.length_eq_two.mp hlen
    calc
      _ = g.op.eval [readOption (σ.getD a none) t, readOption (σ.getD b none) t] := by
        simpa [emit, hg] using reduce_eval t g.op (σ.getD a none) (σ.getD b none) hop
      _ = _ := by rw [← h.2.2 a, ← h.2.2 b]; simp [hg]
  have hb : Bound (t.length + (emit t.length σ g).1.length) (emit t.length σ g).2 :=
    reduce_bound t.length g.op _ _ hop (h.2.1 _) (h.2.1 _)
  refine ⟨by simp [h.1], ?_, ?_⟩
  · intro j
    by_cases hj : j = σ.length
    · subst j
      rw [getD_snoc_eq, length_wiresFrom]
      exact hb
    · intro i hi
      rw [getD_snoc_ne _ _ _ _ hj] at hi
      have := h.2.1 j i hi
      rw [length_wiresFrom]
      omega
  · intro j
    by_cases hj : j = σ.length
    · subst j
      have hs : (s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)]).getD σ.length false =
          g.op.eval (g.inputs.map fun i => s.getD i false) := by
        rw [h.1, getD_snoc_eq]
      rw [hs, getD_snoc_eq]
      exact hev.symm
    · have hjs : j ≠ s.length := by rw [← h.1]; exact hj
      rw [getD_snoc_ne _ _ _ _ hjs, getD_snoc_ne _ _ _ _ hj, h.2.2 j]
      exact (readOption_preserved _ t _ (h.2.1 j)).symm

lemma emit_good (m : ℕ) (σ : List (Option ℕ)) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hbound : ∀ i, Bound m (σ.getD i none)) : Good m (emit m σ g).1 :=
  reduce_good m g.op _ _ hop (hbound _) (hbound _)

def compile (m : ℕ) (σ : List (Option ℕ)) : List Gate → List Gate × List (Option ℕ)
  | [] => ([], σ)
  | g :: gs =>
      let r := emit m σ g
      let rest := compile (m + r.1.length) (σ ++ [r.2]) gs
      (r.1 ++ rest.1, rest.2)

def saved (m : ℕ) (σ : List (Option ℕ)) : List Gate → ℕ
  | [] => 0
  | g :: gs =>
      let r := emit m σ g
      (if (σ.getD (g.inputs.getD 0 0) none).isNone ||
          (σ.getD (g.inputs.getD 1 0) none).isNone then 1 else 0) +
        saved (m + r.1.length) (σ ++ [r.2]) gs

lemma compile_size (gs : List Gate) (m : ℕ) (σ : List (Option ℕ)) :
    (compile m σ gs).1.length + saved m σ gs = gs.length := by
  induction gs generalizing m σ with
  | nil => simp [compile, saved]
  | cons g gs ih =>
    have hstep := reduce_size m g.op (σ.getD (g.inputs.getD 0 0) none)
      (σ.getD (g.inputs.getD 1 0) none)
    have hrest := ih (m + (emit m σ g).1.length) (σ ++ [(emit m σ g).2])
    simp only [compile, saved, List.length_append, List.length_cons]
    change (emit m σ g).1.length + _ + _ = gs.length + 1
    change (emit m σ g).1.length + _ = 1 at hstep
    omega

lemma compile_correct (gs : List Gate) (σ : List (Option ℕ)) (s t : List Bool)
    (h : MapRel σ s t)
    (hbasis : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    Good t.length (compile t.length σ gs).1 ∧
      MapRel (compile t.length σ gs).2 (wiresFrom gs s)
        (wiresFrom (compile t.length σ gs).1 t) := by
  induction gs generalizing σ s t with
  | nil => exact ⟨True.intro, h⟩
  | cons g gs ih =>
    obtain ⟨hop, hlen⟩ := hbasis g List.mem_cons_self
    have hstep := mapRel_step σ s t g h hop hlen
    have hrest := ih (σ ++ [(emit t.length σ g).2])
      (s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)])
      (wiresFrom (emit t.length σ g).1 t) hstep
      (fun g' hg' => hbasis g' (List.mem_cons_of_mem g hg'))
    rw [length_wiresFrom] at hrest
    constructor
    · exact good_append _ _ _ (emit_good _ _ _ hop h.2.1) hrest.1
    · have hcons : wiresFrom (g :: gs) s =
          wiresFrom gs (s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)]) := rfl
      simpa only [compile, wiresFrom_append, hcons] using hrest.2

def initialMap (n : ℕ) (z : Fin n) : List (Option ℕ) :=
  List.ofFn fun i : Fin n => if i = z then none else some i.val

lemma initial_rel (n : ℕ) (z : Fin n) (y : Fin n → Bool) :
    MapRel (initialMap n z) (List.ofFn (Function.update y z false)) (List.ofFn y) := by
  refine ⟨by simp [initialMap], ?_, ?_⟩
  · intro j
    by_cases hj : j < n
    · have he : (initialMap n z).getD j none =
          if (⟨j, hj⟩ : Fin n) = z then none else some j := by simp [initialMap, hj]
      rw [he]
      split <;> simp_all [Bound]
    · rw [List.getD_eq_default _ _ (by simp [initialMap]; omega)]
      simp [Bound]
  · intro j
    by_cases hj : j < n
    · by_cases he : (⟨j, hj⟩ : Fin n) = z
      · simp [initialMap, hj, he, readOption]
      · simp [initialMap, hj, he, readOption]
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp [initialMap]; omega)]
      rfl

lemma read_output (a : Option ℕ) (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).getD (a.getD (w.length + gs.length)) false =
      readOption a (wiresFrom gs w) := by
  cases a <;> simp [readOption, ← length_wiresFrom gs w]

def restricted (n : ℕ) (z : Fin n) (C : Circuit) : Circuit :=
  let r := compile n (initialMap n z) C.gates
  ⟨r.1, (r.2.getD C.output none).getD (n + r.1.length)⟩

def removalCount (n : ℕ) (z : Fin n) (C : Circuit) : ℕ :=
  saved n (initialMap n z) C.gates

lemma restricted_spec (n : ℕ) (z : Fin n) (C : Circuit) (hAO : IsAO2 n C) :
    IsAO2 n (restricted n z C) ∧
      circuitFun n (restricted n z C) =
        (fun y : Fin n → Bool => circuitFun n C (Function.update y z false)) ∧
      (restricted n z C).size + removalCount n z C = C.size := by
  have hbasis : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
    intro g hg
    exact ⟨hAO.1 g hg, hAO.2.2 g hg⟩
  have hc (y : Fin n → Bool) :
      Good n (compile n (initialMap n z) C.gates).1 ∧
        MapRel (compile n (initialMap n z) C.gates).2
          (wiresFrom C.gates (List.ofFn (Function.update y z false)))
          (wiresFrom (compile n (initialMap n z) C.gates).1 (List.ofFn y)) := by
    simpa only [List.length_ofFn] using
      compile_correct C.gates (initialMap n z) _ _ (initial_rel n z y) hbasis
  refine ⟨good_ao2 _ _ _ (hc (fun _ => false)).1, ?_, ?_⟩
  · funext y
    change (wiresFrom (compile n (initialMap n z) C.gates).1 (List.ofFn y)).getD
        (((compile n (initialMap n z) C.gates).2.getD C.output none).getD
          (n + (compile n (initialMap n z) C.gates).1.length)) false = _
    have hout := read_output ((compile n (initialMap n z) C.gates).2.getD C.output none)
      (compile n (initialMap n z) C.gates).1 (List.ofFn y)
    simp only [List.length_ofFn] at hout
    rw [hout]
    exact ((hc y).2.2.2 C.output).symm
  · exact compile_size C.gates n (initialMap n z)

lemma exists_restriction (n : ℕ) (z : Fin n) (C : Circuit) (hAO : IsAO2 n C) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = (fun y : Fin n → Bool => circuitFun n C (Function.update y z false)) ∧
      D.size + removalCount n z C ≤ C.size := by
  obtain ⟨hD, hF, hsize⟩ := restricted_spec n z C hAO
  exact ⟨restricted n z C, hD, hF, hsize.le⟩

def blockStep (op : GateOp) (a b : Bool) : Bool :=
  match op with
  | .or => a && b
  | _ => a || b

lemma reduce_dead (m : ℕ) (op : GateOp) (a b : Option ℕ) :
    (reduceGate m op a b).2.isNone = blockStep op a.isNone b.isNone := by
  cases a <;> cases b <;> cases op <;> rfl

lemma getD_map_none (σ : List (Option ℕ)) (i : ℕ) :
    (σ.map Option.isNone).getD i true = (σ.getD i none).isNone := by
  induction σ generalizing i with
  | nil => simp
  | cons a σ ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

def deadRun (bs : List Bool) : List Gate → List Bool × ℕ
  | [] => (bs, 0)
  | g :: gs =>
      let a := bs.getD (g.inputs.getD 0 0) true
      let b := bs.getD (g.inputs.getD 1 0) true
      let rest := deadRun (bs ++ [blockStep g.op a b]) gs
      (rest.1, (if a || b then 1 else 0) + rest.2)

lemma compile_dead (gs : List Gate) (m : ℕ) (σ : List (Option ℕ)) :
    (compile m σ gs).2.map Option.isNone = (deadRun (σ.map Option.isNone) gs).1 ∧
      saved m σ gs = (deadRun (σ.map Option.isNone) gs).2 := by
  induction gs generalizing m σ with
  | nil => exact ⟨rfl, rfl⟩
  | cons g gs ih =>
    have hstep : (σ ++ [(emit m σ g).2]).map Option.isNone =
        σ.map Option.isNone ++ [blockStep g.op (σ.getD (g.inputs.getD 0 0) none).isNone
          (σ.getD (g.inputs.getD 1 0) none).isNone] := by
      simp [emit, reduce_dead]
    have hrest := ih (m + (emit m σ g).1.length) (σ ++ [(emit m σ g).2])
    simp only [compile, saved, deadRun, getD_map_none]
    rw [← hstep]
    exact ⟨hrest.1, congrArg (fun k => _ + k) hrest.2⟩

def initialDead (n : ℕ) (z : Fin n) : List Bool :=
  List.ofFn fun i : Fin n => decide (i = z)

lemma initial_map_dead (n : ℕ) (z : Fin n) :
    (initialMap n z).map Option.isNone = initialDead n z := by
  simp only [initialMap, initialDead, List.map_ofFn]
  congr 1
  funext i
  by_cases h : i = z <;> simp [h]

def blockedWires (n : ℕ) (z : Fin n) (C : Circuit) : List Bool :=
  (deadRun (initialDead n z) C.gates).1

def blockedCount (n : ℕ) (z : Fin n) (C : Circuit) : ℕ :=
  (deadRun (initialDead n z) C.gates).2

lemma removal_eq_blocked (n : ℕ) (z : Fin n) (C : Circuit) :
    removalCount n z C = blockedCount n z C := by
  have h := (compile_dead C.gates n (initialMap n z)).2
  rw [initial_map_dead] at h
  exact h

lemma exists_blocked_restriction (n : ℕ) (z : Fin n) (C : Circuit) (hAO : IsAO2 n C) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = (fun y : Fin n → Bool => circuitFun n C (Function.update y z false)) ∧
      D.size + blockedCount n z C = C.size := by
  obtain ⟨hD, hF, hsize⟩ := restricted_spec n z C hAO
  rw [removal_eq_blocked] at hsize
  exact ⟨restricted n z C, hD, hF, hsize⟩
end Restrict

namespace SingleRead

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma ofFn_get {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD]

lemma fold_get (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    · exact List.getD_append _ _ _ _ hi
    · simp only [step, List.length_append, List.length_singleton]
      omega

lemma append_compare {u : ℕ} {xs ys : List Bool} (hlen : xs.length = ys.length)
    (hxy : ∀ i, i ≠ u → xs.getD i false = true → ys.getD i false = true)
    {a b : Bool} (hab : a = true → b = true) :
    ∀ i, i ≠ u → (xs ++ [a]).getD i false = true → (ys ++ [b]).getD i false = true := by
  intro i hi hx
  by_cases hil : i < xs.length
  · rw [List.getD_append _ _ _ _ hil] at hx
    rw [List.getD_append _ _ _ _ (by omega)]
    exact hxy i hi hx
  · have hyil : ys.length ≤ i := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : xs.length ≤ i)] at hx
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hyil]
    rw [← hlen]
    by_cases he : i = xs.length
    · simpa [he] using hab (by simpa [he] using hx)
    · have hp : 0 < i - xs.length := by omega
      have hz : [a].length ≤ i - xs.length := by simp only [List.length_singleton]; omega
      simp [List.getElem?_eq_none hz] at hx

lemma gate_compare {xs ys : List Bool} {g : Gate}
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hxy : ∀ i ∈ g.inputs, xs.getD i false = true → ys.getD i false = true) :
    g.op.eval (g.inputs.map fun i => xs.getD i false) = true →
      g.op.eval (g.inputs.map fun i => ys.getD i false) = true := by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h i hi
    exact hxy i hi (h i hi)
  · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, hxy i hi hx⟩

lemma fold_compare {u : ℕ} (gs : List Gate) (xs ys : List Bool)
    (hlen : xs.length = ys.length)
    (hxy : ∀ i, i ≠ u → xs.getD i false = true → ys.getD i false = true)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hno : ∀ g ∈ gs, u ∉ g.inputs) :
    ∀ i, i ≠ u → (gs.foldl step xs).getD i false = true →
      (gs.foldl step ys).getD i false = true := by
  induction gs generalizing xs ys with
  | nil => exact hxy
  | cons g gs ih =>
    rw [List.foldl_cons, List.foldl_cons]
    apply ih
    · simp [step, hlen]
    · apply append_compare hlen hxy
      apply gate_compare (hop g (by simp))
      intro i hi
      exact hxy i (fun h => hno g (by simp) (h ▸ hi))
    · intro g' hg'
      exact hop g' (by simp [hg'])
    · intro g' hg'
      exact hno g' (by simp [hg'])

lemma graph_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
    decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (G.irrefl hab)
    · exact hab
    · exact hab.symm
    · exact False.elim (G.irrefl hab)
  · intro h
    exact ⟨u, v, h, by simp [pairInput], by simp [pairInput]⟩

lemma output_ne {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hfun : circuitFun n C = graphFun G ∅) (u : Fin n) :
    C.output ≠ u.val := by
  intro he
  have h : circuitFun n C (pairInput u u) = true := by
    unfold circuitFun Circuit.eval Circuit.wires
    change (C.gates.foldl step (List.ofFn (pairInput u u))).getD C.output false = true
    rw [he, fold_get _ _ _ (by simp), ofFn_get]
    simp [pairInput]
  rw [hfun] at h
  exact G.irrefl ((graph_pair G u u).1 h)

lemma pair_compare {n : ℕ} (C : Circuit) (u v w : Fin n) (gs : List Gate)
    (hshape : C.gates = { op := GateOp.or, inputs := [u.val, v.val] } :: gs)
    (hao : IsAO2 n C) (hno : ∀ g ∈ gs, u.val ∉ g.inputs)
    (hout : C.output ≠ u.val) :
    circuitFun n C (pairInput u w) = true → circuitFun n C (pairInput v w) = true := by
  have heq (a b : Fin n) (ha : a = u ∨ a = v) :
      step (List.ofFn (pairInput a b)) { op := GateOp.or, inputs := [u.val, v.val] } =
        List.ofFn (pairInput a b) ++ [true] := by
    simp only [step, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
      Bool.or_false, id_eq, ofFn_get]
    congr 1
    rcases ha with rfl | rfl <;> simp [pairInput]
  unfold circuitFun Circuit.eval Circuit.wires
  rw [hshape, List.foldl_cons, List.foldl_cons]
  change (gs.foldl step (step (List.ofFn (pairInput u w)) _)).getD C.output false = true →
    (gs.foldl step (step (List.ofFn (pairInput v w)) _)).getD C.output false = true
  rw [heq u w (Or.inl rfl), heq v w (Or.inr rfl)]
  apply fold_compare gs _ _ (by simp) _ _ hno C.output hout
  · apply append_compare (by simp) _ (fun h => h)
    intro i hi hx
    by_cases hin : i < n
    · let j : Fin n := ⟨i, hin⟩
      change (List.ofFn (pairInput u w)).getD j.val false = true at hx
      change (List.ofFn (pairInput v w)).getD j.val false = true
      rw [ofFn_get] at hx ⊢
      simp only [pairInput, decide_eq_true_eq] at hx ⊢
      rcases hx with h | h
      · exact False.elim (hi (congrArg Fin.val h))
      · exact Or.inr h
    · simp [List.getD_eq_getElem?_getD, hin] at hx
  · intro g hg
    exact hao.1 g (by rw [hshape]; simp [hg])

lemma first_or_single_read {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u v : Fin n) (gs : List Gate)
    (hshape : C.gates = { op := GateOp.or, inputs := [u.val, v.val] } :: gs)
    (hao : IsAO2 n C) (hno : ∀ g ∈ gs, u.val ∉ g.inputs)
    (hfun : circuitFun n C = graphFun G ∅) :
    ¬ G.Adj u v ∧ G.neighborSet u ⊆ G.neighborSet v := by
  have hc (w : Fin n) (hw : G.Adj u w) : G.Adj v w := by
    apply (graph_pair G v w).1
    rw [← hfun]
    apply pair_compare C u v w gs hshape hao hno (output_ne G C hfun u)
    rw [hfun]
    exact (graph_pair G u w).2 hw
  exact ⟨fun huv => G.irrefl (hc v huv), hc⟩

lemma first_or_single_read_degree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u v : Fin n) (gs : List Gate) (huv : u ≠ v)
    (hshape : C.gates = { op := GateOp.or, inputs := [u.val, v.val] } :: gs)
    (hao : IsAO2 n C) (hno : ∀ g ∈ gs, u.val ∉ g.inputs)
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G) :
    G.degree u ≤ 1 := by
  have hsub := (first_or_single_read G C u v gs hshape hao hno hfun).2
  have hcard : (G.neighborFinset u).card ≤
      (Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w).card := by
    apply Finset.card_le_card
    intro w hw
    have huw := (G.mem_neighborFinset u w).1 hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨huw, hsub huw⟩
  rw [G.card_neighborFinset_eq_degree] at hcard
  exact hcard.trans (hfour u v huv)

lemma first_or_second_read {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u v : Fin n) (gs : List Gate) (huv : u ≠ v)
    (hshape : C.gates = { op := GateOp.or, inputs := [u.val, v.val] } :: gs)
    (hao : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hfour : NoFourCycle G) (hdeg : 2 ≤ G.degree u) :
    ∃ g ∈ gs, u.val ∈ g.inputs := by
  by_contra h
  push Not at h
  have hd := first_or_single_read_degree G C u v gs huv hshape hao h hfun hfour
  omega

end SingleRead

end TwinLeaf

namespace TwinLeaf

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def swapFirst (C : Circuit) (u v : ℕ) (gs : List Gate) : Circuit :=
  ⟨{ op := GateOp.or, inputs := [v, u] } :: gs, C.output⟩

lemma swap_first {n : ℕ} (C : Circuit) (u v : Fin n) (gs : List Gate)
    (hshape : C.gates = { op := GateOp.or, inputs := [u.val, v.val] } :: gs)
    (hAO : IsAO2 n C) :
    IsAO2 n (swapFirst C u v gs) ∧
      circuitFun n (swapFirst C u v gs) = circuitFun n C := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact Or.inr rfl
      · exact hAO.1 g (by rw [hshape]; simp [hg])
    · intro j hj i hi
      cases j with
      | zero =>
        have hi' : i = v.val ∨ i = u.val := by
          simpa [swapFirst, NestedCover.gateAt] using hi
        rcases hi' with rfl | rfl
        · exact v.isLt
        · exact u.isLt
      | succ j =>
        apply hAO.2.1 (j + 1) (by simpa [swapFirst, hshape] using hj) i
        simpa [swapFirst, hshape, NestedCover.gateAt] using hi
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · rfl
      · exact hAO.2.2 g (by rw [hshape]; simp [hg])
  · funext x
    unfold circuitFun Circuit.eval Circuit.wires
    simp only [swapFirst, hshape, List.foldl_cons, List.map_cons, List.map_nil,
      GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [Bool.or_comm]

lemma first_or_saves_one {n : ℕ} (C : Circuit) (u v : Fin n) (gs : List Gate)
    (hshape : C.gates = { op := GateOp.or, inputs := [u.val, v.val] } :: gs) :
    1 ≤ Restrict.blockedCount n u C := by
  have hu : (Restrict.initialDead n u).getD u.val true = true := by
    simp [Restrict.initialDead]
  simp only [Restrict.blockedCount, hshape, Restrict.deadRun,
    List.getD_cons_zero, List.getD_cons_succ]
  rw [hu]
  simp

lemma cut_semantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) :
    (fun y : Fin n → Bool =>
      @decide (∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b ∧
        y a = true ∧ y b = true) (Classical.propDecidable _)) =
    (fun y => NestedCover.graphFun G ∅ (Function.update y z false)) := by
  classical
  funext y
  simp only [NestedCover.graphFun, Finset.notMem_empty, false_and, exists_false,
    decide_false, Bool.false_or]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain ⟨hab, haz, hbz⟩ := (cut_adj_iff G z a b).mp hab
    exact ⟨a, b, hab, by simpa [Function.update_of_ne haz] using ha,
      by simpa [Function.update_of_ne hbz] using hb⟩
  · rintro ⟨a, b, hab, ha, hb⟩
    have haz : a ≠ z := by
      intro h
      subst a
      simp at ha
    have hbz : b ≠ z := by
      intro h
      subst b
      simp at hb
    exact ⟨a, b, (cut_adj_iff G z a b).mpr ⟨hab, haz, hbz⟩,
      by simpa [Function.update_of_ne haz] using ha,
      by simpa [Function.update_of_ne hbz] using hb⟩

lemma first_or_positive_of_least {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (u v : Fin n) (gs : List Gate)
    (hshape : C.gates = { op := GateOp.or, inputs := [u.val, v.val] } :: gs)
    (hmin : IsLeastAO G C) : 0 < G.degree u := by
  classical
  by_contra hpos
  have hn : ∀ t : Fin n, ¬ G.Adj u t := by
    intro t ht
    exact hpos ht.degree_pos_left
  have hcut : G.deleteEdges (G.incidenceSet u) = G := by
    ext a b
    rw [cut_adj_iff]
    constructor
    · exact fun h => h.1
    · intro hab
      refine ⟨hab, ?_, ?_⟩
      · intro ha
        subst a
        exact hn b hab
      · intro hb
        subst b
        exact hn a hab.symm
  obtain ⟨D, hD, hf, hsize⟩ := Restrict.exists_blocked_restriction n u C hmin.1
  have hfunD : circuitFun n D = NestedCover.graphFun G ∅ := by
    rw [hmin.2.1] at hf
    rw [← cut_semantics G u] at hf
    refine hf.trans ?_
    funext y
    simp [hcut, NestedCover.graphFun]
  have hm := hmin.2.2 D hD hfunD
  have hs := first_or_saves_one C u v gs hshape
  omega

lemma first_or_twin_cut {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u v : Fin n) (gs : List Gate) (huv : u ≠ v)
    (hshape : C.gates = { op := GateOp.or, inputs := [u.val, v.val] } :: gs)
    (hAO : IsAO2 n C) (hfun : circuitFun n C = NestedCover.graphFun G ∅)
    (hno_u : ∀ g ∈ gs, u.val ∉ g.inputs)
    (hno_v : ∀ g ∈ gs, v.val ∉ g.inputs)
    (hfour : NoFourCycle G) (hpos : 0 < G.degree u) : CutWitness G u C := by
  have hdeg : G.degree u = 1 := by
    have := SingleRead.first_or_single_read_degree G C u v gs huv hshape hAO hno_u hfun hfour
    omega
  obtain ⟨w, huw, hu⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
  have hsubu := (SingleRead.first_or_single_read G C u v gs hshape hAO hno_u hfun).2
  obtain ⟨hAO', hfun'⟩ := swap_first C u v gs hshape hAO
  have hsubv := (SingleRead.first_or_single_read G (swapFirst C u v gs) v u gs
    rfl hAO' hno_v (hfun'.trans hfun)).2
  have hvw : G.Adj v w := hsubu huw
  have hv : ∀ t : Fin n, G.Adj v t → t = w := fun t ht => hu t (hsubv ht)
  obtain ⟨D, hD, hf, hsize⟩ := Restrict.exists_blocked_restriction n u C hAO
  have hfunD : circuitFun n D = (fun y : Fin n → Bool =>
      @decide (∃ a b : Fin n, (G.deleteEdges (G.incidenceSet u)).Adj a b ∧
        y a = true ∧ y b = true) (Classical.propDecidable _)) := by
    rw [hfun] at hf
    exact hf.trans (cut_semantics G u).symm
  apply cutWitness_of_twin_leaves G u v w huv huw hvw hu hv C D hD hfunD
  have hs := first_or_saves_one C u v gs hshape
  omega

lemma first_or_twins_of_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u v : Fin n) (gs : List Gate) (huv : u ≠ v)
    (hshape : C.gates = { op := GateOp.or, inputs := [u.val, v.val] } :: gs)
    (hno_u : ∀ g ∈ gs, u.val ∉ g.inputs)
    (hno_v : ∀ g ∈ gs, v.val ∉ g.inputs)
    (hfour : NoFourCycle G) (hmin : IsLeastAO G C) :
    0 < G.degree u ∧ CutWitness G u C := by
  have hpos := first_or_positive_of_least G C u v gs hshape hmin
  exact ⟨hpos, first_or_twin_cut G C u v gs huv hshape hmin.1 hmin.2.1
    hno_u hno_v hfour hpos⟩

lemma first_or_twins_uniform {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u v : Fin n) (gs : List Gate) (huv : u ≠ v)
    (hshape : C.gates = { op := GateOp.or, inputs := [u.val, v.val] } :: gs)
    (hno_u : ∀ g ∈ gs, u.val ∉ g.inputs)
    (hno_v : ∀ g ∈ gs, v.val ∉ g.inputs)
    (hfour : NoFourCycle G) (hmin : IsLeastAO G C) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ E : Circuit, IsAO2 n E →
      circuitFun n E = NestedCover.graphFun G ∅ → CutWitness G z E := by
  obtain ⟨hpos, hcut⟩ := first_or_twins_of_least G C u v gs huv hshape hno_u hno_v hfour hmin
  exact ⟨u, hpos, fun E hE hf => cutWitness_mono G u C E (hmin.2.2 E hE hf) hcut⟩

end TwinLeaf

namespace TwinLeaf
namespace SingleRead
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma fold_length (gs : List Gate) (xs : List Bool) :
    (gs.foldl step xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

lemma pair_input_compare {n : ℕ} (u v w : Fin n) :
    ∀ i, i ≠ u.val → (List.ofFn (pairInput u w)).getD i false = true →
      (List.ofFn (pairInput v w)).getD i false = true := by
  intro i hi hx
  by_cases hin : i < n
  · let j : Fin n := ⟨i, hin⟩
    change (List.ofFn (pairInput u w)).getD j.val false = true at hx
    change (List.ofFn (pairInput v w)).getD j.val false = true
    rw [ofFn_get] at hx ⊢
    simp only [pairInput, decide_eq_true_eq] at hx ⊢
    rcases hx with h | h
    · exact False.elim (hi (congrArg Fin.val h))
    · exact Or.inr h
  · simp [List.getD_eq_getElem?_getD, hin] at hx

lemma singleton_input_compare {n : ℕ} (v w : Fin n) :
    ∀ i, (List.ofFn (pairInput v v)).getD i false = true →
      (List.ofFn (pairInput v w)).getD i false = true := by
  intro i hx
  by_cases hin : i < n
  · let j : Fin n := ⟨i, hin⟩
    change (List.ofFn (pairInput v v)).getD j.val false = true at hx
    change (List.ofFn (pairInput v w)).getD j.val false = true
    rw [ofFn_get] at hx ⊢
    simp only [pairInput, decide_eq_true_eq, or_self] at hx
    simp [pairInput, hx]
  · simp [List.getD_eq_getElem?_getD, hin] at hx

lemma arbitrary_or_pair_compare {n : ℕ} (C : Circuit) (u v w : Fin n)
    (pre post : List Gate) (g : Gate) (t : ℕ) (huv : u ≠ v)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hsupport : (C.wires (List.ofFn (pairInput v v))).getD t false = true)
    (hout : C.output ≠ u.val) :
    circuitFun n C (pairInput u w) = true → circuitFun n C (pairInput v w) = true := by
  have htmem : t ∈ g.inputs := by rcases hinputs with h | h <;> simp [h]
  have hgate : gateAt C pre.length = g := by
    simp [gateAt, hshape, List.getD_eq_getElem?_getD]
  have ht : t < n + pre.length := by
    apply hao.2.1 pre.length (by simp [hshape])
    rwa [hgate]
  have hs : (pre.foldl step (List.ofFn (pairInput v v))).getD t false = true := by
    unfold Circuit.wires at hsupport
    rw [hshape, List.foldl_append] at hsupport
    change ((g :: post).foldl step (pre.foldl step (List.ofFn (pairInput v v)))).getD t false = true at hsupport
    rw [fold_get _ _ _ (by simpa [fold_length] using ht)] at hsupport
    exact hsupport
  have htn : t ≠ u.val := by
    intro he
    rw [he, fold_get _ _ _ (by simp), ofFn_get] at hs
    simp [pairInput, huv] at hs
  have hpre : ∀ q ∈ pre, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact hao.1 q (by rw [hshape]; simp [hq])
  have hnpre : ∀ q ∈ pre, u.val ∉ q.inputs := by
    intro q hq
    exact hno q (by simp [hq])
  have hpost : ∀ q ∈ post, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact hao.1 q (by rw [hshape]; simp [hq])
  have hnpost : ∀ q ∈ post, u.val ∉ q.inputs := by
    intro q hq
    exact hno q (by simp [hq])
  have httrue : (pre.foldl step (List.ofFn (pairInput v w))).getD t false = true := by
    apply fold_compare pre _ _ (by simp) _ hpre hnpre t htn hs
    intro i _ hi
    exact singleton_input_compare v w i hi
  have hright : g.op.eval (g.inputs.map fun i =>
      (pre.foldl step (List.ofFn (pairInput v w))).getD i false) = true := by
    rcases hinputs with hi | hi <;>
      simp only [hop, hi, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
        List.any_nil, id_eq, Bool.or_false, httrue, Bool.or_true, Bool.true_or]
  unfold circuitFun Circuit.eval Circuit.wires
  rw [hshape, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
  change (post.foldl step (step (pre.foldl step (List.ofFn (pairInput u w))) g)).getD C.output false = true →
    (post.foldl step (step (pre.foldl step (List.ofFn (pairInput v w))) g)).getD C.output false = true
  apply fold_compare post _ _ (by simp [step, fold_length]) _ hpost hnpost C.output hout
  apply append_compare (by simp [fold_length])
  · exact fold_compare pre _ _ (by simp) (pair_input_compare u v w) hpre hnpre
  · intro _
    exact hright

lemma arbitrary_or_single_read {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u v : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ) (huv : u ≠ v)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hsupport : (C.wires (List.ofFn (pairInput v v))).getD t false = true)
    (hfun : circuitFun n C = graphFun G ∅) :
    ¬ G.Adj u v ∧ G.neighborSet u ⊆ G.neighborSet v := by
  have hc (w : Fin n) (hw : G.Adj u w) : G.Adj v w := by
    apply (graph_pair G v w).1
    rw [← hfun]
    apply arbitrary_or_pair_compare C u v w pre post g t huv hshape hop hinputs hao hno hsupport
      (output_ne G C hfun u)
    rw [hfun]
    exact (graph_pair G u w).2 hw
  exact ⟨fun huv => G.irrefl (hc v huv), hc⟩

lemma arbitrary_or_single_read_degree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u v : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ) (huv : u ≠ v)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hsupport : (C.wires (List.ofFn (pairInput v v))).getD t false = true)
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G) :
    G.degree u ≤ 1 := by
  have hsub := (arbitrary_or_single_read G C u v pre post g t huv hshape hop hinputs hao hno hsupport hfun).2
  have hcard : (G.neighborFinset u).card ≤
      (Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w).card := by
    apply Finset.card_le_card
    intro w hw
    have huw := (G.mem_neighborFinset u w).1 hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨huw, hsub huw⟩
  rw [G.card_neighborFinset_eq_degree] at hcard
  exact hcard.trans (hfour u v huv)

end SingleRead

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

lemma deadRun_reader_saves (pre post : List Gate) (g : Gate) (t i : ℕ)
    (hinputs : g.inputs = [i, t] ∨ g.inputs = [t, i])
    (bs : List Bool) (hi : i < bs.length) (hb : bs.getD i true = true) :
    1 ≤ (Restrict.deadRun bs (pre ++ g :: post)).2 := by
  induction pre generalizing bs with
  | nil =>
    rcases hinputs with h | h <;>
      simp only [List.nil_append, Restrict.deadRun, h, List.getD_cons_zero, List.getD_cons_succ] <;>
      rw [hb] <;> simp
  | cons q pre ih =>
    let a := bs.getD (q.inputs.getD 0 0) true
    let b := bs.getD (q.inputs.getD 1 0) true
    let bs' := bs ++ [Restrict.blockStep q.op a b]
    have hi' : i < bs'.length := by simp [bs']; omega
    have hb' : bs'.getD i true = true := by
      rw [List.getD_append _ _ _ _ hi]
      exact hb
    have h := ih bs' hi' hb'
    simp only [List.cons_append, Restrict.deadRun]
    change 1 ≤ (if a || b then 1 else 0) + (Restrict.deadRun bs' (pre ++ g :: post)).2
    omega

lemma or_reader_saves_one {n : ℕ} (C : Circuit) (u v : Fin n)
    (pre post : List Gate) (g : Gate)
    (hshape : C.gates = pre ++ g :: post) (hinputs : g.inputs = [u.val, v.val]) :
    1 ≤ Restrict.blockedCount n u C := by
  unfold Restrict.blockedCount
  rw [hshape]
  apply deadRun_reader_saves pre post g v.val u.val (Or.inl hinputs)
  · simp [Restrict.initialDead]
  · simp [Restrict.initialDead]

lemma input_singleton_support {n : ℕ} (C : Circuit) (v : Fin n) :
    (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput v v))).getD v.val false = true := by
  change (C.gates.foldl SingleRead.step (List.ofFn (PEqualNP.EdgeOwnership.pairInput v v))).getD v.val false = true
  rw [SingleRead.fold_get _ _ _ (by simp)]
  simp [PEqualNP.EdgeOwnership.pairInput]

lemma or_reader_positive_of_least {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (u v : Fin n) (pre post : List Gate) (g : Gate)
    (hshape : C.gates = pre ++ g :: post) (hinputs : g.inputs = [u.val, v.val])
    (hmin : IsLeastAO G C) : 0 < G.degree u := by
  classical
  by_contra hpos
  have hn : ∀ t : Fin n, ¬ G.Adj u t := by
    intro t ht
    exact hpos ht.degree_pos_left
  have hcut : G.deleteEdges (G.incidenceSet u) = G := by
    ext a b
    rw [cut_adj_iff]
    constructor
    · exact fun h => h.1
    · intro hab
      refine ⟨hab, ?_, ?_⟩
      · intro ha
        subst a
        exact hn b hab
      · intro hb
        subst b
        exact hn a hab.symm
  obtain ⟨D, hD, hf, hsize⟩ := Restrict.exists_blocked_restriction n u C hmin.1
  have hfunD : circuitFun n D = NestedCover.graphFun G ∅ := by
    rw [hmin.2.1] at hf
    rw [← cut_semantics G u] at hf
    refine hf.trans ?_
    funext y
    simp [hcut, NestedCover.graphFun]
  have hm := hmin.2.2 D hD hfunD
  have hs := or_reader_saves_one C u v pre post g hshape hinputs
  omega

lemma arbitrary_or_twin_cut {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u v : Fin n) (pre post : List Gate) (g : Gate) (huv : u ≠ v)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, v.val])
    (hAO : IsAO2 n C) (hfun : circuitFun n C = NestedCover.graphFun G ∅)
    (hno_u : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hno_v : ∀ q ∈ pre ++ post, v.val ∉ q.inputs)
    (hfour : NoFourCycle G) (hpos : 0 < G.degree u) : CutWitness G u C := by
  have hsupportu := input_singleton_support C u
  have hsupportv := input_singleton_support C v
  have hdeg : G.degree u = 1 := by
    have := SingleRead.arbitrary_or_single_read_degree G C u v pre post g v.val huv
      hshape hop (Or.inl hinputs) hAO hno_u hsupportv hfun hfour
    omega
  obtain ⟨w, huw, hu⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
  have hsubu := (SingleRead.arbitrary_or_single_read G C u v pre post g v.val huv
    hshape hop (Or.inl hinputs) hAO hno_u hsupportv hfun).2
  have hsubv := (SingleRead.arbitrary_or_single_read G C v u pre post g u.val huv.symm
    hshape hop (Or.inr hinputs) hAO hno_v hsupportu hfun).2
  have hvw : G.Adj v w := hsubu huw
  have hv : ∀ t : Fin n, G.Adj v t → t = w := fun t ht => hu t (hsubv ht)
  obtain ⟨D, hD, hf, hsize⟩ := Restrict.exists_blocked_restriction n u C hAO
  have hfunD : circuitFun n D = (fun y : Fin n → Bool =>
      @decide (∃ a b : Fin n, (G.deleteEdges (G.incidenceSet u)).Adj a b ∧
        y a = true ∧ y b = true) (Classical.propDecidable _)) := by
    rw [hfun] at hf
    exact hf.trans (cut_semantics G u).symm
  apply cutWitness_of_twin_leaves G u v w huv huw hvw hu hv C D hD hfunD
  have hs := or_reader_saves_one C u v pre post g hshape hinputs
  omega

lemma arbitrary_or_twins_uniform {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u v : Fin n) (pre post : List Gate) (g : Gate) (huv : u ≠ v)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, v.val])
    (hno_u : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hno_v : ∀ q ∈ pre ++ post, v.val ∉ q.inputs)
    (hfour : NoFourCycle G) (hmin : IsLeastAO G C) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ E : Circuit, IsAO2 n E →
      circuitFun n E = NestedCover.graphFun G ∅ → CutWitness G z E := by
  have hpos := or_reader_positive_of_least G C u v pre post g hshape hinputs hmin
  have hcut := arbitrary_or_twin_cut G C u v pre post g huv hshape hop hinputs
    hmin.1 hmin.2.1 hno_u hno_v hfour hpos
  exact ⟨u, hpos, fun E hE hf => cutWitness_mono G u C E (hmin.2.2 E hE hf) hcut⟩

end TwinLeaf



namespace ProofWire

open scoped Classical

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma wires_length (gs : List Gate) (w0 : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).length
      = w0.length + gs.length := by
  induction gs generalizing w0 with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega

lemma wires_snoc (gs : List Gate) (g : Gate) (o : ℕ) (x : List Bool) :
    (⟨gs ++ [g], o⟩ : Circuit).wires x = (⟨gs, o⟩ : Circuit).wires x
      ++ [g.op.eval (g.inputs.map fun i => ((⟨gs, o⟩ : Circuit).wires x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]
lemma wireVal_new (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    wireVal n ⟨gs ++ [g], 0⟩ (n + gs.length) x
      = g.op.eval (g.inputs.map fun i => wireVal n ⟨gs, 0⟩ i x) := by
  unfold wireVal
  have : ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).length = n + gs.length := by
    have h := wires_length gs (List.ofFn x)
    rw [List.length_ofFn] at h
    exact h
  rw [wires_snoc, List.getD_append_right _ _ _ _ (by omega), this]
  simp

lemma wires_prefix (gs : List Gate) (w0 : List Bool) (i : ℕ) (hi : i < w0.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).getD i false
      = w0.getD i false := by
  induction gs generalizing w0 with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

lemma input_value_fin (C : Circuit) (i : Fin n) (x : Fin n → Bool) :
    wireVal n C (i : ℕ) x = x i := by
  unfold wireVal Circuit.wires
  rw [wires_prefix _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma input_value (C : Circuit) (w : ℕ) (hw : w < n) (x : Fin n → Bool) :
    wireVal n C w x = x ⟨w, hw⟩ := by
  exact input_value_fin C ⟨w, hw⟩ x

lemma operand_lt (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length)
    (b : Fin 2) : opnd C k b < n + k := by
  have hg : C.gates[k]? = some (gateAt C k) := by
    simp [gateAt, List.getD_eq_getElem?_getD, hk]
  have hmem : gateAt C k ∈ C.gates := List.mem_of_getElem? hg
  have hlen := hC.2.2 _ hmem
  have hb : b.val < (gateAt C k).inputs.length := by simpa [hlen] using b.isLt
  have hin : (gateAt C k).inputs[b.val]? = some (opnd C k b) := by
    simp [opnd, List.getD_eq_getElem?_getD, hb]
  exact hC.2.1 k hk _ (List.mem_of_getElem? hin)

lemma gate_value (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) (x : Fin n → Bool) :
    wireVal n C (n + k) x = (if (gateAt C k).op = GateOp.and then
      wireVal n C (opnd C k 0) x && wireVal n C (opnd C k 1) x
    else wireVal n C (opnd C k 0) x || wireVal n C (opnd C k 1) x) := by
  have hg : C.gates[k]? = some (gateAt C k) := by
    simp [gateAt, List.getD_eq_getElem?_getD, hk]
  have hmem : gateAt C k ∈ C.gates := List.mem_of_getElem? hg
  have hlen := hC.2.2 _ hmem
  have hop := hC.1 _ hmem
  have hback := hC.2.1 k hk
  have hsplit : C.gates = C.gates.take k ++ gateAt C k :: C.gates.drop (k + 1) := by
    have h := List.take_append_drop k C.gates
    rw [List.drop_eq_getElem_cons hk] at h
    have e : C.gates[k] = gateAt C k := by simp [gateAt, List.getD_eq_getElem?_getD, hk]
    rw [e] at h
    exact h.symm
  have htake : (C.gates.take k).length = k := by simp; omega
  have hold : ∀ w < n + k, wireVal n C w x = wireVal n ⟨C.gates.take k, 0⟩ w x := by
    intro w hw
    unfold wireVal Circuit.wires
    conv_lhs => rw [hsplit, List.foldl_append]
    rw [wires_prefix]
    rw [wires_length, htake]
    simpa using hw
  have hnew : wireVal n C (n + k) x = (gateAt C k).op.eval
      ((gateAt C k).inputs.map fun i => wireVal n ⟨C.gates.take k, 0⟩ i x) := by
    rw [← wireVal_new, htake]
    unfold wireVal Circuit.wires
    conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
    rw [wires_prefix]
    · simp [List.foldl_append]
    · rw [List.length_append, wires_length, htake, List.length_ofFn]; simp
  obtain ⟨p, q, hpq⟩ : ∃ p q, (gateAt C k).inputs = [p, q] := List.length_eq_two.1 hlen
  have hp : p < n + k := hback p (by rw [hpq]; simp)
  have hq : q < n + k := hback q (by rw [hpq]; simp)
  rw [hnew]
  simp only [opnd, hpq, List.map_cons, List.map_nil, ← hold p hp, ← hold q hq]
  rcases hop with h | h <;> simp [h, GateOp.eval]

end ProofWire


namespace CertificateCount

lemma sum_indicator {α : Type*} [DecidableEq α] (V S : Finset α) (hS : S ⊆ V) :
    (∑ v ∈ V, if v ∈ S then 1 else 0 : ℕ) = S.card := by
  rw [← Finset.sum_filter]
  have heq : V.filter (fun v => v ∈ S) = S := by
    ext v
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  rw [heq]
  simp

lemma leaf_bound {α : Type*} [DecidableEq α]
    (V L A : Finset α) (E : Finset (α × α)) (r : α)
    (hr : r ∈ V) (hL : L ⊆ V) (hA : A ⊆ V)
    (hsource : ∀ e ∈ E, e.1 ∈ V)
    (hincoming : ∀ v ∈ V, v ≠ r → ∃ u, (u, v) ∈ E)
    (houtgoing : ∀ v ∈ V,
      (E.filter (fun e => e.1 = v)).card + (if v ∈ L then 1 else 0) ≤
        1 + (if v ∈ A then 1 else 0)) :
    L.card ≤ A.card + 1 := by
  have himage : V.erase r ⊆ E.image Prod.snd := by
    intro v hv
    obtain ⟨hvr, hvV⟩ := Finset.mem_erase.mp hv
    obtain ⟨u, hu⟩ := hincoming v hvV hvr
    exact Finset.mem_image.mpr ⟨(u, v), hu, rfl⟩
  have hlow := (Finset.card_le_card himage).trans (Finset.card_image_le)
  have hV : V.card ≤ E.card + 1 := by
    have h := Finset.card_erase_add_one hr
    omega
  have hcount : E.card = ∑ v ∈ V, (E.filter (fun e => e.1 = v)).card :=
    Finset.card_eq_sum_card_fiberwise hsource
  have hsum := Finset.sum_le_sum houtgoing
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← hcount,
    sum_indicator V L hL, sum_indicator V A hA] at hsum
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum
  omega

lemma binary_proof_leaf_bound {α : Type*} [DecidableEq α]
    (V L A : Finset α) (E : Finset (α × α)) (r : α)
    (hr : r ∈ V) (hL : L ⊆ V) (hA : A ⊆ V)
    (hsource : ∀ e ∈ E, e.1 ∈ V)
    (hincoming : ∀ v ∈ V, v ≠ r → ∃ u, (u, v) ∈ E)
    (hleaf : ∀ v ∈ L, (E.filter (fun e => e.1 = v)).card = 0)
    (hand : ∀ v ∈ A, (E.filter (fun e => e.1 = v)).card ≤ 2)
    (hor : ∀ v ∈ V, v ∉ L → v ∉ A →
      (E.filter (fun e => e.1 = v)).card ≤ 1) :
    L.card ≤ A.card + 1 := by
  apply leaf_bound V L A E r hr hL hA hsource hincoming
  intro v hv
  by_cases hl : v ∈ L
  · rw [hleaf v hl]
    simp [hl]
  by_cases ha : v ∈ A
  · have h := hand v ha
    simpa [hl, ha] using h
  · have h := hor v hv hl ha
    simpa [hl, ha] using h

lemma children_leaf_bound {α : Type*} [DecidableEq α]
    (V L A : Finset α) (S : α → Finset α) (r : α)
    (hr : r ∈ V) (hL : L ⊆ V) (hA : A ⊆ V)
    (hincoming : ∀ v ∈ V, v ≠ r → ∃ u ∈ V, v ∈ S u)
    (hleaf : ∀ v ∈ L, S v = ∅)
    (hand : ∀ v ∈ A, (S v).card ≤ 2)
    (hor : ∀ v ∈ V, v ∉ L → v ∉ A → (S v).card ≤ 1) :
    L.card ≤ A.card + 1 := by
  let E : Finset (α × α) := V.biUnion fun v => (S v).image fun w => (v, w)
  have hmem (a b : α) : (a, b) ∈ E ↔ a ∈ V ∧ b ∈ S a := by
    constructor
    · intro h
      obtain ⟨v, hv, h⟩ := Finset.mem_biUnion.mp h
      obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact ⟨hv, hw⟩
    · rintro ⟨ha, hb⟩
      exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩
  have hfiber (v : α) (hv : v ∈ V) :
      (E.filter (fun e => e.1 = v)).card = (S v).card := by
    have heq : E.filter (fun e => e.1 = v) = (S v).image (fun w => (v, w)) := by
      ext e
      rcases e with ⟨a, b⟩
      simp only [Finset.mem_filter, hmem]
      constructor
      · rintro ⟨⟨ha, hb⟩, rfl⟩
        exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
      · intro h
        obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        exact ⟨⟨hv, hw⟩, rfl⟩
    rw [heq]
    exact Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)
  apply binary_proof_leaf_bound V L A E r hr hL hA
  · rintro ⟨a, b⟩ h
    exact ((hmem a b).mp h).1
  · intro v hv hvr
    obtain ⟨u, hu, huv⟩ := hincoming v hv hvr
    exact ⟨u, (hmem u v).mpr ⟨hu, huv⟩⟩
  · intro v hv
    rw [hfiber v (hL hv), hleaf v hv]
    rfl
  · intro v hv
    rw [hfiber v (hA hv)]
    exact hand v hv
  · intro v hv hl ha
    rw [hfiber v hv]
    exact hor v hv hl ha

end CertificateCount

namespace SelectedTrace

lemma exists_trace (S : ℕ → Finset ℕ) (r m : ℕ) (hr : r < m)
    (hback : ∀ v < m, ∀ w ∈ S v, w < v)
    (P : ℕ → Prop) (hroot : P r)
    (hprop : ∀ v < m, P v → ∀ w ∈ S v, P w) :
    ∃ V : Finset ℕ, r ∈ V ∧
      (∀ v ∈ V, v ≤ r) ∧
      (∀ v ∈ V, ∀ w ∈ S v, w ∈ V) ∧
      (∀ v ∈ V, v ≠ r → ∃ p ∈ V, v ∈ S p) ∧
      ∀ v ∈ V, P v := by
  classical
  let R : ℕ → ℕ → Prop := fun v w => w ∈ S v
  have reach_le : ∀ v, Relation.ReflTransGen R r v → v ≤ r := by
    intro v hv
    induction hv with
    | refl => exact Nat.le_refl _
    | @tail b c hbc hstep ih =>
      have hlt := hback b (by omega) c hstep
      omega
  have reach_P : ∀ v, Relation.ReflTransGen R r v → P v := by
    intro v hv
    induction hv with
    | refl => exact hroot
    | @tail b c hbc hstep ih =>
      have hb := reach_le b hbc
      exact hprop b (by omega) ih c hstep
  let V := (Finset.range (r + 1)).filter (fun v => Relation.ReflTransGen R r v)
  have mem_V : ∀ v, v ∈ V ↔ Relation.ReflTransGen R r v := by
    intro v
    simp only [V, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨by have := reach_le v h; omega, h⟩⟩
  refine ⟨V, (mem_V r).2 .refl, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact reach_le v ((mem_V v).1 hv)
  · intro v hv w hw
    exact (mem_V w).2 (((mem_V v).1 hv).tail hw)
  · intro v hv hvr
    rcases ((mem_V v).1 hv).cases_tail with h | ⟨p, hp, hstep⟩
    · exact (hvr h).elim
    · exact ⟨p, (mem_V p).2 hp, hstep⟩
  · intro v hv
    exact reach_P v ((mem_V v).1 hv)

lemma propagate_on_trace (S : ℕ → Finset ℕ) (V : Finset ℕ) (P : ℕ → Prop)
    (hback : ∀ v ∈ V, ∀ w ∈ S v, w < v)
    (hclosed : ∀ v ∈ V, ∀ w ∈ S v, w ∈ V)
    (hstep : ∀ v ∈ V, (∀ w ∈ S v, P w) → P v) :
    ∀ v ∈ V, P v := by
  intro v
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    intro hv
    apply hstep v hv
    intro w hw
    exact ih w (hback v hv w hw) (hclosed v hv w hw)

end SelectedTrace

namespace ProofSelection
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.CleanedNonEdge

noncomputable def selectedChildren (n : ℕ) (C : Circuit) (x : Fin n → Bool) (v : ℕ) : Finset ℕ := by
  classical
  exact if v < n then ∅ else
    if (gateAt C (v - n)).op = GateOp.and then
      {opnd C (v - n) 0, opnd C (v - n) 1}
    else {if wireVal n C (opnd C (v - n) 0) x = true then
      opnd C (v - n) 0 else opnd C (v - n) 1}

lemma selected_back {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (x : Fin n → Bool)
    (v : ℕ) (hv : v < n + C.gates.length) (w : ℕ)
    (hw : w ∈ selectedChildren n C x v) : w < v := by
  classical
  by_cases hin : v < n
  · simp [selectedChildren, hin] at hw
  have hk : v - n < C.gates.length := by omega
  have h0 := ProofWire.operand_lt C hAO (v - n) hk 0
  have h1 := ProofWire.operand_lt C hAO (v - n) hk 1
  simp only [selectedChildren, hin, ↓reduceIte] at hw
  split_ifs at hw with ha hx
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl <;> omega
  · have : w = opnd C (v - n) 0 := Finset.mem_singleton.mp hw
    omega
  · have : w = opnd C (v - n) 1 := Finset.mem_singleton.mp hw
    omega

lemma selected_true {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (x : Fin n → Bool)
    (v : ℕ) (hv : v < n + C.gates.length) (htrue : wireVal n C v x = true)
    (w : ℕ) (hw : w ∈ selectedChildren n C x v) : wireVal n C w x = true := by
  classical
  by_cases hin : v < n
  · simp [selectedChildren, hin] at hw
  have hk : v - n < C.gates.length := by omega
  have heq : n + (v - n) = v := by omega
  have he := ProofWire.gate_value C hAO (v - n) hk x
  rw [heq] at he
  rw [he] at htrue
  simp only [selectedChildren, hin, ↓reduceIte] at hw
  split_ifs at hw with ha hx
  · simp only [ha, ↓reduceIte, Bool.and_eq_true] at htrue
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact htrue.1
    · exact htrue.2
  · exact (Finset.mem_singleton.mp hw) ▸ hx
  · have hew := Finset.mem_singleton.mp hw
    rw [hew]
    simpa [ha, hx] using htrue

lemma selected_eval {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (x y : Fin n → Bool)
    (v : ℕ) (hv : v < n + C.gates.length) (hin : n ≤ v)
    (hall : ∀ w ∈ selectedChildren n C x v, wireVal n C w y = true) :
    wireVal n C v y = true := by
  classical
  have hk : v - n < C.gates.length := by omega
  have heq : n + (v - n) = v := by omega
  have he := ProofWire.gate_value C hAO (v - n) hk y
  rw [heq] at he
  rw [he]
  by_cases ha : (gateAt C (v - n)).op = GateOp.and
  · have h0 := hall (opnd C (v - n) 0) (by simp [selectedChildren, not_lt.mpr hin, ha])
    have h1 := hall (opnd C (v - n) 1) (by simp [selectedChildren, not_lt.mpr hin, ha])
    simp [ha, h0, h1]
  · by_cases hx : wireVal n C (opnd C (v - n) 0) x = true
    · have h0 := hall (opnd C (v - n) 0) (by simp [selectedChildren, not_lt.mpr hin, ha, hx])
      simp [ha, h0]
    · have h1 := hall (opnd C (v - n) 1) (by simp [selectedChildren, not_lt.mpr hin, ha, hx])
      simp [ha, h1]

noncomputable def trueAnds (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (n + C.gates.length)).filter (fun v =>
    n ≤ v ∧ v ≤ r ∧ (gateAt C (v - n)).op = GateOp.and ∧ wireVal n C v x = true)

lemma true_certificate {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (r : ℕ) (hr : r < n + C.gates.length) (x : Fin n → Bool)
    (hx : wireVal n C r x = true) :
    ∃ J : Finset (Fin n), (∀ i ∈ J, x i = true) ∧
      wireVal n C r (fun i => decide (i ∈ J)) = true ∧
      J.card ≤ (trueAnds n C x r).card + 1 := by
  classical
  let S := selectedChildren n C x
  obtain ⟨V, hrV, hbound, hclosed, hincoming, htruth⟩ :=
    SelectedTrace.exists_trace S r (n + C.gates.length) hr
      (selected_back C hAO x) (fun v => wireVal n C v x = true) hx
      (selected_true C hAO x)
  let L := V.filter (fun v => v < n)
  let A := V.filter (fun v => n ≤ v ∧ (gateAt C (v - n)).op = GateOp.and)
  let J : Finset (Fin n) := Finset.univ.filter (fun i => i.val ∈ V)
  have hcard : J.card = L.card := by
    apply Finset.card_bij (fun i _ => i.val)
    · intro i hi
      simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact Finset.mem_filter.mpr ⟨hi, i.isLt⟩
    · intro i hi j hj he
      exact Fin.ext he
    · intro v hv
      obtain ⟨hvV, hvn⟩ := Finset.mem_filter.mp hv
      exact ⟨⟨v, hvn⟩, by simpa [J] using hvV, rfl⟩
  have hcount : L.card ≤ A.card + 1 := by
    apply CertificateCount.children_leaf_bound V L A S r hrV
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) hincoming
    · intro v hv
      have h := (Finset.mem_filter.mp hv).2
      simp [S, selectedChildren, h]
    · intro v hv
      obtain ⟨hvV, hvn, ha⟩ := Finset.mem_filter.mp hv
      simp only [S, selectedChildren, not_lt.mpr hvn, ↓reduceIte, ha]
      by_cases h : opnd C (v - n) 0 = opnd C (v - n) 1 <;> simp [h]
    · intro v hv hl ha
      have hvn : n ≤ v := by
        by_contra h
        exact hl (Finset.mem_filter.mpr ⟨hv, by omega⟩)
      have hop : (gateAt C (v - n)).op ≠ GateOp.and := by
        intro h
        exact ha (Finset.mem_filter.mpr ⟨hv, hvn, h⟩)
      simp [S, selectedChildren, not_lt.mpr hvn, hop]
  have hsub : A ⊆ trueAnds n C x r := by
    intro v hv
    obtain ⟨hvV, hvn, ha⟩ := Finset.mem_filter.mp hv
    have hb := hbound v hvV
    simp only [trueAnds, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hvn, hb, ha, htruth v hvV⟩
  refine ⟨J, ?_, ?_, ?_⟩
  · intro i hi
    have hv : i.val ∈ V := by simpa [J] using hi
    have ht := htruth i.val hv
    rw [ProofWire.input_value] at ht
    exact ht
  · apply SelectedTrace.propagate_on_trace S V
      (fun v => wireVal n C v (fun i => decide (i ∈ J)) = true) ?_ hclosed ?_ r hrV
    · intro v hv w hw
      exact selected_back C hAO x v (by have := hbound v hv; omega) w hw
    · intro v hv ih
      by_cases hvn : v < n
      · rw [ProofWire.input_value C v hvn]
        simpa [J] using hv
      · exact selected_eval C hAO x _ v (by have := hbound v hv; omega)
          (by omega) ih
  · rw [hcard]
    exact hcount.trans (Nat.add_le_add_right (Finset.card_le_card hsub) 1)

end ProofSelection


namespace TwinLeaf.SingleRead

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma ofFn_compare_away {n : ℕ} (u : Fin n) (x y : Fin n → Bool)
    (hxy : ∀ i : Fin n, i ≠ u → x i = true → y i = true) :
    ∀ i : ℕ, i ≠ u.val → (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
  intro i hi hx
  by_cases hin : i < n
  · let j : Fin n := ⟨i, hin⟩
    change (List.ofFn x).getD j.val false = true at hx
    change (List.ofFn y).getD j.val false = true
    rw [ofFn_get] at hx ⊢
    exact hxy j (fun h => hi (congrArg Fin.val h)) hx
  · simp [List.getD_eq_getElem?_getD, hin] at hx

lemma operand_prefix_value {n : ℕ} (C : Circuit) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hao : IsAO2 n C) (htmem : t ∈ g.inputs)
    (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).getD t false = (pre.foldl step (List.ofFn x)).getD t false := by
  have hgate : gateAt C pre.length = g := by simp [gateAt, hshape, List.getD_eq_getElem?_getD]
  have ht : t < n + pre.length := by
    apply hao.2.1 pre.length (by simp [hshape])
    rwa [hgate]
  unfold Circuit.wires
  rw [hshape, List.foldl_append]
  change ((g :: post).foldl step (pre.foldl step (List.ofFn x))).getD t false =
    (pre.foldl step (List.ofFn x)).getD t false
  exact fold_get _ _ _ (by simpa [fold_length] using ht)

lemma other_wire_compare {n : ℕ} (C : Circuit) (u : Fin n)
    (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (htmem : t ∈ g.inputs)
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (htu : t ≠ u.val) (x y : Fin n → Bool)
    (hxy : ∀ i : Fin n, i ≠ u → x i = true → y i = true) :
    (C.wires (List.ofFn x)).getD t false = true → (C.wires (List.ofFn y)).getD t false = true := by
  rw [operand_prefix_value C pre post g t hshape hao htmem x,
    operand_prefix_value C pre post g t hshape hao htmem y]
  apply fold_compare pre _ _ (by simp) (ofFn_compare_away u x y hxy) _ _ t htu
  · intro q hq
    exact hao.1 q (by rw [hshape]; simp [hq])
  · intro q hq
    exact hno q (by simp [hq])

lemma sole_or_transfer {n : ℕ} (C : Circuit) (u : Fin n)
    (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hout : C.output ≠ u.val) (x y : Fin n → Bool)
    (hxy : ∀ i : Fin n, i ≠ u → x i = true → y i = true)
    (hsupport : (C.wires (List.ofFn y)).getD t false = true) :
    circuitFun n C x = true → circuitFun n C y = true := by
  have htmem : t ∈ g.inputs := by rcases hinputs with h | h <;> simp [h]
  have httrue : (pre.foldl step (List.ofFn y)).getD t false = true := by
    rw [← operand_prefix_value C pre post g t hshape hao htmem y]
    exact hsupport
  have hpre : ∀ q ∈ pre, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact hao.1 q (by rw [hshape]; simp [hq])
  have hnpre : ∀ q ∈ pre, u.val ∉ q.inputs := by
    intro q hq
    exact hno q (by simp [hq])
  have hpost : ∀ q ∈ post, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact hao.1 q (by rw [hshape]; simp [hq])
  have hnpost : ∀ q ∈ post, u.val ∉ q.inputs := by
    intro q hq
    exact hno q (by simp [hq])
  have hright : g.op.eval (g.inputs.map fun i => (pre.foldl step (List.ofFn y)).getD i false) = true := by
    rcases hinputs with hi | hi <;>
      simp only [hop, hi, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
        List.any_nil, id_eq, Bool.or_false, httrue, Bool.or_true, Bool.true_or]
  unfold circuitFun Circuit.eval Circuit.wires
  rw [hshape, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
  change (post.foldl step (step (pre.foldl step (List.ofFn x)) g)).getD C.output false = true →
    (post.foldl step (step (pre.foldl step (List.ofFn y)) g)).getD C.output false = true
  apply fold_compare post _ _ (by simp [step, fold_length]) _ hpost hnpost C.output hout
  apply append_compare (by simp [fold_length])
  · exact fold_compare pre _ _ (by simp) (ofFn_compare_away u x y hxy) hpre hnpre
  · intro _
    exact hright

lemma sole_or_neighbor_multiplier {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅) :
    ∀ w : Fin n, G.Adj u w → ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD t false = true → x w = true → graphFun G ∅ x = true := by
  intro w huw x ht hx
  rw [← hfun]
  refine sole_or_transfer C u pre post g t hshape hop hinputs hao hno (output_ne G C hfun u)
    (pairInput u w) x ?_ ht ?_
  · intro i hi hp
    simp only [pairInput, decide_eq_true_eq] at hp
    rcases hp with h | h
    · exact False.elim (hi h)
    · rw [h]
      exact hx
  · rw [hfun]
    exact (graph_pair G u w).2 huw

def setInput {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ S)

lemma graph_insert_independent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (hind : ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b) (w : Fin n) :
    graphFun G ∅ (setInput (insert w S)) = true → ∃ a ∈ S, G.Adj a w := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
    decide_eq_true_eq]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [setInput, decide_eq_true_eq, Finset.mem_insert] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · exact False.elim (G.irrefl hab)
  · exact ⟨b, hb, hab.symm⟩
  · exact ⟨a, ha, hab⟩
  · exact False.elim (hind a ha b hb hab)

lemma sole_or_independent_support_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G) (htu : t ≠ u.val)
    (S : Finset (Fin n)) (huS : u ∉ S) (hind : ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b)
    (hs : (C.wires (List.ofFn (setInput S))).getD t false = true) :
    G.degree u ≤ S.card := by
  have htmem : t ∈ g.inputs := by rcases hinputs with h | h <;> simp [h]
  have hcover (w : Fin n) (huw : G.Adj u w) : ∃ a ∈ S, G.Adj a w := by
    apply graph_insert_independent G S hind w
    apply sole_or_neighbor_multiplier G C u pre post g t hshape hop hinputs hao hno hfun w huw
    · apply other_wire_compare C u pre post g t hshape htmem hao hno htu
        (setInput S) (setInput (insert w S)) _ hs
      intro i _ hi
      simp only [setInput, decide_eq_true_eq] at hi ⊢
      exact Finset.mem_insert_of_mem hi
    · simp [setInput]
  let A : Fin n → Finset (Fin n) := fun a => Finset.univ.filter fun w => G.Adj u w ∧ G.Adj a w
  have hsub : G.neighborFinset u ⊆ S.biUnion A := by
    intro w hw
    have huw := (G.mem_neighborFinset u w).1 hw
    obtain ⟨a, ha, haw⟩ := hcover w huw
    exact Finset.mem_biUnion.mpr ⟨a, ha, by simp [A, huw, haw]⟩
  have hsum : (∑ a ∈ S, (A a).card) ≤ ∑ a ∈ S, 1 := by
    apply Finset.sum_le_sum
    intro a ha
    apply hfour u a
    intro he
    exact huS (he ▸ ha)
  have hc := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  rw [G.card_neighborFinset_eq_degree] at hc
  exact hc.trans (by simpa using hsum)

lemma sole_or_independent_support_erase_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G) (htu : t ≠ u.val)
    (S : Finset (Fin n)) (hind : ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b)
    (hs : (C.wires (List.ofFn (setInput S))).getD t false = true) :
    G.degree u ≤ (S.erase u).card := by
  have htmem : t ∈ g.inputs := by rcases hinputs with h | h <;> simp [h]
  apply sole_or_independent_support_bound G C u pre post g t hshape hop hinputs hao hno hfun hfour htu
    (S.erase u) (by simp)
  · intro a ha b hb
    exact hind a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
  · apply other_wire_compare C u pre post g t hshape htmem hao hno htu
      (setInput S) (setInput (S.erase u)) _ hs
    intro i hi hS
    simp only [setInput, decide_eq_true_eq] at hS ⊢
    exact Finset.mem_erase.mpr ⟨hi, hS⟩

end TwinLeaf.SingleRead

namespace DirtyCertificate
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open TwinLeaf.SingleRead

noncomputable def dirtyAnds {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter (fun j =>
    n + j ≤ r ∧ (gateAt C j).op = GateOp.and ∧ ¬ BelowF G C j)

lemma independent_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I : Finset (Fin n)) (hind : ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b) :
    graphFun G ∅ (setInput I) = false := by
  classical
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false,
    decide_false, Bool.false_or, decide_eq_false_iff_not]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [setInput, decide_eq_true_eq] at ha hb
  exact hind a ha b hb hab

lemma trueAnds_le_dirty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r : ℕ) (I : Finset (Fin n))
    (hind : ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b) :
    (ProofSelection.trueAnds n C (setInput I) r).card ≤ (dirtyAnds G C r).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun v => v - n)
  · intro v hv
    change v - n ∈ dirtyAnds G C r
    obtain ⟨hv, hn, hr, ha, ht⟩ := Finset.mem_filter.mp hv
    have hv' : v < n + C.gates.length := Finset.mem_range.mp hv
    have heq : n + (v - n) = v := by omega
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), by omega, ha, ?_⟩
    intro hbelow
    have hval : gateVal n C (v - n) (setInput I) = true := by
      change wireVal n C (n + (v - n)) (setInput I) = true
      rwa [heq]
    have h := hbelow (setInput I) hval
    rw [independent_false G I hind] at h
    cases h
  · intro v hv w hw he
    have hvn : n ≤ v := (Finset.mem_filter.mp hv).2.1
    have hwn : n ≤ w := (Finset.mem_filter.mp hw).2.1
    change v - n = w - n at he
    omega

lemma sole_or_dirty_and_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hAO : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G) (htu : t ≠ u.val)
    (I : Finset (Fin n)) (hind : ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b)
    (ht : wireVal n C t (setInput I) = true) :
    G.degree u ≤ (dirtyAnds G C t).card + 1 := by
  classical
  have htmem : t ∈ g.inputs := by rcases hinputs with h | h <;> simp [h]
  have hg : gateAt C pre.length = g := by
    simp [gateAt, hshape, List.getD_eq_getElem?_getD]
  have hpre : pre.length < C.gates.length := by simp [hshape]
  have hback := hAO.2.1 pre.length hpre t (by rwa [hg])
  have htrange : t < n + C.gates.length := by omega
  obtain ⟨J, hJ, htJ, hcard⟩ := ProofSelection.true_certificate C hAO t htrange (setInput I) ht
  have hsub : J ⊆ I := by
    intro i hi
    simpa [setInput] using hJ i hi
  have hindJ : ∀ a ∈ J, ∀ b ∈ J, ¬ G.Adj a b :=
    fun a ha b hb => hind a (hsub ha) b (hsub hb)
  have hd := sole_or_independent_support_erase_bound G C u pre post g t hshape hop
    hinputs hAO hno hfun hfour htu J hindJ htJ
  have hc := Finset.card_erase_le (s := J) (a := u)
  have hdirt := trueAnds_le_dirty G C t I hind
  omega

lemma sole_or_dirty_source_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hAO : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G) (htu : t ≠ u.val)
    (hdirty : ¬ ∀ x : Fin n → Bool, wireVal n C t x = true → graphFun G ∅ x = true) :
    G.degree u ≤ (dirtyAnds G C t).card + 1 := by
  classical
  push Not at hdirty
  obtain ⟨x, ht, hfalse⟩ := hdirty
  let I := Finset.univ.filter (fun i : Fin n => x i = true)
  have heq : setInput I = x := by
    funext i
    simp [setInput, I]
  have hind : ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b := by
    intro a ha b hb hab
    apply hfalse
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false,
      decide_false, Bool.false_or, decide_eq_true_eq]
    exact ⟨a, b, hab, by simpa [I] using ha, by simpa [I] using hb⟩
  apply sole_or_dirty_and_bound G C u pre post g t hshape hop hinputs hAO hno hfun hfour htu I hind
  rwa [heq]

end DirtyCertificate



namespace CertificateForest

lemma sum_indicator {α : Type*} [DecidableEq α] (V S : Finset α) (hS : S ⊆ V) :
    (∑ v ∈ V, if v ∈ S then 1 else 0 : ℕ) = S.card := by
  rw [← Finset.sum_filter]
  have heq : V.filter (fun v => v ∈ S) = S := by
    ext v
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  rw [heq]
  simp

lemma leaf_bound {α : Type*} [DecidableEq α]
    (V L A R : Finset α) (E : Finset (α × α))
    (hR : R ⊆ V) (hL : L ⊆ V) (hA : A ⊆ V)
    (hsource : ∀ e ∈ E, e.1 ∈ V)
    (hincoming : ∀ v ∈ V, v ∉ R → ∃ u, (u, v) ∈ E)
    (houtgoing : ∀ v ∈ V,
      (E.filter (fun e => e.1 = v)).card + (if v ∈ L then 1 else 0) ≤
        1 + (if v ∈ A then 1 else 0)) :
    L.card ≤ A.card + R.card := by
  have himage : V \ R ⊆ E.image Prod.snd := by
    intro v hv
    obtain ⟨hvV, hvr⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨u, hu⟩ := hincoming v hvV hvr
    exact Finset.mem_image.mpr ⟨(u, v), hu, rfl⟩
  have hlow := (Finset.card_le_card himage).trans (Finset.card_image_le)
  have hV : V.card ≤ E.card + R.card := by
    have h := Finset.card_sdiff_add_card_eq_card hR
    omega
  have hcount : E.card = ∑ v ∈ V, (E.filter (fun e => e.1 = v)).card :=
    Finset.card_eq_sum_card_fiberwise hsource
  have hsum := Finset.sum_le_sum houtgoing
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← hcount,
    sum_indicator V L hL, sum_indicator V A hA] at hsum
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum
  omega

lemma binary_proof_leaf_bound {α : Type*} [DecidableEq α]
    (V L A R : Finset α) (E : Finset (α × α))
    (hR : R ⊆ V) (hL : L ⊆ V) (hA : A ⊆ V)
    (hsource : ∀ e ∈ E, e.1 ∈ V)
    (hincoming : ∀ v ∈ V, v ∉ R → ∃ u, (u, v) ∈ E)
    (hleaf : ∀ v ∈ L, (E.filter (fun e => e.1 = v)).card = 0)
    (hand : ∀ v ∈ A, (E.filter (fun e => e.1 = v)).card ≤ 2)
    (hor : ∀ v ∈ V, v ∉ L → v ∉ A →
      (E.filter (fun e => e.1 = v)).card ≤ 1) :
    L.card ≤ A.card + R.card := by
  apply leaf_bound V L A R E hR hL hA hsource hincoming
  intro v hv
  by_cases hl : v ∈ L
  · rw [hleaf v hl]
    simp [hl]
  by_cases ha : v ∈ A
  · have h := hand v ha
    simpa [hl, ha] using h
  · have h := hor v hv hl ha
    simpa [hl, ha] using h

lemma children_leaf_bound {α : Type*} [DecidableEq α]
    (V L A R : Finset α) (S : α → Finset α)
    (hR : R ⊆ V) (hL : L ⊆ V) (hA : A ⊆ V)
    (hincoming : ∀ v ∈ V, v ∉ R → ∃ u ∈ V, v ∈ S u)
    (hleaf : ∀ v ∈ L, S v = ∅)
    (hand : ∀ v ∈ A, (S v).card ≤ 2)
    (hor : ∀ v ∈ V, v ∉ L → v ∉ A → (S v).card ≤ 1) :
    L.card ≤ A.card + R.card := by
  let E : Finset (α × α) := V.biUnion fun v => (S v).image fun w => (v, w)
  have hmem (a b : α) : (a, b) ∈ E ↔ a ∈ V ∧ b ∈ S a := by
    constructor
    · intro h
      obtain ⟨v, hv, h⟩ := Finset.mem_biUnion.mp h
      obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact ⟨hv, hw⟩
    · rintro ⟨ha, hb⟩
      exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩
  have hfiber (v : α) (hv : v ∈ V) :
      (E.filter (fun e => e.1 = v)).card = (S v).card := by
    have heq : E.filter (fun e => e.1 = v) = (S v).image (fun w => (v, w)) := by
      ext e
      rcases e with ⟨a, b⟩
      simp only [Finset.mem_filter, hmem]
      constructor
      · rintro ⟨⟨ha, hb⟩, rfl⟩
        exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
      · intro h
        obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        exact ⟨⟨hv, hw⟩, rfl⟩
    rw [heq]
    exact Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)
  apply binary_proof_leaf_bound V L A R E hR hL hA
  · rintro ⟨a, b⟩ h
    exact ((hmem a b).mp h).1
  · intro v hv hvr
    obtain ⟨u, hu, huv⟩ := hincoming v hv hvr
    exact ⟨u, (hmem u v).mpr ⟨hu, huv⟩⟩
  · intro v hv
    rw [hfiber v (hL hv), hleaf v hv]
    rfl
  · intro v hv
    rw [hfiber v (hA hv)]
    exact hand v hv
  · intro v hv hl ha
    rw [hfiber v hv]
    exact hor v hv hl ha

end CertificateForest

namespace SelectedForest

lemma exists_forest (S : ℕ → Finset ℕ) (R : Finset ℕ) (m : ℕ)
    (hR : ∀ r ∈ R, r < m)
    (hback : ∀ v < m, ∀ w ∈ S v, w < v)
    (P : ℕ → Prop) (hroot : ∀ r ∈ R, P r)
    (hprop : ∀ v < m, P v → ∀ w ∈ S v, P w) :
    ∃ V : Finset ℕ, R ⊆ V ∧
      (∀ v ∈ V, v < m) ∧
      (∀ v ∈ V, ∀ w ∈ S v, w ∈ V) ∧
      (∀ v ∈ V, v ∉ R → ∃ p ∈ V, v ∈ S p) ∧
      ∀ v ∈ V, P v := by
  classical
  let rel : ℕ → ℕ → Prop := fun v w => w ∈ S v
  have reach_lt : ∀ r ∈ R, ∀ v, Relation.ReflTransGen rel r v → v < m := by
    intro r hr v hv
    induction hv with
    | refl => exact hR r hr
    | @tail b c hbc hstep ih =>
      exact (hback b ih c hstep).trans ih
  have reach_P : ∀ r ∈ R, ∀ v, Relation.ReflTransGen rel r v → P v := by
    intro r hr v hv
    induction hv with
    | refl => exact hroot r hr
    | @tail b c hbc hstep ih =>
      exact hprop b (reach_lt r hr b hbc) ih c hstep
  let V := (Finset.range m).filter (fun v => ∃ r ∈ R, Relation.ReflTransGen rel r v)
  have mem_V : ∀ v, v ∈ V ↔ ∃ r ∈ R, Relation.ReflTransGen rel r v := by
    intro v
    simp only [V, Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · rintro ⟨r, hr, hv⟩
      exact ⟨reach_lt r hr v hv, r, hr, hv⟩
  refine ⟨V, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    exact (mem_V r).2 ⟨r, hr, .refl⟩
  · intro v hv
    obtain ⟨r, hr, hrv⟩ := (mem_V v).1 hv
    exact reach_lt r hr v hrv
  · intro v hv w hw
    obtain ⟨r, hr, hrv⟩ := (mem_V v).1 hv
    exact (mem_V w).2 ⟨r, hr, hrv.tail hw⟩
  · intro v hv hvr
    obtain ⟨r, hr, hrv⟩ := (mem_V v).1 hv
    rcases hrv.cases_tail with h | ⟨p, hp, hstep⟩
    · exact (hvr (h ▸ hr)).elim
    · exact ⟨p, (mem_V p).2 ⟨r, hr, hp⟩, hstep⟩
  · intro v hv
    obtain ⟨r, hr, hrv⟩ := (mem_V v).1 hv
    exact reach_P r hr v hrv

end SelectedForest

namespace ProofForest
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.CleanedNonEdge ProofSelection

lemma true_certificates {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset ℕ) (hR : ∀ r ∈ R, r < n + C.gates.length) (x : Fin n → Bool)
    (hx : ∀ r ∈ R, wireVal n C r x = true) :
    ∃ J : Finset (Fin n), (∀ i ∈ J, x i = true) ∧
      (∀ r ∈ R, wireVal n C r (fun i => decide (i ∈ J)) = true) ∧
      J.card ≤ (trueAnds n C x (n + C.gates.length)).card + R.card := by
  classical
  let S := selectedChildren n C x
  obtain ⟨V, hRV, hbound, hclosed, hincoming, htruth⟩ :=
    SelectedForest.exists_forest S R (n + C.gates.length) hR
      (selected_back C hAO x) (fun v => wireVal n C v x = true) hx
      (selected_true C hAO x)
  let L := V.filter (fun v => v < n)
  let A := V.filter (fun v => n ≤ v ∧ (gateAt C (v - n)).op = GateOp.and)
  let J : Finset (Fin n) := Finset.univ.filter (fun i => i.val ∈ V)
  have hcard : J.card = L.card := by
    apply Finset.card_bij (fun i _ => i.val)
    · intro i hi
      simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact Finset.mem_filter.mpr ⟨hi, i.isLt⟩
    · intro i hi j hj he
      exact Fin.ext he
    · intro v hv
      obtain ⟨hvV, hvn⟩ := Finset.mem_filter.mp hv
      exact ⟨⟨v, hvn⟩, by simpa [J] using hvV, rfl⟩
  have hcount : L.card ≤ A.card + R.card := by
    apply CertificateForest.children_leaf_bound V L A R S hRV
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) hincoming
    · intro v hv
      have h := (Finset.mem_filter.mp hv).2
      simp [S, selectedChildren, h]
    · intro v hv
      obtain ⟨hvV, hvn, ha⟩ := Finset.mem_filter.mp hv
      simp only [S, selectedChildren, not_lt.mpr hvn, ↓reduceIte, ha]
      by_cases h : opnd C (v - n) 0 = opnd C (v - n) 1 <;> simp [h]
    · intro v hv hl ha
      have hvn : n ≤ v := by
        by_contra h
        exact hl (Finset.mem_filter.mpr ⟨hv, by omega⟩)
      have hop : (gateAt C (v - n)).op ≠ GateOp.and := by
        intro h
        exact ha (Finset.mem_filter.mpr ⟨hv, hvn, h⟩)
      simp [S, selectedChildren, not_lt.mpr hvn, hop]
  have hsub : A ⊆ trueAnds n C x (n + C.gates.length) := by
    intro v hv
    obtain ⟨hvV, hvn, ha⟩ := Finset.mem_filter.mp hv
    have hb := hbound v hvV
    simp only [trueAnds, Finset.mem_filter, Finset.mem_range]
    exact ⟨hb, hvn, Nat.le_of_lt hb, ha, htruth v hvV⟩
  refine ⟨J, ?_, ?_, ?_⟩
  · intro i hi
    have hv : i.val ∈ V := by simpa [J] using hi
    have ht := htruth i.val hv
    rw [ProofWire.input_value] at ht
    exact ht
  · have hall := SelectedTrace.propagate_on_trace S V
      (fun v => wireVal n C v (fun i => decide (i ∈ J)) = true) ?_ hclosed ?_
    · intro r hr
      exact hall r (hRV hr)
    · intro v hv w hw
      exact selected_back C hAO x v (hbound v hv) w hw
    · intro v hv ih
      by_cases hvn : v < n
      · rw [ProofWire.input_value C v hvn]
        simpa [J] using hv
      · exact selected_eval C hAO x _ v (hbound v hv) (by omega) ih
  · rw [hcard]
    exact hcount.trans (Nat.add_le_add_right (Finset.card_le_card hsub) R.card)

end ProofForest


namespace MultiReader

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open TwinLeaf.SingleRead

lemma wire_mono {n : ℕ} (C : Circuit) (hao : IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (r : ℕ) (hr : r < n + C.gates.length) :
    wireVal n C r x = true → wireVal n C r y = true := by
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    by_cases hin : r < n
    · rw [ProofWire.input_value C r hin x, ProofWire.input_value C r hin y]
      exact hxy _
    · have hn : n ≤ r := by omega
      let k := r - n
      have hk : k < C.gates.length := by omega
      have he : r = n + k := by omega
      have hzero := ProofWire.operand_lt C hao k hk 0
      have hone := ProofWire.operand_lt C hao k hk 1
      rw [he, ProofWire.gate_value C hao k hk x, ProofWire.gate_value C hao k hk y]
      split_ifs with hop
      · intro ht
        simp only [Bool.and_eq_true] at ht ⊢
        exact ⟨ih _ (by omega) (by omega) ht.1,
          ih _ (by omega) (by omega) ht.2⟩
      · intro ht
        simp only [Bool.or_eq_true] at ht ⊢
        rcases ht with ht | ht
        · exact Or.inl (ih _ (by omega) (by omega) ht)
        · exact Or.inr (ih _ (by omega) (by omega) ht)

lemma wire_compare_away {n : ℕ} (C : Circuit) (hao : IsAO2 n C) (u : Fin n)
    (x y : Fin n → Bool)
    (hxy : ∀ i, i ≠ u → x i = true → y i = true)
    (hread : ∀ k < C.gates.length, u.val ∈ (gateAt C k).inputs →
      wireVal n C (n + k) y = true)
    (r : ℕ) (hr : r < n + C.gates.length) (hru : r ≠ u.val) :
    wireVal n C r x = true → wireVal n C r y = true := by
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    by_cases hin : r < n
    · rw [ProofWire.input_value C r hin x, ProofWire.input_value C r hin y]
      exact hxy _ (fun he => hru (congrArg Fin.val he))
    · have hn : n ≤ r := by omega
      let k := r - n
      have hk : k < C.gates.length := by omega
      have he : r = n + k := by omega
      by_cases hreader : u.val ∈ (gateAt C k).inputs
      · intro _
        rw [he]
        exact hread k hk hreader
      · have hzero := ProofWire.operand_lt C hao k hk 0
        have hone := ProofWire.operand_lt C hao k hk 1
        have hmem (b : Fin 2) : opnd C k b ∈ (gateAt C k).inputs := by
          have hg : C.gates[k]? = some (gateAt C k) := by
            simp [gateAt, List.getD_eq_getElem?_getD, hk]
          have hlen := hao.2.2 _ (List.mem_of_getElem? hg)
          have hb : b.val < (gateAt C k).inputs.length := by simpa [hlen] using b.isLt
          have ho : (gateAt C k).inputs[b.val]? = some (opnd C k b) := by
            simp [opnd, List.getD_eq_getElem?_getD, hb]
          exact List.mem_of_getElem? ho
        have haway (b : Fin 2) : opnd C k b ≠ u.val := by
          intro heq
          exact hreader (heq ▸ hmem b)
        rw [he, ProofWire.gate_value C hao k hk x, ProofWire.gate_value C hao k hk y]
        split_ifs with hop
        · intro ht
          simp only [Bool.and_eq_true] at ht ⊢
          exact ⟨ih _ (by omega) (by omega) (haway 0) ht.1,
            ih _ (by omega) (by omega) (haway 1) ht.2⟩
        · intro ht
          simp only [Bool.or_eq_true] at ht ⊢
          rcases ht with ht | ht
          · exact Or.inl (ih _ (by omega) (by omega) (haway 0) ht)
          · exact Or.inr (ih _ (by omega) (by omega) (haway 1) ht)

lemma true_wire_bound {n : ℕ} (C : Circuit) (x : Fin n → Bool) (r : ℕ)
    (ht : wireVal n C r x = true) : r < n + C.gates.length := by
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    simpa [Circuit.wires] using ProofWire.wires_length C.gates (List.ofFn x)
  by_contra hb
  have hb' : ¬r < (C.wires (List.ofFn x)).length := by omega
  simp [wireVal, List.getD_eq_getElem?_getD, hb'] at ht

lemma readers_or_transfer {n : ℕ} (C : Circuit) (hao : IsAO2 n C) (u : Fin n)
    (R : Finset ℕ)
    (hread : ∀ k < C.gates.length, u.val ∈ (gateAt C k).inputs →
      (gateAt C k).op = GateOp.or ∧ ∃ t ∈ R,
        (gateAt C k).inputs = [u.val, t] ∨ (gateAt C k).inputs = [t, u.val])
    (x y : Fin n → Bool) (hxy : ∀ i, i ≠ u → x i = true → y i = true)
    (hs : ∀ t ∈ R, wireVal n C t y = true) (hout : C.output ≠ u.val) :
    circuitFun n C x = true → circuitFun n C y = true := by
  intro ht
  have houtx : wireVal n C C.output x = true := ht
  have hbound := true_wire_bound C x C.output houtx
  apply wire_compare_away C hao u x y hxy _ C.output hbound hout houtx
  intro k hk hkread
  obtain ⟨hop, t, htR, hinputs⟩ := hread k hk hkread
  rw [ProofWire.gate_value C hao k hk y]
  rcases hinputs with hi | hi <;> simp [hop, opnd, hi, hs t htR]

lemma independent_neighbor_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u : Fin n) (J : Finset (Fin n)) (hfour : NoFourCycle G) (huJ : u ∉ J)
    (hcover : ∀ w : Fin n, G.Adj u w → ∃ a ∈ J, G.Adj a w) :
    G.degree u ≤ J.card := by
  let A : Fin n → Finset (Fin n) := fun a => Finset.univ.filter fun w => G.Adj u w ∧ G.Adj a w
  have hsub : G.neighborFinset u ⊆ J.biUnion A := by
    intro w hw
    have huw := (G.mem_neighborFinset u w).1 hw
    obtain ⟨a, ha, haw⟩ := hcover w huw
    exact Finset.mem_biUnion.mpr ⟨a, ha, by simp [A, huw, haw]⟩
  have hsum : (∑ a ∈ J, (A a).card) ≤ ∑ a ∈ J, 1 := by
    apply Finset.sum_le_sum
    intro a ha
    apply hfour u a
    intro he
    exact huJ (he ▸ ha)
  have hc := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  rw [G.card_neighborFinset_eq_degree] at hc
  exact hc.trans (by simpa using hsum)

lemma independent_insert_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u : Fin n) (J : Finset (Fin n)) (hfour : NoFourCycle G) (huJ : u ∉ J)
    (hind : ∀ a ∈ J, ∀ b ∈ J, ¬ G.Adj a b)
    (hinsert : ∀ w : Fin n, G.Adj u w → graphFun G ∅ (setInput (insert w J)) = true) :
    G.degree u ≤ J.card := by
  apply independent_neighbor_bound G u J hfour huJ
  intro w huw
  exact graph_insert_independent G J hind w (hinsert w huw)

lemma readers_or_independent_support_bound {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (u : Fin n)
    (R : Finset ℕ) (hao : IsAO2 n C)
    (hread : ∀ k < C.gates.length, u.val ∈ (gateAt C k).inputs →
      (gateAt C k).op = GateOp.or ∧ ∃ t ∈ R,
        (gateAt C k).inputs = [u.val, t] ∨ (gateAt C k).inputs = [t, u.val])
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G)
    (J : Finset (Fin n)) (huJ : u ∉ J)
    (hind : ∀ a ∈ J, ∀ b ∈ J, ¬ G.Adj a b)
    (hs : ∀ t ∈ R, wireVal n C t (setInput J) = true) :
    G.degree u ≤ J.card := by
  apply independent_insert_bound G u J hfour huJ hind
  intro w huw
  rw [← hfun]
  refine readers_or_transfer C hao u R hread (pairInput u w) (setInput (insert w J))
    ?_ ?_ (output_ne G C hfun u) ?_
  · intro i hi hp
    simp only [pairInput, decide_eq_true_eq] at hp
    rcases hp with he | he
    · exact False.elim (hi he)
    · simp [setInput, he]
  · intro t ht
    apply wire_mono C hao (setInput J) (setInput (insert w J)) _ t
      (true_wire_bound C (setInput J) t (hs t ht)) (hs t ht)
    intro i hi
    simp only [setInput, decide_eq_true_eq] at hi ⊢
    exact Finset.mem_insert_of_mem hi
  · rw [hfun]
    exact (graph_pair G u w).2 huw

end MultiReader


namespace MultiReader

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open TwinLeaf.SingleRead

lemma readers_or_sources_compare {n : ℕ} (C : Circuit) (hao : IsAO2 n C) (u : Fin n)
    (R : Finset ℕ)
    (hread : ∀ k < C.gates.length, u.val ∈ (gateAt C k).inputs →
      (gateAt C k).op = GateOp.or ∧ ∃ t ∈ R, t ≠ u.val ∧
        ((gateAt C k).inputs = [u.val, t] ∨ (gateAt C k).inputs = [t, u.val]))
    (x y : Fin n → Bool) (hxy : ∀ i, i ≠ u → x i = true → y i = true)
    (hs : ∀ t ∈ R, wireVal n C t x = true)
    (r : ℕ) (hr : r < n + C.gates.length) (hru : r ≠ u.val) :
    wireVal n C r x = true → wireVal n C r y = true := by
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    by_cases hin : r < n
    · rw [ProofWire.input_value C r hin x, ProofWire.input_value C r hin y]
      exact hxy _ (fun he => hru (congrArg Fin.val he))
    · have hn : n ≤ r := by omega
      let k := r - n
      have hk : k < C.gates.length := by omega
      have he : r = n + k := by omega
      by_cases hreader : u.val ∈ (gateAt C k).inputs
      · intro _
        obtain ⟨hop, t, htR, htu, hinputs⟩ := hread k hk hreader
        have htmem : t ∈ (gateAt C k).inputs := by
          rcases hinputs with hi | hi <;> simp [hi]
        have htlt : t < n + k := hao.2.1 k hk t htmem
        have hty : wireVal n C t y = true := ih t (by omega) (by omega) htu (hs t htR)
        rw [he, ProofWire.gate_value C hao k hk y]
        rcases hinputs with hi | hi <;> simp [hop, opnd, hi, hty]
      · have hzero := ProofWire.operand_lt C hao k hk 0
        have hone := ProofWire.operand_lt C hao k hk 1
        have hmem (b : Fin 2) : opnd C k b ∈ (gateAt C k).inputs := by
          have hg : C.gates[k]? = some (gateAt C k) := by
            simp [gateAt, List.getD_eq_getElem?_getD, hk]
          have hlen := hao.2.2 _ (List.mem_of_getElem? hg)
          have hb : b.val < (gateAt C k).inputs.length := by simpa [hlen] using b.isLt
          have ho : (gateAt C k).inputs[b.val]? = some (opnd C k b) := by
            simp [opnd, List.getD_eq_getElem?_getD, hb]
          exact List.mem_of_getElem? ho
        have haway (b : Fin 2) : opnd C k b ≠ u.val := by
          intro heq
          exact hreader (heq ▸ hmem b)
        rw [he, ProofWire.gate_value C hao k hk x, ProofWire.gate_value C hao k hk y]
        split_ifs with hop
        · intro ht
          simp only [Bool.and_eq_true] at ht ⊢
          exact ⟨ih _ (by omega) (by omega) (haway 0) ht.1,
            ih _ (by omega) (by omega) (haway 1) ht.2⟩
        · intro ht
          simp only [Bool.or_eq_true] at ht ⊢
          rcases ht with ht | ht
          · exact Or.inl (ih _ (by omega) (by omega) (haway 0) ht)
          · exact Or.inr (ih _ (by omega) (by omega) (haway 1) ht)

lemma readers_or_independent_support_erase_bound {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (u : Fin n)
    (R : Finset ℕ) (hao : IsAO2 n C)
    (hread : ∀ k < C.gates.length, u.val ∈ (gateAt C k).inputs →
      (gateAt C k).op = GateOp.or ∧ ∃ t ∈ R, t ≠ u.val ∧
        ((gateAt C k).inputs = [u.val, t] ∨ (gateAt C k).inputs = [t, u.val]))
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G)
    (J : Finset (Fin n)) (hind : ∀ a ∈ J, ∀ b ∈ J, ¬ G.Adj a b)
    (hs : ∀ t ∈ R, wireVal n C t (setInput J) = true) :
    G.degree u ≤ (J.erase u).card := by
  refine readers_or_independent_support_bound G C u (R.erase u.val) hao ?_ hfun hfour
    (J.erase u) (by simp) ?_ ?_
  · intro k hk hr
    obtain ⟨hop, t, htR, htu, hin⟩ := hread k hk hr
    exact ⟨hop, t, Finset.mem_erase.mpr ⟨htu, htR⟩, hin⟩
  · intro a ha b hb
    exact hind a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
  · intro t ht
    have htR := Finset.mem_of_mem_erase ht
    have htu := (Finset.mem_erase.mp ht).1
    apply readers_or_sources_compare C hao u R hread (setInput J) (setInput (J.erase u))
      _ hs t (true_wire_bound C (setInput J) t (hs t htR)) htu (hs t htR)
    intro i hi hiJ
    simp only [setInput, decide_eq_true_eq] at hiJ ⊢
    exact Finset.mem_erase.mpr ⟨hi, hiJ⟩

end MultiReader

namespace MultiDirty
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open TwinLeaf.SingleRead

lemma readers_or_dirty_and_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (R : Finset ℕ) (hAO : IsAO2 n C)
    (hread : ∀ k < C.gates.length, u.val ∈ (gateAt C k).inputs →
      (gateAt C k).op = GateOp.or ∧ ∃ t ∈ R,
        (gateAt C k).inputs = [u.val, t] ∨ (gateAt C k).inputs = [t, u.val])
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G)
    (I : Finset (Fin n)) (huI : u ∉ I)
    (hind : ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b)
    (hs : ∀ t ∈ R, wireVal n C t (setInput I) = true) :
    G.degree u ≤ (DirtyCertificate.dirtyAnds G C (n + C.gates.length)).card + R.card := by
  classical
  have hR : ∀ t ∈ R, t < n + C.gates.length :=
    fun t ht => MultiReader.true_wire_bound C (setInput I) t (hs t ht)
  obtain ⟨J, hJ, hsJ, hcard⟩ := ProofForest.true_certificates C hAO R hR (setInput I) hs
  have hsub : J ⊆ I := by
    intro i hi
    simpa [setInput] using hJ i hi
  have huJ : u ∉ J := fun h => huI (hsub h)
  have hindJ : ∀ a ∈ J, ∀ b ∈ J, ¬ G.Adj a b :=
    fun a ha b hb => hind a (hsub ha) b (hsub hb)
  have hd := MultiReader.readers_or_independent_support_bound G C u R hAO hread hfun hfour J huJ hindJ hsJ
  have hc := DirtyCertificate.trueAnds_le_dirty G C (n + C.gates.length) I hind
  omega

lemma readers_or_joint_dirty_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (R : Finset ℕ) (hAO : IsAO2 n C)
    (hread : ∀ k < C.gates.length, u.val ∈ (gateAt C k).inputs →
      (gateAt C k).op = GateOp.or ∧ ∃ t ∈ R,
        (gateAt C k).inputs = [u.val, t] ∨ (gateAt C k).inputs = [t, u.val])
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G)
    (hdirty : ¬ ∀ x : Fin n → Bool, x u = false →
      (∀ t ∈ R, wireVal n C t x = true) → graphFun G ∅ x = true) :
    G.degree u ≤ (DirtyCertificate.dirtyAnds G C (n + C.gates.length)).card + R.card := by
  classical
  push Not at hdirty
  obtain ⟨x, hu, hs, hf⟩ := hdirty
  let I := Finset.univ.filter (fun i : Fin n => x i = true)
  have heq : setInput I = x := by
    funext i
    simp [setInput, I]
  have huI : u ∉ I := by simp [I, hu]
  have hind : ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b := by
    intro a ha b hb hab
    apply hf
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false,
      decide_false, Bool.false_or, decide_eq_true_eq]
    exact ⟨a, b, hab, by simpa [I] using ha, by simpa [I] using hb⟩
  apply readers_or_dirty_and_bound G C u R hAO hread hfun hfour I huI hind
  simpa [heq] using hs

lemma readers_or_dirty_and_erase_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (R : Finset ℕ) (hAO : IsAO2 n C)
    (hread : ∀ k < C.gates.length, u.val ∈ (gateAt C k).inputs →
      (gateAt C k).op = GateOp.or ∧ ∃ t ∈ R, t ≠ u.val ∧
        ((gateAt C k).inputs = [u.val, t] ∨ (gateAt C k).inputs = [t, u.val]))
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G)
    (I : Finset (Fin n)) (hind : ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b)
    (hs : ∀ t ∈ R, wireVal n C t (setInput I) = true) :
    G.degree u ≤ (DirtyCertificate.dirtyAnds G C (n + C.gates.length)).card + R.card := by
  classical
  have hR : ∀ t ∈ R, t < n + C.gates.length :=
    fun t ht => MultiReader.true_wire_bound C (setInput I) t (hs t ht)
  obtain ⟨J, hJ, hsJ, hcard⟩ := ProofForest.true_certificates C hAO R hR (setInput I) hs
  have hsub : J ⊆ I := by
    intro i hi
    simpa [setInput] using hJ i hi
  have hindJ : ∀ a ∈ J, ∀ b ∈ J, ¬ G.Adj a b :=
    fun a ha b hb => hind a (hsub ha) b (hsub hb)
  have hd := MultiReader.readers_or_independent_support_erase_bound G C u R hAO hread hfun hfour J hindJ hsJ
  have he := Finset.card_erase_le (s := J) (a := u)
  have hc := DirtyCertificate.trueAnds_le_dirty G C (n + C.gates.length) I hind
  omega

lemma readers_or_joint_dirty_erase_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (R : Finset ℕ) (hAO : IsAO2 n C)
    (hread : ∀ k < C.gates.length, u.val ∈ (gateAt C k).inputs →
      (gateAt C k).op = GateOp.or ∧ ∃ t ∈ R, t ≠ u.val ∧
        ((gateAt C k).inputs = [u.val, t] ∨ (gateAt C k).inputs = [t, u.val]))
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G)
    (hdirty : ¬ ∀ x : Fin n → Bool,
      (∀ t ∈ R, wireVal n C t x = true) → graphFun G ∅ x = true) :
    G.degree u ≤ (DirtyCertificate.dirtyAnds G C (n + C.gates.length)).card + R.card := by
  classical
  push Not at hdirty
  obtain ⟨x, hs, hf⟩ := hdirty
  let I := Finset.univ.filter (fun i : Fin n => x i = true)
  have heq : setInput I = x := by
    funext i
    simp [setInput, I]
  have hind : ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b := by
    intro a ha b hb hab
    apply hf
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false,
      decide_false, Bool.false_or, decide_eq_true_eq]
    exact ⟨a, b, hab, by simpa [I] using ha, by simpa [I] using hb⟩
  apply readers_or_dirty_and_erase_bound G C u R hAO hread hfun hfour I hind
  simpa [heq] using hs

end MultiDirty


namespace DirtyCertificate
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma dirtyAnds_subset_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r : ℕ) : dirtyAnds G C r ⊆ junk G C := by
  classical
  intro j hj
  obtain ⟨hj, _, hand, hdirty⟩ := Finset.mem_filter.mp hj
  have hjlt : j < C.gates.length := Finset.mem_range.mp hj
  unfold BelowF at hdirty
  push Not at hdirty
  obtain ⟨x, hx, hf⟩ := hdirty
  exact Finset.mem_filter.mpr ⟨hj, hand, hjlt, x, hx, by simpa using hf⟩

lemma dirtyAnds_all_eq_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : dirtyAnds G C (n + C.gates.length) = junk G C := by
  classical
  apply Finset.Subset.antisymm (dirtyAnds_subset_junk G C _)
  intro j hj
  obtain ⟨hj, hand, hjlt, x, hx, hf⟩ := Finset.mem_filter.mp hj
  apply Finset.mem_filter.mpr
  refine ⟨hj, by omega, hand, ?_⟩
  intro hbelow
  have h := hbelow x hx
  rw [hf] at h
  cases h

end DirtyCertificate


namespace ProofLocalized
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.CleanedNonEdge ProofSelection

def ClosedWires (n : ℕ) (C : Circuit) (K : Finset ℕ) : Prop :=
  ∀ v ∈ K, n ≤ v → v < n + C.gates.length →
    opnd C (v - n) 0 ∈ K ∧ opnd C (v - n) 1 ∈ K

lemma selected_closed {n : ℕ} (C : Circuit) (K : Finset ℕ) (hK : ClosedWires n C K)
    (x : Fin n → Bool) (v : ℕ) (hv : v < n + C.gates.length) (hvK : v ∈ K)
    (w : ℕ) (hw : w ∈ selectedChildren n C x v) : w ∈ K := by
  classical
  by_cases hin : v < n
  · simp [selectedChildren, hin] at hw
  have hk := hK v hvK (by omega) hv
  simp only [selectedChildren, hin, ↓reduceIte] at hw
  split_ifs at hw with ha hx
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hk.1
    · exact hk.2
  · exact (Finset.mem_singleton.mp hw) ▸ hk.1
  · exact (Finset.mem_singleton.mp hw) ▸ hk.2

lemma true_certificates {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset ℕ) (hR : ∀ r ∈ R, r < n + C.gates.length)
    (K : Finset ℕ) (hRK : R ⊆ K) (hK : ClosedWires n C K) (x : Fin n → Bool)
    (hx : ∀ r ∈ R, wireVal n C r x = true) :
    ∃ J : Finset (Fin n), (∀ i ∈ J, x i = true) ∧
      (∀ r ∈ R, wireVal n C r (fun i => decide (i ∈ J)) = true) ∧
      J.card ≤ ((trueAnds n C x (n + C.gates.length)).filter (fun v => v ∈ K)).card + R.card := by
  classical
  let S := selectedChildren n C x
  obtain ⟨V, hRV, hbound, hclosed, hincoming, htruthK⟩ :=
    SelectedForest.exists_forest S R (n + C.gates.length) hR
      (selected_back C hAO x) (fun v => wireVal n C v x = true ∧ v ∈ K)
      (fun r hr => ⟨hx r hr, hRK hr⟩)
      (fun v hv hp w hw => ⟨selected_true C hAO x v hv hp.1 w hw,
        selected_closed C K hK x v hv hp.2 w hw⟩)
  have htruth (v : ℕ) (hv : v ∈ V) := (htruthK v hv).1
  let L := V.filter (fun v => v < n)
  let A := V.filter (fun v => n ≤ v ∧ (gateAt C (v - n)).op = GateOp.and)
  let J : Finset (Fin n) := Finset.univ.filter (fun i => i.val ∈ V)
  have hcard : J.card = L.card := by
    apply Finset.card_bij (fun i _ => i.val)
    · intro i hi
      simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact Finset.mem_filter.mpr ⟨hi, i.isLt⟩
    · intro i hi j hj he
      exact Fin.ext he
    · intro v hv
      obtain ⟨hvV, hvn⟩ := Finset.mem_filter.mp hv
      exact ⟨⟨v, hvn⟩, by simpa [J] using hvV, rfl⟩
  have hcount : L.card ≤ A.card + R.card := by
    apply CertificateForest.children_leaf_bound V L A R S hRV
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) hincoming
    · intro v hv
      have h := (Finset.mem_filter.mp hv).2
      simp [S, selectedChildren, h]
    · intro v hv
      obtain ⟨hvV, hvn, ha⟩ := Finset.mem_filter.mp hv
      simp only [S, selectedChildren, not_lt.mpr hvn, ↓reduceIte, ha]
      by_cases h : opnd C (v - n) 0 = opnd C (v - n) 1 <;> simp [h]
    · intro v hv hl ha
      have hvn : n ≤ v := by
        by_contra h
        exact hl (Finset.mem_filter.mpr ⟨hv, by omega⟩)
      have hop : (gateAt C (v - n)).op ≠ GateOp.and := by
        intro h
        exact ha (Finset.mem_filter.mpr ⟨hv, hvn, h⟩)
      simp [S, selectedChildren, not_lt.mpr hvn, hop]
  have hsub : A ⊆ (trueAnds n C x (n + C.gates.length)).filter (fun v => v ∈ K) := by
    intro v hv
    obtain ⟨hvV, hvn, ha⟩ := Finset.mem_filter.mp hv
    have hb := hbound v hvV
    simp only [trueAnds, Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨hb, hvn, Nat.le_of_lt hb, ha, htruth v hvV⟩, (htruthK v hvV).2⟩
  refine ⟨J, ?_, ?_, ?_⟩
  · intro i hi
    have hv : i.val ∈ V := by simpa [J] using hi
    have ht := htruth i.val hv
    rw [ProofWire.input_value] at ht
    exact ht
  · have hall := SelectedTrace.propagate_on_trace S V
      (fun v => wireVal n C v (fun i => decide (i ∈ J)) = true) ?_ hclosed ?_
    · intro r hr
      exact hall r (hRV hr)
    · intro v hv w hw
      exact selected_back C hAO x v (hbound v hv) w hw
    · intro v hv ih
      by_cases hvn : v < n
      · rw [ProofWire.input_value C v hvn]
        simpa [J] using hv
      · exact selected_eval C hAO x _ v (hbound v hv) (by omega) ih
  · rw [hcard]
    exact hcount.trans (Nat.add_le_add_right (Finset.card_le_card hsub) R.card)

end ProofLocalized

namespace LocalizedDirty
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open TwinLeaf.SingleRead

noncomputable def dirtyInside {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (K : Finset ℕ) : Finset ℕ := by
  classical
  exact (junk G C).filter (fun j => n + j ∈ K)

lemma trueAnds_inside_le_dirty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (K : Finset ℕ) (I : Finset (Fin n))
    (hind : ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b) :
    ((ProofSelection.trueAnds n C (setInput I) (n + C.gates.length)).filter (fun v => v ∈ K)).card ≤
      (dirtyInside G C K).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun v => v - n)
  · intro v hv
    change v - n ∈ dirtyInside G C K
    obtain ⟨hvA, hvK⟩ := Finset.mem_filter.mp hv
    obtain ⟨hv, hn, _, hand, ht⟩ := Finset.mem_filter.mp hvA
    have hv' : v < n + C.gates.length := Finset.mem_range.mp hv
    have heq : n + (v - n) = v := by omega
    apply Finset.mem_filter.mpr
    refine ⟨?_, by rwa [heq]⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), hand, by omega, setInput I, ?_,
      DirtyCertificate.independent_false G I hind⟩
    change wireVal n C (n + (v - n)) (setInput I) = true
    rwa [heq]
  · intro v hv w hw he
    have hvn : n ≤ v := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2.1
    have hwn : n ≤ w := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2.1
    change v - n = w - n at he
    omega

lemma readers_or_dirty_bound_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (R K : Finset ℕ) (hAO : IsAO2 n C)
    (hRK : R ⊆ K) (hK : ProofLocalized.ClosedWires n C K)
    (hread : ∀ k < C.gates.length, u.val ∈ (gateAt C k).inputs →
      (gateAt C k).op = GateOp.or ∧ ∃ t ∈ R, t ≠ u.val ∧
        ((gateAt C k).inputs = [u.val, t] ∨ (gateAt C k).inputs = [t, u.val]))
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G)
    (I : Finset (Fin n)) (hind : ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b)
    (hs : ∀ t ∈ R, wireVal n C t (setInput I) = true) :
    G.degree u ≤ (dirtyInside G C K).card + R.card := by
  classical
  have hR : ∀ t ∈ R, t < n + C.gates.length :=
    fun t ht => MultiReader.true_wire_bound C (setInput I) t (hs t ht)
  obtain ⟨J, hJ, hsJ, hcard⟩ := ProofLocalized.true_certificates C hAO R hR K hRK hK (setInput I) hs
  have hsub : J ⊆ I := by
    intro i hi
    simpa [setInput] using hJ i hi
  have hindJ : ∀ a ∈ J, ∀ b ∈ J, ¬ G.Adj a b :=
    fun a ha b hb => hind a (hsub ha) b (hsub hb)
  have hd := MultiReader.readers_or_independent_support_erase_bound G C u R hAO hread hfun hfour J hindJ hsJ
  have he := Finset.card_erase_le (s := J) (a := u)
  have hc := trueAnds_inside_le_dirty G C K I hind
  omega

lemma readers_or_joint_dirty_bound_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (R K : Finset ℕ) (hAO : IsAO2 n C)
    (hRK : R ⊆ K) (hK : ProofLocalized.ClosedWires n C K)
    (hread : ∀ k < C.gates.length, u.val ∈ (gateAt C k).inputs →
      (gateAt C k).op = GateOp.or ∧ ∃ t ∈ R, t ≠ u.val ∧
        ((gateAt C k).inputs = [u.val, t] ∨ (gateAt C k).inputs = [t, u.val]))
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G)
    (hdirty : ¬ ∀ x : Fin n → Bool,
      (∀ t ∈ R, wireVal n C t x = true) → graphFun G ∅ x = true) :
    G.degree u ≤ (dirtyInside G C K).card + R.card := by
  classical
  push Not at hdirty
  obtain ⟨x, hs, hf⟩ := hdirty
  let I := Finset.univ.filter (fun i : Fin n => x i = true)
  have heq : setInput I = x := by funext i; simp [setInput, I]
  have hind : ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b := by
    intro a ha b hb hab
    apply hf
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false,
      decide_false, Bool.false_or, decide_eq_true_eq]
    exact ⟨a, b, hab, by simpa [I] using ha, by simpa [I] using hb⟩
  apply readers_or_dirty_bound_closed G C u R K hAO hRK hK hread hfun hfour I hind
  simpa [heq] using hs

end LocalizedDirty


namespace WireCone

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def child (n : ℕ) (C : Circuit) (p q : ℕ) : Prop :=
  n ≤ p ∧ p < n + C.gates.length ∧ q ∈ (gateAt C (p - n)).inputs

noncomputable def backwardCone (n : ℕ) (C : Circuit) (R : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (n + C.gates.length)).filter
    (fun v => ∃ r ∈ R, Relation.ReflTransGen (child n C) r v)

lemma mem_iff {n : ℕ} (C : Circuit) (R : Finset ℕ) (v : ℕ) :
    v ∈ backwardCone n C R ↔ v < n + C.gates.length ∧
      ∃ r ∈ R, Relation.ReflTransGen (child n C) r v := by
  classical
  simp [backwardCone]

lemma mem_bound {n : ℕ} (C : Circuit) (R : Finset ℕ) {v : ℕ}
    (hv : v ∈ backwardCone n C R) : v < n + C.gates.length :=
  ((mem_iff C R v).mp hv).1

lemma roots_subset {n : ℕ} (C : Circuit) (R : Finset ℕ)
    (hR : ∀ r ∈ R, r < n + C.gates.length) : R ⊆ backwardCone n C R := by
  intro r hr
  exact (mem_iff C R r).mpr ⟨hR r hr, r, hr, .refl⟩

lemma child_back {n : ℕ} (C : Circuit) (hao : IsAO2 n C) {p q : ℕ}
    (h : child n C p q) : q < p := by
  obtain ⟨hn, hp, hq⟩ := h
  have hk : p - n < C.gates.length := by omega
  have hlt := hao.2.1 (p - n) hk q hq
  omega

lemma closed {n : ℕ} (C : Circuit) (hao : IsAO2 n C) (R : Finset ℕ)
    {p q : ℕ} (hp : p ∈ backwardCone n C R) (hpq : child n C p q) :
    q ∈ backwardCone n C R := by
  obtain ⟨hbound, r, hr, hreach⟩ := (mem_iff C R p).mp hp
  exact (mem_iff C R q).mpr
    ⟨(child_back C hao hpq).trans hbound, r, hr, hreach.tail hpq⟩

lemma gate_closed {n : ℕ} (C : Circuit) (hao : IsAO2 n C) (R : Finset ℕ)
    {p q : ℕ} (hp : p ∈ backwardCone n C R) (hn : n ≤ p)
    (hq : q ∈ (gateAt C (p - n)).inputs) : q ∈ backwardCone n C R := by
  exact closed C hao R hp ⟨hn, mem_bound C R hp, hq⟩

lemma opnd_mem {n : ℕ} (C : Circuit) (hao : IsAO2 n C)
    (k : ℕ) (hk : k < C.gates.length) (b : Fin 2) :
    opnd C k b ∈ (gateAt C k).inputs := by
  have hg : C.gates[k]? = some (gateAt C k) := by
    simp [gateAt, List.getD_eq_getElem?_getD, hk]
  have hlen := hao.2.2 _ (List.mem_of_getElem? hg)
  have hb : b.val < (gateAt C k).inputs.length := by simpa [hlen] using b.isLt
  have ho : (gateAt C k).inputs[b.val]? = some (opnd C k b) := by
    simp [opnd, List.getD_eq_getElem?_getD, hb]
  exact List.mem_of_getElem? ho

lemma operands_closed {n : ℕ} (C : Circuit) (hao : IsAO2 n C) (R : Finset ℕ)
    {p : ℕ} (hp : p ∈ backwardCone n C R) (hn : n ≤ p) :
    opnd C (p - n) 0 ∈ backwardCone n C R ∧
      opnd C (p - n) 1 ∈ backwardCone n C R := by
  have hb := mem_bound C R hp
  have hk : p - n < C.gates.length := by omega
  exact ⟨gate_closed C hao R hp hn (opnd_mem C hao (p - n) hk 0),
    gate_closed C hao R hp hn (opnd_mem C hao (p - n) hk 1)⟩

lemma subset_closed {n : ℕ} (C : Circuit) (R K : Finset ℕ) (hR : R ⊆ K)
    (hK : ∀ p ∈ K, ∀ q, child n C p q → q ∈ K) : backwardCone n C R ⊆ K := by
  intro v hv
  obtain ⟨hbound, r, hr, hreach⟩ := (mem_iff C R v).mp hv
  clear hv hbound
  induction hreach with
  | refl => exact hR hr
  | @tail b c hbc hstep ih => exact hK b ih c hstep

end WireCone

namespace ConeDirty
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open TwinLeaf.SingleRead LocalizedDirty

lemma backwardCone_closed {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (R : Finset ℕ) :
    ProofLocalized.ClosedWires n C (WireCone.backwardCone n C R) := by
  intro v hv hn _
  exact WireCone.operands_closed C hAO R hv hn

lemma readers_or_dirty_bound_cone {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (R : Finset ℕ) (hAO : IsAO2 n C)
    (hread : ∀ k < C.gates.length, u.val ∈ (gateAt C k).inputs →
      (gateAt C k).op = GateOp.or ∧ ∃ t ∈ R, t ≠ u.val ∧
        ((gateAt C k).inputs = [u.val, t] ∨ (gateAt C k).inputs = [t, u.val]))
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G)
    (I : Finset (Fin n)) (hind : ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b)
    (hs : ∀ t ∈ R, wireVal n C t (setInput I) = true) :
    G.degree u ≤ (dirtyInside G C (WireCone.backwardCone n C R)).card + R.card := by
  have hR : ∀ t ∈ R, t < n + C.gates.length :=
    fun t ht => MultiReader.true_wire_bound C (setInput I) t (hs t ht)
  exact readers_or_dirty_bound_closed G C u R _ hAO (WireCone.roots_subset C R hR)
    (backwardCone_closed C hAO R) hread hfun hfour I hind hs

lemma readers_or_joint_dirty_bound_cone {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (R : Finset ℕ) (hAO : IsAO2 n C)
    (hread : ∀ k < C.gates.length, u.val ∈ (gateAt C k).inputs →
      (gateAt C k).op = GateOp.or ∧ ∃ t ∈ R, t ≠ u.val ∧
        ((gateAt C k).inputs = [u.val, t] ∨ (gateAt C k).inputs = [t, u.val]))
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G)
    (hdirty : ¬ ∀ x : Fin n → Bool,
      (∀ t ∈ R, wireVal n C t x = true) → graphFun G ∅ x = true) :
    G.degree u ≤ (dirtyInside G C (WireCone.backwardCone n C R)).card + R.card := by
  classical
  have hR : ∀ t ∈ R, t < n + C.gates.length := by
    have h := hdirty
    push Not at h
    obtain ⟨x, hs, _⟩ := h
    exact fun t ht => MultiReader.true_wire_bound C x t (hs t ht)
  exact readers_or_joint_dirty_bound_closed G C u R _ hAO (WireCone.roots_subset C R hR)
    (backwardCone_closed C hAO R) hread hfun hfour hdirty

lemma sole_or_dirty_source_cone_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hAO : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G) (htu : t ≠ u.val)
    (hdirty : ¬ ∀ x : Fin n → Bool, wireVal n C t x = true → graphFun G ∅ x = true) :
    G.degree u ≤ (dirtyInside G C (WireCone.backwardCone n C {t})).card + 1 := by
  classical
  have hread : ∀ k < C.gates.length, u.val ∈ (gateAt C k).inputs →
      (gateAt C k).op = GateOp.or ∧ ∃ s ∈ ({t} : Finset ℕ), s ≠ u.val ∧
        ((gateAt C k).inputs = [u.val, s] ∨ (gateAt C k).inputs = [s, u.val]) := by
    intro k hk hu
    have hm : gateAt C k ∈ C.gates := List.mem_of_getElem? (show C.gates[k]? = some (gateAt C k) by
      simp [gateAt, List.getD_eq_getElem?_getD, hk])
    have hm' : gateAt C k ∈ pre ∨ gateAt C k = g ∨ gateAt C k ∈ post := by
      simpa [hshape] using hm
    rcases hm' with hp | he | hp
    · exact False.elim (hno _ (by simp [hp]) hu)
    · exact ⟨by rwa [he], t, by simp, htu, by rwa [he]⟩
    · exact False.elim (hno _ (by simp [hp]) hu)
  have hdirty' : ¬ ∀ x : Fin n → Bool,
      (∀ s ∈ ({t} : Finset ℕ), wireVal n C s x = true) → graphFun G ∅ x = true := by
    intro h
    apply hdirty
    intro x hx
    apply h x
    intro s hs
    have he := Finset.mem_singleton.mp hs
    simpa [he] using hx
  simpa using readers_or_joint_dirty_bound_cone G C u {t} hAO hread hfun hfour hdirty'

end ConeDirty



namespace Normalization

open PEqualNP.MetaComplexity

namespace Lift

open PEqualNP.CircuitLowerBounds


def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma foldl_step_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ s : List Bool, gs.foldl step w = w ++ s ∧ s.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨s, hs, hl⟩ := ih (step w g)
    refine ⟨(g.op.eval (g.inputs.map fun i => w.getD i false)) :: s, ?_, by simp [hl]⟩
    rw [List.foldl_cons, hs]
    simp [step]

lemma foldl_step_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨s, hs, hl⟩ := foldl_step_prefix gs w
  simp [hs, hl]

lemma getD_append_left (w s : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ s).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_step_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨s, hs, _⟩ := foldl_step_prefix gs w
  rw [hs, getD_append_left w s i hi]

lemma getD_append_singleton_last (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_append_singleton (w : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · exact getD_append_left w [b] i h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega : (w ++ [b]).length ≤ i),
      List.getElem?_eq_none (by omega : w.length ≤ i)]

end Lift

namespace LiftFix

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3566.Normalization.Lift
open PEqualNP.MetaComplexity.NestedCover



lemma foldl_set_equiv (gs : List Gate) (k : ℕ) (g g' : Gate) (hg : gs[k]? = some g)
    (heq : ∀ w : List Bool, g'.op.eval (g'.inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false)) (w0 : List Bool) :
    (gs.set k g').foldl step w0 = gs.foldl step w0 := by
  induction gs generalizing k w0 with
  | nil => simp
  | cons h gs ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
      subst hg
      simp only [List.set_cons_zero, List.foldl_cons]
      congr 1
      unfold step
      rw [heq]
    | succ k =>
      simp only [List.getElem?_cons_succ] at hg
      simp only [List.set_cons_succ, List.foldl_cons]
      exact ih k hg _



lemma foldl_split (gs : List Gate) (k : ℕ) (g : Gate) (hg : gs[k]? = some g) (w0 : List Bool) :
    gs.foldl step w0 = (gs.drop (k + 1)).foldl step (step ((gs.take k).foldl step w0) g) := by
  have hk : k < gs.length := by
    rcases (List.getElem?_eq_some_iff.mp hg) with ⟨hk, _⟩
    exact hk
  have hgk : gs[k] = g := (List.getElem?_eq_some_iff.mp hg).2
  conv_lhs => rw [← List.take_append_drop k gs, List.drop_eq_getElem_cons hk, hgk]
  rw [List.foldl_append, List.foldl_cons]

lemma take_fold_length (gs : List Gate) (k : ℕ) (hk : k < gs.length) (w0 : List Bool) :
    ((gs.take k).foldl step w0).length = w0.length + k := by
  rw [foldl_step_length, List.length_take]
  omega


lemma wires_copy (F : Circuit) (k u : ℕ) (hk : F.gates[k]? = some ⟨GateOp.or, [u]⟩)
    (w0 : List Bool) (hu : u < w0.length + k) :
    (F.wires w0).getD (w0.length + k) false = (F.wires w0).getD u false := by
  have hk' : k < F.gates.length := (List.getElem?_eq_some_iff.mp hk).1
  rw [wires_eq, foldl_split F.gates k _ hk w0]
  have hl := take_fold_length F.gates k hk' w0
  set Wp := (F.gates.take k).foldl step w0
  rw [foldl_step_getD _ _ _ (by simp [step]; omega), foldl_step_getD _ _ _ (by simp [step]; omega)]
  unfold step
  rw [← hl, getD_append_singleton_last, getD_append_left _ _ _ (by omega)]
  simp [GateOp.eval]




def sig (m u : ℕ) (i : ℕ) : ℕ := if i < m then i else if i = m then u else i - 1


def rd (m u : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sig m u)⟩


def sg (k : ℕ) (j : ℕ) : ℕ := if j < k then j else j - 1


def del (n k u : ℕ) (E : Circuit) : Circuit :=
  ⟨(E.gates.eraseIdx k).map (rd (n + k) u), sig (n + k) u E.output⟩

lemma sig_gate (n k u j : ℕ) (hj : j ≠ k) : sig (n + k) u (n + j) = n + sg k j := by
  unfold sig sg
  split_ifs <;> omega


def Rel (m u : ℕ) (a b : List Bool) : Prop :=
  a.length = b.length + 1 ∧ m < a.length ∧ ∀ i, b.getD (sig m u i) false = a.getD i false

lemma getD_oob (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma rel_step (m u : ℕ) (hu : u < m) (a b : List Bool) (g : Gate) (h : Rel m u a b) :
    Rel m u (step a g) (step b (rd m u g)) := by
  obtain ⟨hl, hm, hv⟩ := h
  have hev : (rd m u g).op.eval ((rd m u g).inputs.map fun i => b.getD i false) =
      g.op.eval (g.inputs.map fun i => a.getD i false) := by
    simp only [rd, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact hv i
  unfold step
  rw [hev]
  set v := g.op.eval (g.inputs.map fun i => a.getD i false)
  refine ⟨by simp [hl], by simp; omega, ?_⟩
  intro i
  rcases Nat.lt_trichotomy i a.length with h1 | h1 | h1
  · have hs : sig m u i < b.length := by unfold sig; split_ifs <;> omega
    rw [getD_append_left _ _ _ hs, getD_append_left _ _ _ h1, hv]
  · have hs : sig m u i = b.length := by unfold sig; split_ifs <;> omega
    rw [hs, getD_append_singleton_last, h1, getD_append_singleton_last]
  · have hs : sig m u i > b.length := by unfold sig; split_ifs <;> omega
    rw [getD_oob _ _ (by simp; omega), getD_oob _ _ (by simp; omega)]

lemma rel_fold (m u : ℕ) (hu : u < m) (gs : List Gate) : ∀ a b : List Bool, Rel m u a b →
    Rel m u (gs.foldl step a) ((gs.map (rd m u)).foldl step b) := by
  induction gs with
  | nil => intro a b h; simpa using h
  | cons g gs ih =>
    intro a b h
    simp only [List.foldl_cons, List.map_cons]
    exact ih _ _ (rel_step m u hu a b g h)

lemma rd_id (m u : ℕ) (g : Gate) (h : ∀ i ∈ g.inputs, i < m) : rd m u g = g := by
  obtain ⟨op, ins⟩ := g
  simp only [rd, Gate.mk.injEq, true_and]
  conv_rhs => rw [← List.map_id ins]
  apply List.map_congr_left
  intro i hi
  have := h i hi
  simp [sig, this]

lemma del_fun (n k u : ℕ) (E : Circuit) (hk : k < E.gates.length) (hu : u < n + k)
    (hpre : ∀ g ∈ E.gates.take k, ∀ i ∈ g.inputs, i < n + k)
    (hcopy : ∀ x : Fin n → Bool,
      (E.wires (List.ofFn x)).getD (n + k) false = (E.wires (List.ofFn x)).getD u false) :
    circuitFun n (del n k u E) = circuitFun n E := by
  funext x
  have hc := hcopy x
  unfold circuitFun Circuit.eval
  have hgk : E.gates[k]? = some E.gates[k] := List.getElem?_eq_getElem hk
  set gk := E.gates[k]
  set w0 := List.ofFn x with hw0
  have hw0l : w0.length = n := by simp [hw0]
  have hl := take_fold_length E.gates k hk w0
  rw [hw0l] at hl
  set Wp := (E.gates.take k).foldl step w0 with hWp
  have hW : E.wires w0 = (E.gates.drop (k + 1)).foldl step (step Wp gk) := by
    rw [wires_eq, foldl_split E.gates k gk hgk w0]
  have hD : (del n k u E).wires w0 =
      ((E.gates.drop (k + 1)).map (rd (n + k) u)).foldl step Wp := by
    rw [wires_eq]
    simp only [del]
    rw [List.eraseIdx_eq_take_drop_succ, List.map_append, List.foldl_append]
    congr 1
    rw [hWp]
    congr 1
    conv_rhs => rw [← List.map_id (E.gates.take k)]
    apply List.map_congr_left
    intro g hg
    exact rd_id _ _ g (hpre g hg)

  have hvk : (step Wp gk).getD (n + k) false = Wp.getD u false := by
    rw [hW, foldl_step_getD _ _ _ (by simp [step]; omega),
      foldl_step_getD _ _ _ (by simp [step]; omega)] at hc
    rw [hc]
    unfold step
    exact getD_append_left _ _ _ (by omega)
  have hrel0 : Rel (n + k) u (step Wp gk) Wp := by
    refine ⟨by simp [step], by simp [step]; omega, ?_⟩
    intro i
    rcases Nat.lt_trichotomy i (n + k) with h1 | h1 | h1
    · have : sig (n + k) u i = i := by simp [sig, h1]
      rw [this]
      unfold step
      rw [getD_append_left _ _ _ (by omega)]
    · have : sig (n + k) u i = u := by simp [sig, h1]
      rw [this, h1, hvk]
    · have : sig (n + k) u i = i - 1 := by
        unfold sig; split_ifs <;> omega
      rw [this, getD_oob _ _ (by omega), getD_oob _ _ (by simp [step]; omega)]
  have hrel := rel_fold (n + k) u hu (E.gates.drop (k + 1)) _ _ hrel0
  rw [hD, hW]
  exact hrel.2.2 E.output

lemma del_length (n k u : ℕ) (E : Circuit) (hk : k < E.gates.length) :
    (del n k u E).gates.length + 1 = E.gates.length := by
  simp only [del, List.length_map, List.length_eraseIdx, if_pos hk]
  omega

lemma del_get (n k u : ℕ) (E : Circuit) (j : ℕ) (g : Gate) (hj : j ≠ k)
    (h : E.gates[j]? = some g) : (del n k u E).gates[sg k j]? = some (rd (n + k) u g) := by
  by_cases h1 : j < k
  · simp only [del, sg, if_pos h1, List.getElem?_map, List.getElem?_eraseIdx, h]; rfl
  · have h2 : ¬ (j - 1 < k) := by omega
    have h3 : j - 1 + 1 = j := by omega
    simp only [del, sg, if_neg h1, List.getElem?_map, List.getElem?_eraseIdx, if_neg h2, h3, h]
    rfl

lemma del_get_inv (n k u : ℕ) (E : Circuit) (j : ℕ) (g : Gate)
    (h : (del n k u E).gates[j]? = some g) :
    ∃ g0, E.gates[if j < k then j else j + 1]? = some g0 ∧ g = rd (n + k) u g0 := by
  simp only [del, List.getElem?_map, List.getElem?_eraseIdx] at h
  split_ifs at h ⊢ with h1
  · cases hh : E.gates[j]? with
    | none => rw [hh] at h; simp at h
    | some g0 => rw [hh] at h; simp at h; exact ⟨g0, rfl, h.symm⟩
  · cases hh : E.gates[j + 1]? with
    | none => rw [hh] at h; simp at h
    | some g0 => rw [hh] at h; simp at h; exact ⟨g0, rfl, h.symm⟩

lemma del_mono (n k u : ℕ) (E : Circuit) (hE : Monotone2 E) : Monotone2 (del n k u E) := by
  intro g hg
  simp only [del, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  have := hE g0 (List.mem_of_mem_eraseIdx hg0)
  simpa [rd] using this

lemma gateAt_some (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    C.gates[j]? = some (gateAt C j) := by
  rw [List.getElem?_eq_getElem hj]
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma readsBack_get (n : ℕ) (C : Circuit) (h : ReadsBack n C) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) : ∀ i ∈ g.inputs, i < n + j := by
  have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
  have := gateAt_some C j hj
  rw [hg] at this
  cases this
  exact h j hj

lemma readsBack_of_get (n : ℕ) (C : Circuit)
    (h : ∀ j (g : Gate), C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j) : ReadsBack n C := by
  intro j hj
  exact h j _ (gateAt_some C j hj)

lemma del_readsBack (n k u : ℕ) (E : Circuit) (hE : ReadsBack n E) (hu : u < n + k) :
    ReadsBack n (del n k u E) := by
  apply readsBack_of_get
  intro j g hg
  obtain ⟨g0, hg0, rfl⟩ := del_get_inv n k u E j g hg
  have hr := readsBack_get n E hE _ g0 hg0
  intro i hi
  simp only [rd, List.mem_map] at hi
  obtain ⟨i0, hi0, rfl⟩ := hi
  have := hr i0 hi0
  unfold sig
  split_ifs at this ⊢ <;> omega

lemma readsBack_take (n : ℕ) (C : Circuit) (h : ReadsBack n C) (k : ℕ) :
    ∀ g ∈ C.gates.take k, ∀ i ∈ g.inputs, i < n + k := by
  intro g hg i hi
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  rw [List.getElem_take] at hi
  have hjl : j < k := by simp at hj; omega
  have hj' : j < C.gates.length := by simp at hj; omega
  have := readsBack_get n C h j _ (List.getElem?_eq_getElem hj') i hi
  omega

end LiftFix


open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_3566.Normalization.Lift

lemma L2604 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j u t : ℕ),
  PEqualNP.MetaComplexity.Monotone2 C →
  j < C.gates.length →
  C.gates[j]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u, t] } →
  t < n + j →
  (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      PEqualNP.MetaComplexity.circuitFun n C x = true) →
  PEqualNP.MetaComplexity.circuitFun n
    { gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] } ++
        [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [C.output, t] }],
      output := n + C.gates.length } =
  PEqualNP.MetaComplexity.circuitFun n C := by
  intro n C j u t _ hj hg ht himp
  funext x
  have hgj : C.gates[j] = { op := GateOp.or, inputs := [u, t] } := by
    rw [List.getElem?_eq_some_iff] at hg
    exact hg.2
  have hsplit : C.gates = C.gates.take j ++
      ({ op := GateOp.or, inputs := [u, t] } : Gate) :: C.gates.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.drop_eq_getElem_cons hj, hgj]
  have hset : C.gates.set j ({ op := GateOp.or, inputs := [u] } : Gate) = C.gates.take j ++
      ({ op := GateOp.or, inputs := [u] } : Gate) :: C.gates.drop (j + 1) := by
    rw [List.set_eq_take_append_cons_drop, if_pos hj]
  have himpx := himp x
  unfold circuitFun Circuit.eval at himpx ⊢
  simp only [wires_eq] at himpx ⊢

  set A := C.gates.take j with hA
  set B := C.gates.drop (j + 1) with hB
  set w0 := List.ofFn x with hw0
  set wA := A.foldl step w0 with hwA
  have hlenA : wA.length = n + j := by
    rw [hwA, foldl_step_length, hw0, List.length_ofFn, hA, List.length_take]
    omega
  have htA : t < wA.length := by omega

  have hW : C.gates.foldl step w0 =
      B.foldl step (step wA { op := GateOp.or, inputs := [u, t] }) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]

  set W' := (A ++ ({ op := GateOp.or, inputs := [u] } : Gate) :: B).foldl step w0 with hW'
  have hW'eq : W' = B.foldl step (step wA { op := GateOp.or, inputs := [u] }) := by
    rw [hW', List.foldl_append, List.foldl_cons]
  have hlenW' : W'.length = n + C.gates.length := by
    have : (A ++ ({ op := GateOp.or, inputs := [u] } : Gate) :: B).length = C.gates.length := by
      conv_rhs => rw [hsplit]
      simp
    rw [hW', foldl_step_length, this, hw0, List.length_ofFn]
  have hW't : W'.getD t false = wA.getD t false := by
    rw [hW'eq, foldl_step_getD _ _ t (by simp [step]; omega)]
    exact getD_append_left _ _ t htA
  have hWt : (C.gates.foldl step w0).getD t false = wA.getD t false := by
    rw [hW, foldl_step_getD _ _ t (by simp [step]; omega)]
    exact getD_append_left _ _ t htA

  have hLHS : ((C.gates.set j ({ op := GateOp.or, inputs := [u] } : Gate) ++
      [({ op := GateOp.or, inputs := [C.output, t] } : Gate)]).foldl step w0).getD
        (n + C.gates.length) false = (W'.getD C.output false || W'.getD t false) := by
    rw [hset, List.foldl_append, ← hW']
    simp only [List.foldl_cons, List.foldl_nil]
    rw [← hlenW']
    unfold step
    rw [getD_append_singleton_last]
    simp [GateOp.eval]
  rw [hLHS, hW't]
  cases hval : wA.getD t false with
  | true =>
    rw [← hWt] at hval
    rw [himpx hval]
    simp
  | false =>
    have hstep : step wA ({ op := GateOp.or, inputs := [u] } : Gate) =
        step wA { op := GateOp.or, inputs := [u, t] } := by
      unfold step
      rw [List.getD_eq_getElem?_getD] at hval
      simp [GateOp.eval, hval]
    rw [hW'eq, hstep, ← hW]
    simp


namespace LiftFix

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3566.Normalization.Lift
open PEqualNP.MetaComplexity.NestedCover


def PA (D : Circuit) (T : Finset ℕ) : Prop :=
  ∀ j ∈ T, ∃ g : Gate, D.gates[j]? = some g ∧ g.op = GateOp.or


def PB (n : ℕ) (D : Circuit) (T : Finset ℕ) : Prop :=
  ∀ j ∈ T, D.output = n + j ∨ ∃ k ∈ T, ∃ g : Gate, D.gates[k]? = some g ∧ n + j ∈ g.inputs


def PC (n : ℕ) (D : Circuit) (T : Finset ℕ) : Prop :=
  ∀ (k : ℕ) (g : Gate), D.gates[k]? = some g → g.op = GateOp.or → ∀ t ∈ g.inputs,
    (∃ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true) →
    (∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true → circuitFun n D x = true) →
    k ∈ T

lemma pick_u (g : Gate) (hor : g.op = GateOp.or) (hl : g.inputs.length ≤ 2) (t : ℕ)
    (ht : t ∈ g.inputs) : ∃ u ∈ g.inputs, ∀ w : List Bool,
      GateOp.or.eval ([u, t].map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨op, ins⟩ := g
  simp only at hor hl ht ⊢
  subst hor
  match ins, hl, ht with
  | [], _, ht => simp at ht
  | [a], _, ht =>
    simp at ht; subst ht
    exact ⟨t, by simp, fun w => by simp [GateOp.eval]⟩
  | [a, b], _, ht =>
    simp at ht
    rcases ht with rfl | rfl
    · exact ⟨b, by simp, fun w => by simp [GateOp.eval, Bool.or_comm]⟩
    · exact ⟨a, by simp, fun w => by simp [GateOp.eval]⟩
  | _ :: _ :: _ :: _, hl, _ => simp at hl

lemma sg_injOn (k : ℕ) (S : Finset ℕ) (hS : k ∉ S) : Set.InjOn (sg k) (S : Set ℕ) := by
  intro a ha b hb hab
  have ha' : a ≠ k := fun h => hS (h ▸ ha)
  have hb' : b ≠ k := fun h => hS (h ▸ hb)
  unfold sg at hab
  split_ifs at hab <;> omega


end LiftFix

namespace LiftFix

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3566.Normalization.Lift
open PEqualNP.MetaComplexity.NestedCover

lemma lift_step_AO (n : ℕ) (D : Circuit) (T : Finset ℕ) (hM : Monotone2 D) (hR : ReadsBack n D)
    (hL2 : ∀ g ∈ D.gates, g.inputs.length = 2)
    (hA : PA D T) (hB : PB n D T) (k : ℕ) (g : Gate) (hkg : D.gates[k]? = some g)
    (hor : g.op = GateOp.or) (t : ℕ) (ht : t ∈ g.inputs)
    (hsat : ∃ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true)
    (himp : ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true →
      circuitFun n D x = true)
    (hkT : k ∉ T) :
    ∃ D1 : Circuit, ∃ T1 : Finset ℕ, Monotone2 D1 ∧ ReadsBack n D1 ∧
      (∀ g ∈ D1.gates, g.inputs.length = 2) ∧
      D1.gates.length = D.gates.length ∧ circuitFun n D1 = circuitFun n D ∧
      PA D1 T1 ∧ PB n D1 T1 ∧ T1.card = T.card + 1 := by
  have hk : k < D.gates.length := (List.getElem?_eq_some_iff.mp hkg).1
  have hrk := readsBack_get n D hR k g hkg
  have htk : t < n + k := hrk t ht
  have hgl : g.inputs.length ≤ 2 := (hM g (List.mem_of_getElem? hkg)).2
  obtain ⟨u, hu, hequ⟩ := pick_u g hor hgl t ht
  have huk : u < n + k := hrk u hu
  obtain ⟨x0, hx0⟩ := hsat
  have hout : D.output < n + D.gates.length := by
    by_contra hcon
    have h1 := himp x0 hx0
    unfold circuitFun Circuit.eval at h1
    rw [getD_oob] at h1
    · exact absurd h1 (by simp)
    · rw [wires_eq, foldl_step_length]; simp; omega
  have hTlt : ∀ j ∈ T, j < D.gates.length := fun j hj => by
    obtain ⟨g', hg', _⟩ := hA j hj
    exact (List.getElem?_eq_some_iff.mp hg').1

  have hE0w : ∀ w, (D.gates.set k ⟨GateOp.or, [u, t]⟩).foldl step w = D.gates.foldl step w :=
    fun w => foldl_set_equiv D.gates k g _ hkg hequ w
  have hE0f : circuitFun n ⟨D.gates.set k ⟨GateOp.or, [u, t]⟩, D.output⟩ = circuitFun n D := by
    funext x
    simp only [circuitFun, Circuit.eval, wires_eq, hE0w]
  have hE0M : Monotone2 ⟨D.gates.set k ⟨GateOp.or, [u, t]⟩, D.output⟩ := by
    intro g' hg'
    rcases List.mem_or_eq_of_mem_set hg' with h | h
    · exact hM g' h
    · subst h; simp
  have hE0k : (D.gates.set k ⟨GateOp.or, [u, t]⟩)[k]? = some ⟨GateOp.or, [u, t]⟩ := by
    simp [List.getElem?_set, hk]
  have hL := L2604 n ⟨D.gates.set k ⟨GateOp.or, [u, t]⟩, D.output⟩ k u t hE0M
    (by simpa using hk) hE0k htk (by
      intro x hx
      rw [hE0f]
      apply himp
      simpa [wires_eq, hE0w] using hx)
  simp only [List.set_set, List.length_set] at hL
  rw [hE0f] at hL

  set E : Circuit := ⟨D.gates.set k ⟨GateOp.or, [u]⟩ ++ [⟨GateOp.or, [D.output, t]⟩], n + D.gates.length⟩
    with hE
  have hElen : E.gates.length = D.gates.length + 1 := by simp [hE]
  have hEget : ∀ j, j ≠ k → j < D.gates.length → E.gates[j]? = D.gates[j]? := by
    intro j hjk hj
    simp only [hE]
    rw [List.getElem?_append_left (by simpa using hj), List.getElem?_set_ne (Ne.symm hjk)]
  have hEk : E.gates[k]? = some ⟨GateOp.or, [u]⟩ := by
    simp only [hE]
    rw [List.getElem?_append_left (by simpa using hk)]
    simp [List.getElem?_set, hk]
  have hEN : E.gates[D.gates.length]? = some ⟨GateOp.or, [D.output, t]⟩ := by
    simp only [hE]
    rw [List.getElem?_append_right (by simp)]
    simp
  have hEM : Monotone2 E := by
    intro g' hg'
    simp only [hE, List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · rcases List.mem_or_eq_of_mem_set hg' with h | h
      · exact hM g' h
      · subst h; simp
    · simp
  have hER : ReadsBack n E := by
    apply readsBack_of_get
    intro j g' hg' i hi
    rcases Nat.lt_trichotomy j D.gates.length with hj | hj | hj
    · by_cases hjk : j = k
      · subst hjk
        rw [hEk] at hg'
        cases hg'
        simp at hi
        omega
      · rw [hEget j hjk hj] at hg'
        exact readsBack_get n D hR j g' hg' i hi
    · subst hj
      rw [hEN] at hg'
      cases hg'
      simp at hi
      omega
    · have : E.gates[j]? = none := List.getElem?_eq_none (by omega)
      rw [this] at hg'
      cases hg'
  have hcopy : ∀ x : Fin n → Bool,
      (E.wires (List.ofFn x)).getD (n + k) false = (E.wires (List.ofFn x)).getD u false := by
    intro x
    have := wires_copy E k u hEk (List.ofFn x) (by simp; omega)
    simpa using this
  have hEf : circuitFun n E = circuitFun n D := by
    rw [← hL]

  refine ⟨del n k u E, (insert D.gates.length T).image (sg k), del_mono n k u E hEM,
    del_readsBack n k u E hER huk, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g' hg'
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hg'
    obtain ⟨g0, hg0, rfl⟩ := del_get_inv n k u E j g' hj
    have hne : (if j < k then j else j + 1) ≠ k := by split_ifs <;> omega
    simp only [rd, List.length_map]
    set j' := (if j < k then j else j + 1) with hj'
    rcases Nat.lt_trichotomy j' D.gates.length with h1 | h1 | h1
    · rw [hEget j' hne h1] at hg0
      exact hL2 g0 (List.mem_of_getElem? hg0)
    · rw [h1, hEN] at hg0
      cases hg0
      rfl
    · rw [List.getElem?_eq_none (by omega)] at hg0
      cases hg0
  · have := del_length n k u E (by omega)
    omega
  · rw [del_fun n k u E (by omega) huk (readsBack_take n E hER k) hcopy, hEf]
  · intro j' hj'
    simp only [Finset.mem_image, Finset.mem_insert] at hj'
    obtain ⟨j, hj, rfl⟩ := hj'
    rcases hj with rfl | hj
    · exact ⟨_, del_get n k u E _ _ (by omega) hEN, rfl⟩
    · obtain ⟨g', hg', hor'⟩ := hA j hj
      have hjk : j ≠ k := fun h => hkT (h ▸ hj)
      rw [← hEget j hjk (hTlt j hj)] at hg'
      exact ⟨_, del_get n k u E _ _ hjk hg', hor'⟩
  · intro j' hj'
    simp only [Finset.mem_image, Finset.mem_insert] at hj'
    obtain ⟨j, hj, rfl⟩ := hj'
    rcases hj with rfl | hj
    · left
      simp only [del, hE]
      exact sig_gate n k u _ (by omega)
    · right
      have hjk : j ≠ k := fun h => hkT (h ▸ hj)
      have hread : ∃ k'' ∈ insert D.gates.length T, k'' ≠ k ∧ ∃ g' : Gate, E.gates[k'']? = some g' ∧
          n + j ∈ g'.inputs := by
        rcases hB j hj with h | ⟨k', hk', g', hg', hin⟩
        · exact ⟨D.gates.length, Finset.mem_insert_self _ _, by omega, _, hEN, by simp [h]⟩
        · have hk'k : k' ≠ k := fun h => hkT (h ▸ hk')
          rw [← hEget k' hk'k (hTlt k' hk')] at hg'
          exact ⟨k', Finset.mem_insert_of_mem hk', hk'k, g', hg', hin⟩
      obtain ⟨k'', hk'', hk''k, g', hg', hin⟩ := hread
      refine ⟨sg k k'', Finset.mem_image_of_mem _ hk'', _, del_get n k u E _ _ hk''k hg', ?_⟩
      simp only [rd, List.mem_map]
      exact ⟨n + j, hin, sig_gate n k u j hjk⟩
  · have hNT : D.gates.length ∉ T := fun h => by have := hTlt D.gates.length h; omega
    rw [Finset.card_image_of_injOn (sg_injOn k _ (by
      simp only [Finset.mem_insert, not_or]
      exact ⟨by omega, hkT⟩)), Finset.card_insert_of_notMem hNT]

lemma mono_of_AO2 (n : ℕ) (D : Circuit) (h : PEqualNP.TopForm.IsAO2 n D) : Monotone2 D := by
  intro g hg
  refine ⟨?_, by rw [h.2.2 g hg]⟩
  rcases h.1 g hg with h1 | h1 <;> simp [h1]

lemma AO2_of (n : ℕ) (D : Circuit) (hM : Monotone2 D) (hR : ReadsBack n D)
    (hL : ∀ g ∈ D.gates, g.inputs.length = 2) : PEqualNP.TopForm.IsAO2 n D := by
  refine ⟨fun g hg => ?_, hR, hL⟩
  have := (hM g hg).1
  simpa using this

lemma main_AO (n : ℕ) : ∀ m (D : Circuit) (T : Finset ℕ), 2 * D.gates.length - T.card = m →
    PEqualNP.TopForm.IsAO2 n D → PA D T → PB n D T →
    ∃ D' : Circuit, PEqualNP.TopForm.IsAO2 n D' ∧ D'.gates.length = D.gates.length ∧
      circuitFun n D' = circuitFun n D ∧ ∃ T' : Finset ℕ, PA D' T' ∧ PB n D' T' ∧ PC n D' T' := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro D T hm hAO hA hB
  by_cases hC : PC n D T
  · exact ⟨D, hAO, rfl, rfl, T, hA, hB, hC⟩
  · unfold PC at hC
    push Not at hC
    obtain ⟨k, g, hkg, hor, t, ht, hsat, himp, hkT⟩ := hC
    obtain ⟨D1, T1, hM1, hR1, hL1, hl1, hf1, hA1, hB1, hc1⟩ :=
      lift_step_AO n D T (mono_of_AO2 n D hAO) hAO.2.1 hAO.2.2 hA hB k g hkg hor t ht hsat
        himp hkT
    have hk : k < D.gates.length := (List.getElem?_eq_some_iff.mp hkg).1
    have hTc : T.card ≤ D.gates.length := by
      have hsub : T ⊆ Finset.range D.gates.length := fun j hj => by
        obtain ⟨g', hg', _⟩ := hA j hj
        simpa using (List.getElem?_eq_some_iff.mp hg').1
      simpa using Finset.card_le_card hsub
    obtain ⟨D', hAO', hs', hf', T', hT'⟩ :=
      ih (2 * D1.gates.length - T1.card) (by omega) D1 T1 rfl (AO2_of n D1 hM1 hR1 hL1) hA1 hB1
    exact ⟨D', hAO', hs'.trans hl1, hf'.trans hf1, T', hT'⟩

end LiftFix

namespace LiftFix

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3566.Normalization.Lift
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm


def SwapHyp : Prop := ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (g b w w' : ℕ),
  (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ g < C.gates.length ∧ b < 2 ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD b 0 = w ∧ w' < n + g ∧
  (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w⟩ (List.ofFn x) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true) ∧
  (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true →
    PEqualNP.MetaComplexity.circuitFun n C x = true)) →
  PEqualNP.TopForm.IsAO2 n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧
  PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) = PEqualNP.MetaComplexity.circuitFun n C ∧
  (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size

lemma wires_set_lt (gs : List Gate) (g : ℕ) (X : Gate) :
    ∀ (x : List Bool) (i : ℕ), i < x.length + g →
      ((gs.set g X).foldl step x).getD i false = (gs.foldl step x).getD i false := by
  induction gs generalizing g with
  | nil => intro x i _; simp
  | cons a gs ih =>
    intro x i hi
    cases g with
    | zero =>
      simp only [List.set_cons_zero, List.foldl_cons]
      rw [foldl_step_getD _ _ _ (by simp [step]; omega),
        foldl_step_getD _ _ _ (by simp [step]; omega)]
      unfold step
      rw [getD_append_left _ _ _ (by omega), getD_append_left _ _ _ (by omega)]
    | succ g =>
      simp only [List.set_cons_succ, List.foldl_cons]
      exact ih g _ _ (by simp [step]; omega)

lemma eval_set_lt (n : ℕ) (gs : List Gate) (g : ℕ) (X : Gate) (i : ℕ) (hi : i < n + g)
    (x : Fin n → Bool) :
    Circuit.eval ⟨gs.set g X, i⟩ (List.ofFn x) = Circuit.eval ⟨gs, i⟩ (List.ofFn x) := by
  simp only [Circuit.eval, wires_eq]
  exact wires_set_lt gs g X _ i (by simpa using hi)

lemma gateAt_set (C : Circuit) (o h : ℕ) (X : Gate) (hh : h < C.gates.length) (j : ℕ) :
    gateAt ⟨C.gates.set h X, o⟩ j = if j = h then X else gateAt C j := by
  unfold gateAt
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hj : j = h
  · subst hj; simp [hh]
  · simp [Ne.symm hj, hj]

lemma isAO2_set (n : ℕ) (C : Circuit) (o h : ℕ) (X : Gate) (hC : IsAO2 n C)
    (hh : h < C.gates.length) (hop : X.op = GateOp.and ∨ X.op = GateOp.or)
    (hl : X.inputs.length = 2) (hr : ∀ i ∈ X.inputs, i < n + h) :
    IsAO2 n ⟨C.gates.set h X, o⟩ := by
  refine ⟨fun g hg => ?_, fun j hj => ?_, fun g hg => ?_⟩
  · rcases List.mem_or_eq_of_mem_set hg with h1 | h1
    · exact hC.1 g h1
    · subst h1; exact hop
  · rw [gateAt_set C o h X hh j]
    simp only [List.length_set] at hj
    split_ifs with h1
    · subst h1; exact hr
    · exact hC.2.1 j hj
  · rcases List.mem_or_eq_of_mem_set hg with h1 | h1
    · exact hC.2.2 g h1
    · subst h1; exact hl


def mu (w : ℕ) (C : Circuit) : ℕ := ∑ j ∈ Finset.range C.gates.length, (gateAt C j).inputs.count w

lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates :=
  List.mem_of_getElem? (gateAt_some C j hj)

lemma swap_all (n : ℕ) (hswap : SwapHyp) (h t : ℕ) (ht : t < n + h) :
    ∀ N (C : Circuit), mu (n + h) C = N → IsAO2 n C →
      (∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, n + h⟩ (List.ofFn x) = true →
        Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true) →
      (∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true →
        circuitFun n C x = true) →
      ∃ C' : Circuit, IsAO2 n C' ∧ circuitFun n C' = circuitFun n C ∧
        C'.gates.length = C.gates.length ∧ C'.output = C.output ∧
        ∀ j < C'.gates.length, n + h ∉ (gateAt C' j).inputs := by
  intro N
  induction N with
  | zero =>
    intro C hmu hC _ _
    refine ⟨C, hC, rfl, rfl, rfl, fun j hj hmem => ?_⟩
    have h0 := (Finset.sum_eq_zero_iff.mp hmu) j (by simpa using hj)
    exact (List.count_eq_zero.mp h0) hmem
  | succ N ih =>
    intro C hmu hC hw ht'
    have hex : ∃ j ∈ Finset.range C.gates.length, (gateAt C j).inputs.count (n + h) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have := Finset.sum_eq_zero hcon
      unfold mu at hmu
      omega
    obtain ⟨j, hjr, hjc⟩ := hex
    have hj : j < C.gates.length := by simpa using hjr
    have hmem : n + h ∈ (gateAt C j).inputs := List.count_pos_iff.mp (Nat.pos_of_ne_zero hjc)
    have hhj : n + h < n + j := hC.2.1 j hj _ hmem
    have hl2 := hC.2.2 _ (gateAt_mem C j hj)
    obtain ⟨b, hb, hget⟩ : ∃ b, b < 2 ∧ (gateAt C j).inputs.getD b 0 = n + h := by
      match hins : (gateAt C j).inputs, hl2, hmem with
      | [a, c], _, hm =>
        simp at hm
        rcases hm with hm | hm
        · exact ⟨0, by omega, by simp [hm]⟩
        · exact ⟨1, by omega, by simp [hm]⟩
    obtain ⟨hC1, hf1, _⟩ := hswap n C j b (n + h) t
      ⟨hC, hC.2.1, hj, hb, hget, by omega, hw, ht'⟩
    set X : Gate := ⟨(gateAt C j).op, (gateAt C j).inputs.set b t⟩ with hX
    set C1 : Circuit := ⟨C.gates.set j X, C.output⟩ with hC1def
    have hlen : C1.gates.length = C.gates.length := by simp [hC1def]
    have hcount : X.inputs.count (n + h) + 1 = (gateAt C j).inputs.count (n + h) := by
      simp only [hX]
      match hins : (gateAt C j).inputs, hl2, hget with
      | [a, c], _, hg =>
        have htne : t ≠ n + h := by omega
        interval_cases b
        · simp at hg; subst hg; simp [List.count_cons, htne]
        · simp at hg; subst hg; simp [List.count_cons, htne]; omega
    have hmu1 : mu (n + h) C1 = N := by
      unfold mu at hmu ⊢
      rw [hlen] at *
      rw [← Finset.add_sum_erase _ _ hjr] at hmu ⊢
      have hrest : ∑ x ∈ (Finset.range C.gates.length).erase j, (gateAt C1 x).inputs.count (n + h) =
          ∑ x ∈ (Finset.range C.gates.length).erase j, (gateAt C x).inputs.count (n + h) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hC1def, gateAt_set C _ j X hj x, if_neg (Finset.ne_of_mem_erase hx)]
      rw [hrest]
      have : gateAt C1 j = X := by rw [hC1def, gateAt_set C _ j X hj j, if_pos rfl]
      rw [this]
      omega
    obtain ⟨C', h1, h2, h3, h4, h5⟩ := ih C1 hmu1 hC1
      (fun x hx => by
        rw [eval_set_lt n C.gates j X t (by omega)]
        rw [eval_set_lt n C.gates j X (n + h) hhj] at hx
        exact hw x hx)
      (fun x hx => by
        rw [eval_set_lt n C.gates j X t (by omega)] at hx
        rw [hf1]
        exact ht' x hx)
    exact ⟨C', h1, h2.trans hf1, h3.trans hlen, h4, h5⟩

lemma fold_agree (m : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, m ∉ g.inputs) :
    ∀ a b : List Bool, a.length = b.length → (∀ i, i ≠ m → a.getD i false = b.getD i false) →
      (gs.foldl step a).length = (gs.foldl step b).length ∧
      ∀ i, i ≠ m → (gs.foldl step a).getD i false = (gs.foldl step b).getD i false := by
  induction gs with
  | nil => intro a b hl hab; exact ⟨hl, hab⟩
  | cons g gs ih =>
    intro a b hl hab
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · have hv : g.op.eval (g.inputs.map fun i => a.getD i false) =
          g.op.eval (g.inputs.map fun i => b.getD i false) := by
        congr 1
        apply List.map_congr_left
        intro i hi
        exact hab i (fun e => hgs g (by simp) (e ▸ hi))
      intro i hi
      unfold step
      by_cases hia : i = a.length
      · subst hia
        rw [getD_append_singleton_last, hl, getD_append_singleton_last]
        exact hv
      · rw [getD_append_singleton _ _ _ hia, getD_append_singleton _ _ _ (by rw [← hl]; exact hia)]
        exact hab i hi

lemma set_unread_fun (n : ℕ) (C : Circuit) (h : ℕ) (X : Gate) (hh : h < C.gates.length)
    (hun : ∀ j < C.gates.length, n + h ∉ (gateAt C j).inputs) (ho : C.output ≠ n + h) :
    circuitFun n ⟨C.gates.set h X, C.output⟩ = circuitFun n C := by
  funext x
  unfold circuitFun Circuit.eval
  simp only [wires_eq]
  have hw0l : (List.ofFn x).length = n := by simp
  have hgk : C.gates[h]? = some C.gates[h] := List.getElem?_eq_getElem hh
  have hsk : (C.gates.set h X)[h]? = some X := by simp [List.getElem?_set, hh]
  rw [foldl_split C.gates h _ hgk, foldl_split (C.gates.set h X) h X hsk,
    List.take_set_of_le (le_refl h), List.drop_set_of_lt (Nat.lt_succ_self h)]
  have hl := take_fold_length C.gates h hh (List.ofFn x)
  set Wp := (C.gates.take h).foldl step (List.ofFn x)
  have hall : ∀ g ∈ C.gates.drop (h + 1), n + h ∉ g.inputs := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (List.mem_of_mem_drop hg)
    have := hun j hj
    rwa [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this
  have := fold_agree (n + h) _ hall (step Wp X) (step Wp C.gates[h]) (by simp [step]) (by
    intro i hi
    unfold step
    rw [getD_append_singleton _ _ _ (by omega), getD_append_singleton _ _ _ (by omega)])
  exact this.2 _ ho

lemma wires_gate (F : Circuit) (k : ℕ) (g : Gate) (hk : F.gates[k]? = some g) (w0 : List Bool)
    (hr : ∀ i ∈ g.inputs, i < w0.length + k) :
    (F.wires w0).getD (w0.length + k) false =
      g.op.eval (g.inputs.map fun i => (F.wires w0).getD i false) := by
  have hk' : k < F.gates.length := (List.getElem?_eq_some_iff.mp hk).1
  rw [wires_eq, foldl_split F.gates k _ hk w0]
  have hl := take_fold_length F.gates k hk' w0
  set Wp := (F.gates.take k).foldl step w0
  rw [foldl_step_getD _ _ _ (by simp [step]; omega)]
  have hm : g.inputs.map (fun i => ((F.gates.drop (k + 1)).foldl step (step Wp g)).getD i false) =
      g.inputs.map fun i => Wp.getD i false := by
    apply List.map_congr_left
    intro i hi
    have := hr i hi
    rw [foldl_step_getD _ _ _ (by simp [step]; omega)]
    unfold step
    rw [getD_append_left _ _ _ (by omega)]
  rw [hm]
  unfold step
  rw [← hl, getD_append_singleton_last]

lemma del_AO (n k u : ℕ) (E : Circuit) (hE : IsAO2 n E) (hu : u < n + k) :
    IsAO2 n (del n k u E) := by
  refine ⟨fun g hg => ?_, del_readsBack n k u E hE.2.1 hu, fun g hg => ?_⟩
  · simp only [del, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    simpa [rd] using hE.1 g0 (List.mem_of_mem_eraseIdx hg0)
  · simp only [del, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    simpa [rd] using hE.2.2 g0 (List.mem_of_mem_eraseIdx hg0)

lemma gateAt_eq (D : Circuit) (j : ℕ) (g : Gate) (hg : D.gates[j]? = some g) : gateAt D j = g := by
  have hj := (List.getElem?_eq_some_iff.mp hg).1
  rw [gateAt_some D j hj] at hg
  exact Option.some.inj hg

lemma least_noAndBelow (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hswap : SwapHyp) (D : Circuit) (hD : IsLeastAO G D) :
    ∀ k < D.gates.length, (gateAt D k).op = GateOp.and → ∀ t ∈ (gateAt D k).inputs,
      ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) = true →
        graphFun G ∅ x = true) := by
  intro h hh hand t ht hbelow
  obtain ⟨hAO, hF, hmin⟩ := hD
  have htl : t < n + h := hAO.2.1 h hh t ht
  have hw : ∀ x : Fin n → Bool, Circuit.eval ⟨D.gates, n + h⟩ (List.ofFn x) = true →
      Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) = true := by
    intro x hx
    have hg := wires_gate D h (gateAt D h) (gateAt_some D h hh) (List.ofFn x)
      (by simpa using hAO.2.1 h hh)
    simp only [List.length_ofFn] at hg
    change (D.wires (List.ofFn x)).getD (n + h) false = true at hx
    change (D.wires (List.ofFn x)).getD t false = true
    rw [hg, hand] at hx
    simp only [GateOp.eval] at hx
    have := List.all_eq_true.mp hx _ (List.mem_map_of_mem ht)
    simpa using this
  set o' := if D.output = n + h then t else D.output with ho'
  set C1 : Circuit := ⟨D.gates, o'⟩ with hC1
  have hC1AO : IsAO2 n C1 := hAO
  have hC1f : circuitFun n C1 = circuitFun n D := by
    funext x
    by_cases ho : D.output = n + h
    · have e1 : circuitFun n C1 x = Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) := by
        simp only [circuitFun, hC1, ho', if_pos ho]
      have e2 : circuitFun n D x = Circuit.eval ⟨D.gates, n + h⟩ (List.ofFn x) := by
        simp only [circuitFun, Circuit.eval, ← ho]
      rw [e1, e2]
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hx
        have := hbelow x hx
        rw [← hF, e2] at this
        exact this
      · exact hw x
    · simp only [circuitFun, hC1, ho', if_neg ho]
  have hlen1 : C1.gates.length = D.gates.length := rfl
  obtain ⟨C2, hC2AO, hC2f, hC2l, hC2o, hC2un⟩ := swap_all n hswap h t htl _ C1 rfl hC1AO
    (fun x hx => hw x hx)
    (fun x hx => by rw [hC1f, hF]; exact hbelow x hx)
  have hh2 : h < C2.gates.length := by omega
  have ho2 : C2.output ≠ n + h := by
    rw [hC2o]
    show o' ≠ n + h
    by_cases ho : D.output = n + h
    · rw [ho', if_pos ho]; omega
    · rw [ho', if_neg ho]; exact ho
  set X : Gate := ⟨GateOp.and, [t, t]⟩ with hX
  set E : Circuit := ⟨C2.gates.set h X, C2.output⟩ with hE
  have hEAO : IsAO2 n E := isAO2_set n C2 _ h X hC2AO hh2 (Or.inl rfl) rfl
    (by intro i hi; simp [hX] at hi; omega)
  have hEf : circuitFun n E = circuitFun n C2 := set_unread_fun n C2 h X hh2 hC2un ho2
  have hEh : E.gates[h]? = some X := by simp [hE, List.getElem?_set, hh2]
  have hEl : E.gates.length = C2.gates.length := by simp [hE]
  have hcopy : ∀ x : Fin n → Bool,
      (E.wires (List.ofFn x)).getD (n + h) false = (E.wires (List.ofFn x)).getD t false := by
    intro x
    have := wires_gate E h X hEh (List.ofFn x) (by intro i hi; simp [hX] at hi; simp; omega)
    simp only [List.length_ofFn] at this
    rw [this]
    simp [hX, GateOp.eval]
  have hDf := del_fun n h t E (by omega) htl (readsBack_take n E hEAO.2.1 h) hcopy
  have hDl := del_length n h t E (by omega)
  have := hmin (del n h t E) (del_AO n h t E hEAO htl) (by rw [hDf, hEf, hC2f, hC1f, hF])
  simp only [Circuit.size] at this
  omega


end LiftFix

namespace Swap
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

lemma wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

lemma getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

lemma ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


lemma mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

lemma wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

lemma wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

lemma wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma snoc_mono (W : List Bool) (v v' : Bool) (h : v = true → v' = true) (i : ℕ) :
    (W ++ [v]).getD i false = true → (W ++ [v']).getD i false = true := by
  rcases Nat.lt_trichotomy i W.length with hi | hi | hi
  · rw [getD_snoc_lt _ _ _ hi, getD_snoc_lt _ _ _ hi]; exact id
  · subst hi; rw [getD_snoc_eq, getD_snoc_eq]; exact h
  · rw [getD_snoc_gt _ _ _ hi]; intro hf; exact absurd hf (by simp)

lemma opmono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (a b a' b' : Bool)
    (ha : a = true → a' = true) (hb : b = true → b' = true) :
    op.eval [a, b] = true → op.eval [a', b'] = true := by
  rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval] <;> tauto

lemma core (n g : ℕ) (gates : List Gate) (hg : g < gates.length) (o w' : ℕ) (ins' : List ℕ)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hw' : w' < n + g) (x : Fin n → Bool)
    (hF : (wf gates (List.ofFn x)).getD w' false = true → (wf gates (List.ofFn x)).getD o false = true)
    (hsame : (wf (gates.take g) (List.ofFn x)).getD w' false = false →
      gates[g].op.eval (ins'.map fun i => (wf (gates.take g) (List.ofFn x)).getD i false)
        = gates[g].op.eval (gates[g].inputs.map fun i => (wf (gates.take g) (List.ofFn x)).getD i false))
    (hup : gates[g].op.eval (gates[g].inputs.map fun i => (wf (gates.take g) (List.ofFn x)).getD i false) = true →
      gates[g].op.eval (ins'.map fun i => (wf (gates.take g) (List.ofFn x)).getD i false) = true) :
    (wf (gates.set g ⟨gates[g].op, ins'⟩) (List.ofFn x)).getD o false
      = (wf gates (List.ofFn x)).getD o false := by
  have h2 : ∀ a : Gate, gates.set g a = gates.take g ++ a :: gates.drop (g + 1) := by
    intro a
    rw [List.set_eq_take_append_cons_drop]
    simp [hg]
  have h1 : gates = gates.take g ++ gates[g] :: gates.drop (g + 1) := by
    rw [← h2]
    exact (List.set_getElem_self _).symm
  generalize hW : wf (gates.take g) (List.ofFn x) = W at *
  have hWlen : W.length = n + g := by
    rw [← hW, wf_len, List.length_ofFn, List.length_take, Nat.min_eq_left (le_of_lt hg)]
  have e1 : wf gates (List.ofFn x) = wf (gates.drop (g + 1))
      (W ++ [gates[g].op.eval (gates[g].inputs.map fun i => W.getD i false)]) := by
    conv_lhs => rw [h1]
    rw [wf_append, wf_cons, hW]
  have e2 : wf (gates.set g ⟨gates[g].op, ins'⟩) (List.ofFn x) = wf (gates.drop (g + 1))
      (W ++ [gates[g].op.eval (ins'.map fun i => W.getD i false)]) := by
    rw [h2, wf_append, wf_cons, hW]
  rw [e2, e1]
  rw [e1] at hF
  cases hc : W.getD w' false
  · rw [hsame hc]
  · have hk : (wf (gates.drop (g + 1)) (W ++ [gates[g].op.eval (gates[g].inputs.map fun i => W.getD i false)])).getD w' false = true := by
      rw [wf_keep _ _ _ (by simp; omega), getD_snoc_lt _ _ _ (by omega)]
      exact hc
    have ht := hF hk
    rw [ht]
    exact mono2 (gates.drop (g + 1)) (fun g' hg' => hleg g' (List.mem_of_mem_drop hg')) _ _ (by simp)
      (snoc_mono W _ _ hup) o ht

end Swap

open PEqualNP.Outside.L_meta_3566.Normalization.Swap PEqualNP.CircuitLowerBounds in
lemma swap_move : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (g b w w' : ℕ),
  (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ g < C.gates.length ∧ b < 2 ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD b 0 = w ∧ w' < n + g ∧
  (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w⟩ (List.ofFn x) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true) ∧
  (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true →
    PEqualNP.MetaComplexity.circuitFun n C x = true)) →
  PEqualNP.TopForm.IsAO2 n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧
  PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) = PEqualNP.MetaComplexity.circuitFun n C ∧
  (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size := by
  intro n C g b w w' ⟨⟨hao, _, h2⟩, hrb, hg, hb, hw, hw', h1, hF⟩
  have hG : PEqualNP.MetaComplexity.NestedCover.gateAt C g = C.gates[g] := by
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ hg]
  rw [hG] at hw ⊢
  have hmem : C.gates[g] ∈ C.gates := List.getElem_mem hg
  obtain ⟨i0, i1, hin⟩ := List.length_eq_two.mp (h2 _ hmem)
  have hop := hao _ hmem
  have hleg : ∀ g' ∈ C.gates, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
    fun g' hg' => ⟨hao g' hg', le_of_eq (h2 g' hg')⟩
  have hlt : ∀ i ∈ C.gates[g].inputs, i < n + g := by
    intro i hi
    have := hrb g hg i
    rw [hG] at this
    exact this hi
  have hwlt : w < n + g := by
    apply hlt
    rw [← hw, hin]
    interval_cases b <;> simp
  have hins : C.gates[g].inputs.set b w' = if b = 0 then [w', i1] else [i0, w'] := by
    rw [hin]
    interval_cases b <;> rfl
  have hwv : w = if b = 0 then i0 else i1 := by
    rw [← hw, hin]
    interval_cases b <;> rfl
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_or_eq_of_mem_set hg' with h | h
    · exact hao g' h
    · rw [h]; exact hop
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa using hj
    by_cases hjg : j = g
    · subst hjg
      have : PEqualNP.MetaComplexity.NestedCover.gateAt (⟨C.gates.set j ⟨C.gates[j].op, C.gates[j].inputs.set b w'⟩, C.output⟩ : Circuit) j = ⟨C.gates[j].op, C.gates[j].inputs.set b w'⟩ := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        simp [List.getD_eq_getElem?_getD, hg]
      rw [this] at hi
      rcases List.mem_or_eq_of_mem_set hi with h | h
      · exact hlt i h
      · rw [h]; exact hw'
    · have : PEqualNP.MetaComplexity.NestedCover.gateAt (⟨C.gates.set g ⟨C.gates[g].op, C.gates[g].inputs.set b w'⟩, C.output⟩ : Circuit) j = PEqualNP.MetaComplexity.NestedCover.gateAt C j := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hjg)]
      rw [this] at hi
      exact hrb j hj' i hi
  · intro g' hg'
    rcases List.mem_or_eq_of_mem_set hg' with h | h
    · exact h2 g' h
    · rw [h]; simp [hin]
  · funext x
    refine core n g C.gates hg C.output w' _ hleg hw' x (hF x) ?_ ?_
    · intro hc
      have hwf : (wf (C.gates.take g) (List.ofFn x)).getD w false = false := by
        by_contra hne
        have ht : (wf (C.gates.take g) (List.ofFn x)).getD w false = true := by simpa using hne
        have := h1 x (by
          show (wf C.gates (List.ofFn x)).getD w false = true
          rw [wire_take C.gates (List.ofFn x) g w (by simpa using hwlt) (le_of_lt hg)]
          exact ht)
        have e : (wf C.gates (List.ofFn x)).getD w' false = true := this
        rw [wire_take C.gates (List.ofFn x) g w' (by simpa using hw') (le_of_lt hg), hc] at e
        exact absurd e (by simp)
      rw [hins, hin]
      rw [hwv] at hwf
      by_cases hb0 : b = 0
      · simp only [hb0, ite_true] at hwf ⊢
        simp only [List.map_cons, List.map_nil]
        rw [hc, hwf]
      · simp only [hb0, ite_false] at hwf ⊢
        simp only [List.map_cons, List.map_nil]
        rw [hc, hwf]
    · rw [hins, hin]
      by_cases hb0 : b = 0
      · simp only [hb0, ite_true, List.map_cons, List.map_nil]
        intro hv
        refine opmono _ hop _ _ _ _ (fun ht => ?_) id hv
        have hwi : w = i0 := by rw [hwv]; simp [hb0]
        have := h1 x (by
          show (wf C.gates (List.ofFn x)).getD w false = true
          rw [wire_take C.gates (List.ofFn x) g w (by simpa using hwlt) (le_of_lt hg), hwi]
          exact ht)
        have e : (wf C.gates (List.ofFn x)).getD w' false = true := this
        rw [wire_take C.gates (List.ofFn x) g w' (by simpa using hw') (le_of_lt hg)] at e
        exact e
      · simp only [hb0, ite_false, List.map_cons, List.map_nil]
        intro hv
        refine opmono _ hop _ _ _ _ id (fun ht => ?_) hv
        have hwi : w = i1 := by rw [hwv]; simp [hb0]
        have := h1 x (by
          show (wf C.gates (List.ofFn x)).getD w false = true
          rw [wire_take C.gates (List.ofFn x) g w (by simpa using hwlt) (le_of_lt hg), hwi]
          exact ht)
        have e : (wf C.gates (List.ofFn x)).getD w' false = true := this
        rw [wire_take C.gates (List.ofFn x) g w' (by simpa using hw') (le_of_lt hg)] at e
        exact e
  · simp [Circuit.size]


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

lemma swap_hyp : LiftFix.SwapHyp := swap_move

lemma noAndBelow_unconditional (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (hD : IsLeastAO G D) :
    ∀ k < D.gates.length, (gateAt D k).op = GateOp.and → ∀ t ∈ (gateAt D k).inputs,
      ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) = true →
        graphFun G ∅ x = true) := by
  exact LiftFix.least_noAndBelow n G swap_hyp D hD

lemma same_minimum_normal_form (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) :
    ∃ D : Circuit, IsLeastAO G D ∧ D.size = C.size ∧
      circuitFun n D = circuitFun n C ∧ ∃ T : Finset ℕ,
      LiftFix.PA D T ∧ LiftFix.PB n D T ∧ LiftFix.PC n D T ∧
      (∀ k < D.gates.length, (gateAt D k).op = GateOp.and → ∀ t ∈ (gateAt D k).inputs,
        ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) = true →
          graphFun G ∅ x = true)) := by
  obtain ⟨D, hAO, hlen, hfun, T, hA, hB, hPC⟩ :=
    LiftFix.main_AO n (2 * C.gates.length) C ∅ (by simp) hC.1
      (by simp [LiftFix.PA]) (by simp [LiftFix.PB])
  have hD : IsLeastAO G D := by
    refine ⟨hAO, hfun.trans hC.2.1, ?_⟩
    intro E hE hEF
    have hmin := hC.2.2 E hE hEF
    simpa only [Circuit.size, hlen] using hmin
  exact ⟨D, hD, hlen, hfun, T, hA, hB, hPC, noAndBelow_unconditional n G D hD⟩

end Normalization

namespace Normalization
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

lemma peel_of_normalized_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hpos : ∃ z : Fin n, 0 < G.degree z)
    (h : ∀ (D : Circuit) (T : Finset ℕ), IsLeastAO G D →
      LiftFix.PA D T → LiftFix.PB n D T → LiftFix.PC n D T →
      (∀ k < D.gates.length, (gateAt D k).op = GateOp.and → ∀ t ∈ (gateAt D k).inputs,
        ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) = true →
          graphFun G ∅ x = true)) →
      ∃ z : Fin n, 0 < G.degree z ∧ CutWitness G z D) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun G ∅ → CutWitness G z C := by
  apply peel_of_least G hpos
  intro C hC
  obtain ⟨D, hD, hsize, _, T, hA, hB, hPC, hNo⟩ := same_minimum_normal_form n G C hC
  obtain ⟨z, hz, hcut⟩ := h D T hD hA hB hPC hNo
  exact ⟨z, hz, cutWitness_mono G z D C (Nat.le_of_eq hsize) hcut⟩

end Normalization

namespace NormalizerFixed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open Normalization

lemma marked_implies_output {n : ℕ} (C : Circuit) (T : Finset ℕ) (hAO : IsAO2 n C)
    (hA : LiftFix.PA C T) (hB : LiftFix.PB n C T) :
    ∀ j ∈ T, ∀ x : Fin n → Bool, wireVal n C (n + j) x = true → circuitFun n C x = true := by
  have hrec : ∀ m (j : ℕ), C.gates.length - j = m → j ∈ T →
      ∀ x : Fin n → Bool, wireVal n C (n + j) x = true → circuitFun n C x = true := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro j hm hj x hx
      obtain ⟨gj, hgj, _⟩ := hA j hj
      have hjlt : j < C.gates.length := (List.getElem?_eq_some_iff.mp hgj).1
      rcases hB j hj with hout | ⟨k, hk, g, hkg, hin⟩
      · unfold circuitFun Circuit.eval
        rw [hout]
        exact hx
      · have hklt : k < C.gates.length := (List.getElem?_eq_some_iff.mp hkg).1
        have hback := LiftFix.readsBack_get n C hAO.2.1 k g hkg (n + j) hin
        obtain ⟨gk, hgk, hork⟩ := hA k hk
        have hgkeq : gk = g := Option.some.inj (hgk.symm.trans hkg)
        have hor : g.op = GateOp.or := by simpa [hgkeq] using hork
        have hktrue : wireVal n C (n + k) x = true := by
          have he := LiftFix.wires_gate C k g hkg (List.ofFn x)
            (by simpa using LiftFix.readsBack_get n C hAO.2.1 k g hkg)
          simp only [List.length_ofFn] at he
          change (C.wires (List.ofFn x)).getD (n + k) false = true
          rw [he, hor]
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
          exact ⟨n + j, hin, hx⟩
        exact ih (C.gates.length - k) (by omega) k rfl hk x hktrue
  intro j hj x hx
  exact hrec (C.gates.length - j) j rfl hj x hx

lemma marked_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (T : Finset ℕ) (hAO : IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅) (hA : LiftFix.PA C T) (hB : LiftFix.PB n C T) :
    ∀ j ∈ T, BelowF G C j := by
  intro j hj x hx
  rw [← hfun]
  exact marked_implies_output C T hAO hA hB j hj x hx

lemma fixed_of_PABC {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (T : Finset ℕ) (hAO : IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅)
    (hA : LiftFix.PA C T) (hB : LiftFix.PB n C T) (hPC : LiftFix.PC n C T) :
    PEqualNP.Core.IsLiftFixedPoint G C := by
  unfold PEqualNP.Core.IsLiftFixedPoint PEqualNP.Core.LiftApplies
  rintro ⟨k, hk, b, hcone, hor, hnot, himp⟩
  have hget : C.gates[k]? = some (gateAt C k) := LiftFix.gateAt_some C k hk
  have htmem := WireCone.opnd_mem C hAO k hk b
  have hkT : k ∈ T := hPC k (gateAt C k) hget hor (opnd C k b) htmem himp.2
    (fun x hx => by rw [hfun]; exact himp.1 x hx)
  exact hnot (marked_below G C T hAO hfun hA hB k hkT)

lemma valid_wire_all_ones {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) :
    ∀ w < n + C.gates.length, wireVal n C w (fun _ => true) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hin : w < n
    · rw [ProofWire.input_value C w hin]
    · have hk : w - n < C.gates.length := by omega
      have h0 := ProofWire.operand_lt C hAO (w - n) hk 0
      have h1 := ProofWire.operand_lt C hAO (w - n) hk 1
      have hv0 := ih (opnd C (w - n) 0) (by omega) (by omega)
      have hv1 := ih (opnd C (w - n) 1) (by omega) (by omega)
      have he := ProofWire.gate_value C hAO (w - n) hk (fun _ => true)
      have hew : n + (w - n) = w := by omega
      rw [hew] at he
      rw [he]
      simp [hv0, hv1]

lemma raw_or_not_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (z : Fin n) (k t : ℕ) (hk : k < C.gates.length)
    (hAO : IsAO2 n C) (hor : (gateAt C k).op = GateOp.or)
    (hinputs : (gateAt C k).inputs = [z.val, t] ∨ (gateAt C k).inputs = [t, z.val]) :
    ¬ BelowF G C k := by
  classical
  intro hbelow
  have hinput : wireVal n C z.val (PEqualNP.EdgeOwnership.pairInput z z) = true := by
    rw [ProofWire.input_value C z.val z.isLt]
    simp [PEqualNP.EdgeOwnership.pairInput]
  have hgate : PEqualNP.EdgeOwnership.gateVal n C k (PEqualNP.EdgeOwnership.pairInput z z) = true := by
    change wireVal n C (n + k) _ = true
    rw [ProofWire.gate_value C hAO k hk]
    rcases hinputs with hinputs | hinputs <;> simp [hor, opnd, hinputs, hinput]
  have hf := hbelow _ hgate
  exact G.irrefl ((TwinLeaf.SingleRead.graph_pair G z z).mp hf)

lemma raw_or_other_dirty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (T : Finset ℕ) (z : Fin n) (k t : ℕ) (hk : k < C.gates.length)
    (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hA : LiftFix.PA C T) (hB : LiftFix.PB n C T) (hPC : LiftFix.PC n C T)
    (hor : (gateAt C k).op = GateOp.or)
    (hinputs : (gateAt C k).inputs = [z.val, t] ∨ (gateAt C k).inputs = [t, z.val]) :
    ¬ ∀ x : Fin n → Bool, wireVal n C t x = true → graphFun G ∅ x = true := by
  intro hbelow
  have htmem : t ∈ (gateAt C k).inputs := by rcases hinputs with h | h <;> simp [h]
  have hback := hAO.2.1 k hk t htmem
  have hsat : ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true :=
    ⟨fun _ => true, valid_wire_all_ones C hAO t (by omega)⟩
  have hget : C.gates[k]? = some (gateAt C k) := LiftFix.gateAt_some C k hk
  have hkT : k ∈ T := hPC k (gateAt C k) hget hor t htmem hsat
    (fun x hx => by rw [hfun]; exact hbelow x hx)
  exact raw_or_not_below G C z k t hk hAO hor hinputs
    (marked_below G C T hAO hfun hA hB k hkT)

lemma raw_or_other_dirty_of_shape {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (T : Finset ℕ) (z : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hor : g.op = GateOp.or)
    (hinputs : g.inputs = [z.val, t] ∨ g.inputs = [t, z.val])
    (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hA : LiftFix.PA C T) (hB : LiftFix.PB n C T) (hPC : LiftFix.PC n C T) :
    ¬ ∀ x : Fin n → Bool, wireVal n C t x = true → graphFun G ∅ x = true := by
  have hk : pre.length < C.gates.length := by simp [hshape]
  have hg : gateAt C pre.length = g := by
    simp [gateAt, hshape, List.getD_eq_getElem?_getD]
  exact raw_or_other_dirty G C T z pre.length t hk hAO hfun hA hB hPC
    (by simpa [hg] using hor) (by simpa [hg] using hinputs)

lemma same_minimum_fixed_normal_form (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) :
    ∃ D : Circuit, IsLeastAO G D ∧ D.size = C.size ∧
      circuitFun n D = circuitFun n C ∧ ∃ T : Finset ℕ,
      LiftFix.PA D T ∧ LiftFix.PB n D T ∧ LiftFix.PC n D T ∧
      PEqualNP.Core.IsLiftFixedPoint G D ∧
      (∀ k < D.gates.length, (gateAt D k).op = GateOp.and → ∀ t ∈ (gateAt D k).inputs,
        ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) = true →
          graphFun G ∅ x = true)) := by
  obtain ⟨D, hD, hs, hf, T, hA, hB, hPC, hno⟩ := same_minimum_normal_form n G C hC
  exact ⟨D, hD, hs, hf, T, hA, hB, hPC, fixed_of_PABC G D T hD.1 hD.2.1 hA hB hPC, hno⟩

end NormalizerFixed

namespace NormalizedCone
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover Normalization

lemma sole_or_dirty_cone_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (T : Finset ℕ) (u : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hAO : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G) (htu : t ≠ u.val)
    (hA : LiftFix.PA C T) (hB : LiftFix.PB n C T) (hPC : LiftFix.PC n C T) :
    G.degree u ≤ (LocalizedDirty.dirtyInside G C (WireCone.backwardCone n C {t})).card + 1 := by
  apply ConeDirty.sole_or_dirty_source_cone_bound G C u pre post g t hshape hop
    hinputs hAO hno hfun hfour htu
  exact NormalizerFixed.raw_or_other_dirty_of_shape G C T u pre post g t hshape hop
    hinputs hAO hfun hA hB hPC

end NormalizedCone


namespace StandardConeBridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def RG (n : ℕ) (gs : List Gate) (i j : ℕ) : Prop :=
  j < gs.length ∧ i < j ∧ n + i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs

lemma tg_last {α : Type} {R : α → α → Prop} {a b : α} (h : Relation.TransGen R a b) :
    ∃ c, R c b := by
  cases h with
  | single h => exact ⟨_, h⟩
  | tail _ h => exact ⟨_, h⟩

lemma cones_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, coneStep, List.length_append,
      List.length_cons, List.length_nil]; omega

lemma RG_snoc (n : ℕ) (gs : List Gate) (g : Gate) (a b : ℕ) (hb : b < gs.length) :
    RG n (gs ++ [g]) a b ↔ RG n gs a b := by
  unfold RG
  have : (gs ++ [g]).getD b ⟨GateOp.or, []⟩ = gs.getD b ⟨GateOp.or, []⟩ := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hb]
  rw [this]
  simp only [List.length_append, List.length_cons, List.length_nil]
  constructor
  · rintro ⟨_, h2, h3⟩; exact ⟨hb, h2, h3⟩
  · rintro ⟨_, h2, h3⟩; exact ⟨by omega, h2, h3⟩

lemma tg_snoc (n : ℕ) (gs : List Gate) (g : Gate) (i j : ℕ) (hj : j < gs.length) :
    Relation.TransGen (RG n (gs ++ [g])) i j ↔ Relation.TransGen (RG n gs) i j := by
  constructor
  · intro h
    induction h with
    | single h => exact Relation.TransGen.single ((RG_snoc n gs g _ _ hj).mp h)
    | @tail b c _ hbc ih =>
      have hb : b < gs.length := by have := hbc.2.1; omega
      exact Relation.TransGen.tail (ih hb) ((RG_snoc n gs g _ _ hj).mp hbc)
  · intro h
    induction h with
    | single h => exact Relation.TransGen.single ((RG_snoc n gs g _ _ h.1).mpr h)
    | tail _ hbc ih => exact Relation.TransGen.tail (ih (lt_trans hbc.2.1 hbc.1)) ((RG_snoc n gs g _ _ hbc.1).mpr hbc)

lemma cone_list (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔ Relation.TransGen (RG n gs) i j := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i j
    simp only [List.foldl_nil, List.getD_nil, List.not_mem_nil, false_iff]
    intro h
    obtain ⟨c, hc⟩ := tg_last h
    exact absurd hc.1 (by simp)
  | append_singleton gs g ih =>
    intro i j
    have hL := cones_length n gs []
    simp only [List.length_nil, Nat.zero_add] at hL
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    set cs := gs.foldl (coneStep n) [] with hcs
    rcases Nat.lt_trichotomy j gs.length with h1 | h1 | h1
    · rw [tg_snoc n gs g i j h1, ← ih i j]
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    · subst h1
      have hget : (coneStep n cs g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
            (fun w => (w - n) :: cs.getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hL]
      rw [hget, hL]
      have hRL : ∀ c, RG n (gs ++ [g]) c gs.length ↔ c < gs.length ∧ n + c ∈ g.inputs := by
        intro c
        unfold RG
        have : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        rw [this]
        simp
      simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro ⟨w, ⟨hw, hw1, hw2⟩, hi | hi⟩
        · apply Relation.TransGen.single
          rw [hRL]
          refine ⟨by omega, ?_⟩
          have : n + i = w := by omega
          rw [this]; exact hw
        · have h2 := (ih i (w - n)).mp hi
          rw [← tg_snoc n gs g i (w - n) (by omega)] at h2
          refine Relation.TransGen.tail h2 ((hRL _).mpr ⟨by omega, ?_⟩)
          have : n + (w - n) = w := by omega
          rw [this]; exact hw
      · intro h
        cases h with
        | single h =>
          obtain ⟨hc, hm⟩ := (hRL i).mp h
          exact ⟨n + i, ⟨hm, by omega, by omega⟩, Or.inl (by omega)⟩
        | @tail c _ hic hc =>
          obtain ⟨hc1, hm⟩ := (hRL c).mp hc
          refine ⟨n + c, ⟨hm, by omega, by omega⟩, Or.inr ?_⟩
          have : n + c - n = c := by omega
          rw [this, ih]
          exact (tg_snoc n gs g i c hc1).mp hic
    · have hnil : (coneStep n cs g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [hnil]
      simp only [List.not_mem_nil, false_iff]
      intro h
      obtain ⟨c, hc⟩ := tg_last h
      have := hc.1
      simp at this
      omega

def RR (n : ℕ) (C : Circuit) (i j : ℕ) : Prop :=
  j < C.gates.length ∧ i < j ∧ n + i ∈ (gateAt C j).inputs

lemma cone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ Relation.TransGen (RR n C) i j := by
  unfold InCone cones
  rw [cone_list n C.gates i j]
  rfl

end StandardConeBridge

namespace NormalizedTopForm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

lemma topForm_of_hooks {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C)
    (hNo : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ∀ t ∈ (gateAt C k).inputs,
        ¬ (∀ x : Fin n → Bool, wireVal n C t x = true → graphFun G ∅ x = true))
    (hOr : ∀ k < C.gates.length, (gateAt C k).op = GateOp.or →
      ∀ t ∈ (gateAt C k).inputs,
        (∀ x : Fin n → Bool, wireVal n C t x = true → graphFun G ∅ x = true) →
          BelowF G C k) : TopForm G C := by
  have step : ∀ a b, StandardConeBridge.RR n C a b → BelowF G C a →
      BelowF G C b ∧ (gateAt C b).op = GateOp.or := by
    intro a b hab ha
    obtain ⟨hb, _, hinput⟩ := hab
    have hmem : gateAt C b ∈ C.gates := List.mem_of_getElem?
      (show C.gates[b]? = some (gateAt C b) by
        simp [gateAt, List.getD_eq_getElem?_getD, hb])
    rcases hAO.1 _ hmem with hand | hor
    · exact False.elim (hNo b hb hand (n + a) hinput ha)
    · exact ⟨hOr b hb hor (n + a) hinput ha, hor⟩
  intro i hi j hj handI hbelow handJ hcone
  have hpath := (StandardConeBridge.cone_iff n C i j).mp hcone
  have hprop : ∀ b, Relation.TransGen (StandardConeBridge.RR n C) i b →
      BelowF G C b ∧ (gateAt C b).op = GateOp.or := by
    intro b hreach
    induction hreach with
    | single h => exact step i _ h hbelow
    | @tail b c hbc hstep ih => exact step b c hstep ih.1
  have hop := (hprop j hpath).2
  rw [handJ] at hop
  cases hop

lemma or_reader_clean {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (T : Finset ℕ) (hAO : IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅)
    (hA : Normalization.LiftFix.PA C T) (hB : Normalization.LiftFix.PB n C T)
    (hPC : Normalization.LiftFix.PC n C T)
    (k : ℕ) (hk : k < C.gates.length) (hor : (gateAt C k).op = GateOp.or)
    (t : ℕ) (ht : t ∈ (gateAt C k).inputs)
    (hbelow : ∀ x : Fin n → Bool, wireVal n C t x = true → graphFun G ∅ x = true) :
    BelowF G C k := by
  have hback := hAO.2.1 k hk t ht
  have hsat : ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true :=
    ⟨fun _ => true, NormalizerFixed.valid_wire_all_ones C hAO t (by omega)⟩
  have hget : C.gates[k]? = some (gateAt C k) :=
    Normalization.LiftFix.gateAt_some C k hk
  have hkT : k ∈ T := hPC k (gateAt C k) hget hor t ht hsat
    (fun x hx => by rw [hfun]; exact hbelow x hx)
  exact NormalizerFixed.marked_below G C T hAO hfun hA hB k hkT

lemma topForm_of_normalized_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (T : Finset ℕ) (hC : IsLeastAO G C)
    (hA : Normalization.LiftFix.PA C T) (hB : Normalization.LiftFix.PB n C T)
    (hPC : Normalization.LiftFix.PC n C T) : TopForm G C := by
  apply topForm_of_hooks G C hC.1
  · exact Normalization.noAndBelow_unconditional n G C hC
  · exact or_reader_clean G C T hC.1 hC.2.1 hA hB hPC

lemma same_minimum_fixed_top_form (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) :
    ∃ D : Circuit, IsLeastAO G D ∧ D.size = C.size ∧
      circuitFun n D = circuitFun n C ∧ ∃ T : Finset ℕ,
      Normalization.LiftFix.PA D T ∧ Normalization.LiftFix.PB n D T ∧
      Normalization.LiftFix.PC n D T ∧ PEqualNP.Core.IsLiftFixedPoint G D ∧
      TopForm G D ∧
      (∀ k < D.gates.length, (gateAt D k).op = GateOp.and → ∀ t ∈ (gateAt D k).inputs,
        ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) = true →
          graphFun G ∅ x = true)) := by
  obtain ⟨D, hD, hs, hf, T, hA, hB, hPC, hfixed, hNo⟩ :=
    NormalizerFixed.same_minimum_fixed_normal_form n G C hC
  exact ⟨D, hD, hs, hf, T, hA, hB, hPC, hfixed,
    topForm_of_normalized_least G D T hD hA hB hPC, hNo⟩

end NormalizedTopForm

namespace NormalizedTopForm
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover Normalization

lemma peel_of_fixed_top_form {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hpos : ∃ z : Fin n, 0 < G.degree z)
    (h : ∀ (D : Circuit) (T : Finset ℕ), IsLeastAO G D →
      LiftFix.PA D T → LiftFix.PB n D T → LiftFix.PC n D T →
      PEqualNP.Core.IsLiftFixedPoint G D → TopForm G D →
      (∀ k < D.gates.length, (gateAt D k).op = GateOp.and → ∀ t ∈ (gateAt D k).inputs,
        ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) = true →
          graphFun G ∅ x = true)) →
      ∃ z : Fin n, 0 < G.degree z ∧ CutWitness G z D) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun G ∅ → CutWitness G z C := by
  apply peel_of_normalized_least G hpos
  intro D T hD hA hB hPC hNo
  exact h D T hD hA hB hPC
    (NormalizerFixed.fixed_of_PABC G D T hD.1 hD.2.1 hA hB hPC)
    (topForm_of_normalized_least G D T hD hA hB hPC) hNo

end NormalizedTopForm

namespace HoistNegative
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3566.Normalization.Lift PEqualNP.Outside.L_meta_3566.Normalization.LiftFix

lemma foldl_set_state (gs : List Gate) (k : ℕ) (g g' : Gate) (hg : gs[k]? = some g)
    (w0 : List Bool)
    (heq : g'.op.eval (g'.inputs.map fun i => ((gs.take k).foldl step w0).getD i false) =
      g.op.eval (g.inputs.map fun i => ((gs.take k).foldl step w0).getD i false)) :
    (gs.set k g').foldl step w0 = gs.foldl step w0 := by
  induction gs generalizing k w0 with
  | nil => simp at hg
  | cons h gs ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
      subst h
      simp only [List.take_zero, List.foldl_nil] at heq
      simp only [List.set_cons_zero, List.foldl_cons]
      congr 1
      unfold step
      rw [heq]
    | succ k =>
      simp only [List.getElem?_cons_succ] at hg
      simp only [List.take_succ_cons, List.foldl_cons] at heq
      simp only [List.set_cons_succ, List.foldl_cons]
      exact ih k hg _ heq

lemma prefix_wire (gs : List Gate) (k : ℕ) (hk : k < gs.length)
    (w0 : List Bool) (i : ℕ) (hi : i < w0.length + k) :
    (gs.foldl step w0).getD i false = ((gs.take k).foldl step w0).getD i false := by
  have hl := take_fold_length gs k hk w0
  have heq : gs.foldl step w0 = (gs.drop k).foldl step ((gs.take k).foldl step w0) := by
    rw [← List.foldl_append, List.take_append_drop]
  rw [heq]
  exact foldl_step_getD _ _ _ (by omega)

lemma copy_or_wires_eq_of_false (n : ℕ) (D : Circuit) (k u t : ℕ)
    (hkg : D.gates[k]? = some ⟨GateOp.or, [u,t]⟩)
    (ht : t < n + k) (x : Fin n → Bool)
    (hfalse : (D.wires (List.ofFn x)).getD t false = false) :
    (D.gates.set k ⟨GateOp.or, [u]⟩).foldl step (List.ofFn x) =
      D.gates.foldl step (List.ofFn x) := by
  have hk := (List.getElem?_eq_some_iff.mp hkg).1
  have htP : ((D.gates.take k).foldl step (List.ofFn x)).getD t false = false := by
    rw [← prefix_wire D.gates k hk (List.ofFn x) t (by simpa using ht)]
    exact hfalse
  apply foldl_set_state D.gates k _ _ hkg (List.ofFn x)
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, htP,
    id_eq, Bool.false_or, Bool.or_false]

def lifted (n : ℕ) (D : Circuit) (k u t : ℕ) : Circuit :=
  ⟨D.gates.set k ⟨GateOp.or, [u]⟩ ++ [⟨GateOp.or, [D.output,t]⟩], n+D.gates.length⟩

lemma lifted_get_ne (n : ℕ) (D : Circuit) (k u t j : ℕ)
    (hjk : j ≠ k) (hj : j < D.gates.length) :
    (lifted n D k u t).gates[j]? = D.gates[j]? := by
  simp only [lifted]
  rw [List.getElem?_append_left (by simpa using hj), List.getElem?_set_ne (Ne.symm hjk)]

lemma lifted_get_copy (n : ℕ) (D : Circuit) (k u t : ℕ) (hk : k < D.gates.length) :
    (lifted n D k u t).gates[k]? = some ⟨GateOp.or,[u]⟩ := by
  simp only [lifted]
  rw [List.getElem?_append_left (by simpa using hk)]
  simp [List.getElem?_set, hk]

lemma lifted_get_last (n : ℕ) (D : Circuit) (k u t : ℕ) :
    (lifted n D k u t).gates[D.gates.length]? = some ⟨GateOp.or,[D.output,t]⟩ := by
  simp only [lifted]
  rw [List.getElem?_append_right (by simp)]
  simp

lemma lifted_readsBack (n : ℕ) (D : Circuit) (k u t : ℕ)
    (hR : ReadsBack n D) (hk : k < D.gates.length)
    (hu : u < n+k) (ht : t < n+k) (ho : D.output < n+D.gates.length) :
    ReadsBack n (lifted n D k u t) := by
  apply readsBack_of_get
  intro j g hg i hi
  rcases Nat.lt_trichotomy j D.gates.length with hj | hj | hj
  · by_cases hjk : j = k
    · subst j
      rw [lifted_get_copy n D k u t hk] at hg
      cases hg
      simp at hi
      omega
    · rw [lifted_get_ne n D k u t j hjk hj] at hg
      exact readsBack_get n D hR j g hg i hi
  · subst j
    rw [lifted_get_last] at hg
    cases hg
    simp at hi
    omega
  · have hlen : (lifted n D k u t).gates.length = D.gates.length+1 := by simp [lifted]
    rw [List.getElem?_eq_none (by omega)] at hg
    cases hg

lemma lifted_negative_wires (n : ℕ) (D : Circuit) (k u t : ℕ)
    (hkg : D.gates[k]? = some ⟨GateOp.or,[u,t]⟩) (ht : t < n+k)
    (x : Fin n → Bool) (htfalse : (D.wires (List.ofFn x)).getD t false = false)
    (hofalse : circuitFun n D x = false) :
    (lifted n D k u t).wires (List.ofFn x) = D.wires (List.ofFn x) ++ [false] := by
  have hc := copy_or_wires_eq_of_false n D k u t hkg ht x htfalse
  change (D.gates.set k _ ++ [_]).foldl step (List.ofFn x) = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hc]
  change step (D.wires (List.ofFn x)) _ = _
  change (D.wires (List.ofFn x)).getD D.output false = false at hofalse
  simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    htfalse, hofalse, id_eq, Bool.false_or]

end HoistNegative

namespace Normalization.LiftFix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3566.Normalization.Lift

lemma del_wire (n k u : ℕ) (E : Circuit) (hk : k < E.gates.length) (hu : u < n + k)
    (hpre : ∀ g ∈ E.gates.take k, ∀ i ∈ g.inputs, i < n + k)
    (hcopy : ∀ x : Fin n → Bool,
      (E.wires (List.ofFn x)).getD (n + k) false = (E.wires (List.ofFn x)).getD u false) :
    ∀ (x : Fin n → Bool) (i : ℕ),
      ((del n k u E).wires (List.ofFn x)).getD (sig (n+k) u i) false =
        (E.wires (List.ofFn x)).getD i false := by
  intro x i
  have hc := hcopy x
  have hgk : E.gates[k]? = some E.gates[k] := List.getElem?_eq_getElem hk
  set gk := E.gates[k]
  set w0 := List.ofFn x with hw0
  have hw0l : w0.length = n := by simp [hw0]
  have hl := take_fold_length E.gates k hk w0
  rw [hw0l] at hl
  set Wp := (E.gates.take k).foldl step w0 with hWp
  have hW : E.wires w0 = (E.gates.drop (k + 1)).foldl step (step Wp gk) := by
    rw [wires_eq, foldl_split E.gates k gk hgk w0]
  have hD : (del n k u E).wires w0 =
      ((E.gates.drop (k + 1)).map (rd (n + k) u)).foldl step Wp := by
    rw [wires_eq]
    simp only [del]
    rw [List.eraseIdx_eq_take_drop_succ, List.map_append, List.foldl_append]
    congr 1
    rw [hWp]
    congr 1
    conv_rhs => rw [← List.map_id (E.gates.take k)]
    apply List.map_congr_left
    intro g hg
    exact rd_id _ _ g (hpre g hg)

  have hvk : (step Wp gk).getD (n + k) false = Wp.getD u false := by
    rw [hW, foldl_step_getD _ _ _ (by simp [step]; omega),
      foldl_step_getD _ _ _ (by simp [step]; omega)] at hc
    rw [hc]
    unfold step
    exact getD_append_left _ _ _ (by omega)
  have hrel0 : Rel (n + k) u (step Wp gk) Wp := by
    refine ⟨by simp [step], by simp [step]; omega, ?_⟩
    intro i
    rcases Nat.lt_trichotomy i (n + k) with h1 | h1 | h1
    · have : sig (n + k) u i = i := by simp [sig, h1]
      rw [this]
      unfold step
      rw [getD_append_left _ _ _ (by omega)]
    · have : sig (n + k) u i = u := by simp [sig, h1]
      rw [this, h1, hvk]
    · have : sig (n + k) u i = i - 1 := by
        unfold sig; split_ifs <;> omega
      rw [this, getD_oob _ _ (by omega), getD_oob _ _ (by simp [step]; omega)]
  have hrel := rel_fold (n + k) u hu (E.gates.drop (k + 1)) _ _ hrel0
  rw [hD, hW]
  exact hrel.2.2 i


end Normalization.LiftFix

namespace HoistNegative
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3566.Normalization.Lift PEqualNP.Outside.L_meta_3566.Normalization.LiftFix

def hoisted (n : ℕ) (D : Circuit) (k u t : ℕ) : Circuit :=
  del n k u (lifted n D k u t)

lemma hoisted_negative_wire (n : ℕ) (D : Circuit) (k u t : ℕ)
    (hR : ReadsBack n D) (hkg : D.gates[k]? = some ⟨GateOp.or,[u,t]⟩)
    (hu : u < n+k) (ht : t < n+k) (ho : D.output < n+D.gates.length)
    (x : Fin n → Bool) (htfalse : (D.wires (List.ofFn x)).getD t false = false)
    (hofalse : circuitFun n D x = false) (i : ℕ) (hi : i < n+D.gates.length) :
    ((hoisted n D k u t).wires (List.ofFn x)).getD (sig (n+k) u i) false =
      (D.wires (List.ofFn x)).getD i false := by
  have hk : k < D.gates.length := (List.getElem?_eq_some_iff.mp hkg).1
  let E := lifted n D k u t
  have hER := lifted_readsBack n D k u t hR hk hu ht ho
  have hEk := lifted_get_copy n D k u t hk
  have hkE : k < E.gates.length := by simp [E, lifted]; omega
  have hcopy : ∀ y : Fin n → Bool,
      (E.wires (List.ofFn y)).getD (n+k) false = (E.wires (List.ofFn y)).getD u false := by
    intro y
    simpa using wires_copy E k u hEk (List.ofFn y) (by simpa using hu)
  have hw := del_wire n k u E hkE hu (readsBack_take n E hER k) hcopy x i
  have hl : (D.wires (List.ofFn x)).length = n+D.gates.length := by
    rw [wires_eq, foldl_step_length, List.length_ofFn]
  change ((hoisted n D k u t).wires (List.ofFn x)).getD _ false = _ at hw
  rw [lifted_negative_wires n D k u t hkg ht x htfalse hofalse,
    List.getD_append _ _ _ _ (by omega)] at hw
  exact hw

lemma hoisted_negative_gate (n : ℕ) (D : Circuit) (k u t j : ℕ)
    (hR : ReadsBack n D) (hkg : D.gates[k]? = some ⟨GateOp.or,[u,t]⟩)
    (hu : u < n+k) (ht : t < n+k) (ho : D.output < n+D.gates.length)
    (hj : j < D.gates.length) (hjk : j ≠ k)
    (x : Fin n → Bool) (htfalse : (D.wires (List.ofFn x)).getD t false = false)
    (hofalse : circuitFun n D x = false) :
    ((hoisted n D k u t).wires (List.ofFn x)).getD (n+sg k j) false =
      (D.wires (List.ofFn x)).getD (n+j) false := by
  have h := hoisted_negative_wire n D k u t hR hkg hu ht ho x htfalse hofalse
    (n+j) (by omega)
  rw [sig_gate n k u j hjk] at h
  exact h

lemma hoisted_get (n : ℕ) (D : Circuit) (k u t j : ℕ) (g : Gate)
    (hjk : j ≠ k) (hj : D.gates[j]? = some g) :
    (hoisted n D k u t).gates[sg k j]? = some (rd (n+k) u g) := by
  have hjlt : j < D.gates.length := (List.getElem?_eq_some_iff.mp hj).1
  apply del_get n k u (lifted n D k u t) j g hjk
  rw [lifted_get_ne n D k u t j hjk hjlt, hj]

lemma clean_hoist_negative_gate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (k u t j : ℕ)
    (hR : ReadsBack n D) (hkg : D.gates[k]? = some ⟨GateOp.or,[u,t]⟩)
    (hu : u < n+k) (ht : t < n+k) (ho : D.output < n+D.gates.length)
    (hfun : circuitFun n D = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true)
    (hj : j < D.gates.length) (hjk : j ≠ k)
    (x : Fin n → Bool) (hx : graphFun G ∅ x = false) :
    ((hoisted n D k u t).wires (List.ofFn x)).getD (n+sg k j) false =
      (D.wires (List.ofFn x)).getD (n+j) false := by
  have htfalse : (D.wires (List.ofFn x)).getD t false = false := by
    cases h : (D.wires (List.ofFn x)).getD t false
    · rfl
    · have hc := hclean x h
      rw [hx] at hc
      cases hc
  exact hoisted_negative_gate n D k u t j hR hkg hu ht ho hj hjk x htfalse (by rw [hfun, hx])

end HoistNegative

namespace HoistNegative
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3566.Normalization.Lift PEqualNP.Outside.L_meta_3566.Normalization.LiftFix

def ordered (D : Circuit) (k u t : ℕ) : Circuit :=
  ⟨D.gates.set k ⟨GateOp.or,[u,t]⟩, D.output⟩

lemma ordered_wires_eq (D : Circuit) (k u t : ℕ) (g : Gate)
    (hkg : D.gates[k]? = some g)
    (hequ : ∀ w : List Bool, GateOp.or.eval ([u,t].map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false)) (x : List Bool) :
    (ordered D k u t).wires x = D.wires x :=
  foldl_set_equiv D.gates k g ⟨GateOp.or,[u,t]⟩ hkg hequ x

lemma ordered_fun_eq (n : ℕ) (D : Circuit) (k u t : ℕ) (g : Gate)
    (hkg : D.gates[k]? = some g)
    (hequ : ∀ w : List Bool, GateOp.or.eval ([u,t].map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false)) :
    circuitFun n (ordered D k u t) = circuitFun n D := by
  funext x
  change ((ordered D k u t).wires (List.ofFn x)).getD D.output false = _
  rw [ordered_wires_eq D k u t g hkg hequ]
  rfl

lemma hoisted_ordered_eq (n : ℕ) (D : Circuit) (k u t : ℕ) :
    hoisted n (ordered D k u t) k u t = hoisted n D k u t := by
  simp [hoisted, lifted, ordered, List.set_set]

lemma ordered_readsBack (n : ℕ) (D : Circuit) (k u t : ℕ)
    (hR : ReadsBack n D) (hu : u < n+k) (ht : t < n+k) :
    ReadsBack n (ordered D k u t) := by
  apply readsBack_of_get
  intro j g hg i hi
  have hj : j < D.gates.length := by
    have h := (List.getElem?_eq_some_iff.mp hg).1
    simpa [ordered] using h
  by_cases hjk : j = k
  · subst j
    have hget : (ordered D k u t).gates[k]? = some ⟨GateOp.or,[u,t]⟩ := by
      simp [ordered, hj]
    rw [hget] at hg
    cases hg
    simp at hi
    omega
  · have hget : (ordered D k u t).gates[j]? = D.gates[j]? := by
      simp only [ordered, List.getElem?_set_ne (Ne.symm hjk)]
    rw [hget] at hg
    exact readsBack_get n D hR j g hg i hi

lemma hoisted_negative_gate_equiv (n : ℕ) (D : Circuit) (k u t j : ℕ) (g : Gate)
    (hR : ReadsBack n D) (hkg : D.gates[k]? = some g)
    (hequ : ∀ w : List Bool, GateOp.or.eval ([u,t].map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false))
    (hu : u < n+k) (ht : t < n+k) (ho : D.output < n+D.gates.length)
    (hj : j < D.gates.length) (hjk : j ≠ k)
    (x : Fin n → Bool) (htfalse : (D.wires (List.ofFn x)).getD t false = false)
    (hofalse : circuitFun n D x = false) :
    ((hoisted n D k u t).wires (List.ofFn x)).getD (n+sg k j) false =
      (D.wires (List.ofFn x)).getD (n+j) false := by
  have hk : k < D.gates.length := (List.getElem?_eq_some_iff.mp hkg).1
  have hkg' : (ordered D k u t).gates[k]? = some ⟨GateOp.or,[u,t]⟩ := by
    simp [ordered, hk]
  have ho' : (ordered D k u t).output < n+(ordered D k u t).gates.length := by
    simpa [ordered] using ho
  have hj' : j < (ordered D k u t).gates.length := by simpa [ordered] using hj
  have htfalse' : ((ordered D k u t).wires (List.ofFn x)).getD t false = false := by
    rw [ordered_wires_eq D k u t g hkg hequ]
    exact htfalse
  have hofalse' : circuitFun n (ordered D k u t) x = false := by
    rw [ordered_fun_eq n D k u t g hkg hequ]
    exact hofalse
  have h := hoisted_negative_gate n (ordered D k u t) k u t j
    (ordered_readsBack n D k u t hR hu ht) hkg' hu ht ho' hj' hjk x htfalse' hofalse'
  rw [hoisted_ordered_eq, ordered_wires_eq D k u t g hkg hequ] at h
  exact h

end HoistNegative

namespace AndIndexTransport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

noncomputable def andIndices (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun j => (gateAt C j).op = .and

noncomputable def badAnds {n : ℕ} (C : Circuit) (P : (Fin n → Bool) → Prop) : Finset ℕ := by
  classical
  exact (andIndices C).filter fun j => ∃ x, P x ∧ gateVal n C j x = true

lemma mem_andIndices {C : Circuit} {j : ℕ} :
    j ∈ andIndices C ↔ j < C.gates.length ∧ (gateAt C j).op = .and := by
  classical
  simp [andIndices]

lemma mem_badAnds {n : ℕ} {C : Circuit} {P : (Fin n → Bool) → Prop} {j : ℕ} :
    j ∈ badAnds C P ↔ j ∈ andIndices C ∧ ∃ x, P x ∧ gateVal n C j x = true := by
  classical
  simp [badAnds]

lemma badAnds_image {n : ℕ} (C D : Circuit) (f : ℕ → ℕ)
    (P : (Fin n → Bool) → Prop)
    (hforward : ∀ j ∈ andIndices C, f j ∈ andIndices D)
    (hsurj : ∀ k ∈ andIndices D, ∃ j ∈ andIndices C, f j = k)
    (hval : ∀ j ∈ andIndices C, ∀ x, P x → gateVal n D (f j) x = gateVal n C j x) :
    badAnds D P = (badAnds C P).image f := by
  classical
  ext k
  constructor
  · intro hk
    obtain ⟨hkA, x, hx, hv⟩ := mem_badAnds.mp hk
    obtain ⟨j, hj, rfl⟩ := hsurj k hkA
    exact Finset.mem_image.mpr ⟨j, mem_badAnds.mpr ⟨hj, x, hx, (hval j hj x hx) ▸ hv⟩, rfl⟩
  · intro hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hjA, x, hx, hv⟩ := mem_badAnds.mp hj
    exact mem_badAnds.mpr ⟨hforward j hjA, x, hx, (hval j hjA x hx).symm ▸ hv⟩

lemma badAnds_card {n : ℕ} (C D : Circuit) (f : ℕ → ℕ)
    (P : (Fin n → Bool) → Prop)
    (hforward : ∀ j ∈ andIndices C, f j ∈ andIndices D)
    (hsurj : ∀ k ∈ andIndices D, ∃ j ∈ andIndices C, f j = k)
    (hinj : Set.InjOn f (andIndices C : Set ℕ))
    (hval : ∀ j ∈ andIndices C, ∀ x, P x → gateVal n D (f j) x = gateVal n C j x) :
    (badAnds D P).card = (badAnds C P).card := by
  classical
  rw [badAnds_image C D f P hforward hsurj hval]
  apply Finset.card_image_of_injOn
  intro i hi j hj hij
  exact hinj (mem_badAnds.mp hi).1 (mem_badAnds.mp hj).1 hij

lemma junk_eq_badAnds {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    junk G C = badAnds C (fun x => graphFun G ∅ x = false) := by
  classical
  ext j
  have hjunk : j ∈ junk G C ↔ j < C.gates.length ∧ IsDirtyAnd n G C j := by
    unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
    rw [Finset.mem_filter, Finset.mem_range]
  rw [hjunk, mem_badAnds, mem_andIndices]
  change (j < C.gates.length ∧ (gateAt C j).op = .and ∧ j < C.gates.length ∧
    ∃ x, gateVal n C j x = true ∧ graphFun G ∅ x = false) ↔ _
  constructor
  · rintro ⟨hj, hop, _, x, hv, hx⟩
    exact ⟨⟨hj, hop⟩, x, hx, hv⟩
  · rintro ⟨⟨hj, hop⟩, x, hx, hv⟩
    exact ⟨hj, hop, hj, x, hv, hx⟩

lemma junk_image {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (f : ℕ → ℕ)
    (hforward : ∀ j ∈ andIndices C, f j ∈ andIndices D)
    (hsurj : ∀ k ∈ andIndices D, ∃ j ∈ andIndices C, f j = k)
    (hval : ∀ j ∈ andIndices C, ∀ x, graphFun G ∅ x = false →
      gateVal n D (f j) x = gateVal n C j x) :
    junk G D = (junk G C).image f := by
  rw [junk_eq_badAnds, junk_eq_badAnds]
  exact badAnds_image C D f _ hforward hsurj hval

lemma junk_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (f : ℕ → ℕ)
    (hforward : ∀ j ∈ andIndices C, f j ∈ andIndices D)
    (hsurj : ∀ k ∈ andIndices D, ∃ j ∈ andIndices C, f j = k)
    (hinj : Set.InjOn f (andIndices C : Set ℕ))
    (hval : ∀ j ∈ andIndices C, ∀ x, graphFun G ∅ x = false →
      gateVal n D (f j) x = gateVal n C j x) :
    (junk G D).card = (junk G C).card := by
  rw [junk_eq_badAnds, junk_eq_badAnds]
  exact badAnds_card C D f _ hforward hsurj hinj hval

noncomputable def pairLeakyAnds {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Finset ℕ := by
  classical
  exact (andIndices C).filter fun j =>
    ∃ a b, ¬ G.Adj a b ∧ gateVal n C j (pairInput a b) = true

lemma mem_pairLeakyAnds {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {j : ℕ} :
    j ∈ pairLeakyAnds G C ↔ j ∈ andIndices C ∧
      ∃ a b, ¬ G.Adj a b ∧ gateVal n C j (pairInput a b) = true := by
  classical
  simp [pairLeakyAnds]

lemma pairLeakyAnds_eq_badAnds {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) :
    pairLeakyAnds G C = badAnds C (fun x => ∃ a b, ¬ G.Adj a b ∧ x = pairInput a b) := by
  classical
  ext j
  rw [mem_pairLeakyAnds, mem_badAnds]
  constructor
  · rintro ⟨hj, a, b, hab, hv⟩
    exact ⟨hj, pairInput a b, ⟨a, b, hab, rfl⟩, hv⟩
  · rintro ⟨hj, x, ⟨a, b, hab, rfl⟩, hv⟩
    exact ⟨hj, a, b, hab, hv⟩

lemma pairLeakyAnds_image {n : ℕ} (G : SimpleGraph (Fin n))
    (C D : Circuit) (f : ℕ → ℕ)
    (hforward : ∀ j ∈ andIndices C, f j ∈ andIndices D)
    (hsurj : ∀ k ∈ andIndices D, ∃ j ∈ andIndices C, f j = k)
    (hval : ∀ j ∈ andIndices C, ∀ a b, ¬ G.Adj a b →
      gateVal n D (f j) (pairInput a b) = gateVal n C j (pairInput a b)) :
    pairLeakyAnds G D = (pairLeakyAnds G C).image f := by
  rw [pairLeakyAnds_eq_badAnds, pairLeakyAnds_eq_badAnds]
  apply badAnds_image C D f _ hforward hsurj
  rintro j hj x ⟨a, b, hab, rfl⟩
  exact hval j hj a b hab

lemma pairLeakyAnds_card {n : ℕ} (G : SimpleGraph (Fin n))
    (C D : Circuit) (f : ℕ → ℕ)
    (hforward : ∀ j ∈ andIndices C, f j ∈ andIndices D)
    (hsurj : ∀ k ∈ andIndices D, ∃ j ∈ andIndices C, f j = k)
    (hinj : Set.InjOn f (andIndices C : Set ℕ))
    (hval : ∀ j ∈ andIndices C, ∀ a b, ¬ G.Adj a b →
      gateVal n D (f j) (pairInput a b) = gateVal n C j (pairInput a b)) :
    (pairLeakyAnds G D).card = (pairLeakyAnds G C).card := by
  rw [pairLeakyAnds_eq_badAnds, pairLeakyAnds_eq_badAnds]
  apply badAnds_card C D f _ hforward hsurj hinj
  rintro j hj x ⟨a, b, hab, rfl⟩
  exact hval j hj a b hab

end AndIndexTransport

namespace HoistAndIndices

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3566.Normalization.LiftFix PEqualNP.Outside.L_meta_3566.HoistNegative
open PEqualNP.Outside.L_meta_3566.AndIndexTransport (andIndices)

lemma mem_andIndices (C : Circuit) (j : ℕ) :
    j ∈ andIndices C ↔ ∃ g, C.gates[j]? = some g ∧ g.op = .and := by
  classical
  simp only [AndIndexTransport.andIndices, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hj, hop⟩
    refine ⟨gateAt C j, ?_, hop⟩
    simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  · rintro ⟨g, hg, hop⟩
    refine ⟨(List.getElem?_eq_some_iff.mp hg).1, ?_⟩
    simpa [gateAt, List.getD_eq_getElem?_getD, hg] using hop

lemma indexShift_injOn (k : ℕ) (S : Finset ℕ) (hS : k ∉ S) :
    Set.InjOn (sg k) (S : Set ℕ) := by
  intro a ha b hb hab
  have ha' : a ≠ k := fun h => hS (h ▸ ha)
  have hb' : b ≠ k := fun h => hS (h ▸ hb)
  unfold sg at hab
  split_ifs at hab <;> omega

lemma changed_not_and (C : Circuit) (k : ℕ) (g : Gate)
    (hkg : C.gates[k]? = some g) (hor : g.op = .or) : k ∉ andIndices C := by
  intro hk
  obtain ⟨g', hg', hand⟩ := (mem_andIndices C k).mp hk
  rw [hkg] at hg'
  cases hg'
  rw [hor] at hand
  cases hand

lemma hoisted_and_injOn (C : Circuit) (k : ℕ) (g : Gate)
    (hkg : C.gates[k]? = some g) (hor : g.op = .or) :
    Set.InjOn (sg k) (andIndices C : Set ℕ) :=
  indexShift_injOn k (andIndices C) (changed_not_and C k g hkg hor)

lemma hoisted_and_forward (n : ℕ) (C : Circuit) (k u t : ℕ) (g : Gate)
    (hkg : C.gates[k]? = some g) (hor : g.op = .or)
    (j : ℕ) (hj : j ∈ andIndices C) : sg k j ∈ andIndices (hoisted n C k u t) := by
  have hjk : j ≠ k := by
    intro heq
    exact changed_not_and C k g hkg hor (heq ▸ hj)
  obtain ⟨g0, hg0, hand⟩ := (mem_andIndices C j).mp hj
  apply (mem_andIndices _ _).mpr
  exact ⟨rd (n + k) u g0, HoistNegative.hoisted_get n C k u t j g0 hjk hg0, hand⟩

lemma hoisted_and_inverse (n : ℕ) (C : Circuit) (k u t j : ℕ)
    (hj : j ∈ andIndices (hoisted n C k u t)) :
    ∃ i ∈ andIndices C, sg k i = j := by
  obtain ⟨g, hg, hand⟩ := (mem_andIndices _ j).mp hj
  obtain ⟨g0, hg0, hrd⟩ := del_get_inv n k u (lifted n C k u t) j g hg
  let i := if j < k then j else j + 1
  have hik : i ≠ k := by dsimp [i]; split_ifs <;> omega
  have hi : i < (lifted n C k u t).gates.length :=
    (List.getElem?_eq_some_iff.mp hg0).1
  have hlen : (lifted n C k u t).gates.length = C.gates.length + 1 := by
    simp [lifted]
  have hiold : i < C.gates.length := by
    by_contra hn
    have heq : i = C.gates.length := by omega
    have hlast := lifted_get_last n C k u t
    change (lifted n C k u t).gates[i]? = some g0 at hg0
    rw [heq, hlast] at hg0
    cases hg0
    simp [hrd, rd] at hand
  have hOld : C.gates[i]? = some g0 := by
    rw [← lifted_get_ne n C k u t i hik hiold]
    exact hg0
  refine ⟨i, (mem_andIndices C i).mpr ⟨g0, hOld, ?_⟩, ?_⟩
  · simpa [hrd, rd] using hand
  · dsimp [i, sg]
    split_ifs <;> omega

lemma hoisted_and_image (n : ℕ) (C : Circuit) (k u t : ℕ) (g : Gate)
    (hkg : C.gates[k]? = some g) (hor : g.op = .or) :
    andIndices (hoisted n C k u t) = (andIndices C).image (sg k) := by
  ext j
  constructor
  · intro hj
    obtain ⟨i, hi, heq⟩ := hoisted_and_inverse n C k u t j hj
    exact Finset.mem_image.mpr ⟨i, hi, heq⟩
  · intro hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact hoisted_and_forward n C k u t g hkg hor i hi

lemma hoisted_and_bijection (n : ℕ) (C : Circuit) (k u t : ℕ) (g : Gate)
    (hkg : C.gates[k]? = some g) (hor : g.op = .or)
    (j : ℕ) (hj : j ∈ andIndices (hoisted n C k u t)) :
    ∃! i, i ∈ andIndices C ∧ sg k i = j := by
  obtain ⟨i, hi, heq⟩ := hoisted_and_inverse n C k u t j hj
  refine ⟨i, ⟨hi, heq⟩, ?_⟩
  intro i' hi'
  exact indexShift_injOn k (andIndices C) (changed_not_and C k g hkg hor)
    hi'.1 hi (hi'.2.trans heq.symm)

lemma hoisted_and_card (n : ℕ) (C : Circuit) (k u t : ℕ) (g : Gate)
    (hkg : C.gates[k]? = some g) (hor : g.op = .or) :
    (andIndices (hoisted n C k u t)).card = (andIndices C).card := by
  rw [hoisted_and_image n C k u t g hkg hor]
  exact Finset.card_image_of_injOn
    (indexShift_injOn k (andIndices C) (changed_not_and C k g hkg hor))

end HoistAndIndices

namespace HoistDirty

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3566.Normalization.LiftFix (sg)
open PEqualNP.Outside.L_meta_3566.HoistNegative (hoisted)
open PEqualNP.Outside.L_meta_3566.AndIndexTransport (andIndices pairLeakyAnds)

lemma negative_and_profile {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some ⟨GateOp.or, [u,t]⟩)
    (ho : C.output < n + C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    ∀ j ∈ andIndices C, ∀ x, graphFun G ∅ x = false →
      gateVal n (hoisted n C k u t) (sg k j) x = gateVal n C j x := by
  have hreads := Normalization.LiftFix.readsBack_get n C hR k ⟨GateOp.or, [u,t]⟩ hkg
  have hu : u < n + k := hreads u (by simp)
  have ht : t < n + k := hreads t (by simp)
  intro j hj x hx
  have hjlt := (AndIndexTransport.mem_andIndices.mp hj).1
  have hjk : j ≠ k := by
    intro h
    exact HoistAndIndices.changed_not_and C k _ hkg rfl (h ▸ hj)
  exact HoistNegative.clean_hoist_negative_gate G C k u t j hR hkg hu ht ho
    hfun hclean hjlt hjk x hx

lemma junk_image {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some ⟨GateOp.or, [u,t]⟩)
    (ho : C.output < n + C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    junk G (hoisted n C k u t) = (junk G C).image (sg k) := by
  exact AndIndexTransport.junk_image G C (hoisted n C k u t) (sg k)
    (HoistAndIndices.hoisted_and_forward n C k u t _ hkg rfl)
    (HoistAndIndices.hoisted_and_inverse n C k u t)
    (negative_and_profile G C k u t hR hkg ho hfun hclean)

lemma junk_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some ⟨GateOp.or, [u,t]⟩)
    (ho : C.output < n + C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    (junk G (hoisted n C k u t)).card = (junk G C).card := by
  exact AndIndexTransport.junk_card G C (hoisted n C k u t) (sg k)
    (HoistAndIndices.hoisted_and_forward n C k u t _ hkg rfl)
    (HoistAndIndices.hoisted_and_inverse n C k u t)
    (HoistAndIndices.hoisted_and_injOn C k _ hkg rfl)
    (negative_and_profile G C k u t hR hkg ho hfun hclean)

lemma graphFun_pair_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : Fin n) (hab : ¬ G.Adj a b) : graphFun G ∅ (pairInput a b) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hh : ∃ p q, G.Adj p q ∧ pairInput a b p = true ∧ pairInput a b q = true := by
    simpa [graphFun] using h
  obtain ⟨p, q, hpq, hp, hq⟩ := hh
  have hp' : p = a ∨ p = b := by simpa [pairInput] using hp
  have hq' : q = a ∨ q = b := by simpa [pairInput] using hq
  rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
  · exact G.loopless.irrefl _ hpq
  · exact hab hpq
  · exact hab hpq.symm
  · exact G.loopless.irrefl _ hpq

lemma pair_negative_and_profile {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some ⟨GateOp.or, [u,t]⟩)
    (ho : C.output < n + C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    ∀ j ∈ andIndices C, ∀ a b, ¬ G.Adj a b →
      gateVal n (hoisted n C k u t) (sg k j) (pairInput a b) =
        gateVal n C j (pairInput a b) := by
  intro j hj a b hab
  exact negative_and_profile G C k u t hR hkg ho hfun hclean j hj
    (pairInput a b) (graphFun_pair_false G a b hab)

lemma pairLeakyAnds_image {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some ⟨GateOp.or, [u,t]⟩)
    (ho : C.output < n + C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    pairLeakyAnds G (hoisted n C k u t) = (pairLeakyAnds G C).image (sg k) := by
  exact AndIndexTransport.pairLeakyAnds_image G C (hoisted n C k u t) (sg k)
    (HoistAndIndices.hoisted_and_forward n C k u t _ hkg rfl)
    (HoistAndIndices.hoisted_and_inverse n C k u t)
    (pair_negative_and_profile G C k u t hR hkg ho hfun hclean)

lemma pairLeakyAnds_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some ⟨GateOp.or, [u,t]⟩)
    (ho : C.output < n + C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    (pairLeakyAnds G (hoisted n C k u t)).card = (pairLeakyAnds G C).card := by
  exact AndIndexTransport.pairLeakyAnds_card G C (hoisted n C k u t) (sg k)
    (HoistAndIndices.hoisted_and_forward n C k u t _ hkg rfl)
    (HoistAndIndices.hoisted_and_inverse n C k u t)
    (HoistAndIndices.hoisted_and_injOn C k _ hkg rfl)
    (pair_negative_and_profile G C k u t hR hkg ho hfun hclean)

end HoistDirty

namespace HoistDirty
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3566.Normalization.LiftFix (sg)
open PEqualNP.Outside.L_meta_3566.HoistNegative (hoisted)
open PEqualNP.Outside.L_meta_3566.AndIndexTransport (andIndices)

lemma negative_and_profile_equiv {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ) (g : Gate)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some g) (hor : g.op = GateOp.or)
    (hu : u ∈ g.inputs) (ht : t ∈ g.inputs)
    (hequ : ∀ w : List Bool, GateOp.or.eval ([u,t].map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false))
    (ho : C.output < n+C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    ∀ j ∈ andIndices C, ∀ x, graphFun G ∅ x = false →
      gateVal n (hoisted n C k u t) (sg k j) x = gateVal n C j x := by
  have hreads := Normalization.LiftFix.readsBack_get n C hR k g hkg
  intro j hj x hx
  have hjlt := (AndIndexTransport.mem_andIndices.mp hj).1
  have hjk : j ≠ k := by
    intro h
    exact HoistAndIndices.changed_not_and C k g hkg hor (h ▸ hj)
  have htfalse : (C.wires (List.ofFn x)).getD t false = false := by
    cases h : (C.wires (List.ofFn x)).getD t false
    · rfl
    · have hc := hclean x h
      rw [hx] at hc
      cases hc
  exact HoistNegative.hoisted_negative_gate_equiv n C k u t j g hR hkg hequ
    (hreads u hu) (hreads t ht) ho hjlt hjk x htfalse (by rw [hfun,hx])

lemma junk_card_equiv {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ) (g : Gate)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some g) (hor : g.op = GateOp.or)
    (hu : u ∈ g.inputs) (ht : t ∈ g.inputs)
    (hequ : ∀ w : List Bool, GateOp.or.eval ([u,t].map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false))
    (ho : C.output < n+C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    (junk G (hoisted n C k u t)).card = (junk G C).card := by
  exact AndIndexTransport.junk_card G C (hoisted n C k u t) (sg k)
    (HoistAndIndices.hoisted_and_forward n C k u t g hkg hor)
    (HoistAndIndices.hoisted_and_inverse n C k u t)
    (HoistAndIndices.hoisted_and_injOn C k g hkg hor)
    (negative_and_profile_equiv G C k u t g hR hkg hor hu ht hequ ho hfun hclean)

end HoistDirty

namespace NormalizerJunk

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open Normalization Normalization.Lift Normalization.LiftFix

lemma lift_step_AO_preserving (n : ℕ) (D : Circuit) (T : Finset ℕ) (P : Circuit → Prop) (hM : Monotone2 D) (hR : ReadsBack n D)
    (hL2 : ∀ g ∈ D.gates, g.inputs.length = 2)
    (hA : PA D T) (hB : PB n D T) (k : ℕ) (g : Gate) (hkg : D.gates[k]? = some g)
    (hor : g.op = GateOp.or) (t : ℕ) (ht : t ∈ g.inputs)
    (hsat : ∃ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true)
    (himp : ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true →
      circuitFun n D x = true)
    (hkT : k ∉ T)
    (hpres : ∀ u, u ∈ g.inputs →
      (∀ w : List Bool, GateOp.or.eval ([u, t].map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false)) →
      D.output < n + D.gates.length → P (HoistNegative.hoisted n D k u t)) :
    ∃ D1 : Circuit, ∃ T1 : Finset ℕ, Monotone2 D1 ∧ ReadsBack n D1 ∧
      (∀ g ∈ D1.gates, g.inputs.length = 2) ∧
      D1.gates.length = D.gates.length ∧ circuitFun n D1 = circuitFun n D ∧
      PA D1 T1 ∧ PB n D1 T1 ∧ T1.card = T.card + 1 ∧
      P D1 := by
  have hk : k < D.gates.length := (List.getElem?_eq_some_iff.mp hkg).1
  have hrk := readsBack_get n D hR k g hkg
  have htk : t < n + k := hrk t ht
  have hgl : g.inputs.length ≤ 2 := (hM g (List.mem_of_getElem? hkg)).2
  obtain ⟨u, hu, hequ⟩ := pick_u g hor hgl t ht
  have huk : u < n + k := hrk u hu
  obtain ⟨x0, hx0⟩ := hsat
  have hout : D.output < n + D.gates.length := by
    by_contra hcon
    have h1 := himp x0 hx0
    unfold circuitFun Circuit.eval at h1
    rw [getD_oob] at h1
    · exact absurd h1 (by simp)
    · rw [wires_eq, foldl_step_length]; simp; omega
  have hTlt : ∀ j ∈ T, j < D.gates.length := fun j hj => by
    obtain ⟨g', hg', _⟩ := hA j hj
    exact (List.getElem?_eq_some_iff.mp hg').1

  have hE0w : ∀ w, (D.gates.set k ⟨GateOp.or, [u, t]⟩).foldl step w = D.gates.foldl step w :=
    fun w => foldl_set_equiv D.gates k g _ hkg hequ w
  have hE0f : circuitFun n ⟨D.gates.set k ⟨GateOp.or, [u, t]⟩, D.output⟩ = circuitFun n D := by
    funext x
    simp only [circuitFun, Circuit.eval, wires_eq, hE0w]
  have hE0M : Monotone2 ⟨D.gates.set k ⟨GateOp.or, [u, t]⟩, D.output⟩ := by
    intro g' hg'
    rcases List.mem_or_eq_of_mem_set hg' with h | h
    · exact hM g' h
    · subst h; simp
  have hE0k : (D.gates.set k ⟨GateOp.or, [u, t]⟩)[k]? = some ⟨GateOp.or, [u, t]⟩ := by
    simp [List.getElem?_set, hk]
  have hL := L2604 n ⟨D.gates.set k ⟨GateOp.or, [u, t]⟩, D.output⟩ k u t hE0M
    (by simpa using hk) hE0k htk (by
      intro x hx
      rw [hE0f]
      apply himp
      simpa [wires_eq, hE0w] using hx)
  simp only [List.set_set, List.length_set] at hL
  rw [hE0f] at hL

  set E : Circuit := ⟨D.gates.set k ⟨GateOp.or, [u]⟩ ++ [⟨GateOp.or, [D.output, t]⟩], n + D.gates.length⟩
    with hE
  have hElen : E.gates.length = D.gates.length + 1 := by simp [hE]
  have hEget : ∀ j, j ≠ k → j < D.gates.length → E.gates[j]? = D.gates[j]? := by
    intro j hjk hj
    simp only [hE]
    rw [List.getElem?_append_left (by simpa using hj), List.getElem?_set_ne (Ne.symm hjk)]
  have hEk : E.gates[k]? = some ⟨GateOp.or, [u]⟩ := by
    simp only [hE]
    rw [List.getElem?_append_left (by simpa using hk)]
    simp [List.getElem?_set, hk]
  have hEN : E.gates[D.gates.length]? = some ⟨GateOp.or, [D.output, t]⟩ := by
    simp only [hE]
    rw [List.getElem?_append_right (by simp)]
    simp
  have hEM : Monotone2 E := by
    intro g' hg'
    simp only [hE, List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · rcases List.mem_or_eq_of_mem_set hg' with h | h
      · exact hM g' h
      · subst h; simp
    · simp
  have hER : ReadsBack n E := by
    apply readsBack_of_get
    intro j g' hg' i hi
    rcases Nat.lt_trichotomy j D.gates.length with hj | hj | hj
    · by_cases hjk : j = k
      · subst hjk
        rw [hEk] at hg'
        cases hg'
        simp at hi
        omega
      · rw [hEget j hjk hj] at hg'
        exact readsBack_get n D hR j g' hg' i hi
    · subst hj
      rw [hEN] at hg'
      cases hg'
      simp at hi
      omega
    · have : E.gates[j]? = none := List.getElem?_eq_none (by omega)
      rw [this] at hg'
      cases hg'
  have hcopy : ∀ x : Fin n → Bool,
      (E.wires (List.ofFn x)).getD (n + k) false = (E.wires (List.ofFn x)).getD u false := by
    intro x
    have := wires_copy E k u hEk (List.ofFn x) (by simp; omega)
    simpa using this
  have hEf : circuitFun n E = circuitFun n D := by
    rw [← hL]

  refine ⟨del n k u E, (insert D.gates.length T).image (sg k), del_mono n k u E hEM,
    del_readsBack n k u E hER huk, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g' hg'
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hg'
    obtain ⟨g0, hg0, rfl⟩ := del_get_inv n k u E j g' hj
    have hne : (if j < k then j else j + 1) ≠ k := by split_ifs <;> omega
    simp only [rd, List.length_map]
    set j' := (if j < k then j else j + 1) with hj'
    rcases Nat.lt_trichotomy j' D.gates.length with h1 | h1 | h1
    · rw [hEget j' hne h1] at hg0
      exact hL2 g0 (List.mem_of_getElem? hg0)
    · rw [h1, hEN] at hg0
      cases hg0
      rfl
    · rw [List.getElem?_eq_none (by omega)] at hg0
      cases hg0
  · have := del_length n k u E (by omega)
    omega
  · rw [del_fun n k u E (by omega) huk (readsBack_take n E hER k) hcopy, hEf]
  · intro j' hj'
    simp only [Finset.mem_image, Finset.mem_insert] at hj'
    obtain ⟨j, hj, rfl⟩ := hj'
    rcases hj with rfl | hj
    · exact ⟨_, del_get n k u E _ _ (by omega) hEN, rfl⟩
    · obtain ⟨g', hg', hor'⟩ := hA j hj
      have hjk : j ≠ k := fun h => hkT (h ▸ hj)
      rw [← hEget j hjk (hTlt j hj)] at hg'
      exact ⟨_, del_get n k u E _ _ hjk hg', hor'⟩
  · intro j' hj'
    simp only [Finset.mem_image, Finset.mem_insert] at hj'
    obtain ⟨j, hj, rfl⟩ := hj'
    rcases hj with rfl | hj
    · left
      simp only [del, hE]
      exact sig_gate n k u _ (by omega)
    · right
      have hjk : j ≠ k := fun h => hkT (h ▸ hj)
      have hread : ∃ k'' ∈ insert D.gates.length T, k'' ≠ k ∧ ∃ g' : Gate, E.gates[k'']? = some g' ∧
          n + j ∈ g'.inputs := by
        rcases hB j hj with h | ⟨k', hk', g', hg', hin⟩
        · exact ⟨D.gates.length, Finset.mem_insert_self _ _, by omega, _, hEN, by simp [h]⟩
        · have hk'k : k' ≠ k := fun h => hkT (h ▸ hk')
          rw [← hEget k' hk'k (hTlt k' hk')] at hg'
          exact ⟨k', Finset.mem_insert_of_mem hk', hk'k, g', hg', hin⟩
      obtain ⟨k'', hk'', hk''k, g', hg', hin⟩ := hread
      refine ⟨sg k k'', Finset.mem_image_of_mem _ hk'', _, del_get n k u E _ _ hk''k hg', ?_⟩
      simp only [rd, List.mem_map]
      exact ⟨n + j, hin, sig_gate n k u j hjk⟩
  · have hNT : D.gates.length ∉ T := fun h => by have := hTlt D.gates.length h; omega
    rw [Finset.card_image_of_injOn (sg_injOn k _ (by
      simp only [Finset.mem_insert, not_or]
      exact ⟨by omega, hkT⟩)), Finset.card_insert_of_notMem hNT]

  · simpa only [HoistNegative.hoisted, HoistNegative.lifted, ← hE] using
      hpres u hu hequ hout

lemma lift_step_AO (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit) (T : Finset ℕ) (hM : Monotone2 D) (hR : ReadsBack n D)
    (hL2 : ∀ g ∈ D.gates, g.inputs.length = 2)
    (hfun : circuitFun n D = graphFun G ∅)
    (hA : PA D T) (hB : PB n D T) (k : ℕ) (g : Gate) (hkg : D.gates[k]? = some g)
    (hor : g.op = GateOp.or) (t : ℕ) (ht : t ∈ g.inputs)
    (hsat : ∃ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true)
    (himp : ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true →
      circuitFun n D x = true)
    (hkT : k ∉ T) :
    ∃ D1 : Circuit, ∃ T1 : Finset ℕ, Monotone2 D1 ∧ ReadsBack n D1 ∧
      (∀ g ∈ D1.gates, g.inputs.length = 2) ∧
      D1.gates.length = D.gates.length ∧ circuitFun n D1 = circuitFun n D ∧
      PA D1 T1 ∧ PB n D1 T1 ∧ T1.card = T.card + 1 ∧
      (junk G D1).card = (junk G D).card := by
  exact lift_step_AO_preserving n D T (fun E => (junk G E).card = (junk G D).card)
    hM hR hL2 hA hB k g hkg hor t ht hsat himp hkT
    (fun u hu hequ hout => HoistDirty.junk_card_equiv G D k u t g hR hkg hor hu ht hequ
      hout hfun (fun x hx => by rw [← hfun]; exact himp x hx))

lemma main_AO (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ∀ m (D : Circuit) (T : Finset ℕ), 2 * D.gates.length - T.card = m →
    PEqualNP.TopForm.IsAO2 n D → circuitFun n D = graphFun G ∅ → PA D T → PB n D T →
    ∃ D' : Circuit, PEqualNP.TopForm.IsAO2 n D' ∧ D'.gates.length = D.gates.length ∧
      circuitFun n D' = circuitFun n D ∧ (junk G D').card = (junk G D).card ∧ ∃ T' : Finset ℕ, PA D' T' ∧ PB n D' T' ∧ PC n D' T' := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro D T hm hAO hfun hA hB
  by_cases hC : PC n D T
  · exact ⟨D, hAO, rfl, rfl, rfl, T, hA, hB, hC⟩
  · unfold PC at hC
    push Not at hC
    obtain ⟨k, g, hkg, hor, t, ht, hsat, himp, hkT⟩ := hC
    obtain ⟨D1, T1, hM1, hR1, hL1, hl1, hf1, hA1, hB1, hc1, hj1⟩ :=
      lift_step_AO n G D T (mono_of_AO2 n D hAO) hAO.2.1 hAO.2.2 hfun hA hB k g hkg hor t ht hsat
        himp hkT
    have hk : k < D.gates.length := (List.getElem?_eq_some_iff.mp hkg).1
    have hTc : T.card ≤ D.gates.length := by
      have hsub : T ⊆ Finset.range D.gates.length := fun j hj => by
        obtain ⟨g', hg', _⟩ := hA j hj
        simpa using (List.getElem?_eq_some_iff.mp hg').1
      simpa using Finset.card_le_card hsub
    obtain ⟨D', hAO', hs', hf', hj', T', hT'⟩ :=
      ih (2 * D1.gates.length - T1.card) (by omega) D1 T1 rfl (AO2_of n D1 hM1 hR1 hL1) (hf1.trans hfun) hA1 hB1
    exact ⟨D', hAO', hs'.trans hl1, hf'.trans hf1, hj'.trans hj1, T', hT'⟩


lemma same_minimum_junk_normal_form (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) :
    ∃ D : Circuit, IsLeastAO G D ∧ D.size = C.size ∧
      circuitFun n D = circuitFun n C ∧ (junk G D).card = (junk G C).card ∧
      ∃ T : Finset ℕ, PA D T ∧ PB n D T ∧ PC n D T ∧
      PEqualNP.Core.IsLiftFixedPoint G D ∧ TopForm G D ∧
      (∀ k < D.gates.length, (gateAt D k).op = GateOp.and → ∀ t ∈ (gateAt D k).inputs,
        ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) = true →
          graphFun G ∅ x = true)) := by
  obtain ⟨D, hAO, hlen, hfun, hjunk, T, hA, hB, hPC⟩ :=
    main_AO n G (2 * C.gates.length) C ∅ (by simp) hC.1 hC.2.1
      (by simp [PA]) (by simp [PB])
  have hD : IsLeastAO G D := by
    refine ⟨hAO, hfun.trans hC.2.1, ?_⟩
    intro E hE hEF
    have hmin := hC.2.2 E hE hEF
    simpa only [Circuit.size, hlen] using hmin
  exact ⟨D, hD, hlen, hfun, hjunk, T, hA, hB, hPC,
    NormalizerFixed.fixed_of_PABC G D T hD.1 hD.2.1 hA hB hPC,
    NormalizedTopForm.topForm_of_normalized_least G D T hD hA hB hPC,
    Normalization.noAndBelow_unconditional n G D hD⟩

end NormalizerJunk

namespace JunkMinimum

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

def IsJunkLeastAO {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Prop :=
  IsLeastAO G C ∧ ∀ D : Circuit, IsLeastAO G D →
    (junk G C).card ≤ (junk G D).card

lemma exists_junk_least_ao {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C0 : Circuit) (hC0 : IsLeastAO G C0) :
    ∃ C : Circuit, IsJunkLeastAO G C := by
  classical
  have hex : ∃ k : ℕ, ∃ C : Circuit,
      IsLeastAO G C ∧ (junk G C).card = k :=
    ⟨(junk G C0).card, C0, hC0, rfl⟩
  obtain ⟨C, hC, hcount⟩ := Nat.find_spec hex
  refine ⟨C, hC, ?_⟩
  intro D hD
  rw [hcount]
  exact Nat.find_min' hex ⟨D, hD, rfl⟩

end JunkMinimum

namespace NormalizedJunkMinimum

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover Normalization.LiftFix

/-- Global junk minimality and all normalization conclusions on the same circuit. -/
def IsNormalizedJunkLeastAO {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Prop :=
  JunkMinimum.IsJunkLeastAO G C ∧ ∃ T : Finset ℕ,
    PA C T ∧ PB n C T ∧ PC n C T ∧ PEqualNP.Core.IsLiftFixedPoint G C ∧
    TopForm G C ∧
    (∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ∀ t ∈ (gateAt C k).inputs,
      ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true →
        graphFun G ∅ x = true))

lemma exists_normalized_junk_least {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsLeastAO G C) :
    ∃ D : Circuit, IsNormalizedJunkLeastAO G D ∧ D.size = C.size ∧
      circuitFun n D = circuitFun n C := by
  obtain ⟨A, hA⟩ := JunkMinimum.exists_junk_least_ao G C hC
  obtain ⟨D, hD, hsize, hfun, hjunk, T, hPA, hPB, hPC, hfixed, htop, hbelow⟩ :=
    NormalizerJunk.same_minimum_junk_normal_form n G A hA.1
  have hJD : JunkMinimum.IsJunkLeastAO G D := by
    refine ⟨hD, ?_⟩
    intro E hE
    rw [hjunk]
    exact hA.2 E hE
  have hAC : A.size = C.size := Nat.le_antisymm
    (hA.1.2.2 C hC.1 hC.2.1) (hC.2.2 A hA.1.1 hA.1.2.1)
  exact ⟨D, ⟨hJD, T, hPA, hPB, hPC, hfixed, htop, hbelow⟩,
    hsize.trans hAC, hD.2.1.trans hC.2.1.symm⟩

lemma peel_of_normalized_junk_least {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hpos : ∃ z : Fin n, 0 < G.degree z)
    (h : ∀ C : Circuit, IsNormalizedJunkLeastAO G C →
      ∃ z : Fin n, 0 < G.degree z ∧ CutWitness G z C) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun G ∅ → CutWitness G z C := by
  apply peel_of_least G hpos
  intro C hC
  obtain ⟨D, hD, hsize, _⟩ := exists_normalized_junk_least G C hC
  obtain ⟨z, hz, hcut⟩ := h D hD
  exact ⟨z, hz, cutWitness_mono G z D C hsize.le hcut⟩

end NormalizedJunkMinimum


namespace NormalizerInvariant

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover Normalization.LiftFix

def StepPreserves (n : ℕ) (P : Circuit → Prop) : Prop :=
  ∀ (D : Circuit) (T : Finset ℕ), IsAO2 n D → PA D T → PB n D T → P D →
    ¬ PC n D T → ∃ (D1 : Circuit) (T1 : Finset ℕ),
      IsAO2 n D1 ∧ D1.gates.length = D.gates.length ∧
      circuitFun n D1 = circuitFun n D ∧ PA D1 T1 ∧ PB n D1 T1 ∧
      T1.card = T.card + 1 ∧ P D1

lemma main {n : ℕ} (P : Circuit → Prop) (hstep : StepPreserves n P) :
    ∀ m (D : Circuit) (T : Finset ℕ), D.gates.length - T.card = m →
      IsAO2 n D → PA D T → PB n D T → P D →
      ∃ (D' : Circuit) (T' : Finset ℕ), IsAO2 n D' ∧
        D'.gates.length = D.gates.length ∧ circuitFun n D' = circuitFun n D ∧
        PA D' T' ∧ PB n D' T' ∧ PC n D' T' ∧ P D' := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro D T hm hAO hA hB hP
    by_cases hPC : PC n D T
    · exact ⟨D, T, hAO, rfl, rfl, hA, hB, hPC, hP⟩
    · obtain ⟨D1, T1, hAO1, hl1, hf1, hA1, hB1, hc1, hP1⟩ :=
        hstep D T hAO hA hB hP hPC
      have hbound : T1.card ≤ D1.gates.length := by
        have hsub : T1 ⊆ Finset.range D1.gates.length := by
          intro j hj
          obtain ⟨g, hg, _⟩ := hA1 j hj
          simpa using (List.getElem?_eq_some_iff.mp hg).1
        simpa using Finset.card_le_card hsub
      obtain ⟨D', T', hAO', hl', hf', hA', hB', hPC', hP'⟩ :=
        ih (D1.gates.length - T1.card) (by omega) D1 T1 rfl hAO1 hA1 hB1 hP1
      exact ⟨D', T', hAO', hl'.trans hl1, hf'.trans hf1, hA', hB', hPC', hP'⟩

lemma normalize {n : ℕ} (P : Circuit → Prop) (hstep : StepPreserves n P)
    (C : Circuit) (hAO : IsAO2 n C) (hP : P C) :
    ∃ (D : Circuit) (T : Finset ℕ), IsAO2 n D ∧ D.size = C.size ∧
      circuitFun n D = circuitFun n C ∧ PA D T ∧ PB n D T ∧ PC n D T ∧ P D := by
  exact main P hstep C.gates.length C ∅ (by simp) hAO
    (by simp [PA]) (by simp [PB]) hP

lemma normalize_least {n : ℕ} (P : Circuit → Prop) (hstep : StepPreserves n P)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hC : IsLeastAO G C) (hP : P C) :
    ∃ (D : Circuit) (T : Finset ℕ), IsLeastAO G D ∧ D.size = C.size ∧
      circuitFun n D = circuitFun n C ∧ PA D T ∧ PB n D T ∧ PC n D T ∧ P D ∧
      PEqualNP.Core.IsLiftFixedPoint G D ∧ TopForm G D ∧
      (∀ k < D.gates.length, (gateAt D k).op = GateOp.and → ∀ t ∈ (gateAt D k).inputs,
        ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) = true →
          graphFun G ∅ x = true)) := by
  obtain ⟨D, T, hAO, hs, hf, hA, hB, hPC, hPD⟩ := normalize P hstep C hC.1 hP
  have hD : IsLeastAO G D := by
    refine ⟨hAO, hf.trans hC.2.1, ?_⟩
    intro E hE hEF
    rw [hs]
    exact hC.2.2 E hE hEF
  exact ⟨D, T, hD, hs, hf, hA, hB, hPC, hPD,
    NormalizerFixed.fixed_of_PABC G D T hD.1 hD.2.1 hA hB hPC,
    NormalizedTopForm.topForm_of_normalized_least G D T hD hA hB hPC,
    Normalization.noAndBelow_unconditional n G D hD⟩

end NormalizerInvariant

namespace AO2Upper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]


end AO2Upper

namespace EdgeProfile

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma eq_of_edges_and_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (F : (Fin n → Bool) → Bool)
    (hMono : ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      F x = true → F y = true)
    (hBelow : ∀ x, F x = true → graphFun G ∅ x = true)
    (hEdges : ∀ a b : Fin n, G.Adj a b → F (pairInput a b) = true) :
    F = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact hBelow x
  · intro hx
    have hx' : ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true := by
      simpa [graphFun] using hx
    obtain ⟨a, b, hab, ha, hb⟩ := hx'
    apply hMono (pairInput a b) x _ (hEdges a b hab)
    intro i hi
    have h : i = a ∨ i = b := by simpa [pairInput] using hi
    rcases h with rfl | rfl <;> assumption


end EdgeProfile

namespace SharedRewrite

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  exact AO2Upper.length_wiresFrom gs w

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  exact AO2Upper.getD_wiresFrom gs w i hi

lemma stepWire_getD_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (stepWire w g).getD i false = w.getD i false := by
  simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma stepWire_getD_len (w : List Bool) (g : Gate) :
    (stepWire w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [stepWire, List.getD_eq_getElem?_getD]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs.take j = pre ∧ gs.drop (j + 1) = post ∧
        gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl, rfl, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma bool_and_rel {a b c d : Bool} (hab : a ≤ b) (hcd : c ≤ d) :
    (a && c) ≤ (b && d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

lemma bool_or_rel {a b c d : Bool} (hab : a ≤ b) (hcd : c ≤ d) :
    (a || c) ≤ (b || d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

lemma ao_eval_mono (g : Gate) (hao : g.op = GateOp.and ∨ g.op = GateOp.or)
    (f h : ℕ → Bool) (hfh : ∀ u, f u ≤ h u) :
    g.op.eval (g.inputs.map f) ≤ g.op.eval (g.inputs.map h) := by
  obtain ⟨op, inputs⟩ := g
  rcases hao with rfl | rfl
  · simp only [GateOp.eval]
    induction inputs with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.all_cons, id_eq]
      exact bool_and_rel (hfh a) ih
  · simp only [GateOp.eval]
    induction inputs with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.any_cons, id_eq]
      exact bool_or_rel (hfh a) ih

def replace (C : Circuit) (j : ℕ) (g : Gate) : Circuit :=
  ⟨C.gates.set j g, C.output⟩

lemma replace_size (C : Circuit) (j : ℕ) (g : Gate) : (replace C j g).size = C.size := by
  simp [replace, Circuit.size]

lemma replace_gateAt (C : Circuit) (j : ℕ) (g : Gate) (hj : j < C.gates.length) (k : ℕ) :
    gateAt (replace C j g) k = if j = k then g else gateAt C k := by
  simp only [gateAt, replace, List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs with he
  · simp
  · rfl

lemma replace_ao {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hgop : g.op = GateOp.and ∨ g.op = GateOp.or) (hglen : g.inputs.length = 2)
    (hgback : ∀ i ∈ g.inputs, i < n + j) : IsAO2 n (replace C j g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h hh
    change h ∈ C.gates.set j g at hh
    rw [List.set_eq_take_cons_drop g hj] at hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hAO.1 _ (List.mem_of_mem_take hh)
    · rcases List.mem_cons.mp hh with rfl | hh
      · exact hgop
      · exact hAO.1 _ (List.mem_of_mem_drop hh)
  · intro k hk i hi
    have hk' : k < C.gates.length := by simpa [replace] using hk
    rw [replace_gateAt C j g hj k] at hi
    by_cases he : j = k
    · subst k
      simp only [ite_true] at hi
      exact hgback i hi
    · rw [ite_eq_right he] at hi
      exact hAO.2.1 k hk' i hi
  · intro h hh
    change h ∈ C.gates.set j g at hh
    rw [List.set_eq_take_cons_drop g hj] at hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hAO.2.2 _ (List.mem_of_mem_take hh)
    · rcases List.mem_cons.mp hh with rfl | hh
      · exact hglen
      · exact hAO.2.2 _ (List.mem_of_mem_drop hh)

lemma step_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b)
    (a b : List Bool) (hlen : a.length = b.length) (g h : Gate)
    (hab : ∀ i, R (a.getD i false) (b.getD i false))
    (hval : R (g.op.eval (g.inputs.map fun i => a.getD i false))
      (h.op.eval (h.inputs.map fun i => b.getD i false))) :
    ∀ i, R ((stepWire a g).getD i false) ((stepWire b h).getD i false) := by
  intro i
  by_cases hi : i < a.length
  · rw [stepWire_getD_lt _ _ _ hi, stepWire_getD_lt _ _ _ (by omega)]
    exact hab i
  · by_cases he : i = a.length
    · rw [he, stepWire_getD_len, hlen, stepWire_getD_len]
      exact hval
    · rw [getD_ge_length _ _ (by simp [stepWire]; omega),
        getD_ge_length _ _ (by simp [stepWire]; omega)]
      exact hrefl false

lemma foldl_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b)
    (gs : List Gate)
    (hmono : ∀ g ∈ gs, ∀ (f h : ℕ → Bool), (∀ i, R (f i) (h i)) →
      R (g.op.eval (g.inputs.map f)) (g.op.eval (g.inputs.map h)))
    (a b : List Bool) (hlen : a.length = b.length)
    (hab : ∀ i, R (a.getD i false) (b.getD i false)) :
    ∀ i, R ((gs.foldl stepWire a).getD i false) ((gs.foldl stepWire b).getD i false) := by
  induction gs generalizing a b with
  | nil => exact hab
  | cons g gs ih =>
    simp only [List.foldl_cons]
    exact ih (fun g hg => hmono g (by simp [hg]))
      (stepWire a g) (stepWire b g) (by simp [stepWire, hlen])
      (step_rel hrefl a b hlen g g hab (hmono g (by simp) _ _ hab))

lemma replace_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b)
    (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hgback : ∀ i ∈ g.inputs, i < n + j)
    (hmono : ∀ g ∈ C.gates, ∀ (f h : ℕ → Bool), (∀ i, R (f i) (h i)) →
      R (g.op.eval (g.inputs.map f)) (g.op.eval (g.inputs.map h)))
    (x : Fin n → Bool)
    (hx : R ((C.wires (List.ofFn x)).getD (n + j) false)
      (g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false))) :
    R (circuitFun n C x) (circuitFun n (replace C j g) x) := by
  obtain ⟨pre, post, old, hgs, hpre_len, htake, hdrop, _⟩ := split_gates C.gates j hj
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0 : w0.length = n + j := by
    dsimp [w0]
    rw [foldl_stepWire_length, List.length_ofFn, hpre_len]
  have hpre : ∀ i, i < n + j →
      (C.wires (List.ofFn x)).getD i false = w0.getD i false := by
    intro i hi
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons,
      foldl_stepWire_getD_lt _ _ _ (by change i < (stepWire w0 old).length; simp [stepWire, hw0]; omega),
      stepWire_getD_lt _ _ _ (by change i < w0.length; omega)]
  have hm : g.inputs.map (fun i => (C.wires (List.ofFn x)).getD i false) =
      g.inputs.map (fun i => w0.getD i false) := by
    apply List.map_congr_left
    intro i hi
    exact hpre i (hgback i hi)
  rw [hm, wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons,
    foldl_stepWire_getD_lt _ _ _ (by change n+j < (stepWire w0 old).length; simp [stepWire, hw0])] at hx
  have hx2 := stepWire_getD_len w0 old
  rw [hw0] at hx2
  rw [hx2] at hx
  have start := step_rel hrefl w0 w0 rfl old g (fun _ => hrefl _) hx
  have result := foldl_rel hrefl post
    (fun h hh => hmono h (hgs ▸ by simp [hh]))
    (stepWire w0 old) (stepWire w0 g) (by simp [stepWire]) start C.output
  simp only [circuitFun, Circuit.eval, replace, wires_eq_foldl]
  rw [List.set_eq_take_cons_drop g hj, htake, hdrop, hgs,
    List.foldl_append, List.foldl_cons, List.foldl_append, List.foldl_cons]
  exact result

lemma replace_le (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hgback : ∀ i ∈ g.inputs, i < n + j) (hAO : AndOrOnly C) (x : Fin n → Bool)
    (hx : (C.wires (List.ofFn x)).getD (n + j) false ≤
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false)) :
    circuitFun n C x ≤ circuitFun n (replace C j g) x :=
  replace_rel (fun _ => le_refl _) n C j hj g hgback
    (fun h hh => ao_eval_mono h (hAO h hh)) x hx

lemma replace_ge (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hgback : ∀ i ∈ g.inputs, i < n + j) (hAO : AndOrOnly C) (x : Fin n → Bool)
    (hx : g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) ≤
      (C.wires (List.ofFn x)).getD (n + j) false) :
    circuitFun n (replace C j g) x ≤ circuitFun n C x :=
  replace_rel (R := fun a b => b ≤ a) (fun _ => le_refl _) n C j hj g hgback
    (fun h hh f k hfk => ao_eval_mono h (hAO h hh) k f hfk) x hx

lemma circuitFun_monotone (n : ℕ) (C : Circuit) (hao : AndOrOnly C) :
    Monotone (circuitFun n C) := by
  intro x y hxy
  apply foldl_rel (R := fun a b => a ≤ b) (fun _ => le_refl _) C.gates
    (fun g hg => ao_eval_mono g (hao g hg)) (List.ofFn x) (List.ofFn y) (by simp)
  intro u
  by_cases hu : u < n
  · rw [List.getD_eq_getElem _ _ (by simpa), List.getD_eq_getElem _ _ (by simpa)]
    simpa using hxy ⟨u, hu⟩
  · rw [getD_ge_length _ _ (by simpa using Nat.le_of_not_gt hu),
      getD_ge_length _ _ (by simpa using Nat.le_of_not_gt hu)]

lemma correct_of_edge_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hgop : g.op = GateOp.and ∨ g.op = GateOp.or) (hglen : g.inputs.length = 2)
    (hgback : ∀ i ∈ g.inputs, i < n + j)
    (hpos : ∀ u v, G.Adj u v →
      (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD (n + j) false = true →
      g.op.eval (g.inputs.map fun i =>
        (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD i false) = true)
    (hclean : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) = true →
      graphFun G ∅ x = true) :
    IsAO2 n (replace C j g) ∧ circuitFun n (replace C j g) = graphFun G ∅ ∧
      (replace C j g).size = C.size := by
  have hd := replace_ao C hAO j hj g hgop hglen hgback
  refine ⟨hd, ?_, replace_size C j g⟩
  apply EdgeProfile.eq_of_edges_and_below G _
  · intro x y hxy hx
    exact Bool.le_iff_imp.mp
      (circuitFun_monotone n _ hd.1 (fun i => Bool.le_iff_imp.mpr (hxy i))) hx
  · intro x hx
    by_contra hG
    have hfalse : g.op.eval (g.inputs.map fun i =>
        (C.wires (List.ofFn x)).getD i false) = false := by
      apply Bool.eq_false_iff.mpr
      exact fun ht => hG (hclean x ht)
    have hle := replace_ge n C j hj g hgback hAO.1 x
      (by rw [hfalse]; exact Bool.false_le _)
    have ht := Bool.le_iff_imp.mp hle hx
    rw [hfun] at ht
    exact hG ht
  · intro u v huv
    apply Bool.le_iff_imp.mp (replace_le n C j hj g hgback hAO.1 _
      (Bool.le_iff_imp.mpr (hpos u v huv)))
    rw [hfun]
    have hp : ∃ a b, G.Adj a b ∧ pairInput u v a = true ∧ pairInput u v b = true :=
      ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
    simpa [graphFun] using hp

lemma input_val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    (C.wires (List.ofFn x)).getD u.val false = x u := by
  rw [wires_eq_foldl, foldl_stepWire_getD_lt _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

end SharedRewrite

namespace JunkNormalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma mem_junk_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k : ℕ) :
    k ∈ junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C k x = true ∧ graphFun G ∅ x = false := by
  change k ∈ (Finset.range C.gates.length).filter (fun i => IsDirtyAnd n G C i) ↔ _
  rw [Finset.mem_filter, Finset.mem_range]
  simp only [IsDirtyAnd, IsDirty]
  constructor
  · rintro ⟨hk, hop, _, h⟩
    exact ⟨hk, hop, h⟩
  · rintro ⟨hk, hop, h⟩
    exact ⟨hk, hop, hk, h⟩

lemma gateVal_le_of_replace (n : ℕ) (C : Circuit) (hAO : AndOrOnly C)
    (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hgback : ∀ i ∈ g.inputs, i < n + j)
    (hDown : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) ≤
        (C.wires (List.ofFn x)).getD (n + j) false)
    (k : ℕ) (x : Fin n → Bool) :
    gateVal n (SharedRewrite.replace C j g) k x ≤ gateVal n C k x := by
  exact SharedRewrite.replace_ge n ⟨C.gates, n + k⟩ j hj g hgback hAO x (hDown x)

lemma junk_subset_of_replace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : AndOrOnly C)
    (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hop : g.op = (gateAt C j).op)
    (hgback : ∀ i ∈ g.inputs, i < n + j)
    (hDown : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) ≤
        (C.wires (List.ofFn x)).getD (n + j) false) :
    junk G (SharedRewrite.replace C j g) ⊆ junk G C := by
  intro k hk
  obtain ⟨hk, hkop, x, hv, hFalse⟩ := (mem_junk_iff G _ k).mp hk
  have hk' : k < C.gates.length := by simpa [SharedRewrite.replace] using hk
  have hsame : (gateAt (SharedRewrite.replace C j g) k).op = (gateAt C k).op := by
    rw [SharedRewrite.replace_gateAt C j g hj k]
    split_ifs with h
    · subst k
      exact hop
    · rfl
  have hv' := Bool.le_iff_imp.mp (gateVal_le_of_replace n C hAO j hj g hgback hDown k x) hv
  exact (mem_junk_iff G C k).mpr ⟨hk', hsame ▸ hkop, x, hv', hFalse⟩

lemma junk_card_lt_of_replace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : AndOrOnly C)
    (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hop : g.op = (gateAt C j).op)
    (hgback : ∀ i ∈ g.inputs, i < n + j)
    (hDown : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) ≤
        (C.wires (List.ofFn x)).getD (n + j) false)
    (hDirty : j ∈ junk G C)
    (hClean : BelowF G (SharedRewrite.replace C j g) j) :
    (junk G (SharedRewrite.replace C j g)).card < (junk G C).card := by
  classical
  have hsub := junk_subset_of_replace G C hAO j hj g hop hgback hDown
  have hjnot : j ∉ junk G (SharedRewrite.replace C j g) := by
    intro hjmem
    obtain ⟨_, _, x, hv, hf⟩ := (mem_junk_iff G _ j).mp hjmem
    have ht := hClean x hv
    rw [hf] at ht
    exact Bool.false_ne_true ht
  have hstrict : junk G (SharedRewrite.replace C j g) ⊂ junk G C := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hsub, ?_⟩
    intro heq
    rw [heq] at hjnot
    exact hjnot hDirty
  exact Finset.card_lt_card hstrict

lemma edge_gate_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (w u : Fin n) (hwu : G.Adj w u) :
    BelowF G (SharedRewrite.replace C j ⟨GateOp.and, [w.val, u.val]⟩) j := by
  let D := SharedRewrite.replace C j ⟨GateOp.and, [w.val, u.val]⟩
  have hD : IsAO2 n D := SharedRewrite.replace_ao C hC j hj _ (Or.inl rfl) rfl (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl <;> omega)
  have hjD : j < D.gates.length := by simpa [D, SharedRewrite.replace] using hj
  have hgate : gateAt D j = ⟨GateOp.and, [w.val, u.val]⟩ := by
    simp [D, SharedRewrite.replace_gateAt C j _ hj j]
  intro x hx
  have heq := ProofWire.gate_value D hD j hjD x
  simp only [hgate, opnd, if_pos rfl] at heq
  have hVal : gateVal n D j x = (x w && x u) := by
    change gateVal n D j x = ((D.wires (List.ofFn x)).getD w.val false &&
      (D.wires (List.ofFn x)).getD u.val false) at heq
    rw [SharedRewrite.input_val, SharedRewrite.input_val] at heq
    exact heq
  rw [hVal] at hx
  have hx' : x w = true ∧ x u = true := by simpa using hx
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq]
  exact ⟨w, u, hwu, hx'.1, hx'.2⟩

end JunkNormalize

namespace JunkNormalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma junk_subset_of_clean_replace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : AndOrOnly C) (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hop : g.op = (gateAt C j).op) (hgback : ∀ i ∈ g.inputs, i < n + j)
    (hClean : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) = true →
        graphFun G ∅ x = true) :
    junk G (SharedRewrite.replace C j g) ⊆ junk G C := by
  intro k hk
  obtain ⟨hk, hkop, x, hv, hFalse⟩ := (mem_junk_iff G _ k).mp hk
  have hk' : k < C.gates.length := by simpa [SharedRewrite.replace] using hk
  have hsame : (gateAt (SharedRewrite.replace C j g) k).op = (gateAt C k).op := by
    rw [SharedRewrite.replace_gateAt C j g hj k]
    split_ifs with h
    · subst k
      exact hop
    · rfl
  have hzero : g.op.eval (g.inputs.map fun i =>
      (C.wires (List.ofFn x)).getD i false) = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    have hF := hClean x ht
    rw [hFalse] at hF
    exact Bool.false_ne_true hF
  have hle : gateVal n (SharedRewrite.replace C j g) k x ≤ gateVal n C k x :=
    SharedRewrite.replace_ge n ⟨C.gates, n + k⟩ j hj g hgback hAO x
      (by change g.op.eval (g.inputs.map fun i =>
            (C.wires (List.ofFn x)).getD i false) ≤ _
          rw [hzero]
          exact Bool.false_le _)
  exact (mem_junk_iff G C k).mpr
    ⟨hk', hsame ▸ hkop, x, Bool.le_iff_imp.mp hle hv, hFalse⟩

lemma junk_card_lt_of_clean_replace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : AndOrOnly C) (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hop : g.op = (gateAt C j).op) (hgback : ∀ i ∈ g.inputs, i < n + j)
    (hClean : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) = true →
        graphFun G ∅ x = true)
    (hDirty : j ∈ junk G C)
    (hNewClean : BelowF G (SharedRewrite.replace C j g) j) :
    (junk G (SharedRewrite.replace C j g)).card < (junk G C).card := by
  have hsub := junk_subset_of_clean_replace G C hAO j hj g hop hgback hClean
  have hjnot : j ∉ junk G (SharedRewrite.replace C j g) := by
    intro hjmem
    obtain ⟨_, _, x, hv, hf⟩ := (mem_junk_iff G _ j).mp hjmem
    have ht := hNewClean x hv
    rw [hf] at ht
    exact Bool.false_ne_true ht
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hsub, ?_⟩
  intro heq
  rw [heq] at hjnot
  exact hjnot hDirty


end JunkNormalize

namespace JunkPivotal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

def disable (C : Circuit) (j : ℕ) : Circuit :=
  SharedRewrite.replace C j ⟨GateOp.or, []⟩

def pivotal {n : ℕ} (C : Circuit) (j : ℕ) (a b : Fin n) : Prop :=
  circuitFun n (disable C j) (pairInput a b) = false

lemma disable_andOr (C : Circuit) (hAO : AndOrOnly C) (j : ℕ) :
    AndOrOnly (disable C j) := by
  intro g hg
  change g ∈ C.gates.set j ⟨GateOp.or, []⟩ at hg
  rcases List.mem_or_eq_of_mem_set hg with hg | rfl
  · exact hAO g hg
  · exact Or.inr rfl

lemma disable_gate_false (n : ℕ) (C : Circuit) (j : ℕ)
    (hj : j < C.gates.length) (x : Fin n → Bool) :
    gateVal n (disable C j) j x = false := by
  let w0 := (C.gates.take j).foldl SharedRewrite.stepWire (List.ofFn x)
  have hlen : w0.length = n + j := by
    rw [SharedRewrite.foldl_stepWire_length]
    simp [Nat.min_eq_left (Nat.le_of_lt hj)]
  change ((C.gates.set j ⟨GateOp.or, []⟩).foldl SharedRewrite.stepWire
    (List.ofFn x)).getD (n + j) false = false
  rw [List.set_eq_take_cons_drop _ hj, List.foldl_append, List.foldl_cons]
  change ((C.gates.drop (j + 1)).foldl SharedRewrite.stepWire
    (SharedRewrite.stepWire w0 ⟨GateOp.or, []⟩)).getD (n + j) false = false
  rw [SharedRewrite.foldl_stepWire_getD_lt _ _ _ (by
    simp [SharedRewrite.stepWire, hlen])]
  rw [← hlen, SharedRewrite.stepWire_getD_len]
  rfl

lemma replace_disable (C : Circuit) (j : ℕ) (g : Gate) :
    SharedRewrite.replace (disable C j) j g = SharedRewrite.replace C j g := by
  simp only [disable, SharedRewrite.replace, List.set_set]

lemma disable_le_replace (n : ℕ) (C : Circuit) (hAO : AndOrOnly C)
    (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hgback : ∀ i ∈ g.inputs, i < n + j) (x : Fin n → Bool) :
    circuitFun n (disable C j) x ≤ circuitFun n (SharedRewrite.replace C j g) x := by
  have hjD : j < (disable C j).gates.length := by
    simpa [disable, SharedRewrite.replace] using hj
  have hle := SharedRewrite.replace_le n (disable C j) j hjD g hgback
    (disable_andOr C hAO j) x (by
      change gateVal n (disable C j) j x ≤ _
      rw [disable_gate_false n C j hj x]
      exact Bool.false_le _)
  simpa only [replace_disable] using hle

end JunkPivotal

namespace JunkPivotal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma correct_of_pivotal_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hFun : circuitFun n C = graphFun G ∅)
    (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hgop : g.op = GateOp.and ∨ g.op = GateOp.or) (hglen : g.inputs.length = 2)
    (hgback : ∀ i ∈ g.inputs, i < n + j)
    (hPos : ∀ a b : Fin n, G.Adj a b → pivotal C j a b →
      g.op.eval (g.inputs.map fun i =>
        (C.wires (List.ofFn (pairInput a b))).getD i false) = true)
    (hClean : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) = true →
        graphFun G ∅ x = true) :
    IsAO2 n (SharedRewrite.replace C j g) ∧
      circuitFun n (SharedRewrite.replace C j g) = graphFun G ∅ ∧
      (SharedRewrite.replace C j g).size = C.size := by
  classical
  have hD := SharedRewrite.replace_ao C hAO j hj g hgop hglen hgback
  refine ⟨hD, ?_, SharedRewrite.replace_size C j g⟩
  apply EdgeProfile.eq_of_edges_and_below G _
  · intro x y hxy hx
    exact Bool.le_iff_imp.mp
      (SharedRewrite.circuitFun_monotone n _ hD.1 (fun i => Bool.le_iff_imp.mpr (hxy i))) hx
  · intro x hx
    by_contra hG
    have hzero : g.op.eval (g.inputs.map fun i =>
        (C.wires (List.ofFn x)).getD i false) = false := by
      apply Bool.eq_false_iff.mpr
      exact fun ht => hG (hClean x ht)
    have hle := SharedRewrite.replace_ge n C j hj g hgback hAO.1 x
      (by rw [hzero]; exact Bool.false_le _)
    have ht := Bool.le_iff_imp.mp hle hx
    rw [hFun] at ht
    exact hG ht
  · intro a b hab
    by_cases hp : pivotal C j a b
    · have hnew := hPos a b hab hp
      apply Bool.le_iff_imp.mp (SharedRewrite.replace_le n C j hj g hgback hAO.1
        (pairInput a b) (by rw [hnew]; exact Bool.le_true _))
      rw [hFun]
      have he : ∃ u v : Fin n, G.Adj u v ∧ pairInput a b u = true ∧ pairInput a b v = true :=
        ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩
      simpa [graphFun] using he
    · have hdisabled : circuitFun n (disable C j) (pairInput a b) = true :=
        Bool.eq_true_of_not_eq_false hp
      exact Bool.le_iff_imp.mp (disable_le_replace n C hAO.1 j hj g hgback (pairInput a b))
        hdisabled

lemma pivotal_on {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hFun : circuitFun n C = graphFun G ∅)
    (j : ℕ) (hj : j < C.gates.length) (a b : Fin n) (hab : G.Adj a b)
    (hp : pivotal C j a b) : gateVal n C j (pairInput a b) = true := by
  cases hv : gateVal n C j (pairInput a b) with
  | true => rfl
  | false =>
    have hle := SharedRewrite.replace_le n C j hj ⟨GateOp.or, []⟩ (by simp)
      hAO.1 (pairInput a b) (by
        change gateVal n C j (pairInput a b) ≤ false
        rw [hv])
    have hold : circuitFun n C (pairInput a b) = true := by
      rw [hFun]
      have he : ∃ u v : Fin n, G.Adj u v ∧ pairInput a b u = true ∧ pairInput a b v = true :=
        ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩
      simpa [graphFun] using he
    have hd := Bool.le_iff_imp.mp hle hold
    change circuitFun n (disable C j) (pairInput a b) = true at hd
    rw [hp] at hd
    exact False.elim (Bool.false_ne_true hd)

lemma one_pivotal_edge_not_dirty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : JunkMinimum.IsJunkLeastAO G C)
    (j : ℕ) (hj : j < C.gates.length) (w u : Fin n) (hwu : G.Adj w u)
    (hKeep : ∀ a b : Fin n, G.Adj a b → pivotal C j a b →
      (pairInput a b w && pairInput a b u) = true) :
    j ∉ junk G C := by
  intro hDirty
  have hOldOp := ((JunkNormalize.mem_junk_iff G C j).mp hDirty).2.1
  have hBack : ∀ i ∈ [w.val, u.val], i < n + j := by
    intro i hi
    simp at hi
    rcases hi with rfl | rfl <;> omega
  have hEval : ∀ x : Fin n → Bool,
      GateOp.and.eval ([w.val, u.val].map fun i =>
        (C.wires (List.ofFn x)).getD i false) = (x w && x u) := by
    intro x
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
    rw [SharedRewrite.input_val, SharedRewrite.input_val]
  have hClean : ∀ x : Fin n → Bool,
      GateOp.and.eval ([w.val, u.val].map fun i =>
        (C.wires (List.ofFn x)).getD i false) = true → graphFun G ∅ x = true := by
    intro x hx
    rw [hEval] at hx
    have hx' : x w = true ∧ x u = true := by simpa using hx
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨w, u, hwu, hx'.1, hx'.2⟩
  obtain ⟨hD, hFun, hSize⟩ := correct_of_pivotal_cover G C hC.1.1 hC.1.2.1
    j hj ⟨GateOp.and, [w.val, u.val]⟩ (Or.inl rfl) rfl hBack
    (by intro a b hab hp; rw [hEval]; exact hKeep a b hab hp) hClean
  have hLeast : IsLeastAO G (SharedRewrite.replace C j ⟨GateOp.and, [w.val, u.val]⟩) :=
    ⟨hD, hFun, fun D hD hFunD => hSize.trans_le (hC.1.2.2 D hD hFunD)⟩
  have hStrict := JunkNormalize.junk_card_lt_of_clean_replace G C hC.1.1.1 j hj
    ⟨GateOp.and, [w.val, u.val]⟩ hOldOp.symm hBack hClean hDirty
    (JunkNormalize.edge_gate_below G C hC.1.1 j hj w u hwu)
  have hMin := hC.2 _ hLeast
  omega

lemma dirty_has_two_pivotal_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hE : ∃ w u : Fin n, G.Adj w u)
    (C : Circuit) (hC : JunkMinimum.IsJunkLeastAO G C)
    (j : ℕ) (hDirty : j ∈ junk G C) :
    ∃ a b c d : Fin n, G.Adj a b ∧ G.Adj c d ∧
      pivotal C j a b ∧ pivotal C j c d ∧ s(a, b) ≠ s(c, d) := by
  classical
  have hj := ((JunkNormalize.mem_junk_iff G C j).mp hDirty).1
  by_contra hTwo
  by_cases hPivot : ∃ w u : Fin n, G.Adj w u ∧ pivotal C j w u
  · obtain ⟨w, u, hwu, hOn⟩ := hPivot
    apply one_pivotal_edge_not_dirty G C hC j hj w u hwu ?_ hDirty
    intro a b hab hp
    have heq : s(a, b) = s(w, u) := by
      by_contra hne
      exact hTwo ⟨w, u, a, b, hwu, hab, hOn, hp, fun he => hne he.symm⟩
    have hw : w ∈ s(a, b) := by rw [heq]; simp
    have hu : u ∈ s(a, b) := by rw [heq]; simp
    have hw' : pairInput a b w = true := by simpa [pairInput] using hw
    have hu' : pairInput a b u = true := by simpa [pairInput] using hu
    simp [hw', hu']
  · obtain ⟨w, u, hwu⟩ := hE
    apply one_pivotal_edge_not_dirty G C hC j hj w u hwu ?_ hDirty
    intro a b hab hp
    exact False.elim (hPivot ⟨a, b, hab, hp⟩)


end JunkPivotal

namespace NormalizedPivotal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover


def IsNormalizedJunkPivotalAO {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Prop :=
  NormalizedJunkMinimum.IsNormalizedJunkLeastAO G C ∧
    ∀ j ∈ junk G C, ∃ a b c d : Fin n, G.Adj a b ∧ G.Adj c d ∧
      JunkPivotal.pivotal C j a b ∧ JunkPivotal.pivotal C j c d ∧ s(a, b) ≠ s(c, d)

lemma normalized_has_two_pivotal_edges {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hE : ∃ a b : Fin n, G.Adj a b)
    (C : Circuit) (hC : NormalizedJunkMinimum.IsNormalizedJunkLeastAO G C) :
    IsNormalizedJunkPivotalAO G C :=
  ⟨hC, fun j hj => JunkPivotal.dirty_has_two_pivotal_edges G hE C hC.1 j hj⟩

lemma exists_normalized_junk_pivotal {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hE : ∃ a b : Fin n, G.Adj a b)
    (C : Circuit) (hC : IsLeastAO G C) :
    ∃ D : Circuit, IsNormalizedJunkPivotalAO G D ∧ D.size = C.size ∧
      circuitFun n D = circuitFun n C := by
  obtain ⟨D, hD, hsize, hfun⟩ := NormalizedJunkMinimum.exists_normalized_junk_least G C hC
  exact ⟨D, normalized_has_two_pivotal_edges G hE D hD, hsize, hfun⟩

end NormalizedPivotal


namespace SingleSlotCone

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover Normalization.LiftFix

lemma unique_read_outside (C : Circuit) (u : ℕ) (pre post : List Gate) (g : Gate)
    (hshape : C.gates = pre ++ g :: post)
    (honce : (C.gates.flatMap Gate.inputs).count u = 1) (hu : u ∈ g.inputs) :
    ∀ q ∈ pre ++ post, u ∉ q.inputs := by
  have hgpos := List.count_pos_iff.mpr hu
  have hc : (pre.flatMap Gate.inputs).count u + g.inputs.count u +
      (post.flatMap Gate.inputs).count u = 1 := by
    simpa only [hshape, List.flatMap_append, List.flatMap_cons, List.count_append,
      Nat.add_assoc] using honce
  have hz : ((pre ++ post).flatMap Gate.inputs).count u = 0 := by
    rw [List.flatMap_append, List.count_append]
    omega
  intro q hq hqu
  have hm : u ∈ (pre ++ post).flatMap Gate.inputs := List.mem_flatMap.mpr ⟨q, hq, hqu⟩
  have hp := List.count_pos_iff.mpr hm
  omega

lemma once_or_dirty_cone_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (T : Finset ℕ) (u : Fin n) (j t : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hinputs : (gateAt C j).inputs = [u.val, t] ∨
      (gateAt C j).inputs = [t, u.val])
    (honce : (C.gates.flatMap Gate.inputs).count u.val = 1)
    (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hfour : NoFourCycle G) (hA : PA C T) (hB : PB n C T) (hPC : PC n C T) :
    G.degree u ≤ (LocalizedDirty.dirtyInside G C (WireCone.backwardCone n C {t})).card + 1 := by
  have hshape : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    have h := List.take_append_drop j C.gates
    rw [List.drop_eq_getElem_cons hj] at h
    have e : C.gates[j] = gateAt C j := by simp [gateAt, List.getD_eq_getElem?_getD, hj]
    rw [e] at h
    exact h.symm
  have hu : u.val ∈ (gateAt C j).inputs := by rcases hinputs with h | h <;> simp [h]
  have htu : t ≠ u.val := by
    intro heq
    have hc : (C.gates.take j |>.flatMap Gate.inputs).count u.val +
        (gateAt C j).inputs.count u.val +
        (C.gates.drop (j + 1) |>.flatMap Gate.inputs).count u.val = 1 := by
      have hc0 := honce
      rw [hshape] at hc0
      simpa only [List.flatMap_append, List.flatMap_cons, List.count_append,
        Nat.add_assoc] using hc0
    rcases hinputs with h | h <;> simp [h, heq] at hc <;> omega
  exact NormalizedCone.sole_or_dirty_cone_bound G C T u _ _ _ t hshape hop hinputs
    hAO (unique_read_outside C u.val _ _ _ hshape honce hu) hfun hfour htu hA hB hPC

end SingleSlotCone

namespace PivotalCone

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

lemma once_or_has_pivotal_dirty_source {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (hC : NormalizedPivotal.IsNormalizedJunkPivotalAO G C)
    (hfour : NoFourCycle G) (u : Fin n) (j t : ℕ)
    (hdegree : 2 ≤ G.degree u) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or)
    (hinputs : (gateAt C j).inputs = [u.val, t] ∨
      (gateAt C j).inputs = [t, u.val])
    (honce : (C.gates.flatMap Gate.inputs).count u.val = 1) :
    ∃ k ∈ LocalizedDirty.dirtyInside G C (WireCone.backwardCone n C {t}),
      ∃ a b c d : Fin n, G.Adj a b ∧ G.Adj c d ∧
        JunkPivotal.pivotal C k a b ∧ JunkPivotal.pivotal C k c d ∧ s(a,b) ≠ s(c,d) := by
  obtain ⟨T, hA, hB, hPC, _⟩ := hC.1.2
  have hbound := SingleSlotCone.once_or_dirty_cone_bound G C T u j t hj hop hinputs
    honce hC.1.1.1.1 hC.1.1.1.2.1 hfour hA hB hPC
  have hpos : 0 < (LocalizedDirty.dirtyInside G C (WireCone.backwardCone n C {t})).card := by
    omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  exact ⟨k, hk, hC.2 k (Finset.mem_filter.mp hk).1⟩

lemma peel_of_normalized_junk_pivotal {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hpos : ∃ z : Fin n, 0 < G.degree z)
    (h : ∀ C : Circuit, NormalizedPivotal.IsNormalizedJunkPivotalAO G C →
      ∃ z : Fin n, 0 < G.degree z ∧ CutWitness G z C) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun G ∅ → CutWitness G z C := by
  apply NormalizedJunkMinimum.peel_of_normalized_junk_least G hpos
  intro C hC
  have hE : ∃ a b : Fin n, G.Adj a b := by
    obtain ⟨z, hz⟩ := hpos
    obtain ⟨v, hv⟩ := (G.degree_pos_iff_exists_adj z).mp hz
    exact ⟨z, v, hv⟩
  exact h C (NormalizedPivotal.normalized_has_two_pivotal_edges G hE C hC)

end PivotalCone

namespace NormalizerJunk

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover Normalization.LiftFix

lemma lift_step_AO_preserving_admissible (n : ℕ) (D : Circuit) (T : Finset ℕ)
    (P : Circuit → Prop) (hM : Monotone2 D) (hR : ReadsBack n D)
    (hL2 : ∀ g ∈ D.gates, g.inputs.length = 2)
    (hA : PA D T) (hB : PB n D T) (k : ℕ) (g : Gate) (hkg : D.gates[k]? = some g)
    (hor : g.op = GateOp.or) (t : ℕ) (ht : t ∈ g.inputs)
    (hsat : ∃ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true)
    (himp : ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true →
      circuitFun n D x = true)
    (hkT : k ∉ T)
    (hpres : ∀ u, u ∈ g.inputs →
      (∀ w : List Bool, GateOp.or.eval ([u, t].map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false)) →
      D.output < n + D.gates.length →
      IsAO2 n (HoistNegative.hoisted n D k u t) →
      (HoistNegative.hoisted n D k u t).size = D.size →
      circuitFun n (HoistNegative.hoisted n D k u t) = circuitFun n D →
      P (HoistNegative.hoisted n D k u t)) :
    ∃ D1 : Circuit, ∃ T1 : Finset ℕ, Monotone2 D1 ∧ ReadsBack n D1 ∧
      (∀ g ∈ D1.gates, g.inputs.length = 2) ∧
      D1.gates.length = D.gates.length ∧ circuitFun n D1 = circuitFun n D ∧
      PA D1 T1 ∧ PB n D1 T1 ∧ T1.card = T.card + 1 ∧ P D1 := by
  obtain ⟨D1, T1, hM1, hR1, hL1, hlen, hfun, hA1, hB1, hcard, hQ⟩ :=
    lift_step_AO_preserving n D T
      (fun E => IsAO2 n E → E.size = D.size → circuitFun n E = circuitFun n D → P E)
      hM hR hL2 hA hB k g hkg hor t ht hsat himp hkT hpres
  exact ⟨D1, T1, hM1, hR1, hL1, hlen, hfun, hA1, hB1, hcard,
    hQ (AO2_of n D1 hM1 hR1 hL1) hlen hfun⟩

end NormalizerJunk

end PEqualNP.Outside.L_meta_3566
