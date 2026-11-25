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

end PEqualNP.Outside.L_meta_3566
