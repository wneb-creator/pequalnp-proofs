import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448_aux.foundation

namespace M1528
namespace P1
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
namespace S98
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership
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
lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]
def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false
lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]
lemma prefix_W (n : ℕ) (pre rest1 rest2 : List Gate) (o1 o2 : ℕ) (x : Fin n → Bool) (u : ℕ)
    (hu : u < n + pre.length) :
    W n ⟨pre ++ rest1, o1⟩ x u = W n ⟨pre ++ rest2, o2⟩ x u := by
  simp only [W, wires_eq_foldl, List.foldl_append]
  have h : u < (pre.foldl stepWire (List.ofFn x)).length := by
    rw [foldl_stepWire_length]; simpa using hu
  rw [foldl_stepWire_getD_lt rest1 (pre.foldl stepWire (List.ofFn x)) u h,
    foldl_stepWire_getD_lt rest2 (pre.foldl stepWire (List.ofFn x)) u h]
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
lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a || W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]
lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a && W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]
def AO (n : ℕ) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k
end S98
end P1
end M1528
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
namespace Close
open M1528.P1.S98 (W AO W_gate W_input W_or W_and gateAt_eq prefix_W)
def orTreeGates (base : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], 0)
  | [w] => ([], w)
  | w :: ws =>
    let (gs, out) := orTreeGates base ws
    (gs ++ [⟨GateOp.or, [w, out]⟩], base + gs.length)
lemma orTreeGates_length (base : ℕ) (ws : List ℕ) (hne : ws ≠ []) :
    (orTreeGates base ws).1.length + 1 = ws.length := by
  induction ws with
  | nil => contradiction
  | cons w ws ih =>
    cases ws with
    | nil => simp [orTreeGates]
    | cons w2 ws2 =>
      have h := ih (by simp)
      simp only [orTreeGates, List.length_append, List.length_cons, List.length_nil] at h ⊢
      omega
lemma orTreeGates_out_lt (base : ℕ) (ws : List ℕ) (hne : ws ≠ [])
    (hws : ∀ w ∈ ws, w < base) :
    (orTreeGates base ws).2 < base + (orTreeGates base ws).1.length := by
  induction ws with
  | nil => contradiction
  | cons w ws ih =>
    cases ws with
    | nil =>
      simp only [orTreeGates, List.length_nil, add_zero]
      exact hws w (by simp)
    | cons w2 ws2 =>
      simp only [orTreeGates, List.length_append, List.length_singleton]
      omega
lemma orTreeGates_eval (n : ℕ) (pre : List Gate) (ws : List ℕ) (hne : ws ≠ [])
    (hws : ∀ w ∈ ws, w < n + pre.length) (x : Fin n → Bool) :
    let res := orTreeGates (n + pre.length) ws
    let C' : Circuit := ⟨pre ++ res.1, res.2⟩
    (∀ k (hk : k < res.1.length),
      let g := res.1[k]'hk
      (g.op = GateOp.or) ∧ ∃ a b, g.inputs = [a, b] ∧ a < n + pre.length + k ∧ b < n + pre.length + k) ∧
    (W n C' x res.2 = true ↔ ∃ w ∈ ws, W n ⟨pre, 0⟩ x w = true) := by
  induction ws with
  | nil => contradiction
  | cons w ws ih =>
    cases ws with
    | nil =>
      simp only [orTreeGates, List.append_nil]
      refine ⟨fun k hk => by simp at hk, ?_⟩
      simp only [List.mem_singleton, exists_eq_left]
      have hpre : W n ⟨pre, w⟩ x w = W n ⟨pre, 0⟩ x w := by
        simp [W, Circuit.wires]
      rw [hpre]
    | cons w2 ws2 =>
      have hne' : w2 :: ws2 ≠ [] := by simp
      have hws' : ∀ u ∈ w2 :: ws2, u < n + pre.length := fun u hu => hws u (by simp [hu])
      have hw : w < n + pre.length := hws w (by simp)
      obtain ⟨hAO', heval'⟩ := ih hne' hws'
      set gs := (orTreeGates (n + pre.length) (w2 :: ws2)).1
      set out := (orTreeGates (n + pre.length) (w2 :: ws2)).2
      have hout_lt : out < n + pre.length + gs.length :=
        orTreeGates_out_lt (n + pre.length) (w2 :: ws2) hne' hws'
      have hres_eq : orTreeGates (n + pre.length) (w :: w2 :: ws2) =
          (gs ++ [⟨GateOp.or, [w, out]⟩], n + pre.length + gs.length) := rfl
      dsimp only
      rw [hres_eq]
      constructor
      · intro k hk
        have hk' : k < gs.length + 1 := by simpa [List.length_append] using hk
        by_cases hkl : k < gs.length
        · have hget : (gs ++ [⟨GateOp.or, [w, out]⟩])[k]'hk = gs[k]'hkl :=
            List.getElem_append_left hkl
          rw [hget]
          exact hAO' k hkl
        · have hkeq : k = gs.length := by omega
          subst hkeq
          have hget : (gs ++ [⟨GateOp.or, [w, out]⟩])[gs.length]'hk = ⟨GateOp.or, [w, out]⟩ := by
            simp
          rw [hget]
          exact ⟨rfl, w, out, rfl, by omega, by omega⟩
      · let C1 : Circuit := ⟨pre ++ gs, out⟩
        let C2 : Circuit := ⟨pre ++ (gs ++ [⟨GateOp.or, [w, out]⟩]), n + pre.length + gs.length⟩
        change W n C2 x (n + pre.length + gs.length) = true ↔ _
        have hlen : C2.gates.length = pre.length + gs.length + 1 := by simp [C2]; omega
        have hidx : pre.length + gs.length < C2.gates.length := by omega
        have hgate : gateAt C2 (pre.length + gs.length) = ⟨GateOp.or, [w, out]⟩ := by
          rw [gateAt_eq C2 (pre.length + gs.length) hidx]
          simp [C2, ← List.append_assoc]
        have hWlast : W n C2 x (n + (pre.length + gs.length)) =
            (W n C2 x w || W n C2 x out) := by
          exact W_or n C2 x (pre.length + gs.length) hidx (by rw [hgate]) w out (by rw [hgate])
            (by omega) (by omega)
        have hCw : W n C2 x w = W n ⟨pre, 0⟩ x w := by
          have := prefix_W n pre (gs ++ [⟨GateOp.or, [w, out]⟩]) []
            (n + pre.length + gs.length) 0 x w hw
          simpa [C2] using this
        have hCout : W n C2 x out = W n C1 x out := by
          have h2 : C2 = ⟨(pre ++ gs) ++ [⟨GateOp.or, [w, out]⟩], n + pre.length + gs.length⟩ := by
            simp [C2, List.append_assoc]
          have h1 : C1 = ⟨(pre ++ gs) ++ [], out⟩ := by simp [C1]
          rw [h2, h1]
          exact prefix_W n (pre ++ gs) [⟨GateOp.or, [w, out]⟩] []
            (n + pre.length + gs.length) out x out (by simp; omega)
        have hadd : n + pre.length + gs.length = n + (pre.length + gs.length) := by omega
        rw [hadd, hWlast, hCw, hCout, Bool.or_eq_true, heval']
        simp
end Close


end PEqualNP.Outside.L_meta_2448_aux.foundation


namespace PEqualNP.Outside.L_meta_2448.cross
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

lemma gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

lemma getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hk]

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover in
lemma valf (n : ℕ) (C : Circuit) (y : Fin n → Bool) (m : ℕ) (hm : m < C.gates.length) :
    gateVal n C m y = (C.gates[m]).op.eval
      (C.gates[m].inputs.map fun i => (wf (C.gates.take m) (List.ofFn y)).getD i false) := by
  have h := gate_val C.gates (List.ofFn y) m hm
  rw [List.length_ofFn] at h
  exact h

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma owns_primary_input {n : ℕ} (C : Circuit) (j : ℕ) (a : Fin n)
    (ha : a.val ∈ (gateAt C j).inputs) {u v : Fin n} (ho : Owns n C j u v) :
    u = a ∨ v = a := by
  obtain ⟨hj, hop, hv, _⟩ := ho
  rw [gateAt_eq C j hj] at ha hop
  rw [valf n C (pairInput u v) j hj, hop] at hv
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hv
  have he := hv a.val ha
  rw [wf_keep _ _ a.val (by simp), getD_ofFn] at he
  have ha' : a = u ∨ a = v := of_decide_eq_true he
  exact ha'.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)

lemma star_of_primary_operands {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (ha : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∃ a : Fin n, a.val ∈ (gateAt C j).inputs) :
    HasStarProfile n G C := by
  intro j hj hop
  obtain ⟨a, hmem⟩ := ha j hj hop
  right
  refine ⟨a, ?_⟩
  intro u v _ ho
  exact owns_primary_input C j a hmem ho

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

end PEqualNP.Outside.L_meta_2448.cross


namespace PEqualNP.Outside.L_meta_2448.StarCoverPrototype
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2448_aux.foundation
open PEqualNP.Outside.L_meta_2448_aux.foundation.Close
open PEqualNP.Outside.L_meta_2448_aux.foundation.M1528.P1.S98

lemma orTree_all_or (base : ℕ) (ws : List ℕ) :
    ∀ g ∈ (orTreeGates base ws).1, g.op = GateOp.or := by
  induction ws with
  | nil => simp [orTreeGates]
  | cons w ws ih =>
    cases ws with
    | nil => simp [orTreeGates]
    | cons u us =>
      intro g hg
      simp only [orTreeGates, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact ih g hg
      · rfl

theorem star_cover_witness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hE : G.edgeFinset.Nonempty)
    (K0 : Finset (Fin n)) (hcov : ∀ e ∈ G.edgeFinset, ∃ v ∈ K0, v ∈ e) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      HasStarProfile n G D ∧ D.size + 1 ≤ G.edgeFinset.card + K0.card := by
  classical
  let owner : Sym2 (Fin n) → Fin n := fun e =>
    if h : e ∈ G.edgeFinset then (hcov e h).choose else (hE.choose.out).1
  have howner_mem : ∀ e (he : e ∈ G.edgeFinset), owner e ∈ K0 ∧ owner e ∈ e := by
    intro e he
    simp only [owner, dite_eq_left, he]
    exact (hcov e he).choose_spec
  let L : Fin n → Finset (Fin n) := fun v =>
    Finset.univ.filter fun u => ∃ h : s(v, u) ∈ G.edgeFinset, owner s(v, u) = v
  have hL_adj : ∀ v u, u ∈ L v → G.Adj v u := by
    intro v u hu
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact SimpleGraph.mem_edgeFinset.mp hu.1
  have hL_edge_iff : ∀ u v, G.Adj u v → (v ∈ L u ∨ u ∈ L v) ∧ (u ∈ K0 ∧ v ∈ L u ∨ v ∈ K0 ∧ u ∈ L v) := by
    intro u v huv
    have he : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
    obtain ⟨hK, hmem⟩ := howner_mem s(u, v) he
    rcases Sym2.mem_iff.mp hmem with h | h
    · have hu : v ∈ L u := by
        simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨he, h⟩
      exact ⟨Or.inl hu, Or.inl ⟨h ▸ hK, hu⟩⟩
    · have hv : u ∈ L v := by
        simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
        have he' : s(v, u) ∈ G.edgeFinset := by rw [Sym2.eq_swap]; exact he
        exact ⟨he', by rw [Sym2.eq_swap]; exact h⟩
      exact ⟨Or.inr hv, Or.inr ⟨h ▸ hK, hv⟩⟩
  have hsum : (∑ v ∈ K0, (L v).card) = G.edgeFinset.card := by
    have hbij : (K0.sigma L).card = G.edgeFinset.card := by
      refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_sigma] at hp
        exact SimpleGraph.mem_edgeFinset.mpr (hL_adj p.1 p.2 hp.2)
      · intro p1 hp1 p2 hp2 heq
        simp only [Finset.mem_sigma, L, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
        have h1 : p1.1 = p2.1 := by
          rw [← hp1.2.2, heq, hp2.2.2]
        have h2 : p1.2 = p2.2 := by
          have : s(p1.1, p1.2) = s(p1.1, p2.2) := by rw [← h1] at heq; exact heq
          rcases Sym2.eq_iff.mp this with ⟨_, hb⟩ | ⟨_, hb⟩
          · exact hb
          · have hadj : G.Adj p1.1 p1.2 := SimpleGraph.mem_edgeFinset.mp hp1.2.1
            rw [hb] at hadj
            exact (G.irrefl hadj).elim
        exact Sigma.ext h1 (heq_of_eq h2)
      · intro e he
        induction e using Sym2.ind with
        | _ u v =>
          have huv := SimpleGraph.mem_edgeFinset.mp he
          rcases (hL_edge_iff u v huv).2 with ⟨huK, hvL⟩ | ⟨hvK, huL⟩
          · exact ⟨⟨u, v⟩, Finset.mem_sigma.mpr ⟨huK, hvL⟩, rfl⟩
          · exact ⟨⟨v, u⟩, Finset.mem_sigma.mpr ⟨hvK, huL⟩, Sym2.eq_swap⟩
    rw [Finset.card_sigma] at hbij
    exact hbij
  let M := K0.filter fun v => (L v).Nonempty
  have hM_sub : M ⊆ K0 := Finset.filter_subset _ _
  have hM_ne : M.Nonempty := by
    obtain ⟨e, he⟩ := hE
    induction e using Sym2.ind with
    | _ u v =>
      rcases (hL_edge_iff u v (SimpleGraph.mem_edgeFinset.mp he)).2 with ⟨huK, hvL⟩ | ⟨hvK, huL⟩
      · exact ⟨u, Finset.mem_filter.mpr ⟨huK, ⟨v, hvL⟩⟩⟩
      · exact ⟨v, Finset.mem_filter.mpr ⟨hvK, ⟨u, huL⟩⟩⟩
  have hsumM : (∑ v ∈ M, (L v).card) = G.edgeFinset.card := by
    rw [← hsum]
    refine Finset.sum_subset hM_sub ?_
    intro v hv hnotM
    simp only [M, Finset.mem_filter, not_and, Finset.not_nonempty_iff_eq_empty] at hnotM
    rw [hnotM hv, Finset.card_empty]
  let buildStars : List (Fin n) → List Gate × List ℕ :=
    List.foldl (fun (acc : List Gate × List ℕ) (v : Fin n) =>
      let ws := (L v).toList.map Fin.val
      let (gs, out) := orTreeGates (n + acc.1.length) ws
      let andGate : Gate := ⟨GateOp.and, [v.val, out]⟩
      let andWire := n + acc.1.length + gs.length
      (acc.1 ++ gs ++ [andGate], acc.2 ++ [andWire])) ([], [])
  have hbuild_aux : ∀ (vs : List (Fin n)), (∀ v ∈ vs, (L v).Nonempty) →
      let res := buildStars vs
      res.1.length = (vs.map fun v => (L v).card).sum ∧
      res.2.length = vs.length ∧
      (∀ w ∈ res.2, w < n + res.1.length) ∧
      AO n ⟨res.1, 0⟩ ∧
      (∀ x : Fin n → Bool, ∀ w ∈ res.2, W n ⟨res.1, 0⟩ x w = true →
        ∃ v ∈ vs, x v = true ∧ ∃ u ∈ L v, x u = true) ∧
      (∀ x : Fin n → Bool, ∀ v ∈ vs, x v = true → (∃ u ∈ L v, x u = true) →
        ∃ w ∈ res.2, W n ⟨res.1, 0⟩ x w = true) := by
    intro vs
    induction vs using List.reverseRecOn with
    | nil =>
      intro _
      simp [buildStars, AO]
    | append_singleton vs v ih =>
      intro hne
      have hne_vs : ∀ u ∈ vs, (L u).Nonempty := fun u hu => hne u (by simp [hu])
      have hne_v : (L v).Nonempty := hne v (by simp)
      obtain ⟨hlen, hlen2, hlt, hAO, hsound, hcomp⟩ := ih hne_vs
      set acc := buildStars vs
      set ws := (L v).toList.map Fin.val
      have hws_ne : ws ≠ [] := by
        simp only [ws, ne_eq, List.map_eq_nil_iff, Finset.toList_eq_nil]
        exact Finset.nonempty_iff_ne_empty.mp hne_v
      have hws_lt : ∀ w ∈ ws, w < n + acc.1.length := by
        intro w hw
        simp only [ws, List.mem_map] at hw
        obtain ⟨u, _, rfl⟩ := hw
        have := u.isLt; omega
      set ot := orTreeGates (n + acc.1.length) ws
      have hot_len : ot.1.length + 1 = (L v).card := by
        have := orTreeGates_length (n + acc.1.length) ws hws_ne
        simpa [ot, ws] using this
      have hot_out_lt : ot.2 < n + acc.1.length + ot.1.length :=
        orTreeGates_out_lt (n + acc.1.length) ws hws_ne hws_lt
      let andGate : Gate := ⟨GateOp.and, [v.val, ot.2]⟩
      let andWire := n + acc.1.length + ot.1.length
      let newGs := acc.1 ++ ot.1 ++ [andGate]
      have hbuild_eq : buildStars (vs ++ [v]) = (newGs, acc.2 ++ [andWire]) := by
        simp [buildStars, List.foldl_append, acc, newGs, ot, ws, andGate, andWire]
      rw [hbuild_eq]
      have hnewLen : newGs.length = acc.1.length + (L v).card := by
        simp only [newGs, List.length_append, List.length_singleton]
        omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hnewLen, hlen]
      · simp [hlen2]
      · intro w hw
        simp only [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · have h1 := hlt w hw
          have h2 : newGs.length = acc.1.length + (L v).card := hnewLen
          change w < n + newGs.length
          omega
        · simp only [andWire, newGs, List.length_append, List.length_singleton]; omega
      · intro k hk
        have hAO_ot := (orTreeGates_eval n acc.1 ws hws_ne hws_lt (fun _ => false)).1
        by_cases hk1 : k < acc.1.length
        · have hg : gateAt ⟨newGs, 0⟩ k = gateAt ⟨acc.1, 0⟩ k := by
            rw [gateAt_eq ⟨newGs, 0⟩ k hk, gateAt_eq ⟨acc.1, 0⟩ k hk1]
            simp only [newGs, List.append_assoc]
            exact List.getElem_append_left hk1
          rw [hg]; exact hAO k hk1
        · by_cases hk2 : k < acc.1.length + ot.1.length
          · have hidx : k - acc.1.length < ot.1.length := by omega
            have hg : gateAt ⟨newGs, 0⟩ k = ot.1[k - acc.1.length]'hidx := by
              rw [gateAt_eq ⟨newGs, 0⟩ k hk]
              simp only [newGs]
              rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
            rw [hg]
            obtain ⟨hop, a, b, hin, ha, hb⟩ := hAO_ot (k - acc.1.length) hidx
            exact ⟨Or.inr hop, a, b, hin, by omega, by omega⟩
          · have hkeq : k = acc.1.length + ot.1.length := by
              simp only [newGs, List.length_append, List.length_singleton] at hk; omega
            subst hkeq
            have hg : gateAt ⟨newGs, 0⟩ (acc.1.length + ot.1.length) = andGate := by
              rw [gateAt_eq ⟨newGs, 0⟩ _ hk]
              simp [newGs]
            rw [hg]
            exact ⟨Or.inl rfl, v.val, ot.2, rfl, by have := v.isLt; omega, by omega⟩
      · intro x w hw hW
        have hpre_eq : ∀ u, u < n + acc.1.length → W n ⟨newGs, 0⟩ x u = W n ⟨acc.1, 0⟩ x u := by
          intro u hu
          have := prefix_W n acc.1 (ot.1 ++ [andGate]) [] 0 0 x u hu
          simpa [newGs, List.append_assoc] using this
        simp only [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · rw [hpre_eq w (hlt w hw)] at hW
          obtain ⟨u0, hu0, hxu0, z, hzL, hxz⟩ := hsound x w hw hW
          exact ⟨u0, by simp [hu0], hxu0, z, hzL, hxz⟩
        · have hk : acc.1.length + ot.1.length < newGs.length := by
            simp [newGs]
          have hg : gateAt ⟨newGs, 0⟩ (acc.1.length + ot.1.length) = andGate := by
            rw [gateAt_eq ⟨newGs, 0⟩ _ hk]; simp [newGs]
          have hadd : andWire = n + (acc.1.length + ot.1.length) := by simp [andWire]; omega
          rw [hadd, W_and n ⟨newGs, 0⟩ x _ hk (by rw [hg]) v.val ot.2 (by rw [hg])
            (by have := v.isLt; omega) (by omega), Bool.and_eq_true] at hW
          rw [W_input n ⟨newGs, 0⟩ x v.val v.isLt] at hW
          have hot_eq : W n ⟨newGs, 0⟩ x ot.2 = W n ⟨acc.1 ++ ot.1, ot.2⟩ x ot.2 := by
            have := prefix_W n (acc.1 ++ ot.1) [andGate] [] 0 ot.2 x ot.2
              (by simp; omega)
            simpa [newGs] using this
          rw [hot_eq, (orTreeGates_eval n acc.1 ws hws_ne hws_lt x).2] at hW
          obtain ⟨uval, huval, hWu⟩ := hW.2
          simp only [ws, List.mem_map, Finset.mem_toList] at huval
          obtain ⟨u, huL, rfl⟩ := huval
          rw [W_input n ⟨acc.1, 0⟩ x u.val u.isLt] at hWu
          exact ⟨v, by simp, hW.1, u, huL, hWu⟩
      · intro x v0 hv0 hxv0 ⟨u, huL, hxu⟩
        have hpre_eq : ∀ u', u' < n + acc.1.length → W n ⟨newGs, 0⟩ x u' = W n ⟨acc.1, 0⟩ x u' := by
          intro u' hu'
          have := prefix_W n acc.1 (ot.1 ++ [andGate]) [] 0 0 x u' hu'
          simpa [newGs, List.append_assoc] using this
        simp only [List.mem_append, List.mem_singleton] at hv0
        rcases hv0 with hv0 | rfl
        · obtain ⟨w, hw, hW⟩ := hcomp x v0 hv0 hxv0 ⟨u, huL, hxu⟩
          exact ⟨w, by simp [hw], by rw [hpre_eq w (hlt w hw)]; exact hW⟩
        · refine ⟨andWire, by simp, ?_⟩
          have hk : acc.1.length + ot.1.length < newGs.length := by simp [newGs]
          have hg : gateAt ⟨newGs, 0⟩ (acc.1.length + ot.1.length) = andGate := by
            rw [gateAt_eq ⟨newGs, 0⟩ _ hk]; simp [newGs]
          have hadd : andWire = n + (acc.1.length + ot.1.length) := by simp [andWire]; omega
          rw [hadd, W_and n ⟨newGs, 0⟩ x _ hk (by rw [hg]) v0.val ot.2 (by rw [hg])
            (by have := v0.isLt; omega) (by omega), Bool.and_eq_true,
            W_input n ⟨newGs, 0⟩ x v0.val v0.isLt]
          refine ⟨hxv0, ?_⟩
          have hot_eq : W n ⟨newGs, 0⟩ x ot.2 = W n ⟨acc.1 ++ ot.1, ot.2⟩ x ot.2 := by
            have := prefix_W n (acc.1 ++ ot.1) [andGate] [] 0 ot.2 x ot.2
              (by simp; omega)
            simpa [newGs] using this
          rw [hot_eq, (orTreeGates_eval n acc.1 ws hws_ne hws_lt x).2]
          refine ⟨u.val, List.mem_map.mpr ⟨u, Finset.mem_toList.mpr huL, rfl⟩, ?_⟩
          rw [W_input n ⟨acc.1, 0⟩ x u.val u.isLt]
          exact hxu
  let vs := M.toList
  have hvs_ne : ∀ v ∈ vs, (L v).Nonempty := by
    intro v hv
    simp only [vs, Finset.mem_toList, M, Finset.mem_filter] at hv
    exact hv.2
  obtain ⟨hlen1, hlen2, hlt, hAO1, hsound1, hcomp1⟩ := hbuild_aux vs hvs_ne
  set bs := buildStars vs
  have hbs2_ne : bs.2 ≠ [] := by
    intro h
    have h1 : vs.length = 0 := by rw [← hlen2, h]; rfl
    have : M = ∅ := by
      rw [← Finset.card_eq_zero, ← Finset.length_toList, h1]
    exact Finset.nonempty_iff_ne_empty.mp hM_ne this
  set top := orTreeGates (n + bs.1.length) bs.2
  let D : Circuit := ⟨bs.1 ++ top.1, top.2⟩
  have hD_AO : AO n D := by
    intro k hk
    have hAO_top := (orTreeGates_eval n bs.1 bs.2 hbs2_ne hlt (fun _ => false)).1
    by_cases hk1 : k < bs.1.length
    · have hg : gateAt D k = gateAt ⟨bs.1, 0⟩ k := by
        rw [gateAt_eq D k hk, gateAt_eq ⟨bs.1, 0⟩ k hk1]
        exact List.getElem_append_left hk1
      rw [hg]; exact hAO1 k hk1
    · have hidx : k - bs.1.length < top.1.length := by simp [D] at hk; omega
      have hg : gateAt D k = top.1[k - bs.1.length]'hidx := by
        rw [gateAt_eq D k hk]
        exact List.getElem_append_right (by omega)
      rw [hg]
      obtain ⟨hop, a, b, hin, ha, hb⟩ := hAO_top (k - bs.1.length) hidx
      exact ⟨Or.inr hop, a, b, hin, by omega, by omega⟩
  have hD_fun : circuitFun n D = graphFun G ∅ := by
    funext x
    rw [Bool.eq_iff_iff]
    have hDeval : circuitFun n D x = W n D x top.2 := rfl
    rw [hDeval, (orTreeGates_eval n bs.1 bs.2 hbs2_ne hlt x).2]
    constructor
    · rintro ⟨w, hw, hW⟩
      obtain ⟨v, hv, hxv, u, huL, hxu⟩ := hsound1 x w hw hW
      have hadj : G.Adj v u := hL_adj v u huL
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq]
      exact ⟨v, u, hadj, hxv, hxu⟩
    · intro hG
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq] at hG
      obtain ⟨u, v, hadj, hxu, hxv⟩ := hG
      rcases (hL_edge_iff u v hadj).2 with ⟨huK, hvL⟩ | ⟨hvK, huL⟩
      · have huM : u ∈ vs := by
          simp only [vs, Finset.mem_toList, M, Finset.mem_filter]
          exact ⟨huK, ⟨v, hvL⟩⟩
        exact hcomp1 x u huM hxu ⟨v, hvL, hxv⟩
      · have hvM : v ∈ vs := by
          simp only [vs, Finset.mem_toList, M, Finset.mem_filter]
          exact ⟨hvK, ⟨u, huL⟩⟩
        exact hcomp1 x v hvM hxv ⟨u, huL, hxu⟩
  have hD_size : D.size + 1 = G.edgeFinset.card + M.card := by
    have htop_len : top.1.length + 1 = bs.2.length :=
      orTreeGates_length (n + bs.1.length) bs.2 hbs2_ne
    have hsum_vs : (vs.map fun v => (L v).card).sum = G.edgeFinset.card := by
      rw [← hsumM]
      simp [vs]
    have hvs_len : vs.length = M.card := Finset.length_toList M
    have h1 : bs.1.length = G.edgeFinset.card := by rw [hlen1, hsum_vs]
    have h2 : bs.2.length = M.card := by rw [hlen2, hvs_len]
    simp only [Circuit.size, D, List.length_append]
    omega
  have hbuild_primary : ∀ vs, ∀ g ∈ (buildStars vs).1, g.op = GateOp.and →
      ∃ a : Fin n, a.val ∈ g.inputs := by
    intro vs
    induction vs using List.reverseRecOn with
    | nil => simp [buildStars]
    | append_singleton vs v ih =>
      intro g hg hop
      simp only [buildStars, List.foldl_append, List.foldl_cons, List.foldl_nil] at hg
      change g ∈ ((buildStars vs).1 ++
        (orTreeGates (n + (buildStars vs).1.length) ((L v).toList.map Fin.val)).1 ++
        [⟨GateOp.and, [v.val,
          (orTreeGates (n + (buildStars vs).1.length) ((L v).toList.map Fin.val)).2]⟩]) at hg
      rcases List.mem_append.mp hg with hg | hg
      · rcases List.mem_append.mp hg with hg | hg
        · exact ih g hg hop
        · have hor := orTree_all_or _ _ g hg
          rw [hop] at hor
          cases hor
      · simp only [List.mem_singleton] at hg
        subst g
        exact ⟨v, by simp⟩
  have hD_primary : ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
      ∃ a : Fin n, a.val ∈ (gateAt D j).inputs := by
    intro j hj hop
    have hmem : gateAt D j ∈ D.gates := by
      rw [gateAt_eq D j hj]
      exact List.getElem_mem hj
    change gateAt D j ∈ bs.1 ++ top.1 at hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hbuild_primary vs _ hmem hop
    · have hor := orTree_all_or _ _ (gateAt D j) hmem
      rw [hop] at hor
      cases hor
  have hD_mono : Monotone2 D := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have h := hD_AO j hj
    rw [gateAt_eq D j hj] at h
    obtain ⟨hop, a, b, hin, _, _⟩ := h
    constructor
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop
    · simp [hin]
  refine ⟨D, hD_mono, hD_fun,
    PEqualNP.Outside.L_meta_2448.cross.star_of_primary_operands G D hD_primary, ?_⟩
  have hM_le : M.card ≤ K0.card := Finset.card_le_card hM_sub
  omega

end PEqualNP.Outside.L_meta_2448.StarCoverPrototype

namespace PEqualNP.Outside.L_meta_2448_aux.oneJunkStar

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma empty_graph_star_minimum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hempty : G.edgeFinset = ∅) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      (∀ E : Circuit, Monotone2 E → circuitFun n E = graphFun G ∅ → D.size ≤ E.size) ∧
      HasStarProfile n G D := by
  let D : Circuit := ⟨[], n⟩
  have hno : ∀ u v : Fin n, ¬ G.Adj u v := by
    intro u v huv
    have hmem : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
    rw [hempty] at hmem
    exact Finset.notMem_empty _ hmem
  have hfun : circuitFun n D = graphFun G ∅ := by
    funext x
    simp [D, circuitFun, Circuit.eval, Circuit.wires, graphFun, hno,
      List.getD_eq_getElem?_getD]
  refine ⟨D, ?_, hfun, ?_, ?_⟩
  · intro g hg
    cases hg
  · intro E _ _
    exact Nat.zero_le _
  · intro j hj
    exact (Nat.not_lt_zero j hj).elim

end PEqualNP.Outside.L_meta_2448_aux.oneJunkStar

namespace PEqualNP.Outside.L_meta_2448_aux.inputBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover


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

lemma dep (n : ℕ) (C : Circuit) (hR : ∀ j < C.gates.length, (gateAt C j).inputs.length ≤ 2) :
    ∀ k, k ≤ C.gates.length → ∀ W : Finset ℕ, (∀ w ∈ W, w < n + k) →
      ∃ T : Finset (Fin n), T.card ≤ k + W.card ∧
        ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) →
          ∀ w ∈ W, val C (List.ofFn x) w = val C (List.ofFn y) w := by
  intro k
  induction k with
  | zero =>
    intro _ W hW
    refine ⟨Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ W), ?_, ?_⟩
    · rw [Nat.zero_add, ← Finset.card_image_of_injective _ Fin.val_injective]
      apply Finset.card_le_card
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
      exact (Finset.mem_filter.1 hi).2
    · intro x y h w hw
      have hw' : w < n := by simpa using hW w hw
      have e : ∀ z : Fin n → Bool, (List.ofFn z).getD w false = z ⟨w, hw'⟩ := by
        intro z; simp [List.getD_eq_getElem?_getD, hw']
      rw [val_input (by simp) hw', val_input (by simp) hw', e, e]
      exact h ⟨w, hw'⟩ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hw⟩)
  | succ k ih =>
    intro hk W hW
    by_cases hmem : n + k ∈ W
    · obtain ⟨W2, hW2⟩ : ∃ W2 : Finset ℕ, W2 = W.erase (n + k) ∪
          ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset := ⟨_, rfl⟩
      have hlt2 : ∀ w ∈ W2, w < n + k := by
        intro w hw
        rw [hW2] at hw
        rcases Finset.mem_union.1 hw with h | h
        · have h1 := hW w (Finset.mem_of_mem_erase h)
          have h2 := Finset.ne_of_mem_erase h
          omega
        · simp at h; exact h.2
      have hs1 : ∀ w ∈ W, w ≠ n + k → w ∈ W2 := by
        intro w hw hne
        rw [hW2]
        exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hw⟩)
      have hs2 : ∀ i ∈ (gateAt C k).inputs, i < n + k → i ∈ W2 := by
        intro i hi hlt
        rw [hW2]
        exact Finset.mem_union_right _ (by simp [hi, hlt])
      have hc : W2.card + 1 ≤ W.card + 2 := by
        rw [hW2]
        have h1 := Finset.card_union_le (W.erase (n + k))
          ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset
        have h2 : ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset.card ≤ 2 :=
          (List.toFinset_card_le _).trans
            ((List.length_filter_le _ _).trans (hR k (by omega)))
        have h3 := Finset.card_erase_of_mem hmem
        have h4 : 0 < W.card := Finset.card_pos.2 ⟨_, hmem⟩
        omega
      obtain ⟨T, hT, hdep⟩ := ih (by omega) W2 hlt2
      refine ⟨T, by omega, ?_⟩
      intro x y h w hw
      by_cases hwk : w = n + k
      · rw [hwk, val_gate (by simp) (by omega), val_gate (by simp) (by omega)]
        congr 1
        apply List.map_congr_left
        intro i hi
        by_cases hlt : i < n + k
        · simp only [ite_eq_left hlt]
          exact hdep x y h i (hs2 i hi hlt)
        · simp only [ite_eq_right hlt]
      · exact hdep x y h w (hs1 w hw hwk)
    · obtain ⟨T, hT, hdep⟩ := ih (by omega) W (by
        intro w hw
        have h1 := hW w hw
        have h2 : w ≠ n + k := fun h => hmem (h ▸ hw)
        omega)
      exact ⟨T, by omega, hdep⟩

lemma main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hF : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅) :
    G.support.ncard ≤ C.size + 1 := by
  obtain ⟨T, hT, hdep⟩ : ∃ T : Finset (Fin n), T.card ≤ C.gates.length + 1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) →
        val C (List.ofFn x) C.output = val C (List.ofFn y) C.output := by
    by_cases ho : C.output < n + C.gates.length
    · obtain ⟨T, hT, hdep⟩ := dep n C (fun j hj => h2 _ (gateAt_mem hj)) C.gates.length le_rfl
        {C.output} (by simpa using ho)
      exact ⟨T, by simpa using hT, fun x y h => hdep x y h _ (by simp)⟩
    · exact ⟨∅, by simp, fun x y _ => by
        rw [val_ge (n := n) (by simp) (by omega), val_ge (n := n) (by simp) (by omega)]⟩
  have hsub : G.support ⊆ (T : Set (Fin n)) := by
    intro v hv
    obtain ⟨u, huv⟩ := (SimpleGraph.mem_support G).1 hv
    by_contra hvT
    have e := hdep (fun w => decide (w = u ∨ w = v)) (fun w => decide (w = u)) (by
      intro i hi
      have hne : i ≠ v := fun h => hvT (h ▸ hi)
      simp [hne])
    have fx : val C (List.ofFn (fun w => decide (w = u ∨ w = v))) C.output =
        graphFun G ∅ (fun w => decide (w = u ∨ w = v)) :=
      congrFun hF (fun w => decide (w = u ∨ w = v))
    have fy : val C (List.ofFn (fun w => decide (w = u))) C.output =
        graphFun G ∅ (fun w => decide (w = u)) :=
      congrFun hF (fun w => decide (w = u))
    have t1 : graphFun G ∅ (fun w => decide (w = u ∨ w = v)) = true := by
      unfold graphFun
      rw [Bool.or_eq_true]
      right
      rw [decide_eq_true_iff]
      exact ⟨v, u, huv, by simp, by simp⟩
    have t2 : graphFun G ∅ (fun w => decide (w = u)) = false := by
      unfold graphFun
      rw [Bool.or_eq_false_iff]
      refine ⟨by simp, ?_⟩
      rw [decide_eq_false_iff_not]
      rintro ⟨a, b, hab, ha, hb⟩
      have ha' : a = u := by simpa using ha
      have hb' : b = u := by simpa using hb
      exact hab.ne (ha'.trans hb'.symm)
    rw [fx, fy, t1, t2] at e
    cases e
  calc G.support.ncard ≤ (T : Set (Fin n)).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet T)
    _ = T.card := Set.ncard_coe_finset T
    _ ≤ C.size + 1 := hT

end PEqualNP.Outside.L_meta_2448_aux.inputBound

namespace PEqualNP.Outside.L_meta_2448_aux.twoSilentProducts

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

def Cross {n : ℕ} (L R : Finset (Fin n)) (u v : Fin n) : Prop :=
  (u ∈ L ∧ v ∈ R) ∨ (v ∈ L ∧ u ∈ R)

lemma cross_mem {n : ℕ} {L R : Finset (Fin n)} {u v : Fin n}
    (h : Cross L R u v) : u ∈ L ∪ R ∧ v ∈ L ∪ R := by
  unfold Cross at h
  simp only [Finset.mem_union]
  tauto

lemma star_forest_cover_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (K : Finset (Fin n))
    (hc : ∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K)
    (hi : ∀ u ∈ K, ∀ v ∈ K, ¬ G.Adj u v)
    (hl : ∀ u, u ∉ K → ∀ v w, G.Adj u v → G.Adj u w → v = w)
    (ha : ∀ u ∈ K, u ∈ G.support) :
    G.edgeFinset.card + K.card ≤ G.support.ncard := by
  classical
  have hex : ∀ e ∈ G.edgeFinset, ∃ u, ∃ v,
      u ∉ K ∧ v ∈ K ∧ G.Adj u v ∧ e = s(u, v) := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      rcases hc u v huv with hu | hv
      · exact ⟨v, u, fun hv => hi u hu v hv huv, hu, huv.symm, Sym2.eq_swap⟩
      · exact ⟨u, v, fun hu => hi u hu v hv huv, hv, huv, rfl⟩
  let leaf : {e // e ∈ G.edgeFinset} → Fin n := fun e => (hex e.val e.property).choose
  have hp : ∀ e : {e // e ∈ G.edgeFinset}, ∃ v,
      leaf e ∉ K ∧ v ∈ K ∧ G.Adj (leaf e) v ∧ e.val = s(leaf e, v) := by
    intro e
    exact (hex e.val e.property).choose_spec
  have hinj : Set.InjOn leaf (G.edgeFinset.attach : Set {e // e ∈ G.edgeFinset}) := by
    intro e1 _ e2 _ he
    obtain ⟨v1, h1, _, ha1, hv1⟩ := hp e1
    obtain ⟨v2, _, _, ha2, hv2⟩ := hp e2
    have hv : v1 = v2 := hl (leaf e1) h1 v1 v2 ha1 (he ▸ ha2)
    apply Subtype.ext
    rw [hv1, hv2, he, hv]
  let L := G.edgeFinset.attach.image leaf
  have hcard : L.card = G.edgeFinset.card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_attach]
  have hd : Disjoint K L := by
    apply Finset.disjoint_left.mpr
    intro u hu hL
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hL
    exact (hp e).choose_spec.1 hu
  have hs : ((K ∪ L : Finset (Fin n)) : Set (Fin n)) ⊆ G.support := by
    intro u hu
    rcases Finset.mem_union.mp hu with huK | huL
    · exact ha u huK
    · obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp huL
      obtain ⟨v, _, _, huv, _⟩ := hp e
      exact huv.mem_support_left
  have hn := Set.ncard_le_ncard hs (Set.toFinite G.support)
  rw [Set.ncard_coe_finset, Finset.card_union_of_disjoint hd, hcard] at hn
  omega

lemma biclique_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (L R : Finset (Fin n))
    (hedge : ∀ u ∈ L, ∀ v ∈ R, G.Adj u v) :
    ∃ K : Finset (Fin n), K ⊆ L ∪ R ∧ K.card ≤ 1 ∧
      (∀ u ∈ K, u ∈ G.support) ∧
      ∀ u v, Cross L R u v → u ∈ K ∨ v ∈ K := by
  classical
  by_cases hL : L.Nonempty
  · by_cases hR : R.Nonempty
    · have hsmall : L.card ≤ 1 ∨ R.card ≤ 1 := by
        by_contra! h
        obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h.1
        have hs : R ⊆ Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj v w) := by
          intro w hw
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hedge u hu w hw, hedge v hv w hw⟩
        have hcard := Finset.card_le_card hs
        have hfour := h4 u v huv
        omega
      rcases hsmall with hsmall | hsmall
      · obtain ⟨u, hLu⟩ := Finset.card_eq_one.mp (le_antisymm hsmall (Finset.card_pos.mpr hL))
        obtain ⟨v, hv⟩ := hR
        refine ⟨{u}, ?_, by simp, ?_, ?_⟩
        · intro w hw
          rw [Finset.mem_singleton] at hw
          subst w
          apply Finset.mem_union_left
          rw [hLu]
          simp
        · intro w hw
          rw [Finset.mem_singleton] at hw
          subst w
          exact (hedge u (by rw [hLu]; simp) v hv).mem_support_left
        · intro a b hab
          simp only [Cross, hLu, Finset.mem_singleton] at hab ⊢
          tauto
      · obtain ⟨v, hRv⟩ := Finset.card_eq_one.mp (le_antisymm hsmall (Finset.card_pos.mpr hR))
        obtain ⟨u, hu⟩ := hL
        refine ⟨{v}, ?_, by simp, ?_, ?_⟩
        · intro w hw
          rw [Finset.mem_singleton] at hw
          subst w
          apply Finset.mem_union_right
          rw [hRv]
          simp
        · intro w hw
          rw [Finset.mem_singleton] at hw
          subst w
          exact (hedge u hu v (by rw [hRv]; simp)).mem_support_right
        · intro a b hab
          simp only [Cross, hRv, Finset.mem_singleton] at hab ⊢
          tauto
    · refine ⟨∅, by simp, by simp, by simp, ?_⟩
      have he : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
      simp [Cross, he]
  · refine ⟨∅, by simp, by simp, by simp, ?_⟩
    have he : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
    simp [Cross, he]

lemma two_disjoint_bicliques_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B C D : Finset (Fin n))
    (hd : Disjoint (A ∪ B) (C ∪ D))
    (hedge : ∀ u v, G.Adj u v ↔ Cross A B u v ∨ Cross C D u v) :
    ∃ K : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K) ∧
      G.edgeFinset.card + K.card ≤ G.support.ncard := by
  classical
  obtain ⟨K1, hs1, hc1, ha1, he1⟩ := biclique_cover G h4 A B
    (fun u hu v hv => (hedge u v).mpr (Or.inl (Or.inl ⟨hu, hv⟩)))
  obtain ⟨K2, hs2, hc2, ha2, he2⟩ := biclique_cover G h4 C D
    (fun u hu v hv => (hedge u v).mpr (Or.inr (Or.inl ⟨hu, hv⟩)))
  have sep : ∀ u, u ∈ A ∪ B → u ∈ C ∪ D → False := Finset.disjoint_left.mp hd
  have k1 (u : Fin n) (hu : u ∈ A ∪ B) (hk : u ∈ K1 ∪ K2) : u ∈ K1 := by
    rcases Finset.mem_union.mp hk with hk | hk
    · exact hk
    · exact (sep u hu (hs2 hk)).elim
  have k2 (u : Fin n) (hu : u ∈ C ∪ D) (hk : u ∈ K1 ∪ K2) : u ∈ K2 := by
    rcases Finset.mem_union.mp hk with hk | hk
    · exact (sep u (hs1 hk) hu).elim
    · exact hk
  have hcov : ∀ u v, G.Adj u v → u ∈ K1 ∪ K2 ∨ v ∈ K1 ∪ K2 := by
    intro u v huv
    rcases (hedge u v).mp huv with h | h
    · rcases he1 u v h with h | h
      · exact Or.inl (Finset.mem_union_left _ h)
      · exact Or.inr (Finset.mem_union_left _ h)
    · rcases he2 u v h with h | h
      · exact Or.inl (Finset.mem_union_right _ h)
      · exact Or.inr (Finset.mem_union_right _ h)
  refine ⟨K1 ∪ K2, hcov, star_forest_cover_budget G (K1 ∪ K2) hcov ?_ ?_ ?_⟩
  · intro u hu v hv huv
    have heq : u = v := by
      rcases (hedge u v).mp huv with h | h
      · exact Finset.card_le_one.mp hc1 u (k1 u (cross_mem h).1 hu) v (k1 v (cross_mem h).2 hv)
      · exact Finset.card_le_one.mp hc2 u (k2 u (cross_mem h).1 hu) v (k2 v (cross_mem h).2 hv)
    exact huv.ne heq
  · intro u hu v w huv huw
    have hv : v ∈ K1 ∪ K2 := (hcov u v huv).resolve_left hu
    have hw : w ∈ K1 ∪ K2 := (hcov u w huw).resolve_left hu
    rcases (hedge u v).mp huv with h1 | h1
    · rcases (hedge u w).mp huw with h2 | h2
      · exact Finset.card_le_one.mp hc1 v (k1 v (cross_mem h1).2 hv) w (k1 w (cross_mem h2).2 hw)
      · exact (sep u (cross_mem h1).1 (cross_mem h2).1).elim
    · rcases (hedge u w).mp huw with h2 | h2
      · exact (sep u (cross_mem h2).1 (cross_mem h1).1).elim
      · exact Finset.card_le_one.mp hc2 v (k2 v (cross_mem h1).2 hv) w (k2 w (cross_mem h2).2 hw)
  · intro u hu
    rcases Finset.mem_union.mp hu with h | h
    · exact ha1 u h
    · exact ha2 u h

set_option maxHeartbeats 4000000 in
lemma four_sides_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (P Q R S : Finset (Fin n))
    (hPQ : Disjoint P Q) (hRS : Disjoint R S)
    (hedge : ∀ u v, G.Adj u v ↔
      (u ∈ P ∨ v ∈ P) ∧ (u ∈ Q ∨ v ∈ Q) ∧ (u ∈ R ∨ v ∈ R) ∧ (u ∈ S ∨ v ∈ S)) :
    ∃ K : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K) ∧
      G.edgeFinset.card + K.card ≤ G.support.ncard := by
  have hpq : ∀ u, u ∈ P → u ∈ Q → False := Finset.disjoint_left.mp hPQ
  have hrs : ∀ u, u ∈ R → u ∈ S → False := Finset.disjoint_left.mp hRS
  apply two_disjoint_bicliques_budget G h4 (P ∩ R) (Q ∩ S) (P ∩ S) (Q ∩ R)
  · apply Finset.disjoint_left.mpr
    intro u h1 h2
    simp only [Finset.mem_union, Finset.mem_inter] at h1 h2
    have hPQu := hpq u
    have hRSu := hrs u
    tauto
  · intro u v
    rw [hedge]
    simp only [Cross, Finset.mem_inter]
    have hPQu := hpq u
    have hPQv := hpq v
    have hRSu := hrs u
    have hRSv := hrs v
    tauto

lemma exists_minimum_star_of_four_sides {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (P Q R S : Finset (Fin n))
    (hPQ : Disjoint P Q) (hRS : Disjoint R S)
    (hedge : ∀ u v, G.Adj u v ↔
      (u ∈ P ∨ v ∈ P) ∧ (u ∈ Q ∨ v ∈ Q) ∧ (u ∈ R ∨ v ∈ R) ∧ (u ∈ S ∨ v ∈ S)) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      (∀ E : Circuit, Monotone2 E → circuitFun n E = graphFun G ∅ → D.size ≤ E.size) ∧
      HasStarProfile n G D := by
  classical
  obtain ⟨K, hK, hbudget⟩ := four_sides_budget G h4 P Q R S hPQ hRS hedge
  by_cases hE : G.edgeFinset.Nonempty
  · have hcover : ∀ e ∈ G.edgeFinset, ∃ u ∈ K, u ∈ e := by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        rcases hK u v (SimpleGraph.mem_edgeFinset.mp he) with hu | hv
        · exact ⟨u, hu, Sym2.mem_mk_left _ _⟩
        · exact ⟨v, hv, Sym2.mem_mk_right _ _⟩
    obtain ⟨D, hD, hDf, hDs, hDsize⟩ :=
      PEqualNP.Outside.L_meta_2448.StarCoverPrototype.star_cover_witness G hE K hcover
    refine ⟨D, hD, hDf, ?_, hDs⟩
    intro E hmono hEf
    have hsupport := PEqualNP.Outside.L_meta_2448_aux.inputBound.main n G E
      (fun g hg => (hmono g hg).2) hEf
    omega
  · exact PEqualNP.Outside.L_meta_2448_aux.oneJunkStar.empty_graph_star_minimum G
      (Finset.not_nonempty_iff_eq_empty.mp hE)

end PEqualNP.Outside.L_meta_2448_aux.twoSilentProducts
