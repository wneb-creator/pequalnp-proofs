import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3679

namespace FlatDag3679
structure D (n : ℕ) where
  m : ℕ
  out : ℕ
  out_lt : out < n+m
  isAnd : ℕ → Bool
  a : ℕ → ℕ
  b : ℕ → ℕ
  a_lt : ∀ w, n ≤ w → w < n+m → a w < w
  b_lt : ∀ w, n ≤ w → w < n+m → b w < w
  val : ℕ → (Fin n → Bool) → Bool
  inp : ∀ i : Fin n, ∀ x, val i.val x = x i
  step : ∀ w, n ≤ w → w < n+m → ∀ x, val w x = if isAnd w then val (a w) x && val (b w) x else val (a w) x || val (b w) x
namespace D
variable {n : ℕ} (d : D n)
def clean (w : ℕ) := ∀ i : Fin n, d.val w (fun j => decide (j=i)) = false
noncomputable def top : Finset ℕ := by classical exact (Finset.range (n+d.m)).filter (fun w => n ≤ w ∧ d.isAnd w=false ∧ d.clean w)
structure Base (U : ℕ → Prop) : Prop where
  children : ∀ w, n ≤ w → w < n+d.m → U w → d.isAnd w=false ∧ U (d.a w) ∧ U (d.b w)
  andArgs : ∀ w, n ≤ w → w < n+d.m → d.isAnd w=true → U (d.a w) ∧ U (d.b w)
def supp (w : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => d.val w (fun j => decide (j=i)) = true)
end D
end FlatDag3679

-- Fourteen selector vertices face eleven data vertices and fourteen private columns.
-- The data sums use the dual of the construction of R. E. Tarjan,
-- Complexity of monotone networks for computing conjunctions (1978).
namespace Upper3679
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
abbrev V := Fin 39
def edges : List (V × V) := [(25,0),(25,9),(25,11),(26,1),(26,10),(26,12),(27,2),(27,9),(27,13),(28,3),(28,10),(28,14),(29,6),(29,9),(29,15),(30,6),(30,7),(30,9),(30,16),(31,6),(31,7),(31,8),(31,9),(31,17),(32,6),(32,10),(32,18),(33,6),(33,7),(33,10),(33,19),(34,6),(34,7),(34,8),(34,10),(34,20),(35,0),(35,4),(35,6),(35,7),(35,8),(35,9),(35,21),(36,1),(36,4),(36,6),(36,7),(36,8),(36,10),(36,22),(37,2),(37,5),(37,6),(37,7),(37,8),(37,9),(37,23),(38,3),(38,5),(38,6),(38,7),(38,8),(38,10),(38,24)]
def G : SimpleGraph V where
  Adj x y := x ≠ y ∧ ((x,y) ∈ edges ∨ (y,x) ∈ edges)
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
instance : DecidableRel G.Adj := fun x y => inferInstanceAs (Decidable (x ≠ y ∧ ((x,y) ∈ edges ∨ (y,x) ∈ edges)))
def side (i : V) := decide (25 ≤ i.val)
theorem bip : ∀ x y, G.Adj x y → side x ≠ side y := by decide +kernel
private theorem noLoops : ∀ e ∈ edges, e.1 ≠ e.2 := by decide +kernel
def C : Circuit := ⟨[⟨.or,[0,9]⟩,⟨.or,[1,10]⟩,⟨.or,[2,9]⟩,⟨.or,[3,10]⟩,⟨.or,[6,9]⟩,⟨.or,[43,7]⟩,⟨.or,[44,8]⟩,⟨.or,[6,10]⟩,⟨.or,[46,7]⟩,⟨.or,[47,8]⟩,⟨.and,[45,48]⟩,⟨.or,[49,4]⟩,⟨.or,[49,5]⟩,⟨.or,[39,50]⟩,⟨.or,[40,50]⟩,⟨.or,[41,51]⟩,⟨.or,[42,51]⟩,⟨.or,[39,11]⟩,⟨.and,[56,25]⟩,⟨.or,[40,12]⟩,⟨.and,[58,26]⟩,⟨.or,[41,13]⟩,⟨.and,[60,27]⟩,⟨.or,[42,14]⟩,⟨.and,[62,28]⟩,⟨.or,[43,15]⟩,⟨.and,[64,29]⟩,⟨.or,[44,16]⟩,⟨.and,[66,30]⟩,⟨.or,[45,17]⟩,⟨.and,[68,31]⟩,⟨.or,[46,18]⟩,⟨.and,[70,32]⟩,⟨.or,[47,19]⟩,⟨.and,[72,33]⟩,⟨.or,[48,20]⟩,⟨.and,[74,34]⟩,⟨.or,[52,21]⟩,⟨.and,[76,35]⟩,⟨.or,[53,22]⟩,⟨.and,[78,36]⟩,⟨.or,[54,23]⟩,⟨.and,[80,37]⟩,⟨.or,[55,24]⟩,⟨.and,[82,38]⟩,⟨.or,[57,59]⟩,⟨.or,[84,61]⟩,⟨.or,[85,63]⟩,⟨.or,[86,65]⟩,⟨.or,[87,67]⟩,⟨.or,[88,69]⟩,⟨.or,[89,71]⟩,⟨.or,[90,73]⟩,⟨.or,[91,75]⟩,⟨.or,[92,77]⟩,⟨.or,[93,79]⟩,⟨.or,[94,81]⟩,⟨.or,[95,83]⟩],96⟩
theorem size : C.size = 58 := by decide
theorem ao : IsAO2 39 C := by decide +kernel
private theorem fun_edges (x : V → Bool) : graphFun G ∅ x = edges.any (fun e => x e.1 && x e.2) := by
  apply Bool.eq_iff_iff.mpr; simp only [graphFun,Finset.notMem_empty, false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq,List.any_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨u,v,⟨_,h|h⟩,hu,hv⟩; exact ⟨(u,v),h,hu,hv⟩; exact ⟨(v,u),h,hv,hu⟩
  · rintro ⟨⟨u,v⟩,h,hu,hv⟩; exact ⟨u,v,⟨noLoops _ h,Or.inl h⟩,hu,hv⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem row0 : ∀ b0 b9 b11 b25 : Bool, (((b0 || b9) || b11) && b25) = ((b25 && b0) || (b25 && b9) || (b25 && b11)) := by decide +kernel
private theorem row1 : ∀ b1 b10 b12 b26 : Bool, (((b1 || b10) || b12) && b26) = ((b26 && b1) || (b26 && b10) || (b26 && b12)) := by decide +kernel
private theorem row2 : ∀ b2 b9 b13 b27 : Bool, (((b2 || b9) || b13) && b27) = ((b27 && b2) || (b27 && b9) || (b27 && b13)) := by decide +kernel
private theorem row3 : ∀ b3 b10 b14 b28 : Bool, (((b3 || b10) || b14) && b28) = ((b28 && b3) || (b28 && b10) || (b28 && b14)) := by decide +kernel
private theorem row4 : ∀ b6 b9 b15 b29 : Bool, (((b6 || b9) || b15) && b29) = ((b29 && b6) || (b29 && b9) || (b29 && b15)) := by decide +kernel
private theorem row5 : ∀ b6 b9 b7 b16 b30 : Bool, ((((b6 || b9) || b7) || b16) && b30) = ((b30 && b6) || (b30 && b7) || (b30 && b9) || (b30 && b16)) := by decide +kernel
private theorem row6 : ∀ b6 b9 b7 b8 b17 b31 : Bool, (((((b6 || b9) || b7) || b8) || b17) && b31) = ((b31 && b6) || (b31 && b7) || (b31 && b8) || (b31 && b9) || (b31 && b17)) := by decide +kernel
private theorem row7 : ∀ b6 b10 b18 b32 : Bool, (((b6 || b10) || b18) && b32) = ((b32 && b6) || (b32 && b10) || (b32 && b18)) := by decide +kernel
private theorem row8 : ∀ b6 b10 b7 b19 b33 : Bool, ((((b6 || b10) || b7) || b19) && b33) = ((b33 && b6) || (b33 && b7) || (b33 && b10) || (b33 && b19)) := by decide +kernel
private theorem row9 : ∀ b6 b10 b7 b8 b20 b34 : Bool, (((((b6 || b10) || b7) || b8) || b20) && b34) = ((b34 && b6) || (b34 && b7) || (b34 && b8) || (b34 && b10) || (b34 && b20)) := by decide +kernel
private theorem row10 : ∀ b0 b9 b6 b7 b8 b10 b4 b21 b35 : Bool, ((((b0 || b9) || (((((b6 || b9) || b7) || b8) && (((b6 || b10) || b7) || b8)) || b4)) || b21) && b35) = ((b35 && b0) || (b35 && b4) || (b35 && b6) || (b35 && b7) || (b35 && b8) || (b35 && b9) || (b35 && b21)) := by decide +kernel
private theorem row11 : ∀ b1 b10 b6 b9 b7 b8 b4 b22 b36 : Bool, ((((b1 || b10) || (((((b6 || b9) || b7) || b8) && (((b6 || b10) || b7) || b8)) || b4)) || b22) && b36) = ((b36 && b1) || (b36 && b4) || (b36 && b6) || (b36 && b7) || (b36 && b8) || (b36 && b10) || (b36 && b22)) := by decide +kernel
private theorem row12 : ∀ b2 b9 b6 b7 b8 b10 b5 b23 b37 : Bool, ((((b2 || b9) || (((((b6 || b9) || b7) || b8) && (((b6 || b10) || b7) || b8)) || b5)) || b23) && b37) = ((b37 && b2) || (b37 && b5) || (b37 && b6) || (b37 && b7) || (b37 && b8) || (b37 && b9) || (b37 && b23)) := by decide +kernel
private theorem row13 : ∀ b3 b10 b6 b9 b7 b8 b5 b24 b38 : Bool, ((((b3 || b10) || (((((b6 || b9) || b7) || b8) && (((b6 || b10) || b7) || b8)) || b5)) || b24) && b38) = ((b38 && b3) || (b38 && b5) || (b38 && b6) || (b38 && b7) || (b38 && b8) || (b38 && b10) || (b38 && b24)) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem computes : circuitFun 39 C = graphFun G ∅ := by
  funext x; rw [fun_edges]; unfold circuitFun
  rw [show List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,x 26,x 27,x 28,x 29,x 30,x 31,x 32,x 33,x 34,x 35,x 36,x 37,x 38] from rfl]
  simp [C,Circuit.eval,Circuit.wires,GateOp.eval,edges]
  generalize x (0 : V) = b0; generalize x (1 : V) = b1; generalize x (2 : V) = b2; generalize x (3 : V) = b3; generalize x (4 : V) = b4; generalize x (5 : V) = b5; generalize x (6 : V) = b6; generalize x (7 : V) = b7; generalize x (8 : V) = b8; generalize x (9 : V) = b9; generalize x (10 : V) = b10; generalize x (11 : V) = b11; generalize x (12 : V) = b12; generalize x (13 : V) = b13; generalize x (14 : V) = b14; generalize x (15 : V) = b15; generalize x (16 : V) = b16; generalize x (17 : V) = b17; generalize x (18 : V) = b18; generalize x (19 : V) = b19; generalize x (20 : V) = b20; generalize x (21 : V) = b21; generalize x (22 : V) = b22; generalize x (23 : V) = b23; generalize x (24 : V) = b24; generalize x (25 : V) = b25; generalize x (26 : V) = b26; generalize x (27 : V) = b27; generalize x (28 : V) = b28; generalize x (29 : V) = b29; generalize x (30 : V) = b30; generalize x (31 : V) = b31; generalize x (32 : V) = b32; generalize x (33 : V) = b33; generalize x (34 : V) = b34; generalize x (35 : V) = b35; generalize x (36 : V) = b36; generalize x (37 : V) = b37; generalize x (38 : V) = b38
  have h0 := row0 b0 b9 b11 b25
  have h1 := row1 b1 b10 b12 b26
  have h2 := row2 b2 b9 b13 b27
  have h3 := row3 b3 b10 b14 b28
  have h4 := row4 b6 b9 b15 b29
  have h5 := row5 b6 b9 b7 b16 b30
  have h6 := row6 b6 b9 b7 b8 b17 b31
  have h7 := row7 b6 b10 b18 b32
  have h8 := row8 b6 b10 b7 b19 b33
  have h9 := row9 b6 b10 b7 b8 b20 b34
  have h10 := row10 b0 b9 b6 b7 b8 b10 b4 b21 b35
  have h11 := row11 b1 b10 b6 b9 b7 b8 b4 b22 b36
  have h12 := row12 b2 b9 b6 b7 b8 b10 b5 b23 b37
  have h13 := row13 b3 b10 b6 b9 b7 b8 b5 b24 b38
  simp only [Bool.or_assoc] at *
  simp only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,Bool.or_assoc]
end Upper3679

namespace FlatDag3679
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
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

open PEqualNP.EdgeOwnership in
lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.EdgeOwnership in
lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h

theorem fromCircuit (C : Circuit) (hao : IsAO2 39 C)
    (hc : circuitFun 39 C = graphFun Upper3679.G ∅)
    (hflat : ∀ i < C.gates.length, ∀ j < C.gates.length, (gateAt C i).op = .and →
      (gateAt C j).op = .and → ¬ InCone 39 C i j) :
    ∃ d : D 39, d.m = C.size ∧ (∀ x, d.val d.out x = graphFun Upper3679.G ∅ x) ∧
      ∃ U : ℕ → Prop, d.Base U := by
  classical
  let a := fun k => (gateAt C k).inputs.getD 0 0
  let b := fun k => (gateAt C k).inputs.getD 1 0
  have spec (k) (hk : k < C.gates.length) :
      ((gateAt C k).op = .and ∨ (gateAt C k).op = .or) ∧
      (gateAt C k).inputs = [a k,b k] := by
    have hm : gateAt C k ∈ C.gates := gateAt_eq C k hk ▸ List.getElem_mem hk
    obtain ⟨p,q,h⟩ := List.length_eq_two.mp (hao.2.2 _ hm)
    exact ⟨hao.1 _ hm, by simp [a,b,h]⟩
  have bounds k (hk : k < C.gates.length) : a k < 39+k ∧ b k < 39+k := by
    constructor <;> apply hao.2.1 k hk <;> simp [(spec k hk).2]
  have hout : C.output < 39 + C.gates.length := by
    by_contra! h
    let x : Fin 39 → Bool := fun _ => true
    have hv := congrFun hc x
    change (C.wires (List.ofFn x)).getD C.output false = _ at hv
    rw [getD_ge_length _ _ (by rw [wires_length]; exact h)] at hv
    have hg : graphFun Upper3679.G ∅ x = true := by
      simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]; right
      exact ⟨25,0, by decide, rfl,rfl⟩
    simp [hg] at hv
  let d : D 39 := {
    m := C.gates.length, out := C.output, out_lt := hout
    isAnd := fun w => decide ((gateAt C (w-39)).op = .and)
    a := fun w => a (w-39), b := fun w => b (w-39)
    a_lt := fun w hw hw' => lt_of_lt_of_eq (bounds (w-39) (by omega)).1 (by omega)
    b_lt := fun w hw hw' => lt_of_lt_of_eq (bounds (w-39) (by omega)).2 (by omega)
    val := fun w x => W 39 C x w, inp := fun i x => W_input _ _ _ _ i.isLt
    step := by
      intro w hw hw' x
      obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hw
      have hk : k < C.gates.length := by omega
      rcases spec k hk with ⟨hop|hop,hin⟩ <;>
        simp [W_gate 39 C x k hk, hop, hin, GateOp.eval, (bounds k hk).1, (bounds k hk).2] }
  let U := fun w => ∀ (hw : 39 ≤ w) i, i = w-39 ∨ InCone 39 C i (w-39) →
    (gateAt C i).op ≠ .and
  refine ⟨d,rfl,congrFun hc,U,?_,?_⟩
  · intro w hw hw' hu
    change w < 39+C.gates.length at hw'
    let k := w-39
    have hk : k < C.gates.length := by dsimp [k]; omega
    have pass (v) (hv : v ∈ (gateAt C k).inputs) : U v := by
      intro hn i hi
      exact hu hw i (Or.inr ((inCone_iff 39 C i k hk).2
        ⟨v,hv,hn,hao.2.1 k hk v hv,hi⟩))
    exact ⟨by simpa [d] using hu hw (w-39) (Or.inl rfl),
      pass (a k) (by simp [(spec k hk).2]),pass (b k) (by simp [(spec k hk).2])⟩
  · intro w hw hw' hand
    change w < 39+C.gates.length at hw'
    let k := w-39
    have hk : k < C.gates.length := by dsimp [k]; omega
    have hop : (gateAt C k).op = .and := by simpa [d,k] using hand
    have pass (v) (hv : v ∈ (gateAt C k).inputs) : U v := by
      intro hn i hi hiand
      have hcone := (inCone_iff 39 C i k hk).2 ⟨v,hv,hn,hao.2.1 k hk v hv,hi⟩
      by_cases hit : i < C.gates.length
      · exact hflat i hit k hk hiand hop hcone
      · simp [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_lt hit)] at hiand
    exact ⟨pass (a k) (by simp [(spec k hk).2]),pass (b k) (by simp [(spec k hk).2])⟩
end FlatDag3679

namespace Rows3679
open Upper3679 PEqualNP.MetaComplexity.NestedCover
def left (i : Fin 14) : V := ⟨25+i.val,by omega⟩
def right (j : Fin 25) : V := ⟨j.val,by omega⟩
def privateCol (i : Fin 14) : Fin 25 := ⟨11+i.val,by omega⟩
def row (i : Fin 14) := Finset.univ.filter (fun j : Fin 25 => G.Adj (left i) (right j))
theorem private_mem : ∀ i j : Fin 14, privateCol j ∈ row i ↔ i=j := by decide +kernel
theorem nonempty (i : Fin 14) : (row i).Nonempty := ⟨_,(private_mem i i).mpr rfl⟩
def mask (S : Finset V) : V → Bool := fun u => decide (u ∈ S)
theorem graph_two (u v : V) : graphFun G ∅ (mask {u,v}) = true ↔ G.Adj u v := by
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq,mask,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨a,b,h,(rfl|rfl),(rfl|rfl)⟩ <;> first | exact h | exact h.symm | exact (G.irrefl h).elim
  · intro h; exact ⟨_,_,h,Or.inl rfl,Or.inr rfl⟩
theorem split : ∀ u : V, (∃ i, left i=u) ∨ (∃ j, right j=u) := by decide +kernel
theorem noLeft : ∀ i j, ¬G.Adj (left i) (left j) := by decide +kernel
theorem noRight : ∀ i j, ¬G.Adj (right i) (right j) := by decide +kernel
end Rows3679

namespace FlatDag3679.D
open Rows3679 Upper3679
open PEqualNP.MetaComplexity.NestedCover
variable {n : ℕ} (d : D n)

theorem baseFacts {U : ℕ → Prop} (base : d.Base U) (w : ℕ) (lim : w < n+d.m) (hu : U w) :
    (d.supp w).Nonempty ∧ ∀ x, d.val w x = true ↔ ∃ i ∈ d.supp w, x i = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · let j : Fin n := ⟨w,hw⟩
      have eq : d.supp w = {j} := by
        ext i; simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        change d.val j.val _ = true ↔ _
        rw [d.inp]; simp [eq_comm]
      rw [eq]; refine ⟨Finset.singleton_nonempty _, ?_⟩
      intro x; simpa [j] using (show d.val j.val x = true ↔ x j = true by rw [d.inp])
    · have hn := Nat.le_of_not_gt hw
      obtain ⟨op,ha,hb⟩ := base.children w hn lim hu
      have la := d.a_lt w hn lim
      have lb := d.b_lt w hn lim
      obtain ⟨na,sa⟩ := ih _ la (la.trans lim) ha
      obtain ⟨_,sb⟩ := ih _ lb (lb.trans lim) hb
      have su : d.supp w = d.supp (d.a w) ∪ d.supp (d.b w) := by
        ext i; simp [supp,d.step w hn lim,op]
      rw [su]; refine ⟨na.mono Finset.subset_union_left,?_⟩
      intro x; simp only [d.step w hn lim,op,Bool.false_eq_true,ite_false,Bool.or_eq_true,sa,sb,Finset.mem_union]
      aesop

private theorem sees {S : Finset V} (i : Fin 14) (j : Fin 25)
    {f : Fin k → V} (onSide : ∀ u ∈ S, ∃ p, f p = u) (other : ∀ p, f p ≠ right j) :
    (∃ u ∈ S, mask {left i,right j} u = true) ↔ left i ∈ S := by
  constructor
  · rintro ⟨u,hu,hit⟩
    have mem : u=left i ∨ u=right j := by simpa [mask] using hit
    rcases mem with rfl|rfl
    · exact hu
    · obtain ⟨p,ep⟩ := onSide _ hu; exact (other p ep).elim
  · intro hi; exact ⟨_,hi,by simp [mask]⟩

private theorem seesRight {S : Finset V} (i : Fin 14) (j : Fin 25)
    (onSide : ∀ u ∈ S, ∃ p, right p = u) :
    (∃ u ∈ S, mask {left i,right j} u = true) ↔ right j ∈ S := by
  constructor
  · rintro ⟨u,hu,hit⟩
    have mem : u=left i ∨ u=right j := by simpa [mask] using hit
    rcases mem with rfl|rfl
    · obtain ⟨p,ep⟩ := onSide _ hu
      have e := congrArg Fin.val ep; simp only [right,left] at e; omega
    · exact hu
  · intro hj; exact ⟨_,hj,by simp [mask]⟩

variable (Dg : D 39)

theorem orient {U : ℕ → Prop} (base : Dg.Base U) (w : ℕ)
    (lo : 39 ≤ w) (lim : w < 39+Dg.m) (op : Dg.isAnd w=true)
    (below : ∀ x, Dg.val w x=true → graphFun G ∅ x=true) :
    ∃ p q : ℕ, p < 39+Dg.m ∧ q < 39+Dg.m ∧ U p ∧ U q ∧
      (∀ u ∈ Dg.supp p, ∃ t, left t=u) ∧ (∀ u ∈ Dg.supp q, ∃ t, right t=u) ∧
      ∀ i j, Dg.val w (mask {left i,right j})=true ↔ left i ∈ Dg.supp p ∧ right j ∈ Dg.supp q := by
  let a := Dg.a w
  let b := Dg.b w
  have al : a < 39+Dg.m := (Dg.a_lt w lo lim).trans lim
  have bl : b < 39+Dg.m := (Dg.b_lt w lo lim).trans lim
  obtain ⟨au,bu⟩ := base.andArgs w lo lim op
  obtain ⟨⟨u,hu⟩,sa⟩ := Dg.baseFacts base a al au
  obtain ⟨⟨v,hv⟩,sb⟩ := Dg.baseFacts base b bl bu
  have sem (x : V → Bool) : Dg.val w x=true ↔ (∃ i ∈ Dg.supp a, x i=true) ∧ (∃ i ∈ Dg.supp b, x i=true) := by
    rw [Dg.step w lo lim,op]; simpa only [ite_true,Bool.and_eq_true] using and_congr (sa x) (sb x)
  have adj (i) (hi : i ∈ Dg.supp a) (j) (hj : j ∈ Dg.supp b) : G.Adj i j :=
    (graph_two i j).mp (below _ ((sem _).mpr ⟨⟨i,hi,by simp [mask]⟩,⟨j,hj,by simp [mask]⟩⟩))
  have isR (i : Fin 14) (z : V) (h : G.Adj (left i) z) : ∃ t, right t=z :=
    (Rows3679.split z).resolve_left (by rintro ⟨t,rfl⟩; exact noLeft i t h)
  have isL (j : Fin 25) (z : V) (h : G.Adj (right j) z) : ∃ t, left t=z :=
    (Rows3679.split z).resolve_right (by rintro ⟨t,rfl⟩; exact noRight j t h)
  have lr (i : Fin 14) (j : Fin 25) : left i ≠ right j := by
    intro e; have e' := congrArg Fin.val e; simp only [left,right] at e'; omega
  rcases Rows3679.split u with ⟨i,rfl⟩|⟨i,rfl⟩
  · have br (z) (hz : z ∈ Dg.supp b) := isR i z (adj _ hu _ hz)
    obtain ⟨t,et⟩ := br _ hv
    have als (z) (hz : z ∈ Dg.supp a) := isL t z (et ▸ (adj _ hz _ hv).symm)
    exact ⟨a,b,al,bl,au,bu,als,br,fun i j => (sem _).trans (and_congr (sees i j als (fun p => lr p j)) (seesRight i j br))⟩
  · have bs (z) (hz : z ∈ Dg.supp b) := isL i z (adj _ hu _ hz)
    obtain ⟨t,et⟩ := bs _ hv
    have ars (z) (hz : z ∈ Dg.supp a) := isR t z (et ▸ (adj _ hz _ hv).symm)
    exact ⟨b,a,bl,al,bu,au,bs,ars,fun i j => (sem _).trans (((and_congr (seesRight i j ars) (sees i j bs (fun p => lr p j)))).trans and_comm)⟩
end FlatDag3679.D

-- Reverse the left OR network, accumulating the right supports of its rectangles.
namespace FlatTranspose3679

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def Av (B : List (Finset α)) (x : Finset α) : Prop := x.card ≤ 1 ∨ x ∈ B
inductive Built : List (Finset α) → Prop
  | nil : Built []
  | cons {B : List (Finset α)} {u v : Finset α} : Built B → Av B u → Av B v → Built ((u ∪ v) :: B)

omit [DecidableEq α] in
private theorem av_cons {B : List (Finset α)} {x t : Finset α} (h : Av B x) : Av (t :: B) x :=
  h.elim Or.inl (fun hh => Or.inr (List.mem_cons_of_mem _ hh))

private structure State (α β : Type*) [DecidableEq β] where
  keys : Finset (Finset α)
  label : Finset α → Finset β
  bank : List (Finset β)
  built : Built bank
  avail : ∀ u ∈ keys, Av bank (label u)

private def State.rel (q : State α β) (x : α) (y : β) : Prop :=
  ∃ u ∈ q.keys, x ∈ u ∧ y ∈ q.label u

private def State.price (q : State α β) := q.bank.length + q.keys.card

private theorem push (q : State α β) (u : Finset α) (v : Finset β) (hv : Av q.bank v) :
    ∃ p : State α β, p.keys = insert u q.keys ∧ p.price ≤ q.price + 1 ∧
      (∀ w, Av q.bank w → Av p.bank w) ∧
      ∀ x y, p.rel x y ↔ q.rel x y ∨ (x ∈ u ∧ y ∈ v) := by
  classical
  by_cases hu : u ∈ q.keys
  · let b := q.label u ∪ v
    let p : State α β := ⟨insert u q.keys, Function.update q.label u b, b :: q.bank,
      .cons q.built (q.avail u hu) hv, by
        intro t ht
        by_cases eq : t = u
        · subst t; exact Or.inr (by simp)
        · simp only [Function.update_of_ne eq]; exact av_cons (q.avail _ ((Finset.mem_insert.mp ht).resolve_left eq))⟩
    refine ⟨p, rfl, ?_, fun _ => av_cons, ?_⟩
    · simp [State.price,p,hu,Nat.add_right_comm]
    · intro x y; constructor
      · rintro ⟨t,ht,hx,hy⟩
        by_cases eq : t = u
        · subst t; change y ∈ Function.update q.label u b u at hy; simp [b] at hy
          exact hy.elim (fun h => Or.inl ⟨u,hu,hx,h⟩) (fun h => Or.inr ⟨hx,h⟩)
        · exact Or.inl ⟨t,(Finset.mem_insert.mp ht).resolve_left eq,hx,by simpa [p,eq] using hy⟩
      · rintro (⟨t,ht,hx,hy⟩ | ⟨hx,hy⟩)
        · refine ⟨t,Finset.mem_insert_of_mem ht,hx,?_⟩
          by_cases eq : t = u
          · subst t; simp [p,b,hy]
          · simpa [p,eq] using hy
        · exact ⟨u,Finset.mem_insert_self ..,hx,by simp [p,b,hy]⟩
  · let p : State α β := ⟨insert u q.keys, Function.update q.label u v, q.bank, q.built, by
        intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · simpa using hv
        · have ne : t ≠ u := fun e => hu (e ▸ ht)
          simpa [ne] using q.avail t ht⟩
    refine ⟨p,rfl,by simp [State.price,p,hu,Nat.add_assoc],fun _ h => h,?_⟩
    intro x y; constructor
    · rintro ⟨t,ht,hx,hy⟩
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact Or.inr ⟨hx,by simpa [p] using hy⟩
      · have ne : t ≠ u := fun e => hu (e ▸ ht)
        exact Or.inl ⟨t,ht,hx,by simpa [p,ne] using hy⟩
    · rintro (⟨t,ht,hx,hy⟩ | ⟨hx,hy⟩)
      · have ne : t ≠ u := fun e => hu (e ▸ ht)
        exact ⟨t,Finset.mem_insert_of_mem ht,hx,by simpa [p,ne] using hy⟩
      · exact ⟨u,Finset.mem_insert_self ..,hx,by simpa [p] using hy⟩

private theorem transfer {L : List (Finset α)} (bl : Built L) (q : State α β)
    (hk : ∀ t ∈ q.keys, Av L t) :
    ∃ p : State α β, (∀ t ∈ p.keys, t.card ≤ 1) ∧ p.price ≤ q.price + L.length ∧
      ∀ x y, p.rel x y ↔ q.rel x y := by
  classical
  induction bl generalizing q with
  | nil => exact ⟨q,fun t ht => by simpa [Av] using hk t ht,by simp,fun _ _ => Iff.rfl⟩
  | @cons L u v _ hu hv ih =>
    by_cases h : u ∪ v ∈ q.keys
    · let s : State α β := ⟨q.keys.erase (u ∪ v),q.label,q.bank,q.built,
        fun t ht => q.avail _ (Finset.mem_erase.mp ht).2⟩
      obtain ⟨s₁,hk₁,hp₁,ha₁,hr₁⟩ := push s u (q.label (u ∪ v)) (q.avail _ h)
      obtain ⟨s₂,hk₂,hp₂,_,hr₂⟩ := push s₁ v (q.label (u ∪ v)) (ha₁ _ (q.avail _ h))
      have hgood : ∀ t ∈ s₂.keys, Av L t := by
        intro t ht; rw [hk₂,hk₁] at ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact hv
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact hu
        obtain ⟨ne,hm⟩ := Finset.mem_erase.mp ht
        simpa [Av,ne] using hk t hm
      obtain ⟨p,hp,hle,hr⟩ := ih s₂ hgood
      refine ⟨p,hp,?_,?_⟩
      · have hc := Finset.card_erase_add_one h
        change s₁.price ≤ q.bank.length + (q.keys.erase (u ∪ v)).card + 1 at hp₁
        simp only [State.price,List.length_cons] at hle hp₂ ⊢; unfold State.price at hp₁; omega
      · intro x y; rw [hr,hr₂,hr₁]; constructor
        · rintro ((⟨t,ht,hx,hy⟩ | ⟨hx,hy⟩) | ⟨hx,hy⟩)
          · exact ⟨t,(Finset.mem_erase.mp ht).2,hx,hy⟩
          · exact ⟨_,h,Finset.mem_union_left _ hx,hy⟩
          · exact ⟨_,h,Finset.mem_union_right _ hx,hy⟩
        · rintro ⟨t,ht,hx,hy⟩
          by_cases eq : t = u ∪ v
          · subst t; exact (Finset.mem_union.mp hx).elim (fun hu => Or.inl (Or.inr ⟨hu,hy⟩)) (fun hv => Or.inr ⟨hv,hy⟩)
          · exact Or.inl (Or.inl ⟨t,Finset.mem_erase.mpr ⟨eq,ht⟩,hx,hy⟩)
    · obtain ⟨p,hp,hle,hr⟩ := ih q (fun t ht => by
        have ne : t ≠ u ∪ v := fun e => h (e ▸ ht)
        simpa [Av,ne] using hk t ht)
      exact ⟨p,hp,by simp only [List.length_cons]; omega,hr⟩

private theorem seed (R : List (Finset α × Finset β)) (B : List (Finset β)) (hb : Built B)
    (h : ∀ w ∈ R, Av B w.2) :
    ∃ q : State α β, (∀ t ∈ q.keys, ∃ w ∈ R, w.1 = t) ∧ q.price ≤ B.length + R.length ∧
      (∀ w, Av B w → Av q.bank w) ∧
      ∀ x y, q.rel x y ↔ ∃ w ∈ R, x ∈ w.1 ∧ y ∈ w.2 := by
  classical
  induction R with
  | nil =>
    let q : State α β := ⟨∅,fun _ => ∅,B,hb,by simp⟩
    exact ⟨q,by simp [q],by simp [State.price,q],fun _ h => h,by simp [State.rel,q]⟩
  | cons w R ih =>
    obtain ⟨q,hk,hp,ha,hr⟩ := ih (fun t ht => h t (List.mem_cons_of_mem _ ht))
    obtain ⟨p,hk',hp',ha',hr'⟩ := push q w.1 w.2 (ha _ (h _ List.mem_cons_self))
    refine ⟨p,?_,by simp only [List.length_cons]; omega, fun t ht => ha' _ (ha _ ht),?_⟩
    · intro t ht; rw [hk'] at ht; rcases Finset.mem_insert.mp ht with rfl | ht
      · exact ⟨w,List.mem_cons_self,rfl⟩
      · obtain ⟨z,hz,eq⟩ := hk _ ht; exact ⟨z,List.mem_cons_of_mem _ hz,eq⟩
    · intro x y; rw [hr',hr]; simp only [List.mem_cons]; aesop

theorem transpose [Fintype α] (L : List (Finset α)) (B : List (Finset β))
    (rect : List (Finset α × Finset β)) (row : α → Finset β)
    (bl : Built L) (bb : Built B) (hb : ∀ w ∈ rect, Av L w.1 ∧ Av B w.2)
    (cover : ∀ x y, y ∈ row x ↔ ∃ w ∈ rect, x ∈ w.1 ∧ y ∈ w.2)
    (ne : ∀ x, (row x).Nonempty) :
    ∃ out : List (Finset β), Built out ∧ (∀ x, Av out (row x)) ∧
      out.length + Fintype.card α ≤ B.length + rect.length + L.length := by
  classical
  obtain ⟨q,hk,hp,_,hr⟩ := seed rect B bb (fun _ hw => (hb _ hw).2)
  obtain ⟨p,hsmall,hp',hr'⟩ := transfer bl q (fun t ht => by
    obtain ⟨w,hw,rfl⟩ := hk t ht; exact (hb _ hw).1)
  have keyeq (x : α) (u : Finset α) (hu : u ∈ p.keys) (hx : x ∈ u) : u = {x} := by
    ext z; simp only [Finset.mem_singleton]
    exact ⟨fun hz => Finset.card_le_one.mp (hsmall _ hu) _ hz _ hx,fun e => e ▸ hx⟩
  have rep (x : α) (y : β) : y ∈ row x ↔ p.rel x y := (cover x y).trans ((hr x y).symm.trans (hr' x y).symm)
  have member (x : α) : {x} ∈ p.keys := by
    obtain ⟨y,hy⟩ := ne x
    obtain ⟨u,hu,hx,_⟩ := (rep x y).mp hy
    exact keyeq x u hu hx ▸ hu
  have size : Fintype.card α ≤ p.keys.card := by
    let f (x : α) : {t // t ∈ p.keys} := ⟨{x},member x⟩
    have inj : Function.Injective f := by intro x y e; simpa [f] using congrArg Subtype.val e
    simpa using Fintype.card_le_of_injective f inj
  refine ⟨p.bank,p.built,?_,?_⟩
  · intro x
    have eq : row x = p.label {x} := by
      ext y; rw [rep]; constructor
      · rintro ⟨t,ht,hx,hy⟩; exact keyeq x t ht hx ▸ hy
      · intro hy; exact ⟨{x},member x,by simp,hy⟩
    rw [eq]; exact p.avail _ (member x)
  · unfold State.price at hp hp'; omega

theorem fooling_bound [Fintype α] (rect : List (Finset α × Finset β))
    (R : α → β → Prop) (marker : α → β)
    (cover : ∀ x y, R x y ↔ ∃ w ∈ rect, x ∈ w.1 ∧ y ∈ w.2)
    (diag : ∀ x z, R x (marker z) ↔ x = z) : Fintype.card α ≤ rect.length := by
  classical
  have pick (x : α) : ∃ j : Fin rect.length, x ∈ rect[j].1 ∧ marker x ∈ rect[j].2 := by
    obtain ⟨w,hw,hx,hm⟩ := (cover x _).mp ((diag x x).mpr rfl)
    obtain ⟨j,hj,ej⟩ := List.getElem_of_mem hw
    exact ⟨⟨j,hj⟩,by simpa [ej] using hx,by simpa [ej] using hm⟩
  let f := fun x => (pick x).choose
  have hf (x : α) : x ∈ rect[f x].1 ∧ marker x ∈ rect[f x].2 := (pick x).choose_spec
  have inj : Function.Injective f := by
    intro x z eq
    exact (diag x z).mp ((cover x _).mpr
      ⟨rect[f x],List.getElem_mem _,(hf x).1,(congrArg (fun j => marker z ∈ (rect.get j).2) eq).mpr (hf z).2⟩)
  simpa using Fintype.card_le_of_injective f inj

theorem flat_price [Fintype α] (L : List (Finset α)) (B : List (Finset β))
    (rect : List (Finset α × Finset β)) (row : α → Finset β) (marker : α → β)
    (bl : Built L) (bb : Built B) (hb : ∀ w ∈ rect, Av L w.1 ∧ Av B w.2)
    (cover : ∀ x y, y ∈ row x ↔ ∃ w ∈ rect, x ∈ w.1 ∧ y ∈ w.2)
    (diag : ∀ x z, marker z ∈ row x ↔ x = z)
    (k size : ℕ) (budget : L.length + B.length + 2 * rect.length ≤ size + 1)
    (hard : ∀ out, Built out → (∀ x, Av out (row x)) → k ≤ out.length) :
    k + 2 * Fintype.card α ≤ size + 1 := by
  have hm := fooling_bound rect (fun x y => y ∈ row x) marker cover diag
  obtain ⟨out,ho,ha,hp⟩ := transpose L B rect row bl bb hb cover
    (fun x => ⟨marker x,(diag x x).mpr rfl⟩)
  have := hard _ ho ha
  omega

end FlatTranspose3679

namespace FlatDag3679.D
open Finset FlatTranspose3679
variable (d : D 39)

def On {k : ℕ} (f : Fin k → Fin 39) (w : ℕ) := ∀ i ∈ d.supp w, ∃ j, f j = i

def proj {k : ℕ} (f : Fin k → Fin 39) (w : ℕ) := univ.filter (fun j => f j ∈ d.supp w)

noncomputable def bots (U : ℕ → Prop) : Finset ℕ := by
  classical exact (range (39+d.m)).filter (fun w => 39 ≤ w ∧ U w ∧ ¬d.clean w)

private def paid {k : ℕ} (f : Fin k → Fin 39) (U : ℕ → Prop) (w : ℕ) :=
  39 ≤ w ∧ U w ∧ d.On f w ∧ 1 < (d.proj f w).card

open Classical in
private theorem bank {k : ℕ} (f : Fin k → Fin 39) (inj : Function.Injective f)
    {U : ℕ → Prop} (base : d.Base U) (t : ℕ) (ht : t ≤ 39+d.m) :
    ∃ L : List (Finset (Fin k)), Built L ∧
      L.length ≤ ((range t).filter (d.paid f U)).card ∧
      ∀ w, w < t → U w → d.On f w → Av L (d.proj f w) := by
  classical
  induction t with
  | zero => exact ⟨[], .nil, by simp, by omega⟩
  | succ t ih =>
    obtain ⟨L, bl, len, avail⟩ := ih (by omega)
    by_cases p : d.paid f U t
    · have ⟨hg, hu, hon, _⟩ := p
      have bound : t < 39+d.m := by omega
      obtain ⟨hor, ua, ub⟩ := base.children t hg bound hu
      have eqs : d.supp t = d.supp (d.a t) ∪ d.supp (d.b t) := by
        ext i; simp [supp, d.step t hg bound, hor]
      have eqp : d.proj f t = d.proj f (d.a t) ∪ d.proj f (d.b t) := by
        ext; simp [proj,eqs]
      rw [On,eqs] at hon
      have ba := Built.cons bl (avail _ (d.a_lt t hg bound) ua (fun i h => hon i (mem_union_left _ h)))
        (avail _ (d.b_lt t hg bound) ub (fun i h => hon i (mem_union_right _ h)))
      rw [← eqp] at ba
      refine ⟨_ :: L, ba, ?_, ?_⟩
      · simpa [range_add_one,filter_insert,p] using Nat.succ_le_succ len
      · intro w hw uw onw
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hw) with h | rfl
        · exact (avail w h uw onw).elim Or.inl (fun m => Or.inr (List.mem_cons_of_mem _ m))
        · exact Or.inr (List.mem_cons_self ..)
    · refine ⟨L, bl, by simpa [range_add_one,filter_insert,p] using len, ?_⟩
      intro w hw uw onw
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hw) with h | rfl
      · exact avail w h uw onw
      · apply Or.inl
        by_cases hg : 39 ≤ w
        · exact le_of_not_gt (fun big => p ⟨hg,uw,onw,big⟩)
        · have hi : w < 39 := by omega
          apply card_le_one.mpr
          intro i mi j mj
          have hx (x : Fin k) (mx : x ∈ d.proj f w) : (⟨w,hi⟩ : Fin 39) = f x := by
            simpa [proj,supp,d.inp (⟨w,hi⟩ : Fin 39)] using mx
          exact inj ((hx _ mi).symm.trans (hx _ mj))

theorem banks {U : ℕ → Prop} (base : d.Base U) :
    ∃ L : List (Finset (Fin 14)), ∃ R : List (Finset (Fin 25)), Built L ∧ Built R ∧
      L.length + R.length ≤ (d.bots U).card ∧
      (∀ w, w < 39+d.m → U w → d.On Rows3679.left w → Av L (d.proj Rows3679.left w)) ∧
      (∀ w, w < 39+d.m → U w → d.On Rows3679.right w → Av R (d.proj Rows3679.right w)) := by
  classical
  obtain ⟨L,bl,cl,al⟩ := d.bank Rows3679.left (by intro i j h; apply Fin.ext; simpa [Rows3679.left] using congrArg Fin.val h) base _ le_rfl
  obtain ⟨R,br,cr,ar⟩ := d.bank Rows3679.right (by intro i j h; apply Fin.ext; simpa [Rows3679.right] using congrArg Fin.val h) base _ le_rfl
  refine ⟨L,R,bl,br,(Nat.add_le_add cl cr).trans ?_,al,ar⟩
  have witness {k} {f : Fin k → Fin 39} {w} (p : d.paid f U w) : (d.supp w).Nonempty := by
    obtain ⟨j,hj⟩ := card_pos.mp (show 0 < (d.proj f w).card from Nat.lt_trans Nat.zero_lt_one p.2.2.2)
    exact ⟨_,(mem_filter.mp hj).2⟩
  rw [← card_union_of_disjoint]
  · apply card_le_card
    intro w hw
    rcases mem_union.mp hw with h | h <;> obtain ⟨bound,p⟩ := mem_filter.mp h
    all_goals
      obtain ⟨i,hi⟩ := witness p
      refine mem_filter.mpr ⟨bound,p.1,p.2.1,fun hc => ?_⟩
      have hh := (mem_filter.mp hi).2
      simp [hc i] at hh
  · apply disjoint_left.mpr
    intro w hl hr
    have pl := (mem_filter.mp hl).2
    have pr := (mem_filter.mp hr).2
    obtain ⟨i,hi⟩ := witness pl
    obtain ⟨a,ea⟩ := pl.2.2.1 i hi
    obtain ⟨b,eb⟩ := pr.2.2.1 i hi
    have e := congrArg Fin.val (ea.trans eb.symm)
    change 25+a.val = b.val at e
    omega
end FlatDag3679.D

namespace FlatDag3679.D
variable {n : ℕ} (d : D n)

private theorem clean_ge {w : ℕ} (h : d.clean w) : n ≤ w := by
  by_contra! hw
  let i : Fin n := ⟨w,hw⟩
  have eq := d.inp i (fun j => decide (j=i))
  have bad := h i
  change d.val w _ = _ at eq
  simp [eq] at bad

private theorem or_iff {w : ℕ} (hn : n ≤ w) (hw : w < n + d.m) (ho : d.isAnd w = false) (x : Fin n → Bool) :
    d.val w x = true ↔ d.val (d.a w) x = true ∨ d.val (d.b w) x = true := by
  rw [d.step w hn hw x]; simp [ho]

private theorem clean_children {w : ℕ} (hn : n ≤ w) (hw : w < n + d.m) (ho : d.isAnd w = false) (hc : d.clean w) :
    d.clean (d.a w) ∧ d.clean (d.b w) := by
  have h (i : Fin n) := hc i
  simp only [d.step w hn hw,ho,Bool.false_eq_true,ite_false,Bool.or_eq_false_iff] at h
  exact ⟨fun i => (h i).1,fun i => (h i).2⟩

private noncomputable def remaining (k : ℕ) := d.top.filter (· < k)

private theorem gather (k : ℕ) (S : Finset ℕ)
    (hs : ∀ w ∈ S, w < n + d.m ∧ d.clean w ∧ (d.isAnd w = true ∨ w < k)) :
    ∃ K : Finset ℕ, (∀ w ∈ K, n ≤ w ∧ w < n+d.m ∧ d.isAnd w = true ∧ d.clean w) ∧
      K.card ≤ S.card + (d.remaining k).card ∧
      ∀ x, (∃ w ∈ S, d.val w x = true) ↔ ∃ w ∈ K, d.val w x = true := by
  classical
  induction k generalizing S with
  | zero =>
    refine ⟨S,?_,by omega,fun _ => Iff.rfl⟩
    intro w hw; obtain ⟨bound,hc,h|hf⟩ := hs w hw
    · exact ⟨d.clean_ge hc,bound,h,hc⟩
    · omega
  | succ k ih =>
    by_cases hit : k ∈ S ∧ d.isAnd k = false
    · obtain ⟨hin,hop⟩ := hit
      obtain ⟨bound,hc,_⟩ := hs k hin
      have hn := d.clean_ge hc
      obtain ⟨ha,hb⟩ := d.clean_children hn bound hop hc
      have la := d.a_lt k hn bound
      have lb := d.b_lt k hn bound
      let T := insert (d.a k) (insert (d.b k) (S.erase k))
      have hT : ∀ w ∈ T, w < n+d.m ∧ d.clean w ∧ (d.isAnd w=true ∨ w < k) := by
        intro w hw
        simp only [T,Finset.mem_insert,Finset.mem_erase] at hw
        rcases hw with rfl | rfl | ⟨ne,hm⟩
        · exact ⟨la.trans bound,ha,Or.inr la⟩
        · exact ⟨lb.trans bound,hb,Or.inr lb⟩
        · obtain ⟨bd,cl,eq|lt⟩ := hs w hm
          · exact ⟨bd,cl,Or.inl eq⟩
          · exact ⟨bd,cl,Or.inr (by omega)⟩
      obtain ⟨K,hK,price,rep⟩ := ih T hT
      have kt : k ∈ d.top := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr bound,hn,hop,hc⟩
      have inc : d.remaining (k+1) = insert k (d.remaining k) := by
        ext i; simp only [remaining,Finset.mem_filter,Finset.mem_insert]; constructor
        · rintro ⟨hi,lt⟩; by_cases e : i = k
          · exact Or.inl e
          · exact Or.inr ⟨hi,by omega⟩
        · rintro (rfl | ⟨hi,lt⟩); exact ⟨kt,by omega⟩; exact ⟨hi,by omega⟩
      have out : k ∉ d.remaining k := by simp [remaining]
      refine ⟨K,hK,?_,?_⟩
      · rw [inc,Finset.card_insert_of_notMem out]
        have h1 := Finset.card_insert_le (d.a k) (insert (d.b k) (S.erase k))
        have h2 := Finset.card_insert_le (d.b k) (S.erase k)
        have h3 := Finset.card_erase_add_one hin
        dsimp only [T] at price; omega
      · intro x; rw [← rep x]; constructor
        · rintro ⟨w,hw,hval⟩
          by_cases e : w = k
          · subst w; rcases (d.or_iff hn bound hop x).mp hval with h | h
            · exact ⟨_,by simp [T],h⟩
            · exact ⟨_,by simp [T],h⟩
          · exact ⟨w,by simp [T,hw,e],hval⟩
        · rintro ⟨w,hw,hval⟩
          simp only [T,Finset.mem_insert,Finset.mem_erase] at hw
          rcases hw with rfl | rfl | ⟨_,hm⟩
          · exact ⟨k,hin,(d.or_iff hn bound hop x).mpr (Or.inl hval)⟩
          · exact ⟨k,hin,(d.or_iff hn bound hop x).mpr (Or.inr hval)⟩
          · exact ⟨w,hm,hval⟩
    · have hs' : ∀ w ∈ S, w < n+d.m ∧ d.clean w ∧ (d.isAnd w = true ∨ w < k) := by
        intro w hw; obtain ⟨bd,cl,eq|lt⟩ := hs w hw
        · exact ⟨bd,cl,Or.inl eq⟩
        · refine ⟨bd,cl,?_⟩; by_cases eq : w = k
          · subst w; left; cases h : d.isAnd k with
            | false => exact (hit ⟨hw,h⟩).elim
            | true => rfl
          · exact Or.inr (by omega)
      obtain ⟨K,hK,price,rep⟩ := ih S hs'
      have le : d.remaining k ⊆ d.remaining (k+1) := fun i hi => by
        obtain ⟨a,b⟩ := Finset.mem_filter.mp hi; exact Finset.mem_filter.mpr ⟨a,by omega⟩
      exact ⟨K,hK,price.trans (Nat.add_le_add_left (Finset.card_le_card le) _),rep⟩

theorem topCover (h : d.clean d.out) : ∃ K : Finset ℕ,
    (∀ w ∈ K, n ≤ w ∧ w < n+d.m ∧ d.isAnd w = true ∧ d.clean w) ∧
    K.card ≤ d.top.card + 1 ∧ ∀ x, d.val d.out x = true ↔ ∃ w ∈ K, d.val w x = true := by
  obtain ⟨K,hK,hp,rep⟩ := d.gather (n+d.m) {d.out} (by
    intro w hw; obtain rfl := Finset.mem_singleton.mp hw; exact ⟨d.out_lt,h,Or.inr d.out_lt⟩)
  have le : (d.remaining (n+d.m)).card ≤ d.top.card := Finset.card_le_card (Finset.filter_subset ..)
  refine ⟨K,hK,?_,fun x => by simpa using rep x⟩
  simp only [Finset.card_singleton] at hp; omega
end FlatDag3679.D

namespace FlatStructure3679
open FlatTranspose3679 FlatDag3679 Rows3679
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Upper3679 (G)

private theorem count (d : D 39) {U} (K : Finset ℕ)
    (ok : ∀ w ∈ K, 39 ≤ w ∧ w < 39+d.m ∧ d.isAnd w=true ∧ d.clean w) :
    (d.bots U).card + d.top.card + K.card ≤ d.m := by
  classical
  have bt : Disjoint (d.bots U) d.top := by
    refine Finset.disjoint_left.mpr ?_; intro w hw ht
    exact (Finset.mem_filter.mp hw).2.2.2 (Finset.mem_filter.mp ht).2.2.2
  have bk : Disjoint (d.bots U ∪ d.top) K := by
    refine Finset.disjoint_left.mpr ?_; intro w hw hk
    obtain ⟨lo,lim,op,cl⟩ := ok w hk
    rcases Finset.mem_union.mp hw with hb|ht
    · exact (Finset.mem_filter.mp hb).2.2.2 cl
    · simpa [op] using (Finset.mem_filter.mp ht).2.2.1
  have subset : (d.bots U ∪ d.top) ∪ K ⊆ Finset.Ico 39 (39+d.m) := by
    intro w hw; apply Finset.mem_Ico.mpr
    rcases Finset.mem_union.mp hw with h|h
    · rcases Finset.mem_union.mp h with hb|ht
      · obtain ⟨a,b⟩ := Finset.mem_filter.mp hb; exact ⟨b.1,Finset.mem_range.mp a⟩
      · obtain ⟨a,b⟩ := Finset.mem_filter.mp ht; exact ⟨b.1,Finset.mem_range.mp a⟩
    · exact ⟨(ok _ h).1,(ok _ h).2.1⟩
  have h := Finset.card_le_card subset
  rw [Finset.card_union_of_disjoint bk,Finset.card_union_of_disjoint bt,Nat.card_Ico] at h
  omega

theorem extract (C : Circuit) (hao : IsAO2 39 C)
    (hc : circuitFun 39 C = graphFun G ∅)
    (hflat : ∀ i < C.gates.length, ∀ j < C.gates.length, (gateAt C i).op = .and →
      (gateAt C j).op = .and → ¬ InCone 39 C i j) :
    ∃ (L : List (Finset (Fin 14))) (R : List (Finset (Fin 25)))
      (rect : List (Finset (Fin 14) × Finset (Fin 25))), Built L ∧ Built R ∧
      (∀ w ∈ rect, Av L w.1 ∧ Av R w.2) ∧
      (∀ x y, y ∈ row x ↔ ∃ w ∈ rect, x ∈ w.1 ∧ y ∈ w.2) ∧
      L.length + R.length + 2*rect.length ≤ C.size+1 := by
  classical
  obtain ⟨d,dm,eq,U,base⟩ := fromCircuit C hao hc hflat
  have cl : d.clean d.out := by
    intro i; apply Bool.eq_false_iff.mpr
    intro h; rw [eq] at h
    have me : mask {i,i} = fun j => decide (j=i) := by funext j; simp [mask]
    have bad : graphFun G ∅ (mask {i,i})=true := me ▸ h
    exact G.irrefl ((graph_two _ _).mp bad)
  obtain ⟨K,ok,kt,rep⟩ := d.topCover cl
  obtain ⟨L,R,bL,bR,sz,avL,avR⟩ := d.banks base
  have elem (w : ↥K) : ∃ r : Finset (Fin 14) × Finset (Fin 25),
      Av L r.1 ∧ Av R r.2 ∧ ∀ i j, d.val w.val (mask {left i,right j})=true ↔ i∈r.1 ∧ j∈r.2 := by
    obtain ⟨lo,lim,op,_⟩ := ok _ w.property
    have below (x) (h : d.val w.val x=true) : graphFun G ∅ x=true := (eq x) ▸ (rep x).mpr ⟨_,w.property,h⟩
    obtain ⟨a,b,al,bl,au,bu,as',bs',geom⟩ := d.orient base w.val lo lim op below
    exact ⟨(d.proj left a,d.proj right b), avL a al au as',avR b bl bu bs',fun i j => by simpa [D.proj] using geom i j⟩
  choose r hr using elem
  let rect := K.attach.toList.map r
  have mem (s) : s ∈ rect ↔ ∃ w : ↥K, r w=s := by simp [rect]
  refine ⟨L,R,rect,bL,bR,?_,?_,?_⟩
  · intro s hs; obtain ⟨w,rfl⟩ := (mem s).mp hs; exact ⟨(hr w).1,(hr w).2.1⟩
  · intro i j
    have step : j ∈ row i ↔ d.val d.out (mask {left i,right j})=true := by
      rw [eq,graph_two]; simp [row]
    rw [step,rep]; constructor
    · rintro ⟨w,hw,H⟩; let t : ↥K := ⟨w,hw⟩
      exact ⟨r t,(mem _).mpr ⟨t,rfl⟩,((hr t).2.2 i j).mp H⟩
    · rintro ⟨s,hs,hi,hj⟩; obtain ⟨t,rfl⟩ := (mem s).mp hs
      exact ⟨t.val,t.property,((hr t).2.2 i j).mpr ⟨hi,hj⟩⟩
  · have tot := count (U := U) d K ok
    have len : rect.length = K.card := by simp [rect]
    omega
end FlatStructure3679

namespace Rectangle3679
open FlatTranspose3679 Rows3679

theorem lower (L : List (Finset (Fin 14))) (B : List (Finset (Fin 25)))
    (rect : List (Finset (Fin 14) × Finset (Fin 25))) (m : ℕ)
    (bl : Built L) (bb : Built B) (hb : ∀ w ∈ rect, Av L w.1 ∧ Av B w.2)
    (cover : ∀ x y, y ∈ row x ↔ ∃ w ∈ rect, x ∈ w.1 ∧ y ∈ w.2)
    (budget : L.length + B.length + 2*rect.length ≤ m+1)
    (hard : ∀ out, Built out → (∀ i, Av out (row i)) → 32 ≤ out.length) : 59 ≤ m := by
  have h := flat_price L B rect row privateCol bl bb hb cover private_mem 32 m budget hard
  simp only [Fintype.card_fin] at h; omega
end Rectangle3679

-- An OR-only network for the fourteen data sums requires at least eighteen gates.
namespace Tarjan3679
abbrev W := BitVec 11

def inputs : List W := [0,1,2,4,8,16,32,64,128,256,512,1024]
def big : List W := [977,1490,996,1512]
def targets : List W := [513,1026,516,1032,576,704,960,1088,1216,1472] ++ big

def split (w u v : W) : Bool := (w != u) && (w != v) && ((u ||| v) == w)
def can (ws : List W) (w : W) : Bool := ws.any fun u => ws.any fun v => split w u v

private abbrev Cat := Fin 12
private def sub (u t : W) := (u &&& t) == u
private def tgt (i : Fin 7) : W := [977,1490,996,1512,464,480,448].get i
private def tag (u : W) : Cat :=
  if (inputs ++ targets).contains u then 0 else
  if u = 464 then 5 else if u = 480 then 6 else if u = 448 then 7 else
  if (big.filter (sub u)) = [977] then 1 else if (big.filter (sub u)) = [1490] then 2 else
  if (big.filter (sub u)) = [996] then 3 else if (big.filter (sub u)) = [1512] then 4 else
  if sub u 448 then 8 else if sub u 464 then 9 else if sub u 480 then 10 else 11
private def allows (i : Fin 7) (c : Cat) : Bool :=
  match i.val with
  | 0 => c == 1 || c == 5 | 1 => c == 2 || c == 5
  | 2 => c == 3 || c == 6 | 3 => c == 4 || c == 6
  | 4 => c == 9 || c == 7 | 5 => c == 10 || c == 7
  | _ => c == 8
private def nonwitnesses (i : Fin 7) := ((List.finRange 2048).map (fun j => BitVec.ofFin j : Fin 2048 → W)).filter (fun u => sub u (tgt i) && !allows i (tag u))
private theorem allmask (u : W) : u ∈ (List.finRange 2048).map (fun j => BitVec.ofFin j : Fin 2048 → W) :=
  List.mem_map.mpr ⟨u.toFin,List.mem_finRange _,rfl⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem pairCert : ∀ i : Fin 7,
    (nonwitnesses i).all (fun u => (nonwitnesses i).all (fun v => !(split (tgt i) u v))) = true := by decide +kernel
private theorem allows_split (i : Fin 7) (u v : W) (h : split (tgt i) u v=true) :
    allows i (tag u)=true ∨ allows i (tag v)=true := by
  simp only [split,Bool.and_eq_true,beq_iff_eq] at h
  have su : sub u (tgt i)=true := by
    rw [←h.2]; apply beq_iff_eq.mpr; ext i hi; simp; exact Or.inl
  have sv : sub v (tgt i)=true := by
    rw [←h.2]; apply beq_iff_eq.mpr; ext i hi; simp; exact Or.inr
  by_contra! bad
  have hu : u ∈ nonwitnesses i := List.mem_filter.mpr ⟨allmask _,by simp [su,bad.1]⟩
  have hv : v ∈ nonwitnesses i := List.mem_filter.mpr ⟨allmask _,by simp [sv,bad.2]⟩
  have contra := List.all_eq_true.mp (List.all_eq_true.mp (pairCert i) _ hu) _ hv
  simp only [split,Bool.not_eq_true'] at contra
  have eq : split (tgt i) u v = true := by simpa only [split,Bool.and_eq_true,beq_iff_eq] using h
  exact (Bool.noConfusion (contra.symm.trans eq))
private def demand (a b c : Cat) (i : Fin 7) := allows i a || allows i b || allows i c
private theorem takeDemand {a b c : W} (i : Fin 7) (h : can (a::b::c::(inputs++targets)) (tgt i)=true) :
    demand (tag a) (tag b) (tag c) i=true := by
  obtain ⟨u,hu,h⟩ := List.any_eq_true.mp h
  obtain ⟨v,hv,h⟩ := List.any_eq_true.mp h
  have one (w : W) (hw : w ∈ a::b::c::(inputs++targets)) (h : allows i (tag w)=true) : demand (tag a) (tag b) (tag c) i=true := by
    simp only [List.mem_cons] at hw; rcases hw with rfl|rfl|rfl|hw
    · simp [demand]; tauto
    · simp [demand]; tauto
    · simp [demand]; tauto
    · have z : tag w = 0 := by simp [tag,hw]
      have f := (by decide : ∀ i : Fin 7, allows i 0=false) i
      rw [z,f] at h; contradiction
  exact (allows_split i u v h).elim (one _ hu) (one _ hv)
private theorem tag_eq : ∀ (i : Fin 3) (u : W), tag u = (⟨5+i.val,by omega⟩ : Cat) → u = tgt ⟨4+i.val,by omega⟩ := by decide +kernel
private theorem tag_noinput : ∀ i : Fin 3, inputs.contains (tgt ⟨4+i.val,by omega⟩) = false := by decide
private theorem tags_impossible : ∀ a b c : Cat,
    (∀ i : Fin 4, demand a b c ⟨i.val,by omega⟩ = true) →
    (∀ i : Fin 3, (⟨5+i.val,by omega⟩ : Cat) ∈ [a,b,c] → demand a b c ⟨4+i.val,by omega⟩ = true) → False := by decide +kernel

private theorem certificate (a b c : W) :
    let pool := a :: b :: c :: (inputs ++ targets)
    ¬ ((big.all (can pool)) && ([a,b,c].all (fun w => inputs.contains w || can pool w))) = true := by
  intro pool ok
  obtain ⟨hb,hh⟩ := Bool.and_eq_true_iff.mp ok
  apply tags_impossible (tag a) (tag b) (tag c)
  · intro i; apply takeDemand
    exact List.all_eq_true.mp hb _ ((by decide : ∀ i : Fin 4, tgt ⟨i.val,by omega⟩ ∈ big) i)
  · intro i hi; apply takeDemand
    have pick : ∃ u ∈ [a,b,c], tag u = (⟨5+i.val,by omega⟩ : Cat) := by
      have eq : [a,b,c].map tag = [tag a,tag b,tag c] := rfl
      exact List.mem_map.mp (eq.symm ▸ hi)
    obtain ⟨u,hu,e⟩ := pick
    have eq := tag_eq i u e; subst u
    simpa only [tag_noinput,Bool.false_or] using List.all_eq_true.mp hh _ hu

inductive Trace : List W → Prop
| nil : Trace []
| gate {tail : List W} {u v : W} : Trace tail → u ∈ inputs ++ tail → v ∈ inputs ++ tail →
    Trace ((u ||| v) :: tail)

private theorem explain {ws : List W} (h : Trace ws) {w : W} (hw : w ∈ ws) :
    w ∈ inputs ∨ ∃ u ∈ inputs ++ ws, ∃ v ∈ inputs ++ ws, split w u v = true := by
  induction h with
  | nil => simp at hw
  | @gate tail u v ht hu hv ih =>
    have lift (x : W) (hx : x ∈ inputs ++ tail) : x ∈ inputs ++ (u ||| v) :: tail := by
      simpa only [List.mem_append, List.mem_cons] using
        (List.mem_append.mp hx).imp_right (fun h => Or.inr h : x ∈ tail → x = u ||| v ∨ x ∈ tail)
    have prev (hw' : w ∈ tail) : _ := ih hw'
    rw [List.mem_cons] at hw
    have transfer (hw' : w ∈ tail) : w ∈ inputs ∨ ∃ x ∈ inputs ++ (u ||| v) :: tail,
        ∃ y ∈ inputs ++ (u ||| v) :: tail, split w x y = true := by
      rcases prev hw' with hi | ⟨x,hx,y,hy,hs⟩
      · exact Or.inl hi
      · exact Or.inr ⟨x,lift _ hx,y,lift _ hy,hs⟩
    rcases hw with rfl | hw
    · by_cases he : u ||| v ∈ tail
      · exact transfer he
      by_cases hi : u ||| v ∈ inputs
      · exact Or.inl hi
      have neq (x : W) (hx : x ∈ inputs ++ tail) : u ||| v ≠ x := by
        rintro rfl; exact (List.mem_append.mp hx).elim hi he
      exact Or.inr ⟨u,lift _ hu,v,lift _ hv,by simp [split, neq _ hu, neq _ hv]⟩
    · exact transfer hw

private theorem three (s : Finset W) (h : s.card ≤ 3) :
    ∃ a b c : W, (∀ w ∈ s, w ∈ [a,b,c]) ∧ ∀ w ∈ [a,b,c], w = 0 ∨ w ∈ s := by
  let l := s.toList
  have hl : l.length ≤ 3 := by simpa [l] using h
  have hm (w : W) : w ∈ s ↔ w ∈ l := by simp [l]
  cases e : l with
  | nil => exact ⟨0,0,0,by simp_all,by simp⟩
  | cons a t => cases et : t with
    | nil => exact ⟨a,0,0,by simp_all,by simp_all⟩
    | cons b r => cases er : r with
      | nil => exact ⟨a,b,0,by simp_all,by simp_all⟩
      | cons c k => cases ek : k with
        | nil => exact ⟨a,b,c,by simp_all,by simp_all⟩
        | cons d z => simp [e, et, er, ek] at hl; omega

theorem length_lower {ws : List W} (trace : Trace ws) (outs : ∀ w ∈ targets, w ∈ ws) :
    18 ≤ ws.length := by
  by_contra! small
  let extra := ws.toFinset \ targets.toFinset
  have sub : targets.toFinset ⊆ ws.toFinset := by
    intro w hw; exact List.mem_toFinset.mpr (outs w (List.mem_toFinset.mp hw))
  have ct : targets.toFinset.card = 14 := by decide
  have ce : extra.card ≤ 3 := by
    change (ws.toFinset \ targets.toFinset).card ≤ 3
    rw [Finset.card_sdiff_of_subset sub, ct]
    have := List.toFinset_card_le ws
    omega
  obtain ⟨a,b,c,cover,valid⟩ := three extra ce
  let pool := a :: b :: c :: (inputs ++ targets)
  have incl (x : W) (hx : x ∈ inputs ++ ws) : x ∈ pool := by
    rcases List.mem_append.mp hx with hi | hw
    · simp [pool, hi]
    by_cases ht : x ∈ targets
    · simp [pool, ht]
    have he : x ∈ extra := by simp [extra, hw, ht]
    have hs := cover x he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> simp [pool]
  have prod (w : W) (hw : w ∈ ws) (hi : w ∉ inputs) : can pool w = true := by
    obtain ⟨u,hu,v,hv,hs⟩ := (explain trace hw).resolve_left hi
    exact List.any_eq_true.mpr ⟨u,incl _ hu,List.any_eq_true.mpr ⟨v,incl _ hv,hs⟩⟩
  apply certificate a b c
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply List.all_eq_true.mpr
    intro w hw
    have inT : w ∈ targets := List.mem_append_right _ hw
    apply prod w (outs w inT)
    simp only [big, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> decide
  · apply List.all_eq_true.mpr
    intro w hw
    by_cases hi : w ∈ inputs
    · simp [hi]
    obtain h0 | he := valid w hw
    · subst w; exact False.elim (hi (by decide))
    have hm : w ∈ ws := by simpa using (Finset.mem_sdiff.mp he).1
    exact Bool.or_eq_true_iff.mpr (Or.inr (prod w hm hi))
end Tarjan3679

-- Delete the private columns, charging a different eliminated gate to each row.
namespace Padding3679
open FlatTranspose3679

abbrev P := BitVec 25
private def unitBit (j : Fin 25) : P := BitVec.ofNat 25 (2 ^ j.val)
private def free (w : P) : Prop := w = 0 ∨ ∃ j, w = unitBit j
private def usable (bank : List P) (w : P) := free w ∨ w ∈ bank

inductive Trace : List P → Prop
  | nil : Trace []
  | gate {t : List P} {u v : P} : Trace t → usable t u → usable t v → Trace ((u ||| v) :: t)

private def low (w : P) : Tarjan3679.W := w.setWidth 11
private def high (w : P) : Finset (Fin 14) :=
  Finset.univ.filter (fun i => w.getLsbD (Rows3679.privateCol i).val = true)
private def key (i : Fin 14) : Finset (Fin 14) := {i}

private def marked (w : P) (i : Fin 14) := high w = key i ∧ low w ≠ 0
private theorem low_union (u v : P) : low (u ||| v) = low u ||| low v := by
  exact BitVec.setWidth_or
private theorem inherit_key (u v : P) (i : Fin 14) (h : high (u ||| v) = key i) :
    high u = key i ∨ high v = key i := by
  have eq : high u ∪ high v = {i} := by
    change high u ∪ high v = key i
    rw [← h]; ext j; simp [high]
  have hi : i ∈ high u ∪ high v := by simp [eq]
  rcases Finset.mem_union.mp hi with hu | hv
  · left; apply Finset.Subset.antisymm _ (Finset.singleton_subset_iff.mpr hu)
    rw [← eq]; exact Finset.subset_union_left
  · right; apply Finset.Subset.antisymm _ (Finset.singleton_subset_iff.mpr hv)
    rw [← eq]; exact Finset.subset_union_right
private theorem key_inj (i j : Fin 14) (h : key i = key j) : i = j := by simpa [key] using h
private theorem free_low {w : P} (h : free w) : low w ∈ Tarjan3679.inputs := by
  rcases h with rfl | ⟨j,rfl⟩
  · decide
  · exact (by decide +kernel : ∀ j : Fin 25, low (unitBit j) ∈ Tarjan3679.inputs) j
private theorem free_unmarked {w : P} (h : free w) (i : Fin 14) : ¬ marked w i := by
  rcases h with rfl | ⟨j,rfl⟩
  · intro hm; exact hm.2 rfl
  · exact (by unfold marked; decide +kernel : ∀ j : Fin 25, ∀ i : Fin 14, ¬ marked (unitBit j) i) j i

private theorem project {ws : List P} (h : Trace ws) :
    ∃ (ts : List Tarjan3679.W) (paid : Finset (Fin 14)), Tarjan3679.Trace ts ∧
    ts.length + paid.card ≤ ws.length ∧
    (∀ w, usable ws w → low w ∈ Tarjan3679.inputs ++ ts) ∧
    ∀ w, usable ws w → ∀ i, marked w i → i ∈ paid := by
  classical
  induction h with
  | nil =>
    refine ⟨[],∅,.nil,by simp,?_,?_⟩
    · intro w hw; have hf : free w := by simpa [usable] using hw
      simpa using free_low hf
    · intro w hw i hm; have hf : free w := by simpa [usable] using hw
      exact (free_unmarked hf i hm).elim
  | @gate t u v ht hu hv ih =>
    obtain ⟨ts,paid,bt,cost,avail,tracked⟩ := ih
    have casesWire (w : P) (hw : usable ((u ||| v) :: t) w) : w = u ||| v ∨ usable t w := by
      simpa only [usable,List.mem_cons] using (show w = u ||| v ∨ free w ∨ w ∈ t by
        rcases hw with hf | h; exact Or.inr (Or.inl hf); exact (List.mem_cons.mp h).imp_right Or.inr)
    by_cases fresh : ∃ i, marked (u ||| v) i ∧ i ∉ paid
    · obtain ⟨i,hm,hi⟩ := fresh
      have zero : low u = 0 ∨ low v = 0 := by
        rcases inherit_key u v i hm.1 with h | h
        · left; by_contra hn; exact hi (tracked u hu i ⟨h,hn⟩)
        · right; by_contra hn; exact hi (tracked v hv i ⟨h,hn⟩)
      refine ⟨ts,insert i paid,bt,by simp [hi]; omega,?_,?_⟩
      · intro w hw; rcases casesWire w hw with rfl | hw
        · rw [low_union]; rcases zero with hz | hz
          · simpa [hz] using avail v hv
          · simpa [hz] using avail u hu
        · exact avail _ hw
      · intro w hw j hj; rcases casesWire w hw with rfl | hw
        · exact Finset.mem_insert.mpr (Or.inl (key_inj j i (hj.1.symm.trans hm.1)))
        · exact Finset.mem_insert_of_mem (tracked _ hw _ hj)
    · let s := (low u ||| low v) :: ts
      have lift (x : Tarjan3679.W) (hx : x ∈ Tarjan3679.inputs ++ ts) : x ∈ Tarjan3679.inputs ++ s :=
        (List.mem_append.mp hx).elim (List.mem_append_left _) (fun h => List.mem_append_right _ (List.mem_cons_of_mem _ h))
      refine ⟨s,paid,.gate bt (avail _ hu) (avail _ hv),by simp [s]; omega,?_,?_⟩
      · intro w hw; rcases casesWire w hw with rfl | hw
        · rw [low_union]; exact List.mem_append_right _ List.mem_cons_self
        · exact lift _ (avail _ hw)
      · intro w hw i hm; rcases casesWire w hw with rfl | hw
        · by_contra hi; exact fresh ⟨i,hm,hi⟩
        · exact tracked _ hw _ hm

private def bitsAux (s : Finset (Fin 25)) : List (Fin 25) → P
  | [] => 0
  | j :: js => (if j ∈ s then unitBit j else 0) ||| bitsAux s js
private def bits (s : Finset (Fin 25)) : P := bitsAux s (List.finRange 25)
private theorem bits_union (a b : Finset (Fin 25)) : bits (a ∪ b) = bits a ||| bits b := by
  unfold bits
  generalize List.finRange 25 = js
  induction js with
  | nil => simp [bitsAux]
  | cons j js ih =>
    by_cases h : j ∈ a <;> by_cases k : j ∈ b <;> simp [bitsAux,h,k,ih] <;>
      apply BitVec.eq_of_getLsbD_eq <;> intro n hn <;>
      simp [BitVec.getLsbD_or,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm]
private theorem small_free (w : Finset (Fin 25)) (h : w.card ≤ 1) : free (bits w) := by
  by_cases he : w = ∅
  · subst w; exact Or.inl rfl
  · have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
    obtain ⟨j,rfl⟩ := Finset.card_eq_one.mp (show w.card = 1 by omega)
    exact Or.inr ⟨j,(by decide +kernel : ∀ j : Fin 25, bits {j} = unitBit j) j⟩
private theorem avail_bits {B : List (Finset (Fin 25))} {w : Finset (Fin 25)} (h : Av B w) :
    usable (B.map bits) (bits w) :=
  h.elim (fun hs => Or.inl (small_free _ hs)) (fun hw => Or.inr (List.mem_map.mpr ⟨w,hw,rfl⟩))
private theorem packed {B : List (Finset (Fin 25))} (h : Built B) : Trace (B.map bits) := by
  induction h with
  | nil => exact .nil
  | cons _ hu hv ih => simp only [List.map_cons,bits_union]; exact .gate ih (avail_bits hu) (avail_bits hv)

set_option maxRecDepth 10000 in
private theorem row_marks : ∀ i : Fin 14, marked (bits (Rows3679.row i)) i := by unfold marked; decide +kernel
set_option maxRecDepth 10000 in
private theorem row_data : List.ofFn (fun i : Fin 14 => low (bits (Rows3679.row i))) = Tarjan3679.targets := by decide +kernel

theorem length_lower {B : List (Finset (Fin 25))} (h : Built B) (out : ∀ i, Av B (Rows3679.row i)) :
    32 ≤ B.length := by
  obtain ⟨ts,paid,ht,cost,avail,tracked⟩ := project (packed h)
  have hall : paid = Finset.univ := Finset.eq_univ_of_forall (fun i => tracked _ (avail_bits (out i)) i (row_marks i))
  have htarg : ∀ w ∈ Tarjan3679.targets, w ∈ ts := by
    intro w hw
    have hn : w ∉ Tarjan3679.inputs := (by decide +kernel : ∀ w ∈ Tarjan3679.targets, w ∉ Tarjan3679.inputs) w hw
    rw [← row_data,List.mem_ofFn] at hw
    obtain ⟨i,rfl⟩ := hw
    exact (List.mem_append.mp (avail _ (avail_bits (out i)))).resolve_left hn
  have hl := Tarjan3679.length_lower ht htarg
  simp [hall] at cost
  omega
end Padding3679

namespace Finish3679
open Upper3679 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
def Flat (D : Circuit) := ∀ i < D.gates.length, ∀ j < D.gates.length, (gateAt D i).op = GateOp.and → (gateAt D j).op = GateOp.and → ¬InCone 39 D i j
theorem finish (lb : ∀ D, IsAO2 39 D → circuitFun 39 D = graphFun G ∅ → Flat D → 59 ≤ D.size) : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (s : Fin n → Bool),
  (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C ∧
    PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G D ∧
    ∀ i < D.gates.length, ∀ j < D.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ¬ PEqualNP.EdgeOwnership.InCone n D i j) := by
  intro h; obtain ⟨D,⟨valid,eval,least⟩,flat⟩ := h 39 G side bip ⟨C,ao,computes⟩
  have hi := least C ao computes; have lo := lb D valid eval flat; rw [Upper3679.size] at hi; omega
end Finish3679

-- The private diagonal needs fourteen rectangles. Transposition and deletion give the extra gate.
namespace Joined3679
open Upper3679 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem flat_lower (D : Circuit) (hao : IsAO2 39 D) (hc : circuitFun 39 D = graphFun G ∅)
    (flat : Finish3679.Flat D) : 59 ≤ D.size := by
  obtain ⟨L,R,rect,bl,br,avail,cover,budget⟩ := FlatStructure3679.extract D hao hc flat
  exact Rectangle3679.lower L R rect D.size bl br avail cover budget (fun _ => Padding3679.length_lower)

end Joined3679

end PEqualNP.Outside.L_meta_3679

theorem PEqualNP.Outside.L_meta_3679 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (s : Fin n → Bool),
  (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C ∧
    PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G D ∧
    ∀ i < D.gates.length, ∀ j < D.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ¬ PEqualNP.EdgeOwnership.InCone n D i j) :=
  PEqualNP.Outside.L_meta_3679.Finish3679.finish PEqualNP.Outside.L_meta_3679.Joined3679.flat_lower
