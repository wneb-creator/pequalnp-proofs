import PEqualNP.Defs
-- Wire evaluation helpers are adapted from L_meta_5779 (Apache-2.0).
namespace PEqualNP.Outside.L_meta_3754.Ledger
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_wireStep_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl wireStep acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wireStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wireStep_prefix (gs : List Gate) (acc : List Bool) (w : ℕ) (hw : w < acc.length) :
    (gs.foldl wireStep acc).getD w false = acc.getD w false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hw' : w < (wireStep acc g).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (wireStep acc g) hw']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_left hw]

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  exact foldl_wireStep_length C.gates x

lemma gateAt_eq_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

lemma wireVal_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wireVal n C w x = x ⟨w, hw⟩ := by
  unfold wireVal Circuit.wires
  have hw' : w < (List.ofFn x).length := by simp [hw]
  have h1 := foldl_wireStep_prefix C.gates (List.ofFn x) w hw'
  change (C.gates.foldl wireStep (List.ofFn x)).getD w false = x ⟨w, hw⟩
  rw [h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw']
  simp

lemma wireVal_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ)
    (hk : k < C.gates.length) (hRB : ReadsBack n C) :
    wireVal n C (n + k) x =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun u => wireVal n C u x) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take k).foldl wireStep (List.ofFn x) with hacc
  have hacc_len : acc.length = n + k := by
    rw [hacc, foldl_wireStep_length, List.length_ofFn, List.length_take]
    omega
  have hpref : ∀ u < n + k, wireVal n C u x = acc.getD u false := by
    intro u hu
    unfold wireVal Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD u false = acc.getD u false
    conv_lhs => rw [← List.take_append_drop k C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_wireStep_prefix (C.gates.drop k) acc u (by omega)
  have hval : wireVal n C (n + k) x =
      C.gates[k].op.eval (C.gates[k].inputs.map fun u => acc.getD u false) := by
    unfold wireVal Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD (n + k) false = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : n + k < (wireStep acc C.gates[k]).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_wireStep_prefix (C.gates.drop (k + 1)) (wireStep acc C.gates[k]) (n + k) hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_right (by omega : acc.length ≤ n + k),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hval, gateAt_eq_getElem C k hk]
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [← gateAt_eq_getElem C k hk] at hu
  exact (hpref u (hRB k hk u hu)).symm


lemma gate_two (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j<C.gates.length) : ∃ a b,(gateAt C j).inputs=[a,b] := by
  have hm : gateAt C j∈C.gates := by rw [gateAt_eq_getElem C j hj];exact List.getElem_mem hj
  exact List.length_eq_two.mp (hAO.2.2 _ hm)

lemma gate_eval_monotone (g : Gate) (hg : g.op=GateOp.and ∨ g.op=GateOp.or)
    (x y : ℕ → Bool) (hxy : ∀i∈g.inputs,x i=true → y i=true) :
    g.op.eval (g.inputs.map x)=true → g.op.eval (g.inputs.map y)=true := by
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval,List.all_map,Function.comp_def,id_eq,List.all_eq_true]
    intro h i hi
    exact hxy i hi (h i hi)
  · rw [hg]
    simp only [GateOp.eval,List.any_map,Function.comp_def,id_eq,List.any_eq_true]
    rintro ⟨i,hi,h⟩
    exact ⟨i,hi,hxy i hi h⟩

lemma wire_monotone (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀i,x i=true → y i=true) :
    ∀w,w<n+C.gates.length → wireVal n C w x=true → wireVal n C w y=true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hx
    by_cases hinput : w<n
    · rw [wireVal_input n C x w hinput] at hx
      rw [wireVal_input n C y w hinput]
      exact hxy _ hx
    · obtain ⟨k,rfl⟩ : ∃k,w=n+k := ⟨w-n,by omega⟩
      have hk : k<C.gates.length := by omega
      have hm : gateAt C k∈C.gates := by rw [gateAt_eq_getElem C k hk];exact List.getElem_mem hk
      rw [wireVal_gate n C x k hk hAO.2.1] at hx
      rw [wireVal_gate n C y k hk hAO.2.1]
      apply gate_eval_monotone (gateAt C k) (hAO.1 _ hm)
        (fun u => wireVal n C u x) (fun u => wireVal n C u y) _ hx
      intro u hu huv
      have hub := hAO.2.1 k hk u hu
      exact ih u hub (by omega) huv

end PEqualNP.Outside.L_meta_3754.Ledger
namespace PEqualNP.Outside.L_meta_3754.MaxFalse
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge Ledger

def maximalFalse {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : Prop :=
  f x=false ∧ ∀i,x i=false → f (Function.update x i true)=true

def isAnd (g : Gate) : Bool :=
  match g.op with
  | .and => true
  | _ => false

def maxFalseSet {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  Finset.univ.filter fun x => f x=false ∧ ∀i,x i=false → f (Function.update x i true)=true

def andSites (C : Circuit) : Finset (Fin C.gates.length) :=
  Finset.univ.filter fun k => isAnd (gateAt C k)=true

def signature {n : ℕ} (C : Circuit) (x : Fin n → Bool) : andSites C → Bool :=
  fun k => wireVal n C (opnd C k.val 0) x

lemma same_signature_join {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (x y : Fin n → Bool) (hs : signature C x=signature C y) :
    ∀w,w<n+C.gates.length → wireVal n C w x=false → wireVal n C w y=false →
      wireVal n C w (fun i=>x i || y i)=false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hx hy
    by_cases hi : w<n
    · rw [wireVal_input n C x w hi] at hx
      rw [wireVal_input n C y w hi] at hy
      rw [wireVal_input n C _ w hi]
      simp [hx,hy]
    · obtain ⟨k,rfl⟩ : ∃k,w=n+k := ⟨w-n,by omega⟩
      have hk : k<C.gates.length := by omega
      obtain ⟨a,b,hab⟩ := gate_two n C hAO k hk
      have ha : a<n+k := hAO.2.1 k hk a (by simp [hab])
      have hb : b<n+k := hAO.2.1 k hk b (by simp [hab])
      have hm : gateAt C k∈C.gates := by
        rw [gateAt_eq_getElem C k hk]
        exact List.getElem_mem hk
      rw [wireVal_gate n C x k hk hAO.2.1,hab] at hx
      rw [wireVal_gate n C y k hk hAO.2.1,hab] at hy
      rw [wireVal_gate n C _ k hk hAO.2.1,hab]
      rcases hAO.1 _ hm with hand | hor
      · have hkA : (⟨k,hk⟩ : Fin C.gates.length)∈andSites C := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _,?_⟩
          change isAnd (gateAt C k)=true
          simp [isAnd,hand]
        have hs' := congrFun hs ⟨⟨k,hk⟩,hkA⟩
        change wireVal n C (opnd C k 0) x=wireVal n C (opnd C k 0) y at hs'
        simp only [opnd,hab] at hs'
        simp only [hand,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,
          List.all_nil,Bool.and_true] at hx hy ⊢
        cases hxa : wireVal n C a x with
        | false =>
          have hya : wireVal n C a y=false := by simpa [hxa] using hs'.symm
          simp [ih a ha (by omega) hxa hya]
        | true =>
          have hya : wireVal n C a y=true := by simpa [hxa] using hs'.symm
          have hxb : wireVal n C b x=false := by simpa [hxa] using hx
          have hyb : wireVal n C b y=false := by simpa [hya] using hy
          simp [ih b hb (by omega) hxb hyb]
      · simp only [hor,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,
          List.any_nil,Bool.or_false,Bool.or_eq_false_iff] at hx hy ⊢
        exact ⟨ih a ha (by omega) hx.1 hy.1,ih b hb (by omega) hx.2 hy.2⟩

lemma signature_injective {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (hout : C.output<n+C.gates.length) :
    Function.Injective (fun x : {x : Fin n → Bool // maximalFalse (circuitFun n C) x} =>
      signature C x.val) := by
  intro x y hsig
  have hj := same_signature_join hAO x.val y.val hsig C.output hout x.property.1 y.property.1
  have hxle : ∀i,x.val i=true → y.val i=true := by
    intro i hi
    by_contra hn
    have hiy : y.val i=false := by simpa using hn
    have hf := y.property.2 i hiy
    have hmono := wire_monotone n C hAO (Function.update y.val i true)
      (fun j=>x.val j || y.val j) (by
        intro j hj
        by_cases hji : j=i
        · subst j
          simp [hi]
        · simp only [Function.update_of_ne hji] at hj
          simp [hj]) C.output hout hf
    rw [hj] at hmono
    cases hmono
  have hyle : ∀i,y.val i=true → x.val i=true := by
    intro i hi
    by_contra hn
    have hix : x.val i=false := by simpa using hn
    have hf := x.property.2 i hix
    have hmono := wire_monotone n C hAO (Function.update x.val i true)
      (fun j=>x.val j || y.val j) (by
        intro j hj
        by_cases hji : j=i
        · subst j
          simp [hi]
        · simp only [Function.update_of_ne hji] at hj
          simp [hj]) C.output hout hf
    rw [hj] at hmono
    cases hmono
  apply Subtype.ext
  funext i
  cases hxi : x.val i <;> cases hyi : y.val i <;> simp_all

lemma count_bound {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (hout : C.output<n+C.gates.length) :
    (maxFalseSet (circuitFun n C)).card ≤
      2^(andSites C).card := by
  classical
  let f : maxFalseSet (circuitFun n C) → (andSites C → Bool) :=
    fun x=>signature C x.val
  have hi : Function.Injective f := by
    intro x y hxy
    have hx : maximalFalse (circuitFun n C) x.val := (Finset.mem_filter.mp x.property).2
    have hy : maximalFalse (circuitFun n C) y.val := (Finset.mem_filter.mp y.property).2
    have heq := signature_injective hAO hout (a₁:=⟨x.val,hx⟩) (a₂:=⟨y.val,hy⟩) hxy
    apply Subtype.ext
    exact congrArg (fun z : {x : Fin n → Bool // maximalFalse (circuitFun n C) x}=>z.val) heq
  have h := Fintype.card_le_of_injective f hi
  simpa [Fintype.card_pi,Fintype.card_bool,Fintype.card_coe] using h

lemma andSites_card (C : Circuit) : (andSites C).card=C.gates.countP isAnd := by
  have heq : (fun k : Fin C.gates.length => gateAt C k)=fun k=>C.gates.get k := by
    funext k
    exact gateAt_eq_getElem C k k.isLt
  have h := List.countP_ofFn (fun k : Fin C.gates.length => gateAt C k) isAnd
  rw [heq,List.ofFn_get] at h
  simpa only [andSites,heq] using h.symm

lemma count_bound_all {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    (maxFalseSet (circuitFun n C)).card ≤ 2^(C.gates.countP isAnd) := by
  by_cases hout : C.output<n+C.gates.length
  · simpa [andSites_card] using count_bound hAO hout
  · have hzero : circuitFun n C=(fun _=>false) := by
      funext x
      change (C.wires (List.ofFn x)).getD C.output false=false
      apply List.getD_eq_default
      rw [wires_length,List.length_ofFn]
      omega
    have hset : maxFalseSet (fun _ : Fin n → Bool=>false)={fun _=>true} := by
      ext x
      simp only [maxFalseSet,Finset.mem_filter,Finset.mem_univ,true_and,
        Finset.mem_singleton]
      constructor
      · intro hx
        funext i
        cases hi : x i with
        | false => exact (Bool.noConfusion (hx i hi))
        | true => rfl
      · rintro rfl
        simp
    rw [hzero,hset,Finset.card_singleton]
    have hp : 0<2^(C.gates.countP isAnd) := by positivity
    omega

end PEqualNP.Outside.L_meta_3754.MaxFalse
namespace PEqualNP.Outside.L_meta_3754.MaxFalse
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership Ledger

abbrev c8 : SimpleGraph (Fin 8) :=
  edgeGraph 8 [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0)]

abbrev c10 : SimpleGraph (Fin 10) :=
  edgeGraph 10 [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c8_maxFalse_count : (maxFalseSet (graphFun c8 ∅)).card=10 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c10_maxFalse_count : (maxFalseSet (graphFun c10 ∅)).card=17 := by
  decide

lemma c8_and_bound (C : Circuit) (hAO : IsAO2 8 C)
    (hc : circuitFun 8 C=graphFun c8 ∅) : 4≤C.gates.countP isAnd := by
  have h := count_bound_all hAO
  rw [hc,c8_maxFalse_count] at h
  by_contra hn
  have hle : C.gates.countP isAnd≤3 := by omega
  have hp := Nat.pow_le_pow_right (by decide : 1≤2) hle
  norm_num at hp
  omega

lemma c10_and_bound (C : Circuit) (hAO : IsAO2 10 C)
    (hc : circuitFun 10 C=graphFun c10 ∅) : 5≤C.gates.countP isAnd := by
  have h := count_bound_all hAO
  rw [hc,c10_maxFalse_count] at h
  by_contra hn
  have hle : C.gates.countP isAnd≤4 := by omega
  have hp := Nat.pow_le_pow_right (by decide : 1≤2) hle
  norm_num at hp
  omega

end PEqualNP.Outside.L_meta_3754.MaxFalse
namespace PEqualNP.Outside.L_meta_3754.MaxFalse
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership Ledger

abbrev cycleLeaf7 : SimpleGraph (Fin 7) :=
  edgeGraph 7 [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),(0,6)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cycleLeaf7_maxFalse_count : (maxFalseSet (graphFun cycleLeaf7 ∅)).card=6 := by
  decide

lemma cycleLeaf7_and_bound (C : Circuit) (hAO : IsAO2 7 C)
    (hc : circuitFun 7 C=graphFun cycleLeaf7 ∅) : 3≤C.gates.countP isAnd := by
  have h := count_bound_all hAO
  rw [hc,cycleLeaf7_maxFalse_count] at h
  by_contra hn
  have hle : C.gates.countP isAnd≤2 := by omega
  have hp := Nat.pow_le_pow_right (by decide : 1≤2) hle
  norm_num at hp
  omega

end PEqualNP.Outside.L_meta_3754.MaxFalse
