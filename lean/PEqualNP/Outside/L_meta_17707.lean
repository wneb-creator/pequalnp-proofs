import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17707

-- The OR lower bound follows L-meta-599.
namespace GraphInduction599
open SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def sparse (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, {e : Sym2 V | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card

def noFour (G : SimpleGraph V) : Prop :=
  ∀ v (c : G.Walk v v), c.IsCycle → c.length ≠ 4

omit [DecidableEq V] in
theorem sparse_subgraph {H G : SimpleGraph V} (h : H ≤ G) (hG : sparse G) : sparse H := by
  intro S
  apply le_trans _ (hG S)
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  intro e he
  exact ⟨SimpleGraph.edgeSet_mono h he.1, he.2⟩

omit [Fintype V] [DecidableEq V] in
theorem noFour_subgraph {H G : SimpleGraph V} (h : H ≤ G) (hG : noFour G) : noFour H := by
  intro v c hc
  simpa only [Walk.length_mapLe] using hG v (c.mapLe h) (hc.mapLe h)

omit [DecidableEq V] in
theorem count_eq (G : SimpleGraph V) : G.edgeSet.ncard = G.edgeFinset.card := by
  exact Set.ncard_eq_toFinset_card' _

omit [DecidableEq V] in
theorem support_count (G : SimpleGraph V) (hs : sparse G) :
    G.edgeFinset.card ≤ G.support.toFinset.card := by
  rw [← count_eq]
  let S := G.support.toFinset
  apply le_trans _ (hs S)
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  intro e he
  refine ⟨he, ?_⟩
  induction e using Sym2.inductionOn with
  | _ a b =>
    have hab : G.Adj a b := he
    intro v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact Set.mem_toFinset.mpr hab.mem_support_left
    · exact Set.mem_toFinset.mpr hab.mem_support_right

omit [DecidableEq V] in

theorem regular_of_no_leaf (G : SimpleGraph V) (hs : sparse G)
    (hl : ∀ v, G.degree v ≠ 1) (v : V) (hv : v ∈ G.support) : G.degree v = 2 := by
  classical
  have hmin : ∀ i ∈ G.support.toFinset, 2 ≤ G.degree i := by
    intro i hi
    have hi' := (G.degree_pos_iff_mem_support i).mpr (Set.mem_toFinset.mp hi)
    have := hl i
    omega
  by_contra hn
  have hv' := Set.mem_toFinset.mpr hv
  have hd := hmin v hv'
  have hsum := Finset.sum_lt_sum hmin (⟨v,hv',by omega⟩ :
    ∃ i ∈ G.support.toFinset, 2 < G.degree i)
  have hmax := support_count G hs
  have hhand := G.sum_degrees_support_eq_twice_card_edges
  simp only [Finset.sum_const, smul_eq_mul] at hsum
  omega

theorem count_after_delete (G : SimpleGraph V) (v : V) :
    (G.deleteIncidenceSet v).edgeSet.ncard + G.degree v = G.edgeSet.ncard := by
  have h := G.card_edgeFinset_deleteIncidenceSet v
  have hle := G.degree_le_card_edgeFinset v
  simpa only [SimpleGraph.edgeFinset, Set.toFinset_card, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] using (h ▸ Nat.sub_add_cancel hle :
      (G.deleteIncidenceSet v).edgeFinset.card + G.degree v = G.edgeFinset.card)


theorem of_paid_deletions (cost : SimpleGraph V → ℕ)
    (leaf : ∀ G : SimpleGraph V, sparse G → noFour G → cost G + 1 < G.edgeSet.ncard →
      ∀ v, G.degree v = 1 → cost (G.deleteIncidenceSet v) + 1 ≤ cost G)
    (core : ∀ G : SimpleGraph V, sparse G → noFour G → cost G + 1 < G.edgeSet.ncard →
      (∀ v ∈ G.support, G.degree v = 2) →
      ∃ v ∈ G.support, cost (G.deleteIncidenceSet v) + 2 ≤ cost G)
    (G : SimpleGraph V) (hs : sparse G) (hf : noFour G) :
    G.edgeSet.ncard ≤ cost G + 1 := by
  induction h : G.edgeSet.ncard using Nat.strong_induction_on generalizing G with
  | ind k ih =>
    by_cases hb : G.edgeSet.ncard ≤ cost G + 1
    · omega
    have hg : cost G + 1 < G.edgeSet.ncard := by omega
    have paid : ∃ v, 0 < G.degree v ∧
        cost (G.deleteIncidenceSet v) + G.degree v ≤ cost G := by
      by_cases hleaf : ∃ v, G.degree v = 1
      · obtain ⟨v,hv⟩ := hleaf
        exact ⟨v,by omega, by simpa only [hv] using leaf G hs hf hg v hv⟩
      · have hreg := regular_of_no_leaf G hs (fun v e => hleaf ⟨v,e⟩)
        obtain ⟨v,hv,hp⟩ := core G hs hf hg hreg
        have hd := hreg v hv
        exact ⟨v,by omega,by omega⟩
    obtain ⟨v,hpos,hpay⟩ := paid
    have hc := count_after_delete G v
    have hlt : (G.deleteIncidenceSet v).edgeSet.ncard < k := by omega
    have H := G.deleteIncidenceSet_le v
    have hrec := ih _ hlt _ (sparse_subgraph H hs) (noFour_subgraph H hf) rfl
    omega

end GraphInduction599

namespace GraphCircuit599
open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped Classical
variable {n : ℕ}

def detects (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
    ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

def covers (C : Circuit) (A : Finset ℕ) : Prop :=
  ∀ j g, C.gates[j]? = some g → g.op = .or → j ∈ A

def feasible (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ C A, Monotone2 C ∧ detects G C ∧ covers C A ∧ A.card = k

private theorem exists_budget (G : SimpleGraph (Fin n)) :
    ∃ k, k = G.edgeSet.ncard ∨ feasible G k := ⟨_, Or.inl rfl⟩


noncomputable def best (G : SimpleGraph (Fin n)) : ℕ := Nat.find (exists_budget G)

theorem best_le {G : SimpleGraph (Fin n)} {k : ℕ} (h : feasible G k) : best G ≤ k :=
  Nat.find_min' (exists_budget G) (Or.inr h)

theorem represents {G : SimpleGraph (Fin n)} (h : best G < G.edgeSet.ncard) :
    feasible G (best G) :=
  (Nat.find_spec (exists_budget G)).resolve_left (Nat.ne_of_lt h)

theorem one_bit {G : SimpleGraph (Fin n)} {C : Circuit} (h : detects G C)
    {v : Fin n} (hv : v ∈ G.support) :
    ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = false ∧
      C.eval (List.ofFn (Function.update x v true)) = true := by
  obtain ⟨u,hu⟩ := G.mem_support.mp hv
  let x : Fin n → Bool := fun i => decide (i=u)
  have hne : v ≠ u := hu.ne
  refine ⟨x, by simp [x,hne], ?_, ?_⟩
  · rw [Bool.eq_false_iff]
    intro ht
    obtain ⟨i,j,hij,hi,hj⟩ := (h x).mp ht
    exact hij.ne ((of_decide_eq_true hi).trans (of_decide_eq_true hj).symm)
  · apply (h _).mpr
    exact ⟨v,u,hu,by simp,by simp [x,Function.update_of_ne hne.symm]⟩

theorem deletion_eval (G : SimpleGraph (Fin n)) (v : Fin n) (x : Fin n → Bool) :
    (∃ a b, G.Adj a b ∧ Function.update x v false a = true ∧
        Function.update x v false b = true) ↔
      ∃ a b, (G.deleteIncidenceSet v).Adj a b ∧ x a = true ∧ x b = true := by
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    have hav : a ≠ v := by rintro rfl; simp at ha
    have hbv : b ≠ v := by rintro rfl; simp at hb
    exact ⟨a,b,(G.deleteIncidenceSet_adj).mpr ⟨hab,hav,hbv⟩,
      (Function.update_of_ne hav _ _).symm.trans ha,(Function.update_of_ne hbv _ _).symm.trans hb⟩
  · rintro ⟨a,b,hab,ha,hb⟩
    obtain ⟨hab,hav,hbv⟩ := G.deleteIncidenceSet_adj.mp hab
    exact ⟨a,b,hab,(Function.update_of_ne hav _ _).trans ha,(Function.update_of_ne hbv _ _).trans hb⟩

theorem accepts_without {G : SimpleGraph (Fin n)} {C : Circuit} (h : detects G C)
    (v : Fin n) (hd : G.degree v < G.edgeSet.ncard) :
    ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = true := by
  have hc := GraphInduction599.count_after_delete G v
  have hcard : 0 < (G.deleteIncidenceSet v).edgeSet.ncard := by omega
  obtain ⟨e,he⟩ := Set.nonempty_of_ncard_ne_zero (Nat.ne_of_gt hcard)
  have hex : ∃ a b, (G.deleteIncidenceSet v).Adj a b := by
    induction e using Sym2.inductionOn with
    | _ a b => exact ⟨a,b,he⟩
  obtain ⟨a,b,hab⟩ := hex
  let x : Fin n → Bool := Function.update (fun _ => true) v false
  apply Exists.intro x
  refine ⟨by simp [x], (h x).mpr ?_⟩
  exact (deletion_eval G v (fun _ => true)).mpr ⟨a,b,hab,rfl,rfl⟩

theorem delete_isolated {G : SimpleGraph (Fin n)} {v : Fin n} (hv : v ∉ G.support) :
    G.deleteIncidenceSet v = G := by
  ext a b
  rw [G.deleteIncidenceSet_adj]
  refine ⟨fun h => h.1, fun hab => ⟨hab,?_,?_⟩⟩
  · rintro rfl
    exact hv hab.mem_support_left
  · rintro rfl
    exact hv hab.mem_support_right

theorem two_neighbors {G : SimpleGraph (Fin n)} {v : Fin n} (hd : 2 ≤ G.degree v) :
    ∃ a b, a ≠ b ∧ G.Adj v a ∧ G.Adj v b := by
  have h : 1 < (G.neighborFinset v).card := hd
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp h
  exact ⟨a,b,hab,(G.mem_neighborFinset _ _).mp ha,(G.mem_neighborFinset _ _).mp hb⟩

theorem accepts_core_without {G : SimpleGraph (Fin n)} {C : Circuit} (h : detects G C)
    (degrees : ∀ u ∈ G.support, G.degree u = 2) {v : Fin n} (hv : v ∈ G.support) :
    ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = true := by
  obtain ⟨u,hvu⟩ := G.mem_support.mp hv
  obtain ⟨a,b,hab,ha,hb⟩ := two_neighbors (le_of_eq (degrees u hvu.mem_support_right).symm)
  have hex : ∃ w, G.Adj u w ∧ w ≠ v := by
    by_cases he : a = v
    · exact ⟨b,hb,fun h => hab (he.trans h.symm)⟩
    · exact ⟨a,ha,he⟩
  obtain ⟨w,hw,hwv⟩ := hex
  let x : Fin n → Bool := Function.update (fun _ => true) v false
  exact ⟨x,by simp [x], (h x).mpr ⟨u,w,hw,
    by simp [x,Function.update_of_ne hvu.ne.symm],by simp [x,Function.update_of_ne hwv]⟩⟩

theorem support_nonempty {G : SimpleGraph (Fin n)} (hg : 0 < G.edgeSet.ncard) :
    G.support.Nonempty := by
  obtain ⟨e,he⟩ := Set.nonempty_of_ncard_ne_zero hg.ne'
  induction e using Sym2.inductionOn with
  | _ a b =>
    have hab : G.Adj a b := he
    exact ⟨a,hab.mem_support_left⟩

end GraphCircuit599

namespace Leaf599
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def readGate (g : Gate) (w : ℕ → Bool) : Bool := g.op.eval (g.inputs.map w)
private def run (gs : List Gate) (input : List Bool) : List Bool :=
  gs.foldl (fun wires g => wires ++ [readGate g (fun j => wires.getD j false)]) input

private theorem run_append (gs : List Gate) (g : Gate) (s : List Bool) :
    run (gs ++ [g]) s = run gs s ++ [readGate g (fun j => (run gs s).getD j false)] := by
  simp [run,List.foldl_append]

private theorem run_len (gs : List Gate) (s : List Bool) : (run gs s).length=s.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => simp [run_append,ih,Nat.add_assoc]

private def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (run gs (List.ofFn x)).getD w false

private theorem new_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    val (gs++[g]) x (n+gs.length) = readGate g (val gs x) := by
  have hl : (run gs (List.ofFn x)).length=n+gs.length := by simp [run_len]
  unfold val
  rw [run_append,←hl]
  simp

private theorem other_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) {w : ℕ}
    (h : w ≠ n+gs.length) : val (gs++[g]) x w = val gs x w := by
  have hl : (run gs (List.ofFn x)).length=n+gs.length := by simp [run_len]
  unfold val
  rw [run_append]
  by_cases hw : w < (run gs (List.ofFn x)).length
  · exact List.getD_append _ _ _ _ hw
  · rw [List.getD_eq_default _ _ (by simp [hl]; omega),List.getD_eq_default _ _ (by omega)]

private def release {n : ℕ} (gs : List Gate) (v : Fin n) : Prop :=
  ∃ (j : ℕ) (g : Gate) (i : ℕ), gs[j]?=some g ∧ g.op=.or ∧ i∈g.inputs ∧ i<n+j ∧
    ∀ z : Fin n → Bool, z v=false → val gs z i=false

private theorem release_initial {n : ℕ} {gs : List Gate} {v : Fin n} (g : Gate)
    (h : release gs v) : release (gs++[g]) v := by
  obtain ⟨j,q,i,hj,hop,hi,hlt,hz⟩ := h
  have hjl := (List.getElem?_eq_some_iff.mp hj).1
  refine ⟨j,q,i,(List.getElem?_append_left hjl).trans hj,hop,hi,hlt,?_⟩
  intro z hv
  exact (other_val gs g z (by omega)).trans (hz z hv)

private theorem sensitive_or_dominated {n : ℕ} (v : Fin n) (x : Fin n → Bool) (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op=.and ∨ g.op=.or) (no : ¬release gs v) (w : ℕ)
    (hd : val gs x w ≠ val gs (Function.update x v true) w) :
    ∀ z : Fin n → Bool, z v=false → val gs z w=false := by
  induction gs using List.reverseRecOn generalizing w with
  | nil =>
    intro z hz
    change (List.ofFn x).getD w false ≠ (List.ofFn (Function.update x v true)).getD w false at hd
    change (List.ofFn z).getD w false = false
    by_cases hw : w<n
    · rw [List.getD_eq_getElem _ _ (by simpa using hw),List.getD_eq_getElem _ _ (by simpa using hw)] at hd
      rw [List.getD_eq_getElem _ _ (by simpa using hw)]
      simp only [List.getElem_ofFn] at hd ⊢
      by_cases hv : (⟨w,hw⟩ : Fin n)=v
      · exact hv ▸ hz
      · exact (hd (Function.update_of_ne hv true x).symm).elim
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hw)]
  | append_singleton gs g ih =>
    have hm' : ∀ q ∈ gs, q.op=.and ∨ q.op=.or := fun q h => hm q (List.mem_append_left _ h)
    have no' : ¬ release gs v := fun h => no (release_initial g h)
    by_cases hw : w=n+gs.length
    · subst w
      rw [new_val,new_val] at hd
      obtain ⟨a,ha,hdif⟩ : ∃ a ∈ g.inputs, val gs x a ≠ val gs (Function.update x v true) a := by
        by_contra! h
        exact hd (congrArg g.op.eval (List.map_congr_left h))
      have bound : a<n+gs.length := by
        by_contra! h
        exact hdif (by
          unfold val
          rw [List.getD_eq_default _ _ (by simpa [run_len] using h),
            List.getD_eq_default _ _ (by simpa [run_len] using h)])
      have hf := ih hm' no' a hdif
      rcases hm g (by simp) with hop | hop
      · intro z hz
        rw [new_val]
        have he := hf z hz
        change (g.op.eval _) = false
        rw [hop]
        apply List.all_eq_false.mpr
        exact ⟨_,List.mem_map.mpr ⟨a,ha,rfl⟩,by simp [he]⟩
      · exact (no ⟨gs.length,g,a,by simp,hop,ha,bound,fun z hz =>
          (other_val _ _ _ (Nat.ne_of_lt bound)).trans (hf z hz)⟩).elim
    · rw [other_val _ _ _ hw,other_val _ _ _ hw] at hd
      intro z hz
      exact (other_val _ _ _ hw).trans (ih hm' no' w hd z hz)


theorem release_exists {n : ℕ} (C : Circuit) (v : Fin n) (hm : Monotone2 C)
    (on : ∃ x : Fin n → Bool, x v=false ∧ C.eval (List.ofFn x)=false ∧
      C.eval (List.ofFn (Function.update x v true))=true)
    (other : ∃ z : Fin n → Bool, z v=false ∧ C.eval (List.ofFn z)=true) :
    ∃ (j : ℕ) (g : Gate) (i : ℕ), C.gates[j]?=some g ∧ g.op=.or ∧ i∈g.inputs ∧ i<n+j ∧
      ∀ z : Fin n → Bool, z v=false → (C.wires (List.ofFn z)).getD i false=false := by
  change release C.gates v
  by_contra h
  obtain ⟨x,_,hx,hy⟩ := on
  obtain ⟨z,hz,ho⟩ := other
  have hd : val C.gates x C.output ≠ val C.gates (Function.update x v true) C.output := by
    change C.eval (List.ofFn x) ≠ _
    exact fun eq => Bool.false_ne_true (hx.symm.trans (eq.trans hy))
  have hf := sensitive_or_dominated v x C.gates (fun g hg => (hm g hg).1) h C.output hd z hz
  exact Bool.false_ne_true (hf.symm.trans ho)

private theorem val_initial {n : ℕ} (a b : List Gate) (x : Fin n → Bool) (w : ℕ) (hw : w<n+a.length) :
    val (a++b) x w=val a x w := by
  induction b using List.reverseRecOn with
  | nil => simp
  | append_singleton b g ih =>
    rw [←List.append_assoc,other_val _ _ _ (by simp; omega),ih]

private def pick (dead i : ℕ) : List ℕ → ℕ
  | a::b::_ => if a=i then b else a
  | _ => dead

private def copyOf (dead i : ℕ) (g : Gate) : Gate := ⟨.and,[pick dead i g.inputs]⟩

private theorem copy_value (dead i : ℕ) (g : Gate) (w : ℕ → Bool)
    (hz : w dead=false) (hi : w i=false) (hop : g.op=.or) (hin : i∈g.inputs)
    (hl : g.inputs.length≤2) : readGate (copyOf dead i g) w = readGate g w := by
  obtain ⟨op,l⟩ := g
  change op=.or at hop
  subst op
  change i∈l at hin
  change l.length≤2 at hl
  rcases l with _|⟨a,_|⟨b,_|⟨c,t⟩⟩⟩
  · simp at hin
  · have e : i=a := by simpa using hin
    subst a
    simp [readGate,copyOf,pick,GateOp.eval,hz,hi]
  · have e : i=a ∨ i=b := by simpa using hin
    rcases e with rfl|rfl
    · simp [readGate,copyOf,pick,GateOp.eval,hi]
    · by_cases eq : a=i <;> simp [readGate,copyOf,pick,GateOp.eval,hi,eq]
  · simp at hl

private theorem patch_val {n : ℕ} (C : Circuit) (f : ℕ → Gate → Gate) (z : Fin n → Bool)
    (same : ∀ (a : List Gate) (g : Gate), (∃ b, C.gates=(a++[g])++b) →
      readGate (f a.length g) (val a z)=readGate g (val a z))
    (gs : List Gate) (pre : ∃ b, C.gates=gs++b) (w : ℕ) :
    val (gs.mapIdx f) z w=val gs z w := by
  induction gs using List.reverseRecOn generalizing w with
  | nil => rfl
  | append_singleton gs g ih =>
    have pre' : ∃ b, C.gates=gs++b := by
      obtain ⟨b,hb⟩ := pre
      exact ⟨[g]++b,hb.trans (List.append_assoc _ _ _)⟩
    rw [List.mapIdx_concat]
    by_cases hw : w=n+gs.length
    · subst w
      have e : n+gs.length=n+(gs.mapIdx f).length := by simp
      rw [e,new_val,←e,new_val,show val (gs.mapIdx f) z=val gs z from funext (ih pre')]
      exact same gs g pre
    · rw [other_val _ _ _ (by simpa using hw),other_val _ _ _ hw]
      exact ih pre' w

private def pin (v dead w : ℕ) := if w=v then dead else w
private def reroute (v dead : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (pin v dead)⟩

private theorem pin_eval {n : ℕ} (v : Fin n) (dead : ℕ) (x : Fin n → Bool)
    (gs : List Gate) (hd : n+gs.length≤dead) (w : ℕ) :
    val (gs.map (reroute v dead)) x (pin v dead w) = val gs (Function.update x v false) w := by
  induction gs using List.reverseRecOn generalizing w with
  | nil =>
    by_cases hw : w=v.val
    · subst w
      simp only [pin,ite_true,List.map_nil,val,run,List.foldl_nil]
      rw [List.getD_eq_default _ _ (by simpa using hd),List.getD_eq_getElem _ _ (by simp)]
      simp
    · rw [show pin v dead w=w by simp [pin,hw]]
      simp only [List.map_nil,val,run,List.foldl_nil]
      by_cases h : w<n
      · rw [List.getD_eq_getElem _ _ (by simpa using h),List.getD_eq_getElem _ _ (by simpa using h)]
        simp only [List.getElem_ofFn]
        exact (Function.update_of_ne (show (⟨w,h⟩ : Fin n) ≠ v from fun e => hw (congrArg Fin.val e)) false x).symm
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h),
          List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)]
  | append_singleton gs g ih =>
    have hlen : n+gs.length<dead := by simp at hd; omega
    have hv := v.isLt
    simp only [List.map_append,List.map_cons,List.map_nil]
    by_cases hw : w=n+gs.length
    · subst w
      rw [show pin v dead (n+gs.length)=n+(gs.map (reroute v dead)).length by simp [pin,show n+gs.length≠v.val by omega],
        new_val,new_val]
      unfold readGate
      simp only [reroute,List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact ih hlen.le j
    · have hne : pin v dead w ≠ n+(gs.map (reroute v dead)).length := by
        simp only [pin,List.length_map]
        split <;> omega
      rw [other_val _ _ _ hne,other_val _ _ _ hw]
      exact ih hlen.le w


def Charged {n : ℕ} (C : Circuit) (v : Fin n) (j : ℕ) : Prop :=
  ∃ (i : ℕ) (g : Gate), C.gates[j]?=some g ∧ g.op=.or ∧ i∈g.inputs ∧ i<n+j ∧
    ∀ z : Fin n → Bool, z v=false → (C.wires (List.ofFn z)).getD i false=false


theorem restrict_many {n : ℕ} (C : Circuit) (v : Fin n) (A S : Finset ℕ) (hm : Monotone2 C)
    (cover : ∀ j g, C.gates[j]?=some g → g.op=.or → j∈A) (charges : ∀ j∈S, Charged C v j) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.gates.length=C.gates.length ∧
      (∀ x : Fin n → Bool, C'.eval (List.ofFn x)=C.eval (List.ofFn (Function.update x v false))) ∧
      ∀ j g, C'.gates[j]?=some g → g.op=.or → j∈A\S := by
  classical
  let dead := n+C.gates.length
  let operand (j : ℕ) : ℕ := if hj : j∈S then (charges j hj).choose else 0
  let change (j : ℕ) (g : Gate) := if j∈S then copyOf dead (operand j) g else g
  let gs := C.gates.mapIdx change
  let C' : Circuit := ⟨gs.map (reroute v dead),pin v dead C.output⟩
  have atGate (j : ℕ) (g : Gate) (h : C'.gates[j]?=some g) :
      ∃ q, C.gates[j]?=some q ∧ g=reroute v dead (change j q) := by
    change (gs.map (reroute v dead))[j]?=some g at h
    simp only [gs,List.getElem?_map,List.getElem?_mapIdx] at h
    cases eq : C.gates[j]? with
    | none => simp [eq] at h
    | some q => exact ⟨q,rfl,by simpa [eq] using h.symm⟩
  refine ⟨C',?_,by simp [C',gs],?_,?_⟩
  · intro g hg
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
    obtain ⟨q,hq,rfl⟩ := atGate j g hj
    have good := hm q (List.mem_of_getElem? hq)
    by_cases h : j∈S
    · simp [change,h,copyOf,reroute]
    · simpa [change,h,reroute] using good
  · intro x
    let z := Function.update x v false
    have hz : z v=false := by simp [z]
    have hstep (a : List Gate) (g : Gate) (pre : ∃ b, C.gates=(a++[g])++b) :
        readGate (change a.length g) (val a z) = readGate g (val a z) := by
      by_cases h : a.length∈S
      · obtain ⟨b,hb⟩ := pre
        have hh := (charges a.length h).choose_spec
        change ∃ (q : Gate), C.gates[a.length]?=some q ∧ q.op=.or ∧ _ at hh
        obtain ⟨q,hq,hop,hin,hi,hzero⟩ := hh
        have hhg : C.gates[a.length]?=some g := by simp [hb,List.append_assoc]
        obtain rfl : q=g := Option.some.inj (hq.symm.trans hhg)
        let i := (charges a.length h).choose
        have hlen : a.length ≤ C.gates.length := by simp [hb]
        have hdead : val a z dead=false := by
          unfold val
          apply List.getD_eq_default
          simp only [run_len,List.length_ofFn]
          dsimp [dead]
          omega
        have hfull : val C.gates z i=false := hzero z hz
        have ha : val a z i=false := by
          rw [hb,List.append_assoc] at hfull
          exact (val_initial a ([q]++b) z i hi).symm.trans hfull
        have hep : change a.length q=copyOf dead i q := by
          unfold change operand
          simp only [h,↓reduceIte,↓reduceDIte]
          rfl
        rw [hep]
        exact copy_value dead i q (val a z) hdead ha hop hin (hm q (List.mem_of_getElem? hhg)).2
      · simp [change,h]
    have hp := patch_val C change z hstep C.gates ⟨[],by simp⟩ C.output
    have hpin := pin_eval v dead x gs (by simp [gs,dead]) C.output
    exact hpin.trans hp
  · intro j g hg hop
    obtain ⟨q,hq,rfl⟩ := atGate j g hg
    by_cases h : j∈S
    · simp [reroute,change,h,copyOf] at hop
    · refine Finset.mem_sdiff.mpr ⟨cover j q hq ?_,h⟩
      simpa [reroute,change,h] using hop


theorem restrict_charged {n : ℕ} (C : Circuit) (v : Fin n) (A S : Finset ℕ) (hm : Monotone2 C)
    (cover : ∀ j g, C.gates[j]?=some g → g.op=.or → j∈A) (charges : ∀ j∈S, Charged C v j) :
    ∃ (C' : Circuit) (B : Finset ℕ), B.card+S.card=A.card ∧ Monotone2 C' ∧
      (∀ x : Fin n → Bool, C'.eval (List.ofFn x)=C.eval (List.ofFn (Function.update x v false))) ∧
      ∀ j g, C'.gates[j]?=some g → g.op=.or → j∈B := by
  have sub : S⊆A := by
    intro j hj
    obtain ⟨_,g,hg,hop,_⟩ := charges j hj
    exact cover j g hg hop
  obtain ⟨C',hM,_,hF,hB⟩ := restrict_many C v A S hm cover charges
  exact ⟨C',A\S,Finset.card_sdiff_add_card_eq_card sub,hM,hF,hB⟩


theorem restrict_one {n : ℕ} (C : Circuit) (v : Fin n) (A : Finset ℕ) (hm : Monotone2 C)
    (cover : ∀ j g, C.gates[j]?=some g → g.op=.or → j∈A)
    (on : ∃ x : Fin n → Bool, x v=false ∧ C.eval (List.ofFn x)=false ∧
      C.eval (List.ofFn (Function.update x v true))=true)
    (other : ∃ z : Fin n → Bool, z v=false ∧ C.eval (List.ofFn z)=true) :
    ∃ (C' : Circuit) (B : Finset ℕ), B.card+1=A.card ∧ Monotone2 C' ∧
      (∀ x : Fin n → Bool, C'.eval (List.ofFn x)=C.eval (List.ofFn (Function.update x v false))) ∧
      ∀ j g, C'.gates[j]?=some g → g.op=.or → j∈B := by
  obtain ⟨j,g,i,hg,hop,hin,hi,hv⟩ := release_exists C v hm on other
  have hp : Charged C v j := ⟨i,g,hg,hop,hin,hi,hv⟩
  simpa only [Finset.card_singleton] using restrict_charged C v A {j} hm cover
    (fun k hk => Finset.mem_singleton.mp hk ▸ hp)


theorem discard_redundant_or {n : ℕ} (C : Circuit) (A : Finset ℕ) (j : ℕ) (g : Gate)
    (hm : Monotone2 C) (cover : ∀ k h, C.gates[k]?=some h → h.op=.or → k∈A)
    (hg : C.gates[j]?=some g) (hop : g.op=.or)
    (same : (∃ w<n+j, ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n+j) false = (C.wires (List.ofFn x)).getD w false) ∨
      ∃ b : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n+j) false=b) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.gates.length=C.gates.length ∧
      (∀ x : Fin n → Bool, C'.eval (List.ofFn x)=C.eval (List.ofFn x)) ∧
      (∀ k h, C'.gates[k]?=some h → h.op=.or → k∈A.erase j) ∧ (A.erase j).card+1=A.card := by
  let dead := n+C.gates.length
  obtain ⟨l,hl,allowed,glob⟩ : ∃ l : List ℕ, l.length≤1 ∧
      (∀ w∈l, w<n+j ∨ w=dead) ∧
      ∀ x : Fin n → Bool, readGate ⟨.and,l⟩ (val C.gates x)=val C.gates x (n+j) := by
    rcases same with ⟨w,hw,eq⟩ | ⟨b,eq⟩
    · refine ⟨[w],by simp,fun z hz => (List.mem_singleton.mp hz) ▸ (Or.inl hw),?_⟩
      intro x
      have hx : val C.gates x w=val C.gates x (n+j) := (eq x).symm
      simpa [readGate,GateOp.eval] using hx
    · cases b
      · refine ⟨[dead],by simp,fun w hw => Or.inr (List.mem_singleton.mp hw),?_⟩
        intro x
        have hd : val C.gates x dead=false := by
          unfold val
          exact List.getD_eq_default _ _ (by simp [run_len,dead])
        have hx : false=val C.gates x (n+j) := (eq x).symm
        simpa [readGate,GateOp.eval,hd] using hx
      · exact ⟨[],by simp,by simp,fun x => (eq x).symm⟩
  let f (k : ℕ) (h : Gate) : Gate := if k=j then ⟨.and,l⟩ else h
  let C' : Circuit := ⟨C.gates.mapIdx f,C.output⟩
  have source (k : ℕ) (h : Gate) (hh : C'.gates[k]?=some h) :
      ∃ h', C.gates[k]?=some h' ∧ h=f k h' := by
    change (C.gates.mapIdx f)[k]?=some h at hh
    rw [List.getElem?_mapIdx] at hh
    cases h0 : C.gates[k]? with
    | none => simp [h0] at hh
    | some h' => exact ⟨h',rfl,by simpa [h0] using hh.symm⟩
  refine ⟨C',?_,by simp [C'],?_,?_,?_⟩
  · intro h hh
    obtain ⟨k,hk⟩ := List.mem_iff_getElem?.mp hh
    obtain ⟨h',h0,rfl⟩ := source k h hk
    by_cases hk : k=j
    · simp [f,hk]; omega
    · simpa [f,hk] using hm h' (List.mem_of_getElem? h0)
  · intro x
    apply patch_val C f x _ C.gates ⟨[],by simp⟩ C.output
    intro a h ⟨b,hb⟩
    by_cases ha : a.length=j
    · have hout : val C.gates x (n+j)=readGate h (val a x) := by
        rw [hb,← ha,val_initial (a++[h]) b x _ (by simp),new_val]
      have hdata : l.map (val a x)=l.map (val C.gates x) := by
        apply List.map_congr_left
        intro w hw
        rcases allowed w hw with h|rfl
        · rw [hb,List.append_assoc]
          exact (val_initial a ([_]++b) x w (by omega)).symm
        · have ha' : a.length≤C.gates.length := by simp [hb]
          unfold val
          rw [List.getD_eq_default _ _ (by simp [run_len,dead];omega),
            List.getD_eq_default _ _ (by simp [run_len,dead])]
      have hval : readGate ⟨.and,l⟩ (val a x)=readGate ⟨.and,l⟩ (val C.gates x) :=
        congrArg GateOp.and.eval hdata
      simpa [f,ha] using hval.trans ((glob x).trans hout)
    · simp [f,ha]
  · intro k h hh ha
    obtain ⟨h',h0,rfl⟩ := source k h hh
    by_cases hk : k=j
    · simp [f,hk] at ha
    · exact Finset.mem_erase.mpr ⟨hk,cover k h' h0 (by simpa [f,hk] using ha)⟩
  · exact Finset.card_erase_add_one (cover j g hg hop)

end Leaf599

namespace PaidGraph599
open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity GraphCircuit599
open scoped Classical
variable {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {A : Finset ℕ}

theorem after_restriction {v : Fin n} {C' : Circuit} (h : detects G C)
    (heq : ∀ x : Fin n → Bool,
      C'.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v false))) :
    detects (G.deleteIncidenceSet v) C' := by
  intro x
  rw [heq]
  exact (h _).trans (deletion_eval G v x)

theorem charged_saving (hm : Monotone2 C) (h : detects G C) (hc : covers C A)
    (v : Fin n) (S : Finset ℕ) (charged : ∀ j∈S, Leaf599.Charged C v j) :
    best (G.deleteIncidenceSet v) + S.card ≤ A.card := by
  obtain ⟨C',B,hB,hM,heq,hcov⟩ := Leaf599.restrict_charged C v A S hm hc charged
  have hb := best_le (show feasible (G.deleteIncidenceSet v) B.card from
    ⟨C',B,hM,after_restriction h heq,hcov,rfl⟩)
  omega

theorem charge_is_active (hm : Monotone2 C) (h : detects G C) (hc : covers C A)
    (hmin : A.card = best G) {v : Fin n} {j : ℕ} (hj : Leaf599.Charged C v j) :
    v ∈ G.support := by
  by_contra hv
  have hh := charged_saving hm h hc v {j} (fun k hk => Finset.mem_singleton.mp hk ▸ hj)
  simp only [delete_isolated hv,Finset.card_singleton,hmin,Nat.not_succ_le_self] at hh

theorem double_saving (hm : Monotone2 C) (h : detects G C) (hc : covers C A)
    (v : Fin n) {i j : ℕ} (hne : i ≠ j) (hi : Leaf599.Charged C v i)
    (hj : Leaf599.Charged C v j) : best (G.deleteIncidenceSet v) + 2 ≤ A.card := by
  have hh := charged_saving hm h hc v {i,j} (fun k hk => by
    rcases Finset.mem_insert.mp hk with he|he
    · exact he ▸ hi
    · exact Finset.mem_singleton.mp he ▸ hj)
  simpa [hne] using hh

theorem leaf_paid (hg : best G + 1 < G.edgeSet.ncard) (v : Fin n) (degree : G.degree v = 1) :
    best (G.deleteIncidenceSet v) + 1 ≤ best G := by
  obtain ⟨C,A,hm,h,hc,hmin⟩ := represents (show best G < G.edgeSet.ncard by omega)
  have hv := (G.degree_pos_iff_mem_support v).mp (show 0 < G.degree v by omega)
  obtain ⟨C',B,hB,hM,heq,hcov⟩ := Leaf599.restrict_one C v A hm hc (one_bit h hv)
    (accepts_without h v (by omega))
  have hb := best_le (show feasible (G.deleteIncidenceSet v) B.card from
    ⟨C',B,hM,after_restriction h heq,hcov,rfl⟩)
  omega

def corePaid (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), GraphInduction599.sparse G → GraphInduction599.noFour G →
    best G + 1 < G.edgeSet.ncard → (∀ v ∈ G.support, G.degree v = 2) →
    ∃ v ∈ G.support, best (G.deleteIncidenceSet v) + 2 ≤ best G

theorem edge_bound (core : corePaid n) (hs : GraphInduction599.sparse G)
    (hf : GraphInduction599.noFour G) (hm : Monotone2 C) (h : detects G C)
    (hc : covers C A) : G.edgeSet.ncard ≤ A.card + 1 := by
  have hb := best_le (show feasible G A.card from ⟨C,A,hm,h,hc,rfl⟩)
  exact (GraphInduction599.of_paid_deletions best (fun _ _ _ hg => leaf_paid hg)
    core G hs hf).trans (by omega)

end PaidGraph599

namespace CycleModule599

open Finset
variable {V : Type*} [DecidableEq V]

def edgeAt (G : SimpleGraph V) (X : Finset V) : Prop :=
  ∃ u ∈ X, ∃ v ∈ X, G.Adj u v

theorem edgeAt_mono {G : SimpleGraph V} {X Y : Finset V} (h : X ⊆ Y) :
    edgeAt G X → edgeAt G Y :=
  fun ⟨a,ha,b,hb,he⟩ => ⟨a,h ha,b,h hb,he⟩

@[simp] theorem no_edge_empty (G : SimpleGraph V) : ¬edgeAt G ∅ := by simp [edgeAt]
@[simp] theorem no_edge_singleton (G : SimpleGraph V) (v : V) : ¬edgeAt G {v} := by
  simp [edgeAt]

@[simp] theorem edgeAt_pair (G : SimpleGraph V) (u v : V) : edgeAt G {u,v} ↔ G.Adj u v := by
  simp only [edgeAt,mem_insert,mem_singleton]
  constructor
  · rintro ⟨a,rfl|rfl,b,rfl|rfl,h⟩
    · exact (G.irrefl h).elim
    · exact h
    · exact h.symm
    · exact (G.irrefl h).elim
  · intro h
    exact ⟨u,Or.inl rfl,v,Or.inr rfl,h⟩

theorem pair_minimal {G : SimpleGraph V} {Y : Finset V} {p q : V}
    (hY : edgeAt G Y) (hs : Y ⊆ {p,q}) : Y = {p,q} := by
  obtain ⟨a,ha,b,hb,hab⟩ := hY
  have ha' := hs ha
  have hb' := hs hb
  simp only [mem_insert,mem_singleton] at ha' hb'
  apply subset_antisymm hs
  intro i hi
  simp only [mem_insert,mem_singleton] at hi
  have hne := hab.ne
  grind


def bit (A B X : Finset V) : Prop := A ⊆ X ∨ B ⊆ X


def factors (G : SimpleGraph V) (S A B : Finset V) : Prop :=
  ∀ X ⊆ S, ∀ Y ⊆ S, (bit A B X ↔ bit A B Y) →
    ∀ T : Finset V, Disjoint T S → (edgeAt G (X ∪ T) ↔ edgeAt G (Y ∪ T))

private theorem bit_empty {A B : Finset V} (hA : A.Nonempty) (hB : B.Nonempty) :
    ¬ bit A B ∅ := by
  simpa [bit,hA.ne_empty,hB.ne_empty]


theorem interior_bit {G : SimpleGraph V} {S A B : Finset V}
    (fac : factors G S A B) (hA : A.Nonempty) (hB : B.Nonempty) (internal : edgeAt G S) :
    ∀ X ⊆ S, edgeAt G X ↔ bit A B X := by
  classical
  have lo := bit_empty hA hB
  have hbit (X : Finset V) (hX : X⊆S) (edge : edgeAt G X) : bit A B X := by
    by_contra h
    have same := fac X hX ∅ (empty_subset _) (iff_of_false h lo) ∅ (by simp)
    simpa using same.mp (by simpa using edge)
  have hi := hbit S (fun _ h => h) internal
  intro X hX
  refine ⟨hbit X hX,fun hx => ?_⟩
  have same := fac X hX S (fun _ h => h) (iff_of_true hx hi) ∅ (by simp)
  simpa using same.mpr (by simpa using internal)

theorem isolated_from_outside {G : SimpleGraph V} {S A B : Finset V}
    (fac : factors G S A B) (hA : A.Nonempty) (hB : B.Nonempty) (internal : edgeAt G S)
    {p : V} (hp : p∈S) {q : V} (hpq : G.Adj p q) : q ∈ S := by
  by_contra hq
  have hsingle : ¬bit A B {p} := by
    rw [← interior_bit fac hA hB internal {p} (Finset.singleton_subset_iff.mpr hp)]
    exact no_edge_singleton G p
  have same := fac {p} (singleton_subset_iff.mpr hp) ∅ (empty_subset _)
    (iff_of_false hsingle (bit_empty hA hB)) {q} (by simpa using hq)
  have yes : edgeAt G ({p}∪{q}) := by simpa using hpq
  simpa using same.mp yes

private theorem independent_bit {G : SimpleGraph V} {S A B : Finset V}
    (fac : factors G S A B) (hA : A.Nonempty) (hB : B.Nonempty) (indep : ¬edgeAt G S)
    {p : V} (hp : p∈S) {q : V} (hpq : G.Adj p q) : bit A B {p} := by
  by_contra hn
  have hq : q∉S := fun hh => indep ⟨p,hp,q,hh,hpq⟩
  have same := fac {p} (singleton_subset_iff.mpr hp) ∅ (empty_subset _)
    (iff_of_false hn (bit_empty hA hB)) {q} (by simpa using hq)
  have yes : edgeAt G ({p}∪{q}) := by simpa using hpq
  simpa using same.mp yes


theorem independent_twins {G : SimpleGraph V} {S A B : Finset V}
    (fac : factors G S A B) (hA : A.Nonempty) (hB : B.Nonempty) (indep : ¬edgeAt G S)
    {p q : V} (hp : p∈S) (hq : q∈S) (pactive : ∃ a, G.Adj p a) (qactive : ∃ a, G.Adj q a) :
    ∀ t, G.Adj p t ↔ G.Adj q t := by
  intro t
  obtain ⟨a,ha⟩ := pactive
  obtain ⟨b,hb⟩ := qactive
  by_cases ht : t ∈ S
  · exact iff_of_false (fun h => indep ⟨p,hp,t,ht,h⟩) (fun h => indep ⟨q,hq,t,ht,h⟩)
  · have same := fac {p} (singleton_subset_iff.mpr hp) {q} (singleton_subset_iff.mpr hq)
      (iff_of_true (independent_bit fac hA hB indep hp ha) (independent_bit fac hA hB indep hq hb))
      {t} (by simpa using ht)
    simpa using same

theorem at_most_two_edges {G : SimpleGraph V} {A B S : Finset V}
    (fac : factors G S A B) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAS : A⊆S) (hBS : B⊆S) (internal : edgeAt G S) {p q : V} (hp : p∈S) (hq : q∈S)
    (he : G.Adj p q) : ({p,q} : Finset V)=A ∨ ({p,q} : Finset V)=B := by
  have encode := interior_bit fac hA hB internal
  have hpair : ({p,q} : Finset V)⊆S := by
    intro i hi
    simp only [mem_insert,mem_singleton] at hi
    rcases hi with rfl|rfl <;> assumption
  rcases (encode _ hpair).mp ((edgeAt_pair _ _ _).mpr he) with h|h
  · exact Or.inl (pair_minimal ((encode _ hAS).mpr (Or.inl (fun _ hi => hi))) h).symm
  · exact Or.inr (pair_minimal ((encode _ hBS).mpr (Or.inr (fun _ hi => hi))) h).symm


theorem no_module {G : SimpleGraph V} {A B S : Finset V} (hAS : A⊆S) (hBS : B⊆S)
    (hA : A.Nonempty) (hB : B.Nonempty) (two : ∃ p ∈ S, ∃ q ∈ S, p≠q)
    (degree : ∀ p∈S, ∃ q r, q≠r ∧ G.Adj p q ∧ G.Adj p r)
    (not_twins : ∀ p∈S, ∀ q∈S, p≠q → ¬∀ t, G.Adj p t ↔ G.Adj q t) :
    ¬ factors G S A B := by
  classical
  intro fac
  obtain ⟨p,hp,q,hq,hneq⟩ := two
  by_cases inside : edgeAt G S
  · have closed := @isolated_from_outside _ _ G S A B fac hA hB inside
    obtain ⟨a,b,hab,hpa,hpb⟩ := degree p hp
    have ha := closed hp hpa
    have hb := closed hp hpb
    obtain ⟨c,d,hcd,hac,had⟩ := degree a ha
    obtain ⟨z,hzp,haz⟩ : ∃ z, z≠p ∧ G.Adj a z := by
      by_cases hc : c=p
      · exact ⟨d,fun he => hcd (hc.trans he.symm),had⟩
      · exact ⟨c,hc,hac⟩
    have hz := closed ha haz
    have f := @at_most_two_edges _ _ G A B S fac hA hB hAS hBS inside
    have h1 := f hp ha hpa
    have h2 := f hp hb hpb
    have h3 := f ha hz haz
    have hpna := hpa.ne
    have hpnb := hpb.ne
    have hanz := haz.ne
    have diff12 : ({p,a}:Finset V) ≠ {p,b} := by
      intro eq
      have : a∈({p,b}:Finset V) := eq ▸ (by simp : a∈({p,a}:Finset V))
      simpa [Ne.symm hpna,hab] using this
    have diff13 (x : V) : ({p,x}:Finset V) ≠ {a,z} := by
      intro eq
      have : p∈({a,z}:Finset V) := eq ▸ (by simp : p∈({p,x}:Finset V))
      simpa [hpna,Ne.symm hzp] using this
    rcases h1 with h1|h1 <;> rcases h2 with h2|h2 <;> rcases h3 with h3|h3 <;> grind
  · apply not_twins p hp q hq hneq
    obtain ⟨a,_,_,ha,_⟩ := degree p hp
    obtain ⟨b,_,_,hb,_⟩ := degree q hq
    exact independent_twins fac hA hB inside hp hq ⟨a,ha⟩ ⟨b,hb⟩


theorem twins_force_square {G : SimpleGraph V} {p q : V} (hpq : p≠q)
    {a b : V} (hab : a≠b) (hpa : G.Adj p a) (hpb : G.Adj p b)
    (hqa : G.Adj q a) (hqb : G.Adj q b) :
    ∃ W : G.Walk p p, W.IsCycle ∧ W.length=4 := by
  let W : G.Walk p p := .cons hpa (.cons hqa.symm (.cons hqb (.cons hpb.symm .nil)))
  have hlen : W.length=4 := rfl
  refine ⟨W,SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_,by omega⟩,hlen⟩
  simp only [W,SimpleGraph.Walk.tail_cons,SimpleGraph.Walk.isPath_copy,
    SimpleGraph.Walk.isPath_def,SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil]
  simp [hab,hpa.ne.symm,hqa.ne.symm,hqb.ne,hpb.ne.symm,hpq.symm]

theorem no_module_of_no_four {G : SimpleGraph V} {A B S : Finset V}
    (hAS : A⊆S) (hBS : B⊆S) (hA : A.Nonempty) (hB : B.Nonempty)
    (two : ∃ p ∈ S, ∃ q ∈ S, p≠q)
    (degree : ∀ p∈S, ∃ q r, q≠r ∧ G.Adj p q ∧ G.Adj p r)
    (no4 : ∀ v (c : G.Walk v v), c.IsCycle → c.length ≠ 4) : ¬ factors G S A B := by
  apply no_module hAS hBS hA hB two degree
  intro p hp q hq hpq eq
  obtain ⟨a,b,hab,hpa,hpb⟩ := degree p hp
  obtain ⟨c,hc,hlen⟩ := twins_force_square hpq hab hpa hpb ((eq a).mp hpa) ((eq b).mp hpb)
  exact no4 p c hc hlen

end CycleModule599

namespace CycleCut599
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def readGate (g : Gate) (w : ℕ → Bool) : Bool := g.op.eval (g.inputs.map w)
private def run (gs : List Gate) (input : List Bool) : List Bool :=
  gs.foldl (fun wires g => wires ++ [readGate g (fun j => wires.getD j false)]) input

private theorem run_append (gs : List Gate) (g : Gate) (s : List Bool) :
    run (gs ++ [g]) s = run gs s ++ [readGate g (fun j => (run gs s).getD j false)] := by
  simp [run,List.foldl_append]

private theorem run_len (gs : List Gate) (s : List Bool) : (run gs s).length=s.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => simp [run_append,ih,Nat.add_assoc]

private def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (run gs (List.ofFn x)).getD w false

private theorem new_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    val (gs++[g]) x (n+gs.length) = readGate g (val gs x) := by
  have hl : (run gs (List.ofFn x)).length=n+gs.length := by simp [run_len]
  unfold val
  rw [run_append,←hl]
  simp

private theorem other_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) {w : ℕ}
    (h : w ≠ n+gs.length) : val (gs++[g]) x w = val gs x w := by
  have hl : (run gs (List.ofFn x)).length=n+gs.length := by simp [run_len]
  unfold val
  rw [run_append]
  by_cases hw : w < (run gs (List.ofFn x)).length
  · exact List.getD_append _ _ _ _ hw
  · rw [List.getD_eq_default _ _ (by simp [hl]; omega),List.getD_eq_default _ _ (by omega)]

def releaseAt {n : ℕ} (gs : List Gate) (v : Fin n) (j : ℕ) : Prop :=
  ∃ g i, gs[j]?=some g ∧ g.op=.or ∧ i∈g.inputs ∧ i<n+j ∧
    ∀ z : Fin n → Bool, z v=false → ((⟨gs,0⟩ : Circuit).wires (List.ofFn z)).getD i false=false

private theorem push_release {n j : ℕ} {gs : List Gate} {v : Fin n} (g : Gate)
    (h : releaseAt gs v j) : releaseAt (gs++[g]) v j := by
  obtain ⟨q,i,hj,hop,hi,hlt,hz⟩ := h
  have hjl := (List.getElem?_eq_some_iff.mp hj).1
  refine ⟨q,i,(List.getElem?_append_left hjl).trans hj,hop,hi,hlt,?_⟩
  intro z hv
  exact (other_val gs g z (by omega)).trans (hz z hv)

private theorem changed_dominated {n : ℕ} (S : Finset (Fin n)) (x y : Fin n → Bool)
    (agree : ∀ i, i ∉ S → x i = y i) (p : ℕ) (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op=.and ∨ g.op=.or)
    (only : ∀ v ∈ S, ∀ j, releaseAt gs v j → j=p)
    (same : p<gs.length → val gs x (n+p)=val gs y (n+p)) (w : ℕ)
    (hd : val gs x w ≠ val gs y w) :
    ∃ v∈S, ∀ z : Fin n → Bool, z v=false → val gs z w=false := by
  induction gs using List.reverseRecOn generalizing w with
  | nil =>
    change (List.ofFn x).getD w false ≠ (List.ofFn y).getD w false at hd
    by_cases hw : w<n
    · let i : Fin n := ⟨w,hw⟩
      have hx : ∀ t : Fin n → Bool, val [] t w = t i := by
        intro t; change (List.ofFn t).getD w false=t i
        rw [List.getD_eq_getElem _ _ (by simpa using hw)]
        simp [i]
      refine ⟨i,by
        by_contra hi
        exact hd ((hx x).trans ((agree i hi).trans (hx y).symm)),?_⟩
      intro z hz
      exact (hx z).trans hz
    · exact (hd (by rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hw),
          List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hw)])).elim
  | append_singleton gs g ih =>
    have hm' : ∀ q∈gs, q.op=.and ∨ q.op=.or := fun q h => hm q (List.mem_append_left _ h)
    have only' : ∀ v∈S, ∀ j, releaseAt gs v j → j=p :=
      fun v hv j hj => only v hv j (push_release g hj)
    have same' (h : p<gs.length) : val gs x (n+p)=val gs y (n+p) := by
      have he := same (by simp; omega)
      simpa only [other_val gs g _ (by omega : n+p ≠ n+gs.length)] using he
    by_cases hw : w=n+gs.length
    · subst w
      have hd' := hd
      rw [new_val,new_val] at hd'
      obtain ⟨a,ha,had⟩ : ∃ a∈g.inputs, val gs x a ≠ val gs y a := by
        by_contra! h
        exact hd' (congrArg g.op.eval (List.map_congr_left h))
      have bound : a<n+gs.length := by
        by_contra! h
        unfold val at had
        exact had (by rw [List.getD_eq_default _ _ (by simpa [run_len] using h),
          List.getD_eq_default _ _ (by simpa [run_len] using h)])
      obtain ⟨v,hv,below⟩ := ih hm' only' same' a had
      rcases hm g (by simp) with hand|hor
      · refine ⟨v,hv,fun z hz => ?_⟩
        rw [new_val]
        change (g.op.eval _) = false
        rw [hand]
        apply List.all_eq_false.mpr
        exact ⟨_,List.mem_map.mpr ⟨a,ha,rfl⟩,by simp [below z hz]⟩
      · have atGate : releaseAt (gs++[g]) v gs.length := by
          refine ⟨g,a,by simp,hor,ha,bound,fun z hz => ?_⟩
          exact (other_val _ _ _ (Nat.ne_of_lt bound)).trans (below z hz)
        have e := only v hv _ atGate
        subst p
        exact (hd (same (by simp))).elim
    · rw [other_val _ _ _ hw,other_val _ _ _ hw] at hd
      obtain ⟨v,hv,below⟩ := ih hm' only' same' w hd
      exact ⟨v,hv,fun z hz => (other_val _ _ _ hw).trans (below z hz)⟩

theorem factor_gate {n : ℕ} (S : Finset (Fin n)) (C : Circuit) (p : ℕ) (hm : Monotone2 C)
    (only : ∀ v∈S, ∀ j, releaseAt C.gates v j → j=p)
    (free : ∀ v∈S, ∃ z : Fin n → Bool, z v=false ∧ C.eval (List.ofFn z)=true)
    (x y : Fin n → Bool) (agree : ∀ i, i∉S → x i=y i)
    (same : (C.wires (List.ofFn x)).getD (n+p) false=(C.wires (List.ofFn y)).getD (n+p) false) :
    C.eval (List.ofFn x)=C.eval (List.ofFn y) := by
  by_contra hd
  obtain ⟨v,hv,below⟩ := changed_dominated S x y agree p C.gates (fun g hg => (hm g hg).1)
    only (fun _ => same) C.output hd
  obtain ⟨z,hz,ho⟩ := free v hv
  exact Bool.false_ne_true ((below z hz).symm.trans ho)

def mask {n : ℕ} (X : Finset (Fin n)) (i : Fin n) : Bool := decide (i∈X)

theorem graph_factors {n : ℕ} (G : SimpleGraph (Fin n)) (S A B : Finset (Fin n))
    (C : Circuit) (p : ℕ) (hm : Monotone2 C)
    (hAS : A⊆S) (hBS : B⊆S)
    (only : ∀ v∈S, ∀ j, releaseAt C.gates v j → j=p)
    (free : ∀ v∈S, ∃ z : Fin n → Bool, z v=false ∧ C.eval (List.ofFn z)=true)
    (bit_eq : ∀ U : Finset (Fin n), (C.wires (List.ofFn (mask U))).getD (n+p) false=true ↔
      CycleModule599.bit A B U)
    (spec : ∀ U : Finset (Fin n), C.eval (List.ofFn (mask U))=true ↔ CycleModule599.edgeAt G U) :
    CycleModule599.factors G S A B := by
  intro X hX Y hY bits T ht
  have part (U Q : Finset (Fin n)) (hU : U⊆S) : U⊆Q∪T ↔ U⊆Q := by
    constructor
    · intro h i hi
      exact (Finset.mem_union.mp (h hi)).resolve_right (fun he => Finset.disjoint_left.mp ht he (hU hi))
    · intro h i hi
      exact Finset.mem_union_left _ (h hi)
  have beq : CycleModule599.bit A B (X∪T) ↔ CycleModule599.bit A B (Y∪T) := by
    simpa only [CycleModule599.bit,part A _ hAS,part B _ hBS] using bits
  have eq := factor_gate S C p hm only free (mask (X∪T)) (mask (Y∪T)) (by
    intro i hi
    have hx : i∉X := fun h => hi (hX h)
    have hy : i∉Y := fun h => hi (hY h)
    simp [mask,hx,hy]) (Bool.eq_iff_iff.mpr ((bit_eq _).trans (beq.trans (bit_eq _).symm)))
  exact (spec _).symm.trans ((iff_of_eq (congrArg (fun b => b = true) eq)).trans (spec _))

private theorem val_initial {n : ℕ} (a b : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : w<n+a.length) : val (a++b) x w=val a x w := by
  induction b using List.reverseRecOn with
  | nil => simp
  | append_singleton b g ih => rw [←List.append_assoc,other_val _ _ _ (by simp; omega),ih]

private theorem out_val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : n+gs.length ≤ w) : val gs x w=false := by
  exact List.getD_eq_default _ _ (by simpa [run_len] using hw)

def monomial {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) := ∀ v∈A, x v=true

def principal {n : ℕ} (f : (Fin n → Bool) → Bool) :=
  (∀ x, f x=false) ∨ ∃ A : Finset (Fin n), ∀ x, f x=true ↔ monomial A x

private theorem principal_all {n : ℕ} (l : List ℕ) (z : (Fin n → Bool) → ℕ → Bool)
    (h : ∀ j∈l, principal (fun x => z x j)) : principal (fun x => (l.map (z x)).all id) := by
  induction l with
  | nil => right; exact ⟨∅,by simp [monomial]⟩
  | cons a l ih =>
    rcases h a (by simp) with ha|⟨A,ha⟩
    · left; intro x; simp [ha]
    rcases ih (fun j hj => h j (by simp [hj])) with hl|⟨B,hB⟩
    · left; intro x; simp [hl]
    right; refine ⟨A∪B,fun x => ?_⟩
    simp only [List.map_cons,List.all_cons,id_eq,Bool.and_eq_true]
    rw [ha,hB]
    simp [monomial,Finset.mem_union,or_imp,forall_and]

theorem all_and_principal {n : ℕ} (gs : List Gate)
    (hall : ∀g∈gs, g.op=.and) (w : ℕ) :
    principal (fun x : Fin n → Bool => ((⟨gs,0⟩ : Circuit).wires (List.ofFn x)).getD w false) := by
  change principal (fun x : Fin n → Bool => val gs x w)
  induction gs using List.reverseRecOn generalizing w with
  | nil =>
    by_cases h : w<n
    · right; refine ⟨{⟨w,h⟩},fun x => ?_⟩
      change (List.ofFn x).getD w false=true ↔ _
      rw [List.getD_eq_getElem _ _ (by simpa using h)]
      simp [monomial]
    · left; exact fun x => out_val _ _ _ (by simp; omega)
  | append_singleton gs g ih =>
    have h : ∀q∈gs, q.op=.and := fun q hq => hall q (List.mem_append_left _ hq)
    by_cases hw : w=n+gs.length
    · subst w
      simp only [new_val,readGate,hall g (by simp),GateOp.eval]
      exact principal_all _ _ (fun j _ => ih h j)
    · simpa only [other_val gs g _ hw] using ih h w

private theorem mono_antitone {n : ℕ} {A B : Finset (Fin n)} (h : A⊆B) {x : Fin n → Bool}
    (hx : monomial B x) : monomial A x := fun v hv => hx v (h hv)

theorem initial_decision {n : ℕ} (pre post : List Gate) (g : Gate)
    (hall : ∀q∈pre, q.op=.and) (hop : g.op=.or) (hlen : g.inputs.length≤2) :
    let gs := (pre++[g])++post
    (∃ w, ∀ x : Fin n → Bool,
      ((⟨gs,0⟩ : Circuit).wires (List.ofFn x)).getD (n+pre.length) false =
      ((⟨pre,0⟩ : Circuit).wires (List.ofFn x)).getD w false) ∨
    (∃ A B : Finset (Fin n), ¬ A⊆B ∧ ¬ B⊆A ∧
      (∀ v∈A∪B, releaseAt gs v pre.length) ∧
      (∀ U : Finset (Fin n), ((⟨gs,0⟩ : Circuit).wires (List.ofFn (mask U))).getD
        (n+pre.length) false=true ↔ CycleModule599.bit A B U)) := by
  dsimp only
  let gs := (pre++[g])++post
  have thisGate (x : Fin n → Bool) : val gs x (n+pre.length)=readGate g (val pre x) :=
    (val_initial (pre++[g]) post x _ (by simp)).trans (new_val pre g x)
  cases hi : g.inputs with
  | nil =>
    left; refine ⟨n+pre.length,fun x => ?_⟩
    change val gs x _=val pre x _
    rw [thisGate,out_val _ _ _ (by omega)]
    simp [readGate,hop,hi,GateOp.eval]
  | cons a l =>
    cases hj : l with
    | nil =>
      left; refine ⟨a,fun x => ?_⟩
      change val gs x _=val pre x _
      rw [thisGate]; simp [readGate,hop,hi,hj,GateOp.eval]
    | cons b tail =>
      have ht : tail=[] := by apply List.length_eq_zero_iff.mp; rw [hi,hj] at hlen; simp only [List.length_cons] at hlen; omega
      subst tail
      have ins : g.inputs=[a,b] := by rw [hi,hj]
      have gate (x : Fin n → Bool) : val gs x (n+pre.length) = (val pre x a || val pre x b) := by
        rw [thisGate]; simp [readGate,hop,ins,GateOp.eval]
      have pure (w : ℕ) : principal (fun x : Fin n → Bool => val pre x w) := all_and_principal pre hall w
      rcases pure a with ha|⟨A,ha⟩
      · left; exact ⟨b,fun x => by change val gs x _=val pre x _; rw [gate,show val pre x a=false from ha x]; simp⟩
      rcases pure b with hb|⟨B,hb⟩
      · left; exact ⟨a,fun x => by change val gs x _=val pre x _; rw [gate,show val pre x b=false from hb x]; simp⟩
      by_cases hab : A⊆B
      · left; refine ⟨a,fun x => ?_⟩
        change val gs x _=val pre x _
        apply Bool.eq_iff_iff.mpr
        rw [gate,Bool.or_eq_true,ha,hb]
        exact or_iff_left_of_imp (mono_antitone hab)
      by_cases hba : B⊆A
      · left; refine ⟨b,fun x => ?_⟩
        change val gs x _=val pre x _
        apply Bool.eq_iff_iff.mpr
        rw [gate,Bool.or_eq_true,ha,hb]
        exact or_iff_right_of_imp (mono_antitone hba)
      right
      have charge (w : ℕ) (L : Finset (Fin n)) (hin : w∈g.inputs)
          (rep : ∀ x : Fin n → Bool, val pre x w=true ↔ monomial L x) (v : Fin n) (hv : v∈L) :
          releaseAt gs v pre.length := by
        have valid : w<n+pre.length := by
          by_contra! h
          have yes := (rep (fun _ => true)).mpr (by intro i _; rfl)
          rw [out_val _ _ _ h] at yes
          contradiction
        refine ⟨g,w,?_,hop,hin,valid,fun x hx => ?_⟩
        · rw [List.getElem?_append_left (by simp)]; simp
        · change val ((pre++[g])++post) x w=false
          rw [List.append_assoc,val_initial _ _ _ _ valid]
          cases e : val pre x w with
          | false => rfl
          | true => exact (Bool.false_ne_true (hx.symm.trans ((rep x).mp e v hv))).elim
      refine ⟨A,B,hab,hba,?_,fun U => ?_⟩
      · intro v hv
        rcases Finset.mem_union.mp hv with hv|hv
        · exact charge a A (by simp [ins]) ha v hv
        · exact charge b B (by simp [ins]) hb v hv
      · change val gs (mask U) _=true ↔ _
        rw [gate,Bool.or_eq_true,ha,hb]
        simp only [monomial,mask,decide_eq_true_eq,CycleModule599.bit]; rfl

theorem global_copy {n : ℕ} (pre post : List Gate) (g : Gate)
    (copy : ∃ w, ∀ x : Fin n → Bool, ((⟨(pre++[g])++post,0⟩ : Circuit).wires
      (List.ofFn x)).getD (n+pre.length) false = ((⟨pre,0⟩ : Circuit).wires (List.ofFn x)).getD w false) :
    let C : Circuit := ⟨(pre++[g])++post,0⟩
    (∃ w<n+pre.length, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n+pre.length) false =
      (C.wires (List.ofFn x)).getD w false) ∨
      ∃ b : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n+pre.length) false=b := by
  obtain ⟨w,eq⟩ := copy
  by_cases h : w<n+pre.length
  · left; refine ⟨w,h,fun x => (eq x).trans ?_⟩
    change val pre x w=val ((pre++[g])++post) x w
    rw [List.append_assoc,val_initial _ _ _ _ h]
  · right; exact ⟨false,fun x => (eq x).trans (out_val pre x w (by omega))⟩

end CycleCut599

namespace CoreFacts599
open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity GraphCircuit599 PaidGraph599
open scoped Classical
variable {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {A : Finset ℕ}

theorem forbids_copy (hm : Monotone2 C) (h : detects G C) (hc : covers C A)
    (hmin : A.card = best G) {p : ℕ} {g : Gate}
    (hg : C.gates[p]? = some g) (hop : g.op = .or)
    (same : (∃ w<n+p, ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n+p) false = (C.wires (List.ofFn x)).getD w false) ∨
      ∃ b : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n+p) false=b) : False := by
  obtain ⟨C',hm',_,heq,cover,hcard⟩ := Leaf599.discard_redundant_or C A p g hm hc hg hop same
  have hdet : detects G C' := by
    intro x
    rw [heq]
    exact h x
  have hh := best_le (show feasible G (A.erase p).card from ⟨C',A.erase p,hm',hdet,cover,rfl⟩)
  omega

theorem charged_iff_release (v : Fin n) (j : ℕ) :
    Leaf599.Charged C v j ↔ CycleCut599.releaseAt C.gates v j := by
  constructor
  · rintro ⟨i,g,hg,hop,hi,hij,hz⟩
    exact ⟨g,i,hg,hop,hi,hij,hz⟩
  · rintro ⟨g,i,hg,hop,hi,hij,hz⟩
    exact ⟨i,g,hg,hop,hi,hij,hz⟩


theorem pay_from_bit (hm : Monotone2 C) (h : detects G C) (hc : covers C A)
    (hmin : A.card = best G) (hf : GraphInduction599.noFour G)
    (degrees : ∀ u∈G.support, G.degree u = 2) (p : ℕ)
    (X Y : Finset (Fin n)) (hx : ¬ X ⊆ Y) (hy : ¬ Y ⊆ X)
    (hp : ∀ v∈X∪Y, Leaf599.Charged C v p)
    (bit_eq : ∀ U : Finset (Fin n), (C.wires (List.ofFn (CycleCut599.mask U))).getD (n+p) false=true ↔
      CycleModule599.bit X Y U) :
    ∃ v ∈ G.support, best (G.deleteIncidenceSet v) + 2 ≤ best G := by
  let S := X ∪ Y
  have active : ∀ v∈S, v ∈ G.support := fun v hv => charge_is_active hm h hc hmin (hp v hv)
  by_contra hn
  have only : ∀ v∈S, ∀ j, CycleCut599.releaseAt C.gates v j → j=p := by
    intro v hv j hj
    by_contra hne
    have pay := double_saving hm h hc v hne (charged_iff_release v j |>.mpr hj) (hp v hv)
    exact hn ⟨v,active v hv,hmin ▸ pay⟩
  have free := fun v hv => accepts_core_without h degrees (active v hv)
  have spec (U : Finset (Fin n)) : C.eval (List.ofFn (CycleCut599.mask U)) = true ↔
      CycleModule599.edgeAt G U := by
    rw [h]
    constructor
    · rintro ⟨a,b,hab,ha,hb⟩
      exact ⟨a,of_decide_eq_true ha,b,of_decide_eq_true hb,hab⟩
    · rintro ⟨a,ha,b,hb,hab⟩
      exact ⟨a,b,hab,decide_eq_true ha,decide_eq_true hb⟩
  have hXS : X ⊆ S := Finset.subset_union_left
  have hYS : Y ⊆ S := Finset.subset_union_right
  obtain ⟨u,hu,huy⟩ := Finset.not_subset.mp hx
  obtain ⟨v,hv,hvx⟩ := Finset.not_subset.mp hy
  have neq : u ≠ v := fun e => hvx (e ▸ hu)
  have ff := CycleCut599.graph_factors G S X Y C p hm hXS hYS only free bit_eq spec
  exact CycleModule599.no_module_of_no_four hXS hYS ⟨u,hu⟩ ⟨v,hv⟩
    ⟨u,hXS hu,v,hYS hv,neq⟩
    (fun w hw => two_neighbors (le_of_eq (degrees w (active w hw)).symm)) hf ff

end CoreFacts599

namespace Leaf599
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private theorem split_first_or (gs : List Gate)
    (hm : ∀ q ∈ gs, (q.op=.and ∨ q.op=.or) ∧ q.inputs.length≤2)
    (present : ∃ q ∈ gs, q.op=.or) :
    ∃ (pre : List Gate) (g : Gate) (post : List Gate), gs=(pre++[g])++post ∧
      (∀ q ∈ pre, q.op=.and) ∧ g.op=.or ∧ g.inputs.length≤2 := by
  induction gs with
  | nil => simp at present
  | cons h t ih =>
    obtain ⟨hop,hlen⟩ := hm h List.mem_cons_self
    rcases hop with hand|hor
    · have tail : ∃ q ∈ t, q.op=.or := by
        obtain ⟨q,hq,hor⟩ := present
        rcases List.mem_cons.mp hq with rfl|hq
        · rw [hand] at hor
          cases hor
        · exact ⟨q,hq,hor⟩
      obtain ⟨a,g,b,eq,ha,hg,hl⟩ := ih (fun q hq => hm q (List.mem_cons_of_mem _ hq)) tail
      refine ⟨h::a,g,b,congrArg (List.cons h) eq,?_,hg,hl⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hand
      · exact ha q hq
    · exact ⟨[],h,t,rfl,by simp,hor,hlen⟩


theorem first_or {n : ℕ} (C : Circuit) (v : Fin n) (hm : Monotone2 C)
    (on : ∃ x : Fin n → Bool, x v=false ∧ C.eval (List.ofFn x)=false ∧
      C.eval (List.ofFn (Function.update x v true))=true)
    (other : ∃ z : Fin n → Bool, z v=false ∧ C.eval (List.ofFn z)=true) :
    ∃ (pre : List Gate) (g : Gate) (post : List Gate), C.gates=(pre++[g])++post ∧
      (∀ q ∈ pre, q.op=.and) ∧ g.op=.or ∧ g.inputs.length≤2 := by
  obtain ⟨j,g,_,hg,hop,_⟩ := release_exists C v hm on other
  exact split_first_or C.gates hm ⟨g,List.mem_of_getElem? hg,hop⟩

end Leaf599

namespace Pseudoforest599
open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open GraphCircuit599 PaidGraph599 CoreFacts599
open scoped Classical

theorem pay_core {n : ℕ} : corePaid n := by
  intro G _ hf hg degrees
  obtain ⟨C,A,hm,h,hc,hmin⟩ := represents (show best G < G.edgeSet.ncard by omega)
  obtain ⟨v,hv⟩ := support_nonempty (show 0 < G.edgeSet.ncard by omega)
  obtain ⟨pre,g,post,shape,ands,hor,hlen⟩ :=
    Leaf599.first_or C v hm (one_bit h hv) (accepts_core_without h degrees hv)
  cases C with
  | mk gs out =>
    dsimp at shape
    subst gs
    have hj : (((pre++[g])++post)[pre.length]?) = some g := by
      rw [List.getElem?_append_left (by simp)]
      simp
    rcases CycleCut599.initial_decision (n:=n) pre post g ands hor hlen with copy | choice
    · exact False.elim (forbids_copy hm h hc hmin hj hor (CycleCut599.global_copy pre post g copy))
    · obtain ⟨X,Y,hx,hy,charges,bits⟩ := choice
      exact pay_from_bit hm h hc hmin hf degrees pre.length X Y hx hy
        (fun w hw => (charged_iff_release w pre.length).mpr (charges w hw)) bits

end Pseudoforest599

lemma orBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset ℕ), (∀ S : Finset (Fin n), {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card) → (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → c.length ≠ 4) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → j ∈ A) → G.edgeSet.ncard ≤ A.card + 1 := by
  intro n G C A hs hf hm h hc
  exact PaidGraph599.edge_bound Pseudoforest599.pay_core hs hf hm h hc
-- The circuit translation and restriction helpers adapt L-meta-4682, L-meta-6784, and L-meta-563.
namespace AndConv

open PEqualNP.CircuitLowerBounds

abbrev Rec (n : ℕ) := Finset (Fin n) × Finset ℕ × Finset (Fin n) × Finset ℕ
abbrev Form (n : ℕ) := Option (Finset (Fin n) × Finset ℕ)

def zeroF {n : ℕ} : Form n := some (∅, ∅)

def orF {n : ℕ} : List (Form n) → Form n
  | [] => some (∅, ∅)
  | f :: fs =>
    match f, orF fs with
    | none, _ => none
    | some _, none => none
    | some (a, b), some (c, d) => some (a ∪ c, b ∪ d)

abbrev St (n : ℕ) := List (Form n) × List (Rec n)

def getF {n : ℕ} (s : St n) (i : ℕ) : Form n := s.1.getD i zeroF

def andStep {n : ℕ} (s : St n) (fa fb : Form n) : St n :=
  match fa, fb with
  | none, f => ⟨s.1 ++ [f], s.2⟩
  | some p, none => ⟨s.1 ++ [some p], s.2⟩
  | some (va, ga), some (vb, gb) => ⟨s.1 ++ [some (∅, {s.2.length})], s.2 ++ [(va, ga, vb, gb)]⟩

def step {n : ℕ} (s : St n) (g : Gate) : St n :=
  match g.op, g.inputs with
  | GateOp.or, ins => ⟨s.1 ++ [orF (ins.map (getF s))], s.2⟩
  | GateOp.and, [] => ⟨s.1 ++ [none], s.2⟩
  | GateOp.and, [a] => ⟨s.1 ++ [getF s a], s.2⟩
  | GateOp.and, a :: b :: _ => andStep s (getF s a) (getF s b)
  | _, _ => ⟨s.1 ++ [zeroF], s.2⟩

def sv {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) (V : Finset (Fin n)) (G : Finset ℕ) : Bool :=
  decide (∃ v ∈ V, v ∈ U) || decide (∃ j ∈ G, vs.getD j false = true)

def rvStep {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) (r : Rec n) : List Bool :=
  vs ++ [sv U vs r.1 r.2.1 && sv U vs r.2.2.1 r.2.2.2]

def rvals {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) : List Bool := rs.foldl (rvStep U) []

def fv {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) : Form n → Bool
  | none => true
  | some p => sv U vs p.1 p.2

theorem fv_orF {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) (fs : List (Form n)) :
    fv U vs (orF fs) = fs.any (fv U vs) := by
  induction fs with
  | nil => simp [orF, fv, sv]
  | cons f fs ih =>
    rcases f with _ | ⟨a, b⟩
    · simp [orF, fv]
    · rcases h : orF fs with _ | ⟨c, d⟩
      · rw [h] at ih
        simp only [orF, h, List.any_cons]
        rw [← ih]
        simp [fv]
      · rw [h] at ih
        simp only [orF, h, List.any_cons]
        rw [← ih]
        simp only [fv, sv, Finset.mem_union, or_and_right, exists_or, Bool.decide_or]
        ac_rfl

theorem rv_pre {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) :
    ∀ (vs : List Bool) (j : ℕ), j < vs.length → (rs.foldl (rvStep U) vs).getD j false = vs.getD j false := by
  induction rs with
  | nil => intro vs j _; rfl
  | cons r rs ih =>
    intro vs j hj
    simp only [List.foldl_cons]
    rw [ih _ j (by simp [rvStep]; omega)]
    simp [rvStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem rv_len {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) :
    ∀ vs : List Bool, (rs.foldl (rvStep U) vs).length = vs.length + rs.length := by
  induction rs with
  | nil => intro vs; simp
  | cons r rs ih => intro vs; simp only [List.foldl_cons, ih]; simp [rvStep]; omega

theorem rvals_len {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) : (rvals U rs).length = rs.length := by
  simp [rvals, rv_len]

theorem rvals_snoc {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (r : Rec n) :
    rvals U (rs ++ [r]) = rvStep U (rvals U rs) r := by
  simp [rvals, List.foldl_append]

theorem sv_congr {n : ℕ} (U : Finset (Fin n)) (vs vs' : List Bool) (V : Finset (Fin n)) (G : Finset ℕ)
    (h : ∀ j ∈ G, vs.getD j false = vs'.getD j false) : sv U vs V G = sv U vs' V G := by
  unfold sv
  congr 2
  apply propext
  constructor
  · rintro ⟨j, hj, hv⟩; exact ⟨j, hj, (h j hj) ▸ hv⟩
  · rintro ⟨j, hj, hv⟩; exact ⟨j, hj, (h j hj).symm ▸ hv⟩

def RefsLt {n : ℕ} (m : ℕ) (f : Form n) : Prop := ∀ p, f = some p → ∀ j ∈ p.2, j < m

def GoodRecs {n : ℕ} (rs : List (Rec n)) : Prop :=
  ∀ k (hk : k < rs.length), (∀ j ∈ rs[k].2.1, j < k) ∧ (∀ j ∈ rs[k].2.2.2, j < k)

theorem fv_snoc {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (r : Rec n) (f : Form n)
    (hf : RefsLt rs.length f) : fv U (rvals U (rs ++ [r])) f = fv U (rvals U rs) f := by
  rcases f with _ | p
  · rfl
  · simp only [fv]
    apply sv_congr
    intro j hj
    have hjl := hf p rfl j hj
    rw [rvals_snoc]
    simp [rvStep, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [rvals_len U]; exact hjl)]

theorem refs_orF {n : ℕ} (m : ℕ) (fs : List (Form n)) (h : ∀ f ∈ fs, RefsLt m f) : RefsLt m (orF fs) := by
  induction fs with
  | nil => intro p hp j hj; simp [orF] at hp; subst hp; simp at hj
  | cons f fs ih =>
    have ih' := ih (fun f' hf' => h f' (by simp [hf']))
    have hf := h f (by simp)
    intro p hp j hj
    rcases f with _ | ⟨a, b⟩
    · simp [orF] at hp
    · rcases hq : orF fs with _ | ⟨c, d⟩
      · simp [orF, hq] at hp
      · simp only [orF, hq, Option.some.injEq] at hp
        subst hp
        rcases Finset.mem_union.1 hj with hj | hj
        · exact hf _ rfl j hj
        · exact ih' _ hq j hj

theorem refs_getF {n : ℕ} (m : ℕ) (s : St n) (h : ∀ f ∈ s.1, RefsLt m f) (i : ℕ) : RefsLt m (getF s i) := by
  unfold getF
  by_cases hi : i < s.1.length
  · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    intro p hp j hj
    simp [zeroF] at hp; subst hp; simp at hj

def Fw (W : List Bool) (g : Gate) : List Bool := W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]

def Inv {n : ℕ} (U : Finset (Fin n)) (W : List Bool) (s : St n) : Prop :=
  s.1.length = W.length ∧ (∀ f ∈ s.1, RefsLt s.2.length f) ∧ GoodRecs s.2 ∧
    ∀ i, W.getD i false = fv U (rvals U s.2) (getF s i)

theorem getF_push {n : ℕ} (fs : List (Form n)) (rs : List (Rec n)) (f : Form n) (i : ℕ) :
    getF ⟨fs ++ [f], rs⟩ i = if i < fs.length then fs.getD i zeroF else if i = fs.length then f else zeroF := by
  unfold getF
  split_ifs with h1 h2
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · subst h2; simp [List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem fv_zero {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) : fv U vs zeroF = false := by
  simp [fv, zeroF, sv]

theorem inv_push {n : ℕ} (U : Finset (Fin n)) (W : List Bool) (s : St n) (f : Form n) (x : Bool)
    (hI : Inv U W s) (hf : RefsLt s.2.length f) (hx : x = fv U (rvals U s.2) f) :
    Inv U (W ++ [x]) ⟨s.1 ++ [f], s.2⟩ := by
  obtain ⟨hl, hr, hg, hv⟩ := hI
  refine ⟨by simp [hl], ?_, hg, ?_⟩
  · intro f' hf'
    rcases List.mem_append.1 hf' with h | h
    · exact hr f' h
    · simp at h; subst h; exact hf
  · intro i
    rw [getF_push]
    split_ifs with h1 h2
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      have := hv i
      unfold getF at this
      exact this
    · subst h2; rw [hl]; simp [List.getD_eq_getElem?_getD, hx]
    · rw [List.getD_eq_default _ _ (by simp; omega), fv_zero]

theorem inv_rec {n : ℕ} (U : Finset (Fin n)) (W : List Bool) (s : St n) (r : Rec n) (x : Bool)
    (hI : Inv U W s) (h1 : ∀ j ∈ r.2.1, j < s.2.length) (h2 : ∀ j ∈ r.2.2.2, j < s.2.length)
    (hx : x = (sv U (rvals U s.2) r.1 r.2.1 && sv U (rvals U s.2) r.2.2.1 r.2.2.2)) :
    Inv U (W ++ [x]) ⟨s.1 ++ [some (∅, {s.2.length})], s.2 ++ [r]⟩ := by
  obtain ⟨hl, hr, hg, hv⟩ := hI
  refine ⟨by simp [hl], ?_, ?_, ?_⟩
  · intro f' hf'
    simp only [List.length_append, List.length_cons, List.length_nil]
    rcases List.mem_append.1 hf' with h | h
    · intro p hp j hj; have := hr f' h p hp j hj; omega
    · simp at h; subst h; intro p hp j hj; simp at hp; subst hp; simp at hj; omega
  · intro k hk
    simp only [List.length_append, List.length_cons, List.length_nil] at hk
    by_cases hk' : k < s.2.length
    · rw [List.getElem_append_left hk']; exact hg k hk'
    · have : k = s.2.length := by omega
      subst this
      simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
      exact ⟨h1, h2⟩
  · intro i
    rw [getF_push]
    split_ifs with hi1 hi2
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      have := hv i
      unfold getF at this
      rw [this, fv_snoc U s.2 r]
      have := hr _ (List.getElem_mem (by omega : i < s.1.length))
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact this
    · subst hi2
      rw [hl]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.getD_some]
      have hlen : (rvals U s.2).length = s.2.length := rvals_len U s.2
      simp only [fv, sv, rvals_snoc, rvStep, Finset.mem_singleton, exists_eq_left]
      rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
      simp [hx, sv]
    · rw [List.getD_eq_default _ _ (by simp; omega), fv_zero]

def Ok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem step_inv {n : ℕ} (U : Finset (Fin n)) (W : List Bool) (s : St n) (g : Gate)
    (hI : Inv U W s) (hg : Ok g) : Inv U (Fw W g) (step s g) := by
  have hv := hI.2.2.2
  have hR : ∀ i, RefsLt s.2.length (getF s i) := refs_getF s.2.length s hI.2.1
  obtain ⟨hop, hlen⟩ := hg
  rcases g with ⟨op, ins⟩
  simp only at hop hlen
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · apply inv_push U W s none _ hI (by intro p hp; simp at hp)
      simp [GateOp.eval, fv]
    · apply inv_push U W s (getF s a) _ hI (hR a)
      have := hv a
      simp only [List.getD_eq_getElem?_getD] at this
      simp [Fw, GateOp.eval, this]
    · show Inv U (Fw W ⟨GateOp.and, [a, b]⟩) (andStep s (getF s a) (getF s b))
      have ea := hv a
      have eb := hv b
      rcases hfa : getF s a with _ | ⟨va, ga⟩ <;> rcases hfb : getF s b with _ | ⟨vb, gb⟩
      · apply inv_push U W s none _ hI (by intro p hp; simp at hp)
        rw [hfa] at ea; rw [hfb] at eb
        simp [Fw, GateOp.eval, fv] at ea eb ⊢; simp [ea, eb]
      · apply inv_push U W s (some (vb, gb)) _ hI (hfb ▸ hR b)
        rw [hfa] at ea; rw [hfb] at eb
        simp [GateOp.eval, fv] at ea eb ⊢; simp [ea, eb]
      · apply inv_push U W s (some (va, ga)) _ hI (hfa ▸ hR a)
        rw [hfa] at ea; rw [hfb] at eb
        simp [GateOp.eval, fv] at ea eb ⊢; simp [ea, eb]
      · have ha := hR a; rw [hfa] at ha
        have hb := hR b; rw [hfb] at hb
        apply inv_rec U W s (va, ga, vb, gb) _ hI (ha _ rfl) (hb _ rfl)
        rw [hfa] at ea; rw [hfb] at eb
        simp only [fv, List.getD_eq_getElem?_getD] at ea eb
        simp [Fw, GateOp.eval, ea, eb]
    · simp at hlen
  · apply inv_push U W s (orF (ins.map (getF s))) _ hI
      (refs_orF _ _ (fun f hf => by
        obtain ⟨i, _, rfl⟩ := List.mem_map.1 hf
        exact hR i))
    rw [fv_orF]
    simp only [GateOp.eval, List.any_map]
    congr 1
    funext i
    have := hv i
    simp only [List.getD_eq_getElem?_getD] at this
    simp [Function.comp, this]

theorem fold_inv {n : ℕ} (U : Finset (Fin n)) (gs : List Gate) (hgs : ∀ g ∈ gs, Ok g) :
    ∀ (W : List Bool) (s : St n), Inv U W s → Inv U (gs.foldl Fw W) (gs.foldl step s) := by
  induction gs with
  | nil => intro W s h; exact h
  | cons g gs ih =>
    intro W s h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (by simp [hg'])) _ _ (step_inv U W s g h (hgs g (by simp)))

def isAnd (g : Gate) : Bool := match g.op with
  | GateOp.and => true
  | _ => false

theorem isAnd_iff (g : Gate) : isAnd g = true ↔ g.op = GateOp.and := by
  unfold isAnd
  split <;> simp_all

theorem step_rs {n : ℕ} (s : St n) (g : Gate) :
    (step s g).2.length ≤ s.2.length + (if isAnd g = true then 1 else 0) := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp only [step, isAnd] <;> try simp
  rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp only [step]
  · simp
  · simp
  · unfold andStep
    split <;> simp

theorem fold_rs {n : ℕ} (gs : List Gate) :
    ∀ s : St n, (gs.foldl step s).2.length ≤ s.2.length + gs.countP isAnd := by
  induction gs with
  | nil => intro s; simp
  | cons g gs ih =>
    intro s
    simp only [List.foldl_cons, List.countP_cons]
    have h1 := ih (step s g)
    have h2 := step_rs s g
    split_ifs at h2 ⊢ <;> omega

theorem rvals_split {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (k : ℕ) :
    rvals U rs = (rs.drop k).foldl (rvStep U) (rvals U (rs.take k)) := by
  unfold rvals
  rw [← List.foldl_append, List.take_append_drop]

theorem rvals_take {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (k j : ℕ) (hj : j < k) (hk : k ≤ rs.length) :
    (rvals U rs).getD j false = (rvals U (rs.take k)).getD j false := by
  rw [rvals_split U rs k, rv_pre]
  rw [rvals_len, List.length_take]; omega

theorem rec_val {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (hg : GoodRecs rs) (k : ℕ) (hk : k < rs.length) :
    (rvals U rs).getD k false = (sv U (rvals U rs) rs[k].1 rs[k].2.1 && sv U (rvals U rs) rs[k].2.2.1 rs[k].2.2.2) := by
  rw [rvals_take U rs (k + 1) k (by omega) (by omega)]
  rw [List.take_succ_eq_append_getElem hk, rvals_snoc]
  have hl : (rvals U (rs.take k)).length = k := by rw [rvals_len, List.length_take]; omega
  simp only [rvStep]
  rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self]
  simp only [List.getD_cons_zero]
  obtain ⟨h1, h2⟩ := hg k hk
  congr 1
  · apply sv_congr; intro j hj; exact (rvals_take U rs k j (h1 j hj) (by omega)).symm
  · apply sv_congr; intro j hj; exact (rvals_take U rs k j (h2 j hj) (by omega)).symm

def toACC {n : ℕ} (rs : List (Rec n)) (V : Finset (Fin n)) (G : Finset ℕ) : PEqualNP.AndCount.AndCountCircuit n where
  size := rs.length
  leftVars i := rs[i].1
  leftGates i := Finset.univ.filter (fun j : Fin rs.length => j.val ∈ rs[i].2.1)
  rightVars i := rs[i].2.2.1
  rightGates i := Finset.univ.filter (fun j : Fin rs.length => j.val ∈ rs[i].2.2.2)
  outVars := V
  outGates := Finset.univ.filter (fun j : Fin rs.length => j.val ∈ G)

theorem side_eq {n : ℕ} (U : Finset (Fin n)) (m : ℕ) (B : Finset (Fin n)) (G : Finset ℕ) (i : Fin m)
    (val : Fin m → Bool) (vs : List Bool) (hG : ∀ j ∈ G, j < i.val)
    (hval : ∀ j : Fin m, j < i → val j = vs.getD j false) :
    PEqualNP.AndCount.AndCountCircuit.sideTrue U B (Finset.univ.filter (fun j : Fin m => j.val ∈ G)) i val
      = sv U vs B G := by
  unfold PEqualNP.AndCount.AndCountCircuit.sideTrue sv
  rw [Bool.decide_or]
  congr 2
  apply propext
  constructor
  · rintro ⟨j, hj, hji, hv⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact ⟨j.val, hj, by rw [← hval j hji]; exact hv⟩
  · rintro ⟨j, hj, hv⟩
    have hji := hG j hj
    refine ⟨⟨j, by omega⟩, by simp [hj], hji, ?_⟩
    rw [hval ⟨j, by omega⟩ hji]
    exact hv

theorem fuel {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (hg : GoodRecs rs) (V : Finset (Fin n)) (G : Finset ℕ) :
    ∀ d (i : Fin rs.length), i.val < d →
      (toACC rs V G).gateValFuel U d i = (rvals U rs).getD i false := by
  intro d
  induction d with
  | zero => intro i hi; omega
  | succ d ih =>
    intro i hi
    rw [rec_val U rs hg i i.isLt]
    obtain ⟨h1, h2⟩ := hg i i.isLt
    simp only [PEqualNP.AndCount.AndCountCircuit.gateValFuel]
    have hv : ∀ j : Fin rs.length, j < i → (toACC rs V G).gateValFuel U d j = (rvals U rs).getD j false :=
      fun j hj => ih j (by omega)
    congr 1
    · exact side_eq U rs.length _ _ i _ _ h1 hv
    · exact side_eq U rs.length _ _ i _ _ h2 hv

theorem eval_eq {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (hg : GoodRecs rs) (V : Finset (Fin n)) (G : Finset ℕ)
    (hG : ∀ j ∈ G, j < rs.length) : (toACC rs V G).eval U = sv U (rvals U rs) V G := by
  unfold PEqualNP.AndCount.AndCountCircuit.eval sv
  rw [Bool.decide_or]
  congr 2
  apply propext
  constructor
  · rintro ⟨j, hj, hv⟩
    have hj' : j.val ∈ G := (Finset.mem_filter.1 hj).2
    refine ⟨j.val, hj', ?_⟩
    exact (fuel U rs hg V G rs.length j j.isLt).symm.trans hv
  · rintro ⟨j, hj, hv⟩
    refine ⟨⟨j, hG j hj⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩, ?_⟩
    exact (fuel U rs hg V G rs.length ⟨j, hG j hj⟩ (hG j hj)).trans hv

theorem wf {n : ℕ} (rs : List (Rec n)) (hg : GoodRecs rs) (V : Finset (Fin n)) (G : Finset ℕ) :
    (toACC rs V G).WellFormed := by
  intro i
  obtain ⟨h1, h2⟩ := hg i i.isLt
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · exact h1 j (Finset.mem_filter.1 hj).2
  · exact h2 j (Finset.mem_filter.1 hj).2



theorem convert : ∀ (n : ℕ) (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∃ (x3 : Finset (Fin n)), (PEqualNP.MetaComplexity.circuitFun n x1 fun (x4 : Fin n) => Decidable.decide (x4 ∈ x3)) = Bool.false) → ∃ (x4 : PEqualNP.AndCount.AndCountCircuit n), x4.WellFormed ∧ x4.size ≤ Nat.card { x5 : Fin x1.gates.length // (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and } ∧ ∀ (x5 : Finset (Fin n)), x4.eval x5 = PEqualNP.MetaComplexity.circuitFun n x1 fun (x6 : Fin n) => Decidable.decide (x6 ∈ x5) := by
  intro n C hmono hex
  obtain ⟨U0, hU0⟩ := hex
  have hok : ∀ g ∈ C.gates, PEqualNP.Outside.L_meta_17707.AndConv.Ok g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hmono g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact ⟨h1, h2⟩
  let s0 : PEqualNP.Outside.L_meta_17707.AndConv.St n := ⟨List.ofFn (fun i : Fin n => some ({i}, ∅)), []⟩
  let s := C.gates.foldl PEqualNP.Outside.L_meta_17707.AndConv.step s0
  have hinit : ∀ U : Finset (Fin n), PEqualNP.Outside.L_meta_17707.AndConv.Inv U (List.ofFn fun x : Fin n => decide (x ∈ U)) s0 := by
    intro U
    refine ⟨by simp [s0], ?_, ?_, ?_⟩
    · intro f hf p hp j hj
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hf
      simp only [Option.some.injEq] at hp
      subst hp
      simp at hj
    · intro k hk; simp [s0] at hk
    · intro i
      by_cases hi : i < n
      · simp only [PEqualNP.Outside.L_meta_17707.AndConv.getF, s0]
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn,
          List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
        simp [PEqualNP.Outside.L_meta_17707.AndConv.fv, PEqualNP.Outside.L_meta_17707.AndConv.sv]
      · rw [List.getD_eq_default _ _ (by simp; omega)]
        simp only [PEqualNP.Outside.L_meta_17707.AndConv.getF, s0]
        rw [List.getD_eq_default _ _ (by simp; omega), PEqualNP.Outside.L_meta_17707.AndConv.fv_zero]
  have hinv : ∀ U : Finset (Fin n), PEqualNP.Outside.L_meta_17707.AndConv.Inv U (C.gates.foldl PEqualNP.Outside.L_meta_17707.AndConv.Fw (List.ofFn fun x : Fin n => decide (x ∈ U))) s :=
    fun U => PEqualNP.Outside.L_meta_17707.AndConv.fold_inv U C.gates hok _ _ (hinit U)
  have hfun : ∀ U : Finset (Fin n), PEqualNP.MetaComplexity.circuitFun n C (fun x => decide (x ∈ U))
      = PEqualNP.Outside.L_meta_17707.AndConv.fv U (PEqualNP.Outside.L_meta_17707.AndConv.rvals U s.2) (PEqualNP.Outside.L_meta_17707.AndConv.getF s C.output) := fun U => (hinv U).2.2.2 C.output
  rcases hfo : PEqualNP.Outside.L_meta_17707.AndConv.getF s C.output with _ | ⟨V, G⟩
  · have := hfun U0
    rw [hfo, hU0] at this
    simp [PEqualNP.Outside.L_meta_17707.AndConv.fv] at this
  · have hG : ∀ j ∈ G, j < s.2.length := PEqualNP.Outside.L_meta_17707.AndConv.refs_getF _ s (hinv U0).2.1 C.output _ hfo
    have hgood := (hinv U0).2.2.1
    refine ⟨PEqualNP.Outside.L_meta_17707.AndConv.toACC s.2 V G, PEqualNP.Outside.L_meta_17707.AndConv.wf s.2 hgood V G, ?_, ?_⟩
    · have h1 := PEqualNP.Outside.L_meta_17707.AndConv.fold_rs C.gates s0
      have h2 : C.gates.countP PEqualNP.Outside.L_meta_17707.AndConv.isAnd = Nat.card {x5 : Fin C.gates.length // (C.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and} := by
        classical
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        conv_lhs => rw [← List.ofFn_get C.gates]
        rw [List.countP_ofFn]
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, PEqualNP.Outside.L_meta_17707.AndConv.isAnd_iff]
      change s.2.length ≤ s0.2.length + _ at h1
      have h0 : s0.2.length = 0 := rfl
      show s.2.length ≤ _
      omega
    · intro U
      rw [PEqualNP.Outside.L_meta_17707.AndConv.eval_eq U s.2 hgood V G hG, hfun U, hfo]
      rfl

end AndConv
namespace AndRestrict

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

private lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (h : ∀ j, j < i → v1 j = v2 j) :
    sideTrue U B F i v1 = sideTrue U B F i v2 := by
  unfold sideTrue
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [← h j hji]⟩
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [h j hji]⟩

private lemma gateValFuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      ∀ (d1 d2 : ℕ), i.val < d1 → i.val < d2 →
        C.gateValFuel U d1 i = C.gateValFuel U d2 i := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi d1 d2 hd1 hd2
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d1 ≠ 0) with ⟨k1, rfl⟩
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d2 ≠ 0) with ⟨k2, rfl⟩
    simp only [gateValFuel]
    have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U k1 j = C.gateValFuel U k2 j := by
      intro j hji
      exact ih j (by omega) k1 k2 (by omega) (by omega)
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have heq : C.gateVal U i = C.gateValFuel U (i.val + 1) i :=
    gateValFuel_indep C U (C.size) i i.isLt C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)
  rw [heq]
  simp only [gateValFuel]
  have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U i.val j = C.gateVal U j := by
    intro j hji
    exact gateValFuel_indep C U C.size j j.isLt i.val C.size hji j.isLt
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma sideTrue_mono_U {n k : ℕ} {U V : Finset (Fin n)} (hUV : U ⊆ V)
    (B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (hv : ∀ j, j < i → v1 j = true → v2 j = true)
    (hs : sideTrue U B F i v1 = true) :
    sideTrue V B F i v2 = true := by
  unfold sideTrue at hs ⊢
  rw [decide_eq_true_eq] at hs ⊢
  rcases hs with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hvj⟩
  · exact Or.inl ⟨v, hvB, hUV hvU⟩
  · exact Or.inr ⟨j, hjF, hji, hv j hji hvj⟩

private lemma gateValFuel_mono_U {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)}
    (hUV : U ⊆ V) :
    ∀ (d : ℕ) (i : Fin C.size), C.gateValFuel U d i = true → C.gateValFuel V d i = true := by
  intro d
  induction d with
  | zero =>
    intro i hi
    simp [gateValFuel] at hi
  | succ d ih =>
    intro i hi
    simp only [gateValFuel, Bool.and_eq_true] at hi ⊢
    exact ⟨sideTrue_mono_U hUV _ _ _ _ _ (fun j _ hj => ih j hj) hi.1,
           sideTrue_mono_U hUV _ _ _ _ _ (fun j _ hj => ih j hj) hi.2⟩

private lemma eval_mono_U {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)}
    (hUV : U ⊆ V) (hU : C.eval U = true) : C.eval V = true := by
  unfold AndCountCircuit.eval at hU ⊢
  rw [decide_eq_true_eq] at hU ⊢
  rcases hU with ⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩
  · exact Or.inl ⟨v, hvO, hUV hvU⟩
  · exact Or.inr ⟨j, hjO, gateValFuel_mono_U C hUV C.size j hjv⟩

private def restrictCircuit {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size)) :
    AndCountCircuit n where
  size := K.card
  leftVars i := C.leftVars (K.orderEmbOfFin rfl i)
  leftGates i := Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.leftGates (K.orderEmbOfFin rfl i))
  rightVars i := C.rightVars (K.orderEmbOfFin rfl i)
  rightGates i := Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.rightGates (K.orderEmbOfFin rfl i))
  outVars := C.outVars
  outGates := Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.outGates)

private lemma restrict_mem_leftGates {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (i j : Fin K.card) :
    j ∈ (restrictCircuit C K).leftGates i ↔
      K.orderEmbOfFin rfl j ∈ C.leftGates (K.orderEmbOfFin rfl i) := by
  change j ∈ Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.leftGates (K.orderEmbOfFin rfl i)) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ j)

private lemma restrict_mem_rightGates {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (i j : Fin K.card) :
    j ∈ (restrictCircuit C K).rightGates i ↔
      K.orderEmbOfFin rfl j ∈ C.rightGates (K.orderEmbOfFin rfl i) := by
  change j ∈ Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.rightGates (K.orderEmbOfFin rfl i)) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ j)

private lemma restrict_mem_outGates {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (j : Fin K.card) :
    j ∈ (restrictCircuit C K).outGates ↔ K.orderEmbOfFin rfl j ∈ C.outGates := by
  change j ∈ Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.outGates) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ j)

private lemma restrict_wf {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (hWF : C.WellFormed) : (restrictCircuit C K).WellFormed := by
  intro i
  constructor
  · intro j hj
    have hj' := (restrict_mem_leftGates C K i j).mp hj
    exact (K.orderEmbOfFin rfl).lt_iff_lt.mp ((hWF (K.orderEmbOfFin rfl i)).1 _ hj')
  · intro j hj
    have hj' := (restrict_mem_rightGates C K i j).mp hj
    exact (K.orderEmbOfFin rfl).lt_iff_lt.mp ((hWF (K.orderEmbOfFin rfl i)).2 _ hj')

private lemma restrict_gateVal_le {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin K.card), i.val < m →
      (restrictCircuit C K).gateVal U i = true →
        C.gateVal U (K.orderEmbOfFin rfl i) = true := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi hval
    rw [gateVal_unfold (restrictCircuit C K) U i, Bool.and_eq_true] at hval
    rw [gateVal_unfold C U, Bool.and_eq_true]
    constructor
    · have hL := hval.1
      unfold sideTrue at hL ⊢
      rw [decide_eq_true_eq] at hL ⊢
      rcases hL with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · exact Or.inl ⟨v, hvB, hvU⟩
      · have hjF' := (restrict_mem_leftGates C K i j).mp hjF
        exact Or.inr ⟨K.orderEmbOfFin rfl j, hjF',
          (K.orderEmbOfFin rfl).lt_iff_lt.mpr hji, ih j (by omega) hjv⟩
    · have hR := hval.2
      unfold sideTrue at hR ⊢
      rw [decide_eq_true_eq] at hR ⊢
      rcases hR with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · exact Or.inl ⟨v, hvB, hvU⟩
      · have hjF' := (restrict_mem_rightGates C K i j).mp hjF
        exact Or.inr ⟨K.orderEmbOfFin rfl j, hjF',
          (K.orderEmbOfFin rfl).lt_iff_lt.mpr hji, ih j (by omega) hjv⟩

private lemma restrict_eval_le {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (U : Finset (Fin n)) (h : (restrictCircuit C K).eval U = true) : C.eval U = true := by
  unfold AndCountCircuit.eval at h ⊢
  rw [decide_eq_true_eq] at h ⊢
  rcases h with ⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩
  · exact Or.inl ⟨v, hvO, hvU⟩
  · have hjO' := (restrict_mem_outGates C K j).mp hjO
    exact Or.inr ⟨K.orderEmbOfFin rfl j, hjO', restrict_gateVal_le C K U _ j j.isLt hjv⟩

private lemma restrict_gateVal_ge {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (U : Finset (Fin n)) (hK : ∀ j : Fin C.size, j ∉ K → C.gateVal U j = false) :
    ∀ (m : ℕ) (i : Fin K.card), i.val < m →
      C.gateVal U (K.orderEmbOfFin rfl i) = true →
        (restrictCircuit C K).gateVal U i = true := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi hval
    rw [gateVal_unfold C U, Bool.and_eq_true] at hval
    rw [gateVal_unfold (restrictCircuit C K) U i, Bool.and_eq_true]
    constructor
    · have hL := hval.1
      unfold sideTrue at hL ⊢
      rw [decide_eq_true_eq] at hL ⊢
      rcases hL with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · exact Or.inl ⟨v, hvB, hvU⟩
      · have hjK : j ∈ K := by
          by_contra hnot
          have hf := hK j hnot
          rw [hf] at hjv
          exact Bool.false_ne_true hjv
        have hjr : j ∈ Set.range (K.orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]
          exact hjK
        obtain ⟨j', hj'⟩ := hjr
        have hj'lt : j' < i := (K.orderEmbOfFin rfl).lt_iff_lt.mp (by rw [hj']; exact hji)
        refine Or.inr ⟨j', (restrict_mem_leftGates C K i j').mpr (by rw [hj']; exact hjF),
          hj'lt, ih j' (by omega) (by rw [hj']; exact hjv)⟩
    · have hR := hval.2
      unfold sideTrue at hR ⊢
      rw [decide_eq_true_eq] at hR ⊢
      rcases hR with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · exact Or.inl ⟨v, hvB, hvU⟩
      · have hjK : j ∈ K := by
          by_contra hnot
          have hf := hK j hnot
          rw [hf] at hjv
          exact Bool.false_ne_true hjv
        have hjr : j ∈ Set.range (K.orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]
          exact hjK
        obtain ⟨j', hj'⟩ := hjr
        have hj'lt : j' < i := (K.orderEmbOfFin rfl).lt_iff_lt.mp (by rw [hj']; exact hji)
        refine Or.inr ⟨j', (restrict_mem_rightGates C K i j').mpr (by rw [hj']; exact hjF),
          hj'lt, ih j' (by omega) (by rw [hj']; exact hjv)⟩

private lemma restrict_eval_ge {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (U : Finset (Fin n)) (hK : ∀ j : Fin C.size, j ∉ K → C.gateVal U j = false)
    (h : C.eval U = true) : (restrictCircuit C K).eval U = true := by
  unfold AndCountCircuit.eval at h ⊢
  rw [decide_eq_true_eq] at h ⊢
  rcases h with ⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩
  · exact Or.inl ⟨v, hvO, hvU⟩
  · have hjK : j ∈ K := by
      by_contra hnot
      have hf := hK j hnot
      rw [hf] at hjv
      exact Bool.false_ne_true hjv
    have hjr : j ∈ Set.range (K.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hjK
    obtain ⟨j', hj'⟩ := hjr
    refine Or.inr ⟨j', (restrict_mem_outGates C K j').mpr (by rw [hj']; exact hjO),
      restrict_gateVal_ge C K U hK _ j' j'.isLt (by rw [hj']; exact hjv)⟩


theorem bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem sub_left {n : ℕ} (X U : Finset (Fin n)) : X ⊆ X ∪ U :=
  fun _ hx => Finset.mem_union_left U hx

theorem sub_ins {n : ℕ} (X : Finset (Fin n)) {U : Finset (Fin n)} {v : Fin n} (hv : v ∈ U) :
    X ∪ {v} ⊆ X ∪ U := by
  intro x hx
  rcases Finset.mem_union.mp hx with h | h
  · exact Finset.mem_union_left _ h
  · rw [Finset.mem_singleton.mp h]
    exact Finset.mem_union_right _ hv

theorem gateVal_mono {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)} (h : U ⊆ V)
    (i : Fin C.size) (hi : C.gateVal U i = true) : C.gateVal V i = true :=
  gateValFuel_mono_U C h C.size i hi

theorem side_mono {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)} (h : U ⊆ V)
    (B : Finset (Fin n)) (F : Finset (Fin C.size)) (i : Fin C.size)
    (hs : sideTrue U B F i (C.gateVal U) = true) : sideTrue V B F i (C.gateVal V) = true :=
  sideTrue_mono_U h B F i _ _ (fun j _ hj => gateVal_mono C h j hj) hs

theorem sideTrue_iff {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (val : Fin k → Bool) :
    sideTrue U B F i val = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, j < i ∧ val j = true) := by
  unfold sideTrue
  exact decide_eq_true_iff

theorem eval_iff {n : ℕ} (D : AndCountCircuit n) (U : Finset (Fin n)) :
    D.eval U = true ↔ ((∃ v ∈ D.outVars, v ∈ U) ∨ ∃ j ∈ D.outGates, D.gateVal U j = true) := by
  unfold AndCountCircuit.eval
  exact decide_eq_true_iff

def keep {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) : Finset (Fin C.size) :=
  Finset.univ.filter (fun i => sideTrue X (C.leftVars i) (C.leftGates i) i (C.gateVal X) = false ∧
    sideTrue X (C.rightVars i) (C.rightGates i) i (C.gateVal X) = false)

theorem mem_keep {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (i : Fin C.size) :
    i ∈ keep C X ↔ (sideTrue X (C.leftVars i) (C.leftGates i) i (C.gateVal X) = false ∧
      sideTrue X (C.rightVars i) (C.rightGates i) i (C.gateVal X) = false) := by
  unfold keep
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ i)

theorem chain_step {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (j : Fin C.size)
    (B : Finset (Fin n)) (F : Finset (Fin C.size))
    (hB : sideTrue X B F j (C.gateVal X) = false)
    (hgj : ∀ U : Finset (Fin n), C.gateVal (X ∪ U) j = sideTrue (X ∪ U) B F j (C.gateVal (X ∪ U)))
    (ih : ∀ j' : Fin C.size, j' < j → C.gateVal X j' = false → ∀ U : Finset (Fin n),
       C.gateVal (X ∪ U) j' = true →
       (∃ v ∈ U, v ∉ X ∧ C.gateVal (X ∪ {v}) j' = true) ∨
       ∃ k ∈ keep C X, k ≤ j' ∧ C.gateVal (X ∪ U) k = true ∧
         ∀ U' : Finset (Fin n), C.gateVal (X ∪ U') k = true → C.gateVal (X ∪ U') j' = true)
    (U : Finset (Fin n)) (hU : C.gateVal (X ∪ U) j = true) :
    (∃ v ∈ U, v ∉ X ∧ C.gateVal (X ∪ {v}) j = true) ∨
       ∃ k ∈ keep C X, k ≤ j ∧ C.gateVal (X ∪ U) k = true ∧
         ∀ U' : Finset (Fin n), C.gateVal (X ∪ U') k = true → C.gateVal (X ∪ U') j = true := by
  have hB' : ¬ ((∃ v ∈ B, v ∈ X) ∨ ∃ j' ∈ F, j' < j ∧ C.gateVal X j' = true) := by
    intro h
    have h2 := (sideTrue_iff X B F j (C.gateVal X)).mpr h
    rw [hB] at h2
    exact Bool.false_ne_true h2
  rw [hgj, sideTrue_iff] at hU
  rcases hU with ⟨v, hvB, hvXU⟩ | ⟨j', hj'F, hj'j, hj'v⟩
  · have hvX : v ∉ X := fun h => hB' (Or.inl ⟨v, hvB, h⟩)
    have hvU : v ∈ U := (Finset.mem_union.mp hvXU).resolve_left hvX
    left
    refine ⟨v, hvU, hvX, ?_⟩
    rw [hgj, sideTrue_iff]
    exact Or.inl ⟨v, hvB, Finset.mem_union_right _ (Finset.mem_singleton_self v)⟩
  · have hj'X : C.gateVal X j' = false := by
      cases h : C.gateVal X j'
      · rfl
      · exact absurd (Or.inr ⟨j', hj'F, hj'j, h⟩) hB'
    rcases ih j' hj'j hj'X U hj'v with ⟨v, hvU, hvX, hv⟩ | ⟨k, hkK, hkj', hkU, hkimp⟩
    · left
      refine ⟨v, hvU, hvX, ?_⟩
      rw [hgj, sideTrue_iff]
      exact Or.inr ⟨j', hj'F, hj'j, hv⟩
    · right
      refine ⟨k, hkK, le_trans hkj' (le_of_lt hj'j), hkU, fun U' hU' => ?_⟩
      rw [hgj, sideTrue_iff]
      exact Or.inr ⟨j', hj'F, hj'j, hkimp U' hU'⟩

theorem chain {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) :
    ∀ (m : ℕ) (j : Fin C.size), j.val < m → C.gateVal X j = false → ∀ U : Finset (Fin n),
       C.gateVal (X ∪ U) j = true →
       (∃ v ∈ U, v ∉ X ∧ C.gateVal (X ∪ {v}) j = true) ∨
       ∃ k ∈ keep C X, k ≤ j ∧ C.gateVal (X ∪ U) k = true ∧
         ∀ U' : Finset (Fin n), C.gateVal (X ∪ U') k = true → C.gateVal (X ∪ U') j = true := by
  intro m
  induction m with
  | zero =>
    intro j hj
    exact absurd hj (Nat.not_lt_zero _)
  | succ m ih =>
    intro j hjm hjX U hU
    have ih' := fun (j' : Fin C.size) (hj' : j' < j) =>
      ih j' (lt_of_lt_of_le (Fin.lt_def.mp hj') (Nat.lt_succ_iff.mp hjm))
    by_cases hjK : j ∈ keep C X
    · right
      exact ⟨j, hjK, le_refl j, hU, fun _ h => h⟩
    · rw [mem_keep] at hjK
      have hg := gateVal_unfold C X j
      rw [hjX] at hg
      rcases Bool.eq_false_or_eq_true
          (sideTrue X (C.leftVars j) (C.leftGates j) j (C.gateVal X)) with hL | hL
      · have hR : sideTrue X (C.rightVars j) (C.rightGates j) j (C.gateVal X) = false := by
          rw [hL, Bool.true_and] at hg
          exact hg.symm
        refine chain_step C X j (C.rightVars j) (C.rightGates j) hR ?_ ih' U hU
        intro U'
        rw [gateVal_unfold C (X ∪ U') j, side_mono C (sub_left X U') _ _ j hL, Bool.true_and]
      · rcases Bool.eq_false_or_eq_true
            (sideTrue X (C.rightVars j) (C.rightGates j) j (C.gateVal X)) with hR | hR
        · refine chain_step C X j (C.leftVars j) (C.leftGates j) hL ?_ ih' U hU
          intro U'
          rw [gateVal_unfold C (X ∪ U') j, side_mono C (sub_left X U') _ _ j hR, Bool.and_true]
        · exact absurd ⟨hL, hR⟩ hjK

def eVars {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (B : Finset (Fin n))
    (F : Finset (Fin C.size)) (i : Fin C.size) : Finset (Fin n) :=
  Finset.univ.filter (fun v => i ∈ keep C X ∧ v ∉ X ∧
    sideTrue (X ∪ {v}) B F i (C.gateVal (X ∪ {v})) = true)

def eGates {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (B : Finset (Fin n))
    (F : Finset (Fin C.size)) (i : Fin C.size) : Finset (Fin C.size) :=
  Finset.univ.filter (fun k => i ∈ keep C X ∧ k ∈ keep C X ∧ k < i ∧
    ∀ U' : Finset (Fin n), C.gateVal (X ∪ U') k = true →
      sideTrue (X ∪ U') B F i (C.gateVal (X ∪ U')) = true)

theorem mem_eVars {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (B : Finset (Fin n))
    (F : Finset (Fin C.size)) (i : Fin C.size) (v : Fin n) :
    v ∈ eVars C X B F i ↔ (i ∈ keep C X ∧ v ∉ X ∧
      sideTrue (X ∪ {v}) B F i (C.gateVal (X ∪ {v})) = true) := by
  unfold eVars
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ v)

theorem mem_eGates {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (B : Finset (Fin n))
    (F : Finset (Fin C.size)) (i k : Fin C.size) :
    k ∈ eGates C X B F i ↔ (i ∈ keep C X ∧ k ∈ keep C X ∧ k < i ∧
      ∀ U' : Finset (Fin n), C.gateVal (X ∪ U') k = true →
        sideTrue (X ∪ U') B F i (C.gateVal (X ∪ U')) = true) := by
  unfold eGates
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ k)

def build {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) : AndCountCircuit n where
  size := C.size
  leftVars i := eVars C X (C.leftVars i) (C.leftGates i) i
  leftGates i := eGates C X (C.leftVars i) (C.leftGates i) i
  rightVars i := eVars C X (C.rightVars i) (C.rightGates i) i
  rightGates i := eGates C X (C.rightVars i) (C.rightGates i) i
  outVars := Finset.univ.filter (fun v => v ∉ X ∧ C.eval (X ∪ {v}) = true)
  outGates := Finset.univ.filter (fun k => k ∈ keep C X ∧
    ∀ U' : Finset (Fin n), C.gateVal (X ∪ U') k = true → C.eval (X ∪ U') = true)

theorem mem_outV {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (v : Fin n) :
    v ∈ (build C X).outVars ↔ (v ∉ X ∧ C.eval (X ∪ {v}) = true) := by
  show v ∈ Finset.univ.filter (fun v => v ∉ X ∧ C.eval (X ∪ {v}) = true) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ v)

theorem mem_outG {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (k : Fin C.size) :
    k ∈ (build C X).outGates ↔ (k ∈ keep C X ∧
      ∀ U' : Finset (Fin n), C.gateVal (X ∪ U') k = true → C.eval (X ∪ U') = true) := by
  show k ∈ Finset.univ.filter (fun k => k ∈ keep C X ∧
    ∀ U' : Finset (Fin n), C.gateVal (X ∪ U') k = true → C.eval (X ∪ U') = true) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ k)

theorem build_unfold {n : ℕ} (C : AndCountCircuit n) (X U : Finset (Fin n)) (i : Fin C.size) :
    (build C X).gateVal U i =
      (sideTrue U (eVars C X (C.leftVars i) (C.leftGates i) i)
          (eGates C X (C.leftVars i) (C.leftGates i) i) i ((build C X).gateVal U) &&
        sideTrue U (eVars C X (C.rightVars i) (C.rightGates i) i)
          (eGates C X (C.rightVars i) (C.rightGates i) i) i ((build C X).gateVal U)) :=
  gateVal_unfold (build C X) U i

theorem side_eq {n : ℕ} (C : AndCountCircuit n) (X U : Finset (Fin n)) (B : Finset (Fin n))
    (F : Finset (Fin C.size)) (i : Fin C.size)
    (hiK : i ∈ keep C X) (hB : sideTrue X B F i (C.gateVal X) = false)
    (val : Fin C.size → Bool)
    (hval : ∀ k : Fin C.size, k < i → (val k = true ↔ k ∈ keep C X ∧ C.gateVal (X ∪ U) k = true)) :
    sideTrue U (eVars C X B F i) (eGates C X B F i) i val =
      sideTrue (X ∪ U) B F i (C.gateVal (X ∪ U)) := by
  have hB' : ¬ ((∃ v ∈ B, v ∈ X) ∨ ∃ j' ∈ F, j' < i ∧ C.gateVal X j' = true) := by
    intro h
    have h2 := (sideTrue_iff X B F i (C.gateVal X)).mpr h
    rw [hB] at h2
    exact Bool.false_ne_true h2
  apply bool_ext
  rw [sideTrue_iff, sideTrue_iff]
  constructor
  · rintro (⟨v, hv, hvU⟩ | ⟨k, hk, hki, hkv⟩)
    · rw [mem_eVars] at hv
      exact (sideTrue_iff _ _ _ _ _).mp (side_mono C (sub_ins X hvU) B F i hv.2.2)
    · rw [mem_eGates] at hk
      have h2 := (hval k hki).mp hkv
      exact (sideTrue_iff _ _ _ _ _).mp (hk.2.2.2 U h2.2)
  · rintro (⟨v, hvB, hvXU⟩ | ⟨j, hjF, hji, hjv⟩)
    · have hvX : v ∉ X := fun h => hB' (Or.inl ⟨v, hvB, h⟩)
      have hvU : v ∈ U := (Finset.mem_union.mp hvXU).resolve_left hvX
      left
      refine ⟨v, (mem_eVars C X B F i v).mpr ⟨hiK, hvX, ?_⟩, hvU⟩
      rw [sideTrue_iff]
      exact Or.inl ⟨v, hvB, Finset.mem_union_right _ (Finset.mem_singleton_self v)⟩
    · have hjX : C.gateVal X j = false := by
        cases h : C.gateVal X j
        · rfl
        · exact absurd (Or.inr ⟨j, hjF, hji, h⟩) hB'
      rcases chain C X C.size j j.isLt hjX U hjv with ⟨v, hvU, hvX, hv⟩ | ⟨k, hkK, hkj, hkU, hkimp⟩
      · left
        refine ⟨v, (mem_eVars C X B F i v).mpr ⟨hiK, hvX, ?_⟩, hvU⟩
        rw [sideTrue_iff]
        exact Or.inr ⟨j, hjF, hji, hv⟩
      · right
        have hki : k < i := lt_of_le_of_lt hkj hji
        refine ⟨k, (mem_eGates C X B F i k).mpr ⟨hiK, hkK, hki, fun U' hU' => ?_⟩, hki,
          (hval k hki).mpr ⟨hkK, hkU⟩⟩
        rw [sideTrue_iff]
        exact Or.inr ⟨j, hjF, hji, hkimp U' hU'⟩

theorem build_gateVal {n : ℕ} (C : AndCountCircuit n) (X U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      ((build C X).gateVal U i = true ↔ (i ∈ keep C X ∧ C.gateVal (X ∪ U) i = true)) := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    have hval : ∀ k : Fin C.size, k < i →
        ((build C X).gateVal U k = true ↔ (k ∈ keep C X ∧ C.gateVal (X ∪ U) k = true)) :=
      fun k hk => ih k (lt_of_lt_of_le (Fin.lt_def.mp hk) (Nat.lt_succ_iff.mp hi))
    rw [build_unfold C X U i]
    by_cases hiK : i ∈ keep C X
    · have hK' := (mem_keep C X i).mp hiK
      rw [side_eq C X U _ _ i hiK hK'.1 _ hval, side_eq C X U _ _ i hiK hK'.2 _ hval,
        ← gateVal_unfold C (X ∪ U) i]
      exact ⟨fun h => ⟨hiK, h⟩, fun h => h.2⟩
    · have hfalse : ∀ (B : Finset (Fin n)) (F : Finset (Fin C.size)),
          sideTrue U (eVars C X B F i) (eGates C X B F i) i ((build C X).gateVal U) = false := by
        intro B F
        cases h : sideTrue U (eVars C X B F i) (eGates C X B F i) i ((build C X).gateVal U)
        · rfl
        · exfalso
          have h' := (sideTrue_iff _ _ _ _ _).mp h
          rcases h' with ⟨v, hv, _⟩ | ⟨k, hk, _, _⟩
          · exact hiK ((mem_eVars C X B F i v).mp hv).1
          · exact hiK ((mem_eGates C X B F i k).mp hk).1
      rw [hfalse, Bool.false_and]
      exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h.1 hiK⟩

theorem build_eval {n : ℕ} (C : AndCountCircuit n) (X U : Finset (Fin n))
    (hX : C.eval X = false) : (build C X).eval U = C.eval (X ∪ U) := by
  have hX' : ¬ ((∃ v ∈ C.outVars, v ∈ X) ∨ ∃ j ∈ C.outGates, C.gateVal X j = true) := by
    intro h
    have h2 := (eval_iff C X).mpr h
    rw [hX] at h2
    exact Bool.false_ne_true h2
  apply bool_ext
  rw [eval_iff, eval_iff]
  constructor
  · rintro (⟨v, hv, hvU⟩ | ⟨k, hk, hkv⟩)
    · rw [mem_outV] at hv
      exact (eval_iff C _).mp (eval_mono_U C (sub_ins X hvU) hv.2)
    · have hk' := (mem_outG C X k).mp hk
      have h2 := (build_gateVal C X U C.size k k.isLt).mp hkv
      exact (eval_iff C _).mp (hk'.2 U h2.2)
  · rintro (⟨v, hvO, hvXU⟩ | ⟨j, hjO, hjv⟩)
    · have hvX : v ∉ X := fun h => hX' (Or.inl ⟨v, hvO, h⟩)
      have hvU : v ∈ U := (Finset.mem_union.mp hvXU).resolve_left hvX
      left
      refine ⟨v, (mem_outV C X v).mpr ⟨hvX, ?_⟩, hvU⟩
      rw [eval_iff]
      exact Or.inl ⟨v, hvO, Finset.mem_union_right _ (Finset.mem_singleton_self v)⟩
    · have hjX : C.gateVal X j = false := by
        cases h : C.gateVal X j
        · rfl
        · exact absurd (Or.inr ⟨j, hjO, h⟩) hX'
      rcases chain C X C.size j j.isLt hjX U hjv with ⟨v, hvU, hvX, hv⟩ | ⟨k, hkK, _, hkU, hkimp⟩
      · left
        refine ⟨v, (mem_outV C X v).mpr ⟨hvX, ?_⟩, hvU⟩
        rw [eval_iff]
        exact Or.inr ⟨j, hjO, hv⟩
      · right
        refine ⟨k, (mem_outG C X k).mpr ⟨hkK, fun U' hU' => ?_⟩,
          (build_gateVal C X U C.size k k.isLt).mpr ⟨hkK, hkU⟩⟩
        rw [eval_iff]
        exact Or.inr ⟨j, hjO, hkimp U' hU'⟩

theorem build_wf {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) : (build C X).WellFormed := by
  intro i
  constructor
  · intro j hj
    exact ((mem_eGates C X _ _ i j).mp hj).2.2.1
  · intro j hj
    exact ((mem_eGates C X _ _ i j).mp hj).2.2.1

theorem main (n : ℕ) (C : AndCountCircuit n) (X : Finset (Fin n)) (hX : C.eval X = false) :
    ∃ D : AndCountCircuit n, D.WellFormed ∧
      D.size + {x6 : Fin C.size | ∃ x7 ∈ X, x7 ∈ C.leftVars x6 ∨ x7 ∈ C.rightVars x6}.ncard
        ≤ C.size ∧
      ∀ U : Finset (Fin n), D.eval U = C.eval (X ∪ U) := by
  let K : Finset (Fin (build C X).size) := keep C X
  have hK : ∀ U : Finset (Fin n), ∀ j : Fin (build C X).size, j ∉ K →
      (build C X).gateVal U j = false := by
    intro U j hj
    cases h : (build C X).gateVal U j
    · rfl
    · exact absurd ((build_gateVal C X U C.size j j.isLt).mp h).1 hj
  refine ⟨restrictCircuit (build C X) K, restrict_wf (build C X) K (build_wf C X), ?_, ?_⟩
  · change (keep C X).card + _ ≤ C.size
    have hsub : {x6 : Fin C.size | ∃ x7 ∈ X, x7 ∈ C.leftVars x6 ∨ x7 ∈ C.rightVars x6} ⊆
        ((Finset.univ \ keep C X : Finset (Fin C.size)) : Set (Fin C.size)) := by
      intro i hi
      obtain ⟨x7, hx7X, hx7⟩ := hi
      rw [Finset.mem_coe, Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, fun hiK => ?_⟩
      have hK' := (mem_keep C X i).mp hiK
      rcases hx7 with h | h
      · have h2 : sideTrue X (C.leftVars i) (C.leftGates i) i (C.gateVal X) = true := by
          rw [sideTrue_iff]
          exact Or.inl ⟨x7, h, hx7X⟩
        rw [hK'.1] at h2
        exact Bool.false_ne_true h2
      · have h2 : sideTrue X (C.rightVars i) (C.rightGates i) i (C.gateVal X) = true := by
          rw [sideTrue_iff]
          exact Or.inl ⟨x7, h, hx7X⟩
        rw [hK'.2] at h2
        exact Bool.false_ne_true h2
    have hle := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at hle
    have hcard : (Finset.univ \ keep C X).card + (keep C X).card = C.size := by
      rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin]
    omega
  · intro U
    apply bool_ext
    constructor
    · intro h
      rw [← build_eval C X U hX]
      exact restrict_eval_le (build C X) K U h
    · intro h
      rw [← build_eval C X U hX] at h
      exact restrict_eval_ge (build C X) K U (hK U) h



theorem restrict_true : ∀ (x1 : ℕ) (x2 : PEqualNP.AndCount.AndCountCircuit x1) (x3 : Finset (Fin x1)), x2.eval x3 = Bool.false → ∃ (x5 : PEqualNP.AndCount.AndCountCircuit x1), x5.WellFormed ∧ x5.size + {x6 : Fin x2.size | ∃ x7 ∈ x3, x7 ∈ x2.leftVars x6 ∨ x7 ∈ x2.rightVars x6}.ncard ≤ x2.size ∧ ∀ (x6 : Finset (Fin x1)), x5.eval x6 = x2.eval (x3 ∪ x6) := by
  intro x1 x2 x3 h
  exact PEqualNP.Outside.L_meta_17707.AndRestrict.main x1 x2 x3 h

end AndRestrict
namespace AndNorm

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

private lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (h : ∀ j, j < i → v1 j = v2 j) :
    sideTrue U B F i v1 = sideTrue U B F i v2 := by
  unfold sideTrue
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [← h j hji]⟩
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [h j hji]⟩

private lemma gateValFuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      ∀ (d1 d2 : ℕ), i.val < d1 → i.val < d2 →
        C.gateValFuel U d1 i = C.gateValFuel U d2 i := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi d1 d2 hd1 hd2
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d1 ≠ 0) with ⟨k1, rfl⟩
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d2 ≠ 0) with ⟨k2, rfl⟩
    simp only [gateValFuel]
    have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U k1 j = C.gateValFuel U k2 j := by
      intro j hji
      exact ih j (by omega) k1 k2 (by omega) (by omega)
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have heq : C.gateVal U i = C.gateValFuel U (i.val + 1) i :=
    gateValFuel_indep C U C.size i i.isLt C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)
  rw [heq]
  simp only [gateValFuel]
  have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U i.val j = C.gateVal U j := by
    intro j hji
    exact gateValFuel_indep C U C.size j j.isLt i.val C.size hji j.isLt
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma sideTrue_mono_U {n k : ℕ} {U V : Finset (Fin n)} (hUV : U ⊆ V)
    (B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (hv : ∀ j, j < i → v1 j = true → v2 j = true)
    (hs : sideTrue U B F i v1 = true) :
    sideTrue V B F i v2 = true := by
  unfold sideTrue at hs ⊢
  rw [decide_eq_true_eq] at hs ⊢
  rcases hs with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hvj⟩
  · exact Or.inl ⟨v, hvB, hUV hvU⟩
  · exact Or.inr ⟨j, hjF, hji, hv j hji hvj⟩

private lemma gateValFuel_mono_U {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)}
    (hUV : U ⊆ V) :
    ∀ (d : ℕ) (i : Fin C.size), C.gateValFuel U d i = true → C.gateValFuel V d i = true := by
  intro d
  induction d with
  | zero =>
    intro i hi
    simp [gateValFuel] at hi
  | succ d ih =>
    intro i hi
    simp only [gateValFuel, Bool.and_eq_true] at hi ⊢
    exact ⟨sideTrue_mono_U hUV _ _ _ _ _ (fun j _ hj => ih j hj) hi.1,
           sideTrue_mono_U hUV _ _ _ _ _ (fun j _ hj => ih j hj) hi.2⟩

private lemma gateVal_mono_U {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)}
    (hUV : U ⊆ V) (i : Fin C.size) (h : C.gateVal U i = true) : C.gateVal V i = true :=
  gateValFuel_mono_U C hUV C.size i h

private def singSet {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) : Finset (Fin n) :=
  Finset.univ.filter (fun v => C.gateVal {v} i = true)

private lemma mem_singSet {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ singSet C i ↔ C.gateVal {v} i = true := by
  unfold singSet
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ v)

private def stripCircuit {n : ℕ} (C : AndCountCircuit n) : AndCountCircuit n where
  size := C.size
  leftVars i := (C.leftVars i ∪ ((C.leftGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i
  leftGates := C.leftGates
  rightVars i := (C.rightVars i ∪ ((C.rightGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i
  rightGates := C.rightGates
  outVars := C.outVars ∪ C.outGates.biUnion (singSet C)
  outGates := C.outGates

private lemma mem_strip_leftVars {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ (stripCircuit C).leftVars i ↔
      (v ∈ C.leftVars i ∨ ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal {v} j = true) ∧
      C.gateVal {v} i ≠ true := by
  change v ∈ (C.leftVars i ∪ ((C.leftGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i ↔ _
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
    mem_singSet, and_assoc]

private lemma mem_strip_rightVars {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ (stripCircuit C).rightVars i ↔
      (v ∈ C.rightVars i ∨ ∃ j ∈ C.rightGates i, j < i ∧ C.gateVal {v} j = true) ∧
      C.gateVal {v} i ≠ true := by
  change v ∈ (C.rightVars i ∪ ((C.rightGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i ↔ _
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
    mem_singSet, and_assoc]

private lemma mem_strip_outVars {n : ℕ} (C : AndCountCircuit n) (v : Fin n) :
    v ∈ (stripCircuit C).outVars ↔
      v ∈ C.outVars ∨ ∃ j ∈ C.outGates, C.gateVal {v} j = true := by
  change v ∈ C.outVars ∪ C.outGates.biUnion (singSet C) ↔ _
  simp only [Finset.mem_union, Finset.mem_biUnion, mem_singSet]

private lemma strip_singleton_false {n : ℕ} (C : AndCountCircuit n) (v : Fin n) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m → (stripCircuit C).gateVal {v} i = false := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    cases h : (stripCircuit C).gateVal {v} i
    · rfl
    · exfalso
      rw [gateVal_unfold (stripCircuit C) {v} i, Bool.and_eq_true] at h
      have hL := h.1
      have hR := h.2
      unfold sideTrue at hL hR
      rw [decide_eq_true_eq] at hL hR
      have hvL : v ∈ (stripCircuit C).leftVars i := by
        rcases hL with ⟨w, hwB, hwv⟩ | ⟨j, _, hji, hjv⟩
        · rw [Finset.mem_singleton] at hwv
          rwa [← hwv]
        · rw [ih j (by omega)] at hjv
          exact absurd hjv Bool.false_ne_true
      have hvR : v ∈ (stripCircuit C).rightVars i := by
        rcases hR with ⟨w, hwB, hwv⟩ | ⟨j, _, hji, hjv⟩
        · rw [Finset.mem_singleton] at hwv
          rwa [← hwv]
        · rw [ih j (by omega)] at hjv
          exact absurd hjv Bool.false_ne_true
      rw [mem_strip_leftVars] at hvL
      rw [mem_strip_rightVars] at hvR
      apply hvL.2
      rw [gateVal_unfold C {v} i, Bool.and_eq_true]
      constructor
      · unfold sideTrue
        rw [decide_eq_true_eq]
        rcases hvL.1 with hvB | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvB, Finset.mem_singleton_self v⟩
        · exact Or.inr ⟨j, hjF, hji, hjv⟩
      · unfold sideTrue
        rw [decide_eq_true_eq]
        rcases hvR.1 with hvB | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvB, Finset.mem_singleton_self v⟩
        · exact Or.inr ⟨j, hjF, hji, hjv⟩

private lemma strip_disjoint {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) :
    Disjoint ((stripCircuit C).leftVars i) ((stripCircuit C).rightVars i) := by
  rw [Finset.disjoint_left]
  intro v hvL hvR
  have hf := strip_singleton_false C v C.size i i.isLt
  have ht : (stripCircuit C).gateVal {v} i = true := by
    rw [gateVal_unfold (stripCircuit C) {v} i, Bool.and_eq_true]
    constructor
    · unfold sideTrue
      rw [decide_eq_true_eq]
      exact Or.inl ⟨v, hvL, Finset.mem_singleton_self v⟩
    · unfold sideTrue
      rw [decide_eq_true_eq]
      exact Or.inl ⟨v, hvR, Finset.mem_singleton_self v⟩
  rw [hf] at ht
  exact Bool.false_ne_true ht

private lemma strip_gateVal_le {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      (stripCircuit C).gateVal U i = true → C.gateVal U i = true := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi hval
    rw [gateVal_unfold (stripCircuit C) U i, Bool.and_eq_true] at hval
    rw [gateVal_unfold C U i, Bool.and_eq_true]
    constructor
    · have hL := hval.1
      unfold sideTrue at hL ⊢
      rw [decide_eq_true_eq] at hL ⊢
      rcases hL with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · rw [mem_strip_leftVars] at hvB
        rcases hvB.1 with hvC | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvC, hvU⟩
        · exact Or.inr ⟨j, hjF, hji, gateVal_mono_U C (Finset.singleton_subset_iff.mpr hvU) j hjv⟩
      · exact Or.inr ⟨j, hjF, hji, ih j (by omega) hjv⟩
    · have hR := hval.2
      unfold sideTrue at hR ⊢
      rw [decide_eq_true_eq] at hR ⊢
      rcases hR with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · rw [mem_strip_rightVars] at hvB
        rcases hvB.1 with hvC | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvC, hvU⟩
        · exact Or.inr ⟨j, hjF, hji, gateVal_mono_U C (Finset.singleton_subset_iff.mpr hvU) j hjv⟩
      · exact Or.inr ⟨j, hjF, hji, ih j (by omega) hjv⟩

private lemma strip_gateVal_ge {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      C.gateVal U i = true →
        (∃ v ∈ U, C.gateVal {v} i = true) ∨ (stripCircuit C).gateVal U i = true := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi hval
    by_cases hsing : ∃ v ∈ U, C.gateVal {v} i = true
    · exact Or.inl hsing
    · right
      have hno : ∀ v ∈ U, C.gateVal {v} i ≠ true := fun v hvU hv => hsing ⟨v, hvU, hv⟩
      rw [gateVal_unfold C U i, Bool.and_eq_true] at hval
      rw [gateVal_unfold (stripCircuit C) U i, Bool.and_eq_true]
      constructor
      · have hL := hval.1
        unfold sideTrue at hL ⊢
        rw [decide_eq_true_eq] at hL ⊢
        rcases hL with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, (mem_strip_leftVars C i v).mpr ⟨Or.inl hvB, hno v hvU⟩, hvU⟩
        · rcases ih j (by omega) hjv with ⟨v, hvU, hvs⟩ | hj'
          · exact Or.inl ⟨v, (mem_strip_leftVars C i v).mpr ⟨Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
          · exact Or.inr ⟨j, hjF, hji, hj'⟩
      · have hR := hval.2
        unfold sideTrue at hR ⊢
        rw [decide_eq_true_eq] at hR ⊢
        rcases hR with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, (mem_strip_rightVars C i v).mpr ⟨Or.inl hvB, hno v hvU⟩, hvU⟩
        · rcases ih j (by omega) hjv with ⟨v, hvU, hvs⟩ | hj'
          · exact Or.inl ⟨v, (mem_strip_rightVars C i v).mpr ⟨Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
          · exact Or.inr ⟨j, hjF, hji, hj'⟩

private lemma strip_eval_eq {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    (stripCircuit C).eval U = C.eval U := by
  unfold AndCountCircuit.eval
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
    · rw [mem_strip_outVars] at hvO
      rcases hvO with hvC | ⟨j, hjO, hvs⟩
      · exact Or.inl ⟨v, hvC, hvU⟩
      · exact Or.inr ⟨j, hjO, gateVal_mono_U C (Finset.singleton_subset_iff.mpr hvU) j hvs⟩
    · exact Or.inr ⟨j, hjO, strip_gateVal_le C U C.size j j.isLt hjv⟩
  · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
    · exact Or.inl ⟨v, (mem_strip_outVars C v).mpr (Or.inl hvO), hvU⟩
    · rcases strip_gateVal_ge C U C.size j j.isLt hjv with ⟨v, hvU, hvs⟩ | hj'
      · exact Or.inl ⟨v, (mem_strip_outVars C v).mpr (Or.inr ⟨j, hjO, hvs⟩), hvU⟩
      · exact Or.inr ⟨j, hjO, hj'⟩



theorem normalize : ∀ (n : ℕ) (C : PEqualNP.AndCount.AndCountCircuit n),
    ∃ C' : PEqualNP.AndCount.AndCountCircuit n,
      C'.size ≤ C.size ∧ (∀ U : Finset (Fin n), C'.eval U = C.eval U) ∧
      (∀ (i : Fin C'.size) (v : Fin n), C'.gateVal {v} i = false) ∧
      (∀ i : Fin C'.size, Disjoint (C'.leftVars i) (C'.rightVars i)) ∧
      (C.WellFormed → C'.WellFormed) := by
  intro n C
  refine ⟨PEqualNP.Outside.L_meta_17707.AndNorm.stripCircuit C, le_refl C.size,
    fun U => PEqualNP.Outside.L_meta_17707.AndNorm.strip_eval_eq C U,
    fun i v => PEqualNP.Outside.L_meta_17707.AndNorm.strip_singleton_false C v C.size i i.isLt,
    fun i => PEqualNP.Outside.L_meta_17707.AndNorm.strip_disjoint C i,
    fun hWF => hWF⟩

end AndNorm
namespace Witness

open PEqualNP.AndCount

-- Every gate true at fuel d leads to a gate whose two sides both meet U by bare variables.
theorem fuel_witness {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (d : ℕ) (i : Fin C.size), C.gateValFuel U d i = true →
      ∃ k : Fin C.size, (∃ v ∈ C.leftVars k, v ∈ U) ∧ (∃ v ∈ C.rightVars k, v ∈ U) := by
  intro d
  induction d with
  | zero =>
    intro i h
    simp [AndCountCircuit.gateValFuel] at h
  | succ d ih =>
    intro i h
    simp only [AndCountCircuit.gateValFuel, Bool.and_eq_true,
      AndCountCircuit.sideTrue, decide_eq_true_eq] at h
    obtain ⟨hl, hr⟩ := h
    rcases hl with hl | ⟨j, _, _, hj⟩
    · rcases hr with hr | ⟨j, _, _, hj⟩
      · exact ⟨i, hl, hr⟩
      · exact ih j hj
    · exact ih j hj



theorem crossing : ∀ (x1 : ℕ) (x2 : PEqualNP.AndCount.AndCountCircuit x1) (x3 : SimpleGraph (Fin x1)), x2.Computes x3 → x2.outVars = ∅ → (∀ (x6 : Fin x2.size), Disjoint (x2.leftVars x6) (x2.rightVars x6)) → ∀ (x7 x8 : Fin x1), x3.Adj x7 x8 → ∃ (x10 : Fin x2.size), x7 ∈ x2.leftVars x10 ∧ x8 ∈ x2.rightVars x10 ∨ x8 ∈ x2.leftVars x10 ∧ x7 ∈ x2.rightVars x10 := by
  classical
  intro n C G hC hOut hDisj a b hab
  have hEv : C.eval {a, b} = true :=
    (hC {a, b}).mpr ⟨a, by simp, b, by simp, hab⟩
  rw [PEqualNP.AndCount.AndCountCircuit.eval, decide_eq_true_eq] at hEv
  rcases hEv with ⟨v, hv, _⟩ | ⟨j, _, hj⟩
  · rw [hOut] at hv
    simp at hv
  · obtain ⟨k, ⟨v, hvl, hvU⟩, ⟨w, hwr, hwU⟩⟩ :=
      PEqualNP.Outside.L_meta_17707.Witness.fuel_witness C {a, b} C.size j hj
    refine ⟨k, ?_⟩
    have hd := hDisj k
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvU hwU
    rcases hvU with rfl | rfl <;> rcases hwU with rfl | rfl
    · exact absurd hwr (Finset.disjoint_left.mp hd hvl)
    · exact Or.inl ⟨hvl, hwr⟩
    · exact Or.inr ⟨hvl, hwr⟩
    · exact absurd hwr (Finset.disjoint_left.mp hd hvl)

end Witness
def graph {n m : ℕ} (E : Finset (Fin n × Fin m)) : SimpleGraph (Fin (n + m)) :=
  SimpleGraph.fromRel fun a b => ∃ e ∈ E, a = Fin.castAdd m e.1 ∧ b = Fin.natAdd n e.2

lemma separate {n m : ℕ} (a : Fin n) (b : Fin m) :
    Fin.castAdd m a ≠ Fin.natAdd n b := by
  intro h
  have hn := a.isLt
  have h' := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
  omega

lemma adj_iff {n m : ℕ} (E : Finset (Fin n × Fin m)) (u v : Fin (n + m)) :
    (graph E).Adj u v ↔ ∃ e ∈ E,
      (u = Fin.castAdd m e.1 ∧ v = Fin.natAdd n e.2) ∨
      (v = Fin.castAdd m e.1 ∧ u = Fin.natAdd n e.2) := by
  rw [graph, SimpleGraph.fromRel_adj]
  constructor
  · intro h
    rcases h.2 with ⟨e, he, hu, hv⟩ | ⟨e, he, hu, hv⟩
    · exact ⟨e, he, Or.inl ⟨hu, hv⟩⟩
    · exact ⟨e, he, Or.inr ⟨hu, hv⟩⟩
  · rintro ⟨e, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨separate _ _, Or.inl ⟨e, he, rfl, rfl⟩⟩
    · exact ⟨(separate _ _).symm, Or.inr ⟨e, he, rfl, rfl⟩⟩

lemma edge_card {n m : ℕ} (E : Finset (Fin n × Fin m)) :
    (graph E).edgeSet.ncard = E.card := by
  let em : Fin n × Fin m → Sym2 (Fin (n + m)) :=
    fun e => s(Fin.castAdd m e.1, Fin.natAdd n e.2)
  have em_inj : Function.Injective em := by
    intro p q h
    change s(Fin.castAdd m p.1, Fin.natAdd n p.2) =
      s(Fin.castAdd m q.1, Fin.natAdd n q.2) at h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨ha, hb⟩ | ⟨ha, _⟩
    · exact Prod.ext (Fin.castAdd_injective _ _ ha) (Fin.natAdd_injective _ _ hb)
    · exact False.elim (separate _ _ ha)
  have he : (graph E).edgeSet = em '' (E : Set (Fin n × Fin m)) := by
    ext p
    induction p using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeSet, adj_iff]
      change (∃ e ∈ E, _) ↔ ∃ e, e ∈ E ∧ em e = s(u, v)
      simp only [em, Sym2.eq_iff, eq_comm (a := u), eq_comm (a := v)]
  rw [he, Set.ncard_image_of_injective _ em_inj, Set.ncard_coe_finset]

namespace AndLower
open scoped Classical

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit SimpleGraph

def uses {n : ℕ} (C : AndCountCircuit n) (v : Fin n) (j : Fin C.size) : Prop :=
  v ∈ C.leftVars j ∨ v ∈ C.rightVars j

lemma emptyOut {n : ℕ} {C : AndCountCircuit n} {G : SimpleGraph (Fin n)}
    (hc : C.Computes G) : C.outVars = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have htrue : C.eval {v} = true := by
    unfold eval
    exact decide_eq_true_eq.mpr (Or.inl ⟨v, hv, by simp⟩)
  obtain ⟨a, ha, b, hb, hab⟩ := (hc {v}).mp htrue
  simp only [Finset.mem_singleton] at ha hb
  subst a
  subst b
  exact G.irrefl hab

lemma crossing {n : ℕ} {C : AndCountCircuit n} {G : SimpleGraph (Fin n)}
    (hc : C.Computes G) (hd : ∀ j, Disjoint (C.leftVars j) (C.rightVars j))
    {a b : Fin n} (hab : G.Adj a b) :
    ∃ j, (a ∈ C.leftVars j ∧ b ∈ C.rightVars j) ∨
      (b ∈ C.leftVars j ∧ a ∈ C.rightVars j) :=
  Witness.crossing n C G hc (emptyOut hc) hd a b hab

lemma sideAt {n : ℕ} {C : AndCountCircuit n} {U : Finset (Fin n)} {j : Fin C.size}
    (hl : ∃ v ∈ C.leftVars j, v ∈ U) (hr : ∃ v ∈ C.rightVars j, v ∈ U)
    (d : ℕ) : C.gateValFuel U (d + 1) j = true := by
  simp only [gateValFuel, Bool.and_eq_true, sideTrue, decide_eq_true_eq]
  exact ⟨Or.inl hl, Or.inl hr⟩

lemma pair_eq_of_one_gate {n : ℕ} {C : AndCountCircuit n}
    (hOut : C.outVars = ∅) (j : Fin C.size) (U V : Finset (Fin n))
    (hUnique : ∀ k, k ≠ j → ∀ v ∈ U ∪ V, ¬ uses C v k)
    (hUL : ∃ v ∈ C.leftVars j, v ∈ U) (hUR : ∃ v ∈ C.rightVars j, v ∈ U)
    (hVL : ∃ v ∈ C.leftVars j, v ∈ V) (hVR : ∃ v ∈ C.rightVars j, v ∈ V) :
    C.eval U = C.eval V := by
  have hval : ∀ d : ℕ, ∀ k, C.gateValFuel U d k = C.gateValFuel V d k := by
    intro d
    induction d with
    | zero => intro k; rfl
    | succ d ih =>
      intro k
      by_cases hk : k = j
      · subst k
        rw [sideAt hUL hUR d, sideAt hVL hVR d]
      · have left_eq : (∃ v ∈ C.leftVars k, v ∈ U) ↔ ∃ v ∈ C.leftVars k, v ∈ V := by
          constructor
          · rintro ⟨v, hv, hu⟩
            exact (hUnique k hk v (Finset.mem_union_left _ hu) (Or.inl hv)).elim
          · rintro ⟨v, hv, hu⟩
            exact (hUnique k hk v (Finset.mem_union_right _ hu) (Or.inl hv)).elim
        have right_eq : (∃ v ∈ C.rightVars k, v ∈ U) ↔ ∃ v ∈ C.rightVars k, v ∈ V := by
          constructor
          · rintro ⟨v, hv, hu⟩
            exact (hUnique k hk v (Finset.mem_union_left _ hu) (Or.inr hv)).elim
          · rintro ⟨v, hv, hu⟩
            exact (hUnique k hk v (Finset.mem_union_right _ hu) (Or.inr hv)).elim
        simp only [gateValFuel, sideTrue, ih, left_eq, right_eq]
  simp only [eval, hOut, Finset.notMem_empty, false_and, exists_const, false_or, gateVal, hval]

lemma repeat_on_path {n : ℕ} {C : AndCountCircuit n} {G : SimpleGraph (Fin n)}
    (hc : C.Computes G) (hd : ∀ j, Disjoint (C.leftVars j) (C.rightVars j))
    {a b c d : Fin n} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (had : ¬ G.Adj a d) :
    ∃ v ∈ ({a,b,c,d} : Finset (Fin n)), ∃ j k, j ≠ k ∧ uses C v j ∧ uses C v k := by
  classical
  by_contra h
  have unique : ∀ v ∈ ({a,b,c,d} : Finset (Fin n)), ∀ j k,
      uses C v j → uses C v k → j = k := by
    intro v hv j k hj hk
    by_contra hne
    exact h ⟨v,hv,j,k,hne,hj,hk⟩
  obtain ⟨j,hj⟩ := crossing hc hd hab
  obtain ⟨k,hk⟩ := crossing hc hd hbc
  obtain ⟨m,hm⟩ := crossing hc hd hcd
  have hj_a : uses C a j := hj.elim (fun ht => Or.inl ht.1) (fun ht => Or.inr ht.2)
  have hj_b : uses C b j := hj.elim (fun ht => Or.inr ht.2) (fun ht => Or.inl ht.1)
  have hk_b : uses C b k := hk.elim (fun ht => Or.inl ht.1) (fun ht => Or.inr ht.2)
  have hk_c : uses C c k := hk.elim (fun ht => Or.inr ht.2) (fun ht => Or.inl ht.1)
  have hm_c : uses C c m := hm.elim (fun ht => Or.inl ht.1) (fun ht => Or.inr ht.2)
  have hkj := unique b (by simp) k j hk_b hj_b
  have hmk := unique c (by simp) m k hm_c hk_c
  subst m
  subst k
  have bare : ∀ v ∈ ({a,b,d} : Finset (Fin n)), uses C v j := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact hj_a
    · exact hj_b
    · exact hm.elim (fun ht => Or.inr ht.2) (fun ht => Or.inl ht.1)
  have no_other : ∀ k, k ≠ j → ∀ v ∈ ({a,b} : Finset (Fin n)) ∪ {a,d}, ¬ uses C v k := by
    intro k hk v hv hUse
    have hv' : v ∈ ({a,b,d} : Finset (Fin n)) := by simpa only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] using
      (show v = a ∨ v = b ∨ v = d from by simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hv; tauto)
    exact hk (unique v (by simp only [Finset.mem_insert, Finset.mem_singleton] at hv' ⊢; tauto)
      k j hUse (bare v hv'))
  have side_disj := Finset.disjoint_left.mp (hd j)
  have ad : (a ∈ C.leftVars j ∧ d ∈ C.rightVars j) ∨
      (d ∈ C.leftVars j ∧ a ∈ C.rightVars j) := by
    rcases hj with hj | hj <;> rcases hk with hk | hk <;> rcases hm with hm | hm
    all_goals first
      | exact (side_disj hj.1 hk.2).elim
      | exact (side_disj hk.1 hj.2).elim
      | exact (side_disj hm.1 hk.2).elim
      | exact (side_disj hk.1 hm.2).elim
      | exact Or.inl ⟨hj.1, hm.2⟩
      | exact Or.inr ⟨hm.1, hj.2⟩
  have eq := pair_eq_of_one_gate (emptyOut hc) j {a,b} {a,d} no_other
    (hj.elim (fun w => ⟨a,w.1,by simp⟩) (fun w => ⟨b,w.1,by simp⟩))
    (hj.elim (fun w => ⟨b,w.2,by simp⟩) (fun w => ⟨a,w.2,by simp⟩))
    (ad.elim (fun w => ⟨a,w.1,by simp⟩) (fun w => ⟨d,w.1,by simp⟩))
    (ad.elim (fun w => ⟨d,w.2,by simp⟩) (fun w => ⟨a,w.2,by simp⟩))
  have ht : C.eval {a,b} = true := (hc _).2 ⟨a,by simp,b,by simp,hab⟩
  obtain ⟨u,hu,w,hw,huw⟩ := (hc {a,d}).1 (eq ▸ ht)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
  rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
  · exact G.irrefl huw
  · exact had huw
  · exact had huw.symm
  · exact G.irrefl huw

def omitVars {n : ℕ} (C : AndCountCircuit n) (N : Finset (Fin n)) : AndCountCircuit n :=
  { C with
    leftVars := fun j => C.leftVars j \ N
    rightVars := fun j => C.rightVars j \ N
    outVars := C.outVars \ N }

lemma omit_eval {n : ℕ} (C : AndCountCircuit n) (N U : Finset (Fin n)) :
    (omitVars C N).eval U = C.eval (U \ N) := by
  classical
  have move (B : Finset (Fin n)) : (∃ v ∈ B \ N, v ∈ U) ↔ ∃ v ∈ B, v ∈ U \ N := by
    simp only [Finset.mem_sdiff]
    exact exists_congr fun _ => by tauto
  have unfoldFuel : ∀ d (j : Fin C.size),
      (omitVars C N).gateValFuel U d j = C.gateValFuel (U \ N) d j := by
    intro d
    induction d with
    | zero => intro j; rfl
    | succ d ih =>
      intro j
      change (sideTrue U (C.leftVars j \ N) (C.leftGates j) j
          ((omitVars C N).gateValFuel U d) &&
        sideTrue U (C.rightVars j \ N) (C.rightGates j) j
          ((omitVars C N).gateValFuel U d)) =
        (sideTrue (U \ N) (C.leftVars j) (C.leftGates j) j (C.gateValFuel (U \ N) d) &&
        sideTrue (U \ N) (C.rightVars j) (C.rightGates j) j (C.gateValFuel (U \ N) d))
      simp only [sideTrue, move, ih]
  rw [Bool.eq_iff_iff]
  simp only [eval, decide_eq_true_eq]
  change ((∃ v ∈ C.outVars \ N, v ∈ U) ∨
      ∃ j ∈ C.outGates, (omitVars C N).gateValFuel U C.size j = true) ↔
    ((∃ v ∈ C.outVars, v ∈ U \ N) ∨
      ∃ j ∈ C.outGates, C.gateValFuel (U \ N) C.size j = true)
  simp only [move, unfoldFuel]

def eraseStar {n : ℕ} (G : SimpleGraph (Fin n)) (N : Finset (Fin n)) : SimpleGraph (Fin n) :=
  PEqualNP.Library.Peel.delVerts G N

lemma eraseStar_le {n : ℕ} (G : SimpleGraph (Fin n)) (N : Finset (Fin n)) :
    eraseStar G N ≤ G := fun _ _ h => h.1

def rectangleFree {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)

def bipartition {n : ℕ} (G : SimpleGraph (Fin n)) (color : Fin n → Bool) : Prop :=
  ∀ a b, G.Adj a b → color a ≠ color b

-- A leaf needs one reader. With degree two throughout the support, a path forces a repeated reader.
lemma goodReader {n : ℕ} {G : SimpleGraph (Fin n)} (C : AndCountCircuit n)
    (sp : GraphInduction599.sparse G) (rf : rectangleFree G)
    (color : Fin n → Bool) (hbip : bipartition G color)
    (hEdges : ∃ a b, G.Adj a b) (hc : C.Computes G)
    (hd : ∀ j, Disjoint (C.leftVars j) (C.rightVars j)) :
    ∃ v, 0 < G.degree v ∧
      G.degree v ≤ {j : Fin C.size | uses C v j}.ncard := by
  classical
  have uses_card (v : Fin n) :
      {j : Fin C.size | uses C v j}.ncard = (Finset.univ.filter (uses C v)).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext j
    simp
  by_cases hl : ∃ v, G.degree v = 1
  · obtain ⟨v,hv⟩ := hl
    obtain ⟨w,hw⟩ := (G.degree_pos_iff_exists_adj v).mp (by omega : 0 < G.degree v)
    obtain ⟨j,hj⟩ := crossing hc hd hw
    have hU : uses C v j := hj.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
    exact ⟨v, by omega, by rw [hv, uses_card]; exact Finset.card_pos.mpr ⟨j, by simp [hU]⟩⟩
  · have reg : ∀ v ∈ G.support, G.degree v = 2 :=
      GraphInduction599.regular_of_no_leaf G sp (fun v he => hl ⟨v,he⟩)
    have nbr (u v : Fin n) (huv : G.Adj u v) : ∃ w, G.Adj u w ∧ w ≠ v := by
      have hcard : (G.neighborFinset u).card = 2 := reg u huv.mem_support_left
      by_contra h
      have sub : G.neighborFinset u ⊆ {v} := by
        intro w hw
        rw [Finset.mem_singleton]
        by_contra hw'
        exact h ⟨w, (G.mem_neighborFinset u w).mp hw, hw'⟩
      have := Finset.card_le_card sub
      simp_all
    obtain ⟨b,c,hbc⟩ := hEdges
    obtain ⟨a,hba,hac⟩ := nbr b c hbc
    obtain ⟨d,hcd,hdb⟩ := nbr c b hbc.symm
    have hAd : ¬ G.Adj a d := fun h => rf a b c d hac hdb.symm ⟨hba.symm,hbc,hcd,h.symm⟩
    obtain ⟨v,hv,j,k,hjk,hj,hk⟩ := repeat_on_path hc hd hba.symm hbc hcd hAd
    have hActive : v ∈ G.support := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact hba.mem_support_right
      · exact hbc.mem_support_left
      · exact hbc.mem_support_right
      · exact hcd.mem_support_right
    have hPair : ({j,k} : Finset (Fin C.size)) ⊆ Finset.univ.filter (uses C v) := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · simp [hj]
      · simp [hk]
    have card := Finset.card_le_card hPair
    rw [Finset.card_pair hjk] at card
    exact ⟨v, by rw [reg v hActive]; decide, by rwa [reg v hActive, uses_card]⟩

lemma and_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (sp : GraphInduction599.sparse G) (rf : rectangleFree G)
    (color : Fin n → Bool) (hbip : bipartition G color)
    (C : AndCountCircuit n) (hc : C.Computes G) :
    ∃ T : Finset (Fin n), (∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ T.card ≤ C.size := by
  classical
  induction hm : G.edgeSet.ncard using Nat.strong_induction_on generalizing G C with
  | ind m ih =>
    by_cases hE : ∃ a b, G.Adj a b
    swap
    · exact ⟨∅, fun a b h => (hE ⟨a,b,h⟩).elim, by simp⟩
    obtain ⟨C', hsize, heval, _, hd, _⟩ := AndNorm.normalize n C
    have hc' : C'.Computes G := fun U => heval U ▸ hc U
    obtain ⟨v, hv, hvUses⟩ := goodReader C' sp rf color hbip hE hc' hd
    have hfalse : C'.eval {v} = false := by
      cases h : C'.eval {v}
      · rfl
      · obtain ⟨a,ha,b,hb,hab⟩ := (hc' _).mp h
        simp only [Finset.mem_singleton] at ha hb
        subst a
        subst b
        exact (G.irrefl hab).elim
    obtain ⟨D, _, hDcost, hD⟩ := AndRestrict.main n C' {v} hfalse
    have hcost : D.size + G.degree v ≤ C.size := by
      have hset : {j : Fin C'.size | ∃ x ∈ ({v} : Finset (Fin n)), x ∈ C'.leftVars j ∨ x ∈ C'.rightVars j} =
          {j : Fin C'.size | uses C' v j} := by
        ext j
        simp [uses]
      rw [hset] at hDcost
      omega
    let N := G.neighborFinset v
    let H := eraseStar G N
    let D' := omitVars D N
    have hD' : D'.Computes H := by
      intro U
      rw [omit_eval, hD, hc']
      constructor
      · rintro ⟨a,ha,b,hb,hab⟩
        have hn (x : Fin n) (hx : x ∈ ({v} : Finset (Fin n)) ∪ (U \ N)) : x ∉ N := by
          rcases Finset.mem_union.mp hx with h | h
          · rw [Finset.mem_singleton.mp h]
            exact fun h => G.irrefl ((G.mem_neighborFinset v v).mp h)
          · exact (Finset.mem_sdiff.mp h).2
        have av : a ≠ v := fun e => hn b hb ((G.mem_neighborFinset v b).mpr (e ▸ hab))
        have bv : b ≠ v := fun e => hn a ha ((G.mem_neighborFinset v a).mpr (e ▸ hab.symm))
        have au := (Finset.mem_sdiff.mp ((Finset.mem_union.mp ha).resolve_left (by simpa using av))).1
        have bu := (Finset.mem_sdiff.mp ((Finset.mem_union.mp hb).resolve_left (by simpa using bv))).1
        exact ⟨a, au, b, bu, hab, hn a ha, hn b hb⟩
      · rintro ⟨a,ha,b,hb,hab⟩
        exact ⟨a,Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨ha,hab.2.1⟩),
          b,Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hb,hab.2.2⟩),hab.1⟩
    have sub := eraseStar_le G N
    have lt : H.edgeSet.ncard < m := by
      rw [← hm]
      refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
      apply Set.ssubset_iff_subset_ne.mpr
      constructor
      · exact SimpleGraph.edgeSet_mono sub
      · obtain ⟨w,hw⟩ := (G.degree_pos_iff_exists_adj v).mp hv
        intro h
        have hed : s(v,w) ∈ H.edgeSet := h.symm ▸ G.mem_edgeSet.mpr hw
        exact (H.mem_edgeSet.mp hed).2.2 ((G.mem_neighborFinset v w).mpr hw)
    obtain ⟨T,hT,hTsize⟩ := ih _ lt H (GraphInduction599.sparse_subgraph sub sp)
      (fun a b c d hac hbd h => rf a b c d hac hbd ⟨h.1.1,h.2.1.1,h.2.2.1.1,h.2.2.2.1⟩)
      (fun a b h => hbip a b h.1) D' hD' rfl
    refine ⟨T ∪ N, ?_, ?_⟩
    · intro a b hab
      by_cases ha : a ∈ N
      · exact Or.inl (Finset.mem_union_right _ ha)
      by_cases hb : b ∈ N
      · exact Or.inr (Finset.mem_union_right _ hb)
      exact (hT a b ⟨hab,ha,hb⟩).imp (Finset.mem_union_left _) (Finset.mem_union_left _)
    · have hN : N.card = G.degree v := rfl
      have hD' : D'.size = D.size := rfl
      have hUnion := Finset.card_union_le T N
      omega

end AndLower

namespace Sparsity
open scoped Classical

open SimpleGraph
open AndLower (rectangleFree bipartition eraseStar eraseStar_le)

lemma other_neighbor {n : ℕ} (H : SimpleGraph (Fin n)) {v w : Fin n}
    (hd : 2 ≤ H.degree v) : ∃ u, H.Adj v u ∧ u ≠ w := by
  classical
  by_contra h
  have sub : H.neighborFinset v ⊆ {w} := by
    intro u hu
    rw [Finset.mem_singleton]
    by_contra hne
    exact h ⟨u, (H.mem_neighborFinset v u).mp hu, hne⟩
  have hcard := Finset.card_le_card sub
  change (H.neighborFinset v).card ≤ _ at hcard
  rw [Finset.card_singleton] at hcard
  change 2 ≤ (H.neighborFinset v).card at hd
  exact (by omega : False)

lemma large_support {n : ℕ} (H : SimpleGraph (Fin n))
    (color : Fin n → Bool) (hbip : bipartition H color) (rf : rectangleFree H)
    (hm : ∀ v ∈ H.support, 2 ≤ H.degree v) (v : Fin n) (hv : 2 < H.degree v) :
    8 ≤ H.support.toFinset.card := by
  classical
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp (show 2 < (H.neighborFinset v).card from hv)
  have va := (H.mem_neighborFinset v a).mp ha
  have vb := (H.mem_neighborFinset v b).mp hb
  have vc := (H.mem_neighborFinset v c).mp hc
  obtain ⟨a',haa',ha'⟩ := other_neighbor H (hm a va.mem_support_right : 2 ≤ H.degree a) (w := v)
  obtain ⟨b',hbb',hb'⟩ := other_neighbor H (hm b vb.mem_support_right : 2 ≤ H.degree b) (w := v)
  obtain ⟨c',hcc',hc'⟩ := other_neighbor H (hm c vc.mem_support_right : 2 ≤ H.degree c) (w := v)
  have ha'b' : a' ≠ b' := by
    intro e
    subst b'
    exact rf v a a' b ha'.symm hab ⟨va,haa',hbb'.symm,vb.symm⟩
  have ha'c' : a' ≠ c' := by
    intro e
    subst c'
    exact rf v a a' c ha'.symm hac ⟨va,haa',hcc'.symm,vc.symm⟩
  have hb'c' : b' ≠ c' := by
    intro e
    subst c'
    exact rf v b b' c hb'.symm hbc ⟨vb,hbb',hcc'.symm,vc.symm⟩
  obtain ⟨d,had,hda⟩ := other_neighbor H (hm a' haa'.mem_support_right : 2 ≤ H.degree a') (w := a)
  have hdb : d ≠ b := by
    intro e
    subst d
    exact rf v a a' b ha'.symm hab ⟨va,haa',had,vb.symm⟩
  have hdc : d ≠ c := by
    intro e
    subst d
    exact rf v a a' c ha'.symm hac ⟨va,haa',had,vc.symm⟩
  have flip {x y : Bool} (h : x ≠ y) : y = !x := by
    cases x <;> cases y <;> simp_all
  have hCa := flip (hbip v a va)
  have hCb := flip (hbip v b vb)
  have hCc := flip (hbip v c vc)
  have hCa' : color a' = color v := by simpa [hCa] using flip (hbip a a' haa')
  have hCb' : color b' = color v := by simpa [hCb] using flip (hbip b b' hbb')
  have hCc' : color c' = color v := by simpa [hCc] using flip (hbip c c' hcc')
  have hCd : color d = !color v := by simpa [hCa'] using flip (hbip a' d had)
  let X : Finset (Fin n) := {v,a',b',c'}
  let Y : Finset (Fin n) := {a,b,c,d}
  have hX : X.card = 4 := by
    have n1 : v ∉ ({a',b',c'} : Finset (Fin n)) := by simp [Ne.symm ha', Ne.symm hb', Ne.symm hc']
    rw [show X = insert v {a',b',c'} from rfl, Finset.card_insert_of_notMem n1,
      Finset.card_triple_eq_three_iff.mpr ⟨ha'b',ha'c',hb'c'⟩]
  have hY : Y.card = 4 := by
    have n1 : a ∉ ({b,c,d} : Finset (Fin n)) := by simp [hab,hac,Ne.symm hda]
    rw [show Y = insert a {b,c,d} from rfl, Finset.card_insert_of_notMem n1,
      Finset.card_triple_eq_three_iff.mpr ⟨hbc,Ne.symm hdb,Ne.symm hdc⟩]
  have hdis : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro z hx hy
    have hcx : color z = color v := by
      simp only [X, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · rfl
      · exact hCa'
      · exact hCb'
      · exact hCc'
    have hcy : color z = !color v := by
      simp only [Y, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact hCa
      · exact hCb
      · exact hCc
      · exact hCd
    have con := hcx.symm.trans hcy
    cases he : color v <;> simp [he] at con
  have hs : X ∪ Y ⊆ H.support.toFinset := by
    intro z hz
    rw [Set.mem_toFinset]
    rcases Finset.mem_union.mp hz with hz | hz
    · simp only [X, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact va.mem_support_left
      · exact haa'.mem_support_right
      · exact hbb'.mem_support_right
      · exact hcc'.mem_support_right
    · simp only [Y, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact va.mem_support_right
      · exact vb.mem_support_right
      · exact vc.mem_support_right
      · exact had.mem_support_right
  have := Finset.card_le_card hs
  rwa [Finset.card_union_of_disjoint hdis, hX, hY] at this

lemma delete_support {n : ℕ} (H : SimpleGraph (Fin n)) (v : Fin n) :
    (H.deleteIncidenceSet v).support.toFinset ⊆ H.support.toFinset.erase v := by
  classical
  intro a ha
  have ha' : a ∈ (H.deleteIncidenceSet v).support := Set.mem_toFinset.mp ha
  obtain ⟨b,hab⟩ := (SimpleGraph.mem_support _).mp ha'
  have hDel : H.Adj a b ∧ s(a,b) ∉ H.incidenceSet v := deleteEdges_adj.mp hab
  simp only [Finset.mem_erase, Set.mem_toFinset]
  exact ⟨fun e => hDel.2 ⟨H.mem_edgeSet.mpr hDel.1, Sym2.mem_iff.mpr (Or.inl e.symm)⟩,
    hDel.1.mem_support_left⟩

lemma dense_core {n : ℕ} {G : SimpleGraph (Fin n)} (hn : ¬ GraphInduction599.sparse G) :
    ∃ H : SimpleGraph (Fin n), H ≤ G ∧ H.support.toFinset.card < H.edgeSet.ncard ∧
      (∀ v ∈ H.support, 2 ≤ H.degree v) ∧ ∃ v, 2 < H.degree v := by
  classical
  rw [GraphInduction599.sparse, not_forall] at hn
  obtain ⟨S,hS⟩ := hn
  let G' := eraseStar G Sᶜ
  have hedge : G'.edgeSet = {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S} := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [mem_edgeSet, Set.mem_setOf_eq]
      change (G.Adj a b ∧ a ∉ Sᶜ ∧ b ∉ Sᶜ) ↔ _
      simp only [Finset.mem_compl, not_not]
      constructor
      · rintro ⟨hab,ha,hb⟩
        exact ⟨hab, fun v hv => (Sym2.mem_iff.mp hv).elim (fun h => h.symm ▸ ha) (fun h => h.symm ▸ hb)⟩
      · rintro ⟨hab,h⟩
        exact ⟨hab, h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩
  have hsupp : G'.support.toFinset ⊆ S := by
    intro a ha
    obtain ⟨b,hab⟩ := (SimpleGraph.mem_support _).mp (Set.mem_toFinset.mp ha)
    exact Finset.notMem_compl.mp hab.2.1
  let P := fun m => ∃ H : SimpleGraph (Fin n), H ≤ G ∧ H.support.toFinset.card < H.edgeSet.ncard ∧
    H.edgeSet.ncard = m
  have ex : ∃ m, P m := ⟨_, G', eraseStar_le G _, by
    rw [hedge]
    exact (Finset.card_le_card hsupp).trans_lt (Nat.lt_of_not_ge hS), rfl⟩
  obtain ⟨H,hH,hDense,hMin⟩ := Nat.find_spec ex
  have hd1 : ∀ v ∈ H.support, 2 ≤ H.degree v := by
    intro v hv
    have hpos := (H.degree_pos_iff_mem_support v).mpr hv
    by_contra hlt
    have hv1 : H.degree v = 1 := by omega
    let D := H.deleteIncidenceSet v
    have hed := GraphInduction599.count_after_delete H v
    have hsmall := Finset.card_le_card (delete_support H v)
    rw [Finset.card_erase_of_mem (Set.mem_toFinset.mpr hv)] at hsmall
    have hSuppPos : 0 < H.support.toFinset.card := Finset.card_pos.mpr ⟨v,Set.mem_toFinset.mpr hv⟩
    have hDense' : D.support.toFinset.card < D.edgeSet.ncard := by
      change D.edgeSet.ncard + _ = _ at hed
      change D.support.toFinset.card ≤ _ at hsmall
      omega
    have hbound := Nat.find_min' ex (show P D.edgeSet.ncard from
      ⟨D, (H.deleteIncidenceSet_le v).trans hH, by
        simpa only [← Set.ncard_eq_toFinset_card'] using hDense', rfl⟩)
    change D.edgeSet.ncard + _ = _ at hed
    omega
  refine ⟨H,hH,hDense,hd1,?_⟩
  by_contra h
  have hle : ∀ v ∈ H.support.toFinset, H.degree v ≤ 2 := fun v _ =>
    Nat.le_of_not_gt (fun ht => h ⟨v,ht⟩)
  have hh := Finset.sum_le_sum hle
  rw [H.sum_degrees_support_eq_twice_card_edges, Finset.sum_const, smul_eq_mul] at hh
  rw [← GraphInduction599.count_eq] at hh
  omega

def noSingleEdge {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ a b, G.Adj a b → (∃ c, c ≠ b ∧ G.Adj a c) ∨ (∃ c, c ≠ a ∧ G.Adj b c)

lemma support_after_one_edge {n : ℕ} {G H : SimpleGraph (Fin n)}
    (hsub : H ≤ G) (hcard : G.edgeSet.ncard ≤ H.edgeSet.ncard + 1)
    (hno : noSingleEdge G) : G.support.toFinset.card ≤ H.support.toFinset.card + 1 := by
  classical
  have hSub := edgeFinset_mono hsub
  by_cases heq : H.edgeFinset = G.edgeFinset
  · have hG : H = G := by ext a b; rw [← H.mem_edgeSet, ← H.mem_edgeFinset, heq, G.mem_edgeFinset, G.mem_edgeSet]
    subst H
    omega
  have diffCard : (G.edgeFinset \ H.edgeFinset).card ≤ 1 := by
    have hc := Finset.card_sdiff_add_card_eq_card hSub
    rw [← GraphInduction599.count_eq, ← GraphInduction599.count_eq] at hc
    omega
  obtain ⟨e,he⟩ : (G.edgeFinset \ H.edgeFinset).Nonempty :=
    Finset.sdiff_nonempty.mpr (fun h => heq (Finset.Subset.antisymm hSub h))
  have huniq : ∀ f ∈ G.edgeFinset \ H.edgeFinset, f = e := by
    intro f hf
    by_contra hne
    have hpair := Finset.card_le_card (show ({f,e} : Finset _) ⊆ _ from by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      exact ht.elim (fun h => h ▸ hf) (fun h => h ▸ he))
    rw [Finset.card_pair hne] at hpair
    omega
  obtain ⟨⟨a,b⟩,rfl⟩ := Sym2.mk_surjective e
  have ha : G.Adj a b := G.mem_edgeSet.mp (G.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1)
  have haS : a ∈ H.support ∨ b ∈ H.support := by
    rcases hno a b ha with ⟨c,hne,hgc⟩ | ⟨c,hne,hgc⟩
    · left
      by_contra has
      have hd : s(a,c) ∈ G.edgeFinset \ H.edgeFinset :=
        Finset.mem_sdiff.mpr ⟨G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr hgc), fun h => has (H.mem_edgeSet.mp (H.mem_edgeFinset.mp h)).mem_support_left⟩
      rcases Sym2.eq_iff.mp (huniq _ hd) with ⟨_,h⟩ | ⟨h,_⟩
      · exact hne h
      · exact ha.ne h
    · right
      by_contra hbs
      have hd : s(b,c) ∈ G.edgeFinset \ H.edgeFinset :=
        Finset.mem_sdiff.mpr ⟨G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr hgc), fun h => hbs (H.mem_edgeSet.mp (H.mem_edgeFinset.mp h)).mem_support_left⟩
      rcases Sym2.eq_iff.mp (huniq _ hd) with ⟨h,_⟩ | ⟨_,h⟩
      · exact ha.ne h.symm
      · exact hne h
  have supp : G.support.toFinset ⊆ insert a (insert b H.support.toFinset) := by
    intro v hv
    obtain ⟨w,hw⟩ := (SimpleGraph.mem_support _).mp (Set.mem_toFinset.mp hv)
    by_cases h : H.Adj v w
    · simp [Set.mem_toFinset.mpr h.mem_support_left]
    have hmem := Finset.mem_sdiff.mpr ⟨G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr hw), fun h' => h (H.mem_edgeSet.mp (H.mem_edgeFinset.mp h'))⟩
    rcases Sym2.eq_iff.mp (huniq _ hmem) with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> simp
  have hle := Finset.card_le_card supp
  rcases haS with has | hbs
  · have : a ∈ insert b H.support.toFinset := Finset.mem_insert_of_mem (Set.mem_toFinset.mpr has)
    rw [Finset.insert_eq_of_mem this] at hle
    exact hle.trans (Finset.card_insert_le _ _)
  · rw [Finset.insert_eq_of_mem (Set.mem_toFinset.mpr hbs)] at hle
    exact hle.trans (Finset.card_insert_le _ _)

-- A minimal dense subgraph would use at least nine edges and leave too few supported vertices.
lemma sparse_of_few_edges {n : ℕ} (G : SimpleGraph (Fin n))
    (color : Fin n → Bool) (hbip : bipartition G color) (rf : rectangleFree G)
    (he : G.edgeSet.ncard ≤ 10) (hv : 10 ≤ G.support.toFinset.card) (hno : noSingleEdge G) :
    GraphInduction599.sparse G := by
  classical
  by_contra h
  obtain ⟨H, hsub, hDense, hmin, v, hdeg⟩ := dense_core h
  have hm := large_support H color (fun a b h => hbip a b (hsub h))
    (fun a b c d hac hbd h => rf a b c d hac hbd
      ⟨hsub h.1,hsub h.2.1,hsub h.2.2.1,hsub h.2.2.2⟩)
    hmin v hdeg
  have hcard := support_after_one_edge hsub (by omega) hno
  have hd : H.edgeSet.ncard ≤ G.edgeSet.ncard := Set.ncard_le_ncard (edgeSet_mono hsub)
  by_cases hSame : H.edgeSet.ncard = G.edgeSet.ncard
  · have hEq : H = G := by
      have hedge := Finset.eq_of_subset_of_card_le (edgeFinset_mono hsub) (by
        rw [← GraphInduction599.count_eq, ← GraphInduction599.count_eq, hSame])
      ext a b
      rw [← H.mem_edgeSet, ← H.mem_edgeFinset, hedge, G.mem_edgeFinset, G.mem_edgeSet]
    subst H
    omega
  · omega

lemma noFour_of_rectangle {n : ℕ} {G : SimpleGraph (Fin n)} (rf : rectangleFree G) :
    GraphInduction599.noFour G := by
  intro v c hc hlen
  cases c with
  | nil => simp at hlen
  | cons h1 p1 =>
    cases p1 with
    | nil => simp at hlen
    | cons h2 p2 =>
      cases p2 with
      | nil => simp at hlen
      | cons h3 p3 =>
        cases p3 with
        | nil => simp at hlen
        | cons h4 p4 =>
          cases p4 with
          | nil =>
            have hnd := hc.support_nodup
            simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
              List.tail_cons, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
              not_or] at hnd
            exact rf _ _ _ _ (Ne.symm hnd.2.1.2) hnd.1.2.1 ⟨h1,h2,h3,h4⟩
          | cons h5 p5 =>
            simp only [SimpleGraph.Walk.length_cons] at hlen
            omega

end Sparsity
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity SimpleGraph
open AndLower (rectangleFree bipartition)
open scoped Classical

def color (u : Fin 20) : Bool := decide (u.val < 10)

lemma color_left (u : Fin 10) : color (Fin.castAdd 10 u) = true := by
  simp [color, u.isLt]

lemma color_right (u : Fin 10) : color (Fin.natAdd 10 u) = false := by
  have hn : ¬10 + u.val < 10 := by omega
  simp [color, hn]

lemma graph_color (E : Finset (Fin 10 × Fin 10)) : bipartition (graph E) color := by
  intro a b hab
  rcases (adj_iff _ _ _).mp hab with ⟨e,_,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ <;>
    simp only [color_left,color_right] <;> decide

lemma left_of_adj (E : Finset (Fin 10 × Fin 10)) {a b : Fin 20}
    (ha : color a = true) (hab : (graph E).Adj a b) :
    ∃ e ∈ E, a = Fin.castAdd 10 e.1 ∧ b = Fin.natAdd 10 e.2 := by
  rcases (adj_iff E a b).mp hab with ⟨e,he,h | h⟩
  · exact ⟨e,he,h⟩
  · rw [h.2,color_right] at ha
    cases ha

lemma of_edge (E : Finset (Fin 10 × Fin 10)) {e : Fin 10 × Fin 10} (he : e ∈ E) :
    (graph E).Adj (Fin.castAdd 10 e.1) (Fin.natAdd 10 e.2) :=
  (adj_iff E _ _).mpr ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩

lemma edge_of_adj (E : Finset (Fin 10 × Fin 10)) {a b : Fin 10}
    (hab : (graph E).Adj (Fin.castAdd 10 a) (Fin.natAdd 10 b)) : (a,b) ∈ E := by
  obtain ⟨e,he,ha,hb⟩ := left_of_adj E (color_left a) hab
  have eq : (a,b) = e := Prod.ext (Fin.castAdd_injective _ _ ha) (Fin.natAdd_injective _ _ hb)
  exact eq.symm ▸ he

lemma rect_aux (E : Finset (Fin 10 × Fin 10))
    (h4 : ∀ p q l s : Fin 10, p ≠ q → l ≠ s →
      ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E))
    (a b c d : Fin 20) (ha : color a = true) (hac : a ≠ c) (hbd : b ≠ d)
    (hab : (graph E).Adj a b) (hbc : (graph E).Adj b c)
    (hcd : (graph E).Adj c d) (hda : (graph E).Adj d a) : False := by
  obtain ⟨e,he,rfl,rfl⟩ := left_of_adj E ha hab
  have hc : color c = true := by
    have h := graph_color E _ _ hbc
    rw [color_right] at h
    cases hc : color c <;> simp_all
  obtain ⟨f,hf,rfl,rfl⟩ := left_of_adj E hc hcd
  have h1 : e.1 ≠ f.1 := fun h => hac (congrArg _ h)
  have h2 : e.2 ≠ f.2 := fun h => hbd (congrArg _ h)
  exact h4 _ _ _ _ h1 h2 ⟨he,edge_of_adj E hda.symm,edge_of_adj E hbc.symm,hf⟩

lemma graph_rect (E : Finset (Fin 10 × Fin 10))
    (h4 : ∀ p q l s : Fin 10, p ≠ q → l ≠ s →
      ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) :
    rectangleFree (graph E) := by
  intro a b c d hac hbd h
  obtain ⟨ab,bc,cd,da⟩ := h
  cases ha : color a
  · have hb : color b = true := by
      have h := graph_color E _ _ ab
      rw [ha] at h
      cases hb : color b <;> simp_all
    exact rect_aux E h4 b c d a hb hbd hac.symm bc cd da ab
  · exact rect_aux E h4 a b c d ha hac hbd ab bc cd da

lemma no_isolated (E : Finset (Fin 10 × Fin 10))
    (h : ∀ e ∈ E, ∃ f ∈ E, f ≠ e ∧ (f.1 = e.1 ∨ f.2 = e.2)) :
    Sparsity.noSingleEdge (graph E) := by
  have orient (e : Fin 10 × Fin 10) (he : e ∈ E) :
      (∃ c, c ≠ Fin.natAdd 10 e.2 ∧ (graph E).Adj (Fin.castAdd 10 e.1) c) ∨
      (∃ c, c ≠ Fin.castAdd 10 e.1 ∧ (graph E).Adj (Fin.natAdd 10 e.2) c) := by
    obtain ⟨f,hf,hne,hc | hc⟩ := h e he
    · refine Or.inl ⟨Fin.natAdd 10 f.2, ?_, hc ▸ of_edge E hf⟩
      intro eq
      exact hne (Prod.ext hc (Fin.natAdd_injective _ _ eq))
    · refine Or.inr ⟨Fin.castAdd 10 f.1, ?_, hc ▸ (of_edge E hf).symm⟩
      intro eq
      exact hne (Prod.ext (Fin.castAdd_injective _ _ eq) hc)
  intro a b hab
  rcases (adj_iff E a b).mp hab with ⟨e,he,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
  · exact orient e he
  · exact (orient e he).symm

lemma side_images_disjoint {n m : ℕ} (P : Finset (Fin n)) (Q : Finset (Fin m)) :
    Disjoint (P.image (Fin.castAdd m)) (Q.image (Fin.natAdd n)) := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hv'
  exact separate _ _ hb.symm

lemma support_bound (E : Finset (Fin 10 × Fin 10))
    (hl : 5 ≤ (E.image Prod.fst).card) (hr : 5 ≤ (E.image Prod.snd).card) :
    10 ≤ (graph E).support.toFinset.card := by
  classical
  let P := E.image Prod.fst
  let Q := E.image Prod.snd
  have hsub : P.image (Fin.castAdd 10) ∪ Q.image (Fin.natAdd 10) ⊆ (graph E).support.toFinset := by
    intro z hz
    rw [Set.mem_toFinset]
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp ha
      exact (of_edge E he).mem_support_left
    · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hb
      exact (of_edge E he).mem_support_right
  have hn := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (side_images_disjoint P Q),
    Finset.card_image_of_injective _ (Fin.castAdd_injective _ _),
    Finset.card_image_of_injective _ (Fin.natAdd_injective _ _)] at hn
  dsimp [P,Q] at hn
  omega

lemma spec_adj (E : Finset (Fin 10 × Fin 10)) (C : Circuit)
    (hspec : ∀ x : Fin 20 → Bool, circuitFun 20 C x =
      decide (∃ e ∈ E, x (Fin.castAdd 10 e.1) = true ∧ x (Fin.natAdd 10 e.2) = true))
    (x : Fin 20 → Bool) :
    C.eval (List.ofFn x) = true ↔ ∃ a b, (graph E).Adj a b ∧ x a = true ∧ x b = true := by
  change circuitFun 20 C x = true ↔ _
  rw [hspec,decide_eq_true_eq]
  constructor
  · rintro ⟨e,he,ha,hb⟩
    exact ⟨_,_,of_edge E he,ha,hb⟩
  · rintro ⟨a,b,hab,ha,hb⟩
    rcases (adj_iff E a b).mp hab with ⟨e,he,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · exact ⟨e,he,ha,hb⟩
    · exact ⟨e,he,hb,ha⟩

lemma project_cover (E : Finset (Fin 10 × Fin 10)) (T : Finset (Fin 20))
    (hT : ∀ a b, (graph E).Adj a b → a ∈ T ∨ b ∈ T) :
    ∃ (P Q : Finset (Fin 10)), (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q) ∧ P.card + Q.card ≤ T.card := by
  classical
  let P := Finset.univ.filter fun i : Fin 10 => Fin.castAdd 10 i ∈ T
  let Q := Finset.univ.filter fun i : Fin 10 => Fin.natAdd 10 i ∈ T
  have hsub : P.image (Fin.castAdd 10) ∪ Q.image (Fin.natAdd 10) ⊆ T := by
    intro z hz
    rcases Finset.mem_union.mp hz with h | h
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp ha).2
    · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hb).2
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (side_images_disjoint P Q),
    Finset.card_image_of_injective _ (Fin.castAdd_injective _ _),
    Finset.card_image_of_injective _ (Fin.natAdd_injective _ _)] at hcard
  refine ⟨P,Q,?_,hcard⟩
  intro e he
  simpa [P,Q] using hT _ _ (of_edge E he)

lemma combine_bounds (E : Finset (Fin 10 × Fin 10)) (C : Circuit)
    (hl : 5 ≤ (E.image Prod.fst).card) (hr : 5 ≤ (E.image Prod.snd).card)
    (he : E.card ≤ 10)
    (hn : ∀ e ∈ E, ∃ f ∈ E, f ≠ e ∧ (f.1 = e.1 ∨ f.2 = e.2))
    (h4 : ∀ p q l s : Fin 10, p ≠ q → l ≠ s →
      ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E))
    (hao : PEqualNP.TopForm.IsAO2 20 C)
    (hspec : ∀ x : Fin 20 → Bool, circuitFun 20 C x =
      decide (∃ e ∈ E, x (Fin.castAdd 10 e.1) = true ∧ x (Fin.natAdd 10 e.2) = true)) :
    ∃ (P Q : Finset (Fin 10)), (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q) ∧
      E.card + P.card + Q.card ≤ C.size + 1 := by
  classical
  let G := graph E
  have rf := graph_rect E h4
  have sp := Sparsity.sparse_of_few_edges G color (graph_color E) rf
    (by rw [edge_card]; exact he) (support_bound E hl hr) (no_isolated E hn)
  have hmono : Monotone2 C := fun g hg => ⟨by simpa using hao.1 g hg, le_of_eq (hao.2.2 g hg)⟩
  let O : Finset (Fin C.gates.length) := Finset.univ.filter (fun i => (C.gates.get i).op = .or)
  let A : Finset (Fin C.gates.length) := Finset.univ.filter (fun i => (C.gates.get i).op = .and)
  have ors := orBound 20 G C (O.image Fin.val) sp (Sparsity.noFour_of_rectangle rf)
    hmono (spec_adj E C hspec) (by
      intro j g hg hop
      obtain ⟨hj,hget⟩ := List.getElem?_eq_some_iff.mp hg
      apply Finset.mem_image.mpr
      refine ⟨⟨j,hj⟩, ?_, rfl⟩
      simp [O,hget,hop])
  rw [edge_card,Finset.card_image_of_injective _ Fin.val_injective] at ors
  obtain ⟨D,_,hsize,hev⟩ := AndConv.convert 20 C hmono ⟨∅,by simp [hspec]⟩
  have hsizes : D.size ≤ A.card := by
    simpa [A,Nat.card_eq_fintype_card,Fintype.card_subtype] using hsize
  have hc : D.Computes G := by
    intro U
    rw [hev]
    exact (spec_adj E C hspec (fun x => decide (x ∈ U))).trans (by
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨a,b,hab,ha,hb⟩
        exact ⟨a,ha,b,hb,hab⟩
      · rintro ⟨a,ha,b,hb,hab⟩
        exact ⟨a,b,hab,ha,hb⟩)
  obtain ⟨T,hT,hcard⟩ := AndLower.and_bound G sp rf color (graph_color E) D hc
  have hdis : Disjoint A O := by
    rw [Finset.disjoint_left]
    intro i ha ho
    have ha' := (Finset.mem_filter.mp ha).2
    have ho' := (Finset.mem_filter.mp ho).2
    rw [ha'] at ho'
    cases ho'
  have hsum := Finset.card_le_card (Finset.subset_univ (A ∪ O))
  rw [Finset.card_union_of_disjoint hdis,Finset.card_univ,Fintype.card_fin] at hsum
  obtain ⟨P,Q,hPQ,hcardPQ⟩ := project_cover E T hT
  have : C.size = C.gates.length := rfl
  exact ⟨P,Q,hPQ,by omega⟩

end PEqualNP.Outside.L_meta_17707

theorem PEqualNP.Outside.L_meta_17707 : ∀ (x1 : Finset (Fin (10 : ℕ) × Fin (10 : ℕ))) (x2 : PEqualNP.CircuitLowerBounds.Circuit), (5 : ℕ) ≤ (Finset.image Prod.fst x1).card → (5 : ℕ) ≤ (Finset.image Prod.snd x1).card → x1.card ≤ (10 : ℕ) → (∀ x6 ∈ x1, ∃ x8 ∈ x1, x8 ≠ x6 ∧ (x8.1 = x6.1 ∨ x8.2 = x6.2)) → (∀ (x7 x8 x9 x10 : Fin (10 : ℕ)), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x1 ∧ (x7, x10) ∈ x1 ∧ (x8, x9) ∈ x1 ∧ (x8, x10) ∈ x1)) → PEqualNP.TopForm.IsAO2 (20 : ℕ) x2 → x2.size ≤ (14 : ℕ) → (∀ (x10 : Fin (20 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (20 : ℕ) x2 x10 = Decidable.decide (∃ x11 ∈ x1, x10 (Fin.castAdd (10 : ℕ) x11.1) = Bool.true ∧ x10 (Fin.natAdd (10 : ℕ) x11.2) = Bool.true)) → ∃ (x11 : Finset (Fin (10 : ℕ))) (x12 : Finset (Fin (10 : ℕ))), (∀ x13 ∈ x1, x13.1 ∈ x11 ∨ x13.2 ∈ x12) ∧ x1.card + x11.card + x12.card ≤ x2.size + (1 : ℕ) := by
  intro E C hl hr he hn h4 hao _ hspec
  exact PEqualNP.Outside.L_meta_17707.combine_bounds E C hl hr he hn h4 hao hspec
