import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

-- Pseudoforest OR bound adapted from accepted L_meta_599 (Apache-2.0).
namespace PEqualNP.Outside.L_meta_3754.CycleBound

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

private theorem release_prefix {n : ℕ} {gs : List Gate} {v : Fin n} (g : Gate)
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
    have no' : ¬ release gs v := fun h => no (release_prefix g h)
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

private theorem val_prefix {n : ℕ} (a b : List Gate) (x : Fin n → Bool) (w : ℕ) (hw : w<n+a.length) :
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
          exact (val_prefix a ([q]++b) z i hi).symm.trans hfull
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
        rw [hb,← ha,val_prefix (a++[h]) b x _ (by simp),new_val]
      have hdata : l.map (val a x)=l.map (val C.gates x) := by
        apply List.map_congr_left
        intro w hw
        rcases allowed w hw with h|rfl
        · rw [hb,List.append_assoc]
          exact (val_prefix a ([_]++b) x w (by omega)).symm
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

private theorem val_prefix {n : ℕ} (a b : List Gate) (x : Fin n → Bool) (w : ℕ)
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

theorem prefix_decision {n : ℕ} (pre post : List Gate) (g : Gate)
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
    (val_prefix (pre++[g]) post x _ (by simp)).trans (new_val pre g x)
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
          rw [List.append_assoc,val_prefix _ _ _ _ valid]
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
    rw [List.append_assoc,val_prefix _ _ _ _ h]
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
    rcases CycleCut599.prefix_decision (n:=n) pre post g ands hor hlen with copy | choice
    · exact False.elim (forbids_copy hm h hc hmin hj hor (CycleCut599.global_copy pre post g copy))
    · obtain ⟨X,Y,hx,hy,charges,bits⟩ := choice
      exact pay_from_bit hm h hc hmin hf degrees pre.length X Y hx hy
        (fun w hw => (charged_iff_release w pre.length).mpr (charges w hw)) bits

end Pseudoforest599

theorem edge_bound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset ℕ), (∀ S : Finset (Fin n), {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card) → (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → c.length ≠ 4) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → j ∈ A) → G.edgeSet.ncard ≤ A.card + 1 := by
  intro n G C A hs hf hm h hc
  exact PaidGraph599.edge_bound Pseudoforest599.pay_core hs hf hm h hc

end PEqualNP.Outside.L_meta_3754.CycleBound

namespace PEqualNP.Outside.L_meta_3754.CycleExamples
open PEqualNP.EdgeOwnership

def cycleEdges (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).map fun i => (i,(i+1)%n)

def cycle (n : ℕ) : SimpleGraph (Fin n) := edgeGraph n (cycleEdges n)

instance (n : ℕ) : DecidableRel (cycle n).Adj := by
  unfold cycle
  infer_instance

def finiteSparse {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  ∀ S : Finset (Fin n),(G.edgeFinset.filter fun e=>∀v∈e,v∈S).card≤S.card

def next {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

lemma cycle_adj {n : ℕ} (u v : Fin n) :
    (cycle n).Adj u v → next u=v ∨ next v=u := by
  rintro ⟨_,h | h⟩
  · obtain ⟨i,_,he⟩ := List.mem_map.mp h
    have hu : i=u.val := congrArg Prod.fst he
    have hv : (i+1)%n=v.val := congrArg Prod.snd he
    exact Or.inl (Fin.ext (by simpa only [next,hu] using hv))
  · obtain ⟨i,_,he⟩ := List.mem_map.mp h
    have hv : i=v.val := congrArg Prod.fst he
    have hu : (i+1)%n=u.val := congrArg Prod.snd he
    exact Or.inr (Fin.ext (by simpa only [next,hv] using hu))

lemma functional_sparse {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : Fin n → Fin n) (hf : ∀u v,G.Adj u v → f u=v ∨ f v=u) : finiteSparse G := by
  intro S
  have hsub : (G.edgeFinset.filter fun e=>∀v∈e,v∈S) ⊆
      S.image (fun i=>s(i,f i)) := by
    intro e he
    obtain ⟨he,hS⟩ := Finset.mem_filter.mp he
    induction e using Sym2.inductionOn with
    | _ u v =>
      have huv : G.Adj u v := by simpa using he
      rcases hf u v huv with h | h
      · exact Finset.mem_image.mpr ⟨u,hS u (by simp),by rw [h]⟩
      · exact Finset.mem_image.mpr ⟨v,hS v (by simp),by simp [h,Sym2.eq_swap]⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

lemma cycle_sparse (n : ℕ) : finiteSparse (cycle n) :=
  functional_sparse (cycle n) next cycle_adj

lemma cycle8_sparse : finiteSparse (cycle 8) := cycle_sparse 8
lemma cycle10_sparse : finiteSparse (cycle 10) := cycle_sparse 10

def leafNext (i : Fin 7) : Fin 7 :=
  if i=6 then 0 else ⟨(i.val+1)%6,by have := Nat.mod_lt (i.val+1) (by decide : 0<6);omega⟩

lemma cycleLeaf7_sparse : finiteSparse (edgeGraph 7
    [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),(0,6)]) := by
  apply functional_sparse _ leafNext
  decide +kernel

def tailNext (i : Fin 8) : Fin 8 :=
  if i=7 then 6 else if i=6 then 0 else
    ⟨(i.val+1)%6,by have := Nat.mod_lt (i.val+1) (by decide : 0<6);omega⟩

lemma cycleTail8_sparse : finiteSparse (edgeGraph 8
    [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),(0,6),(6,7)]) := by
  apply functional_sparse _ tailNext
  decide +kernel

lemma cycle8_edges : (cycle 8).edgeFinset.card=8 := by decide +kernel
lemma cycle10_edges : (cycle 10).edgeFinset.card=10 := by decide +kernel

lemma finiteSparse_set {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : finiteSparse G) (S : Finset (Fin n)) :
    {e : Sym2 (Fin n) | e∈G.edgeSet ∧ ∀v∈e,v∈S}.ncard≤S.card := by
  have he : {e : Sym2 (Fin n) | e∈G.edgeSet ∧ ∀v∈e,v∈S}=
      (↑(G.edgeFinset.filter fun e=>∀v∈e,v∈S) : Set (Sym2 (Fin n))) := by
    ext e
    simp
  rw [he,Set.ncard_coe_finset]
  exact h S

end PEqualNP.Outside.L_meta_3754.CycleExamples

namespace PEqualNP.Outside.L_meta_3754.CycleChecks
open PEqualNP.TopForm

lemma no_four_walk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (v : Fin n) (c : G.Walk v v) (hc : c.IsCycle) :
    c.length ≠ 4 := by
  intro hlen
  have h02 : c.getVert 0 ≠ c.getVert 2 := by
    intro h
    have he := hc.getVert_injOn' (by simp [hlen]) (by simp [hlen]) h
    omega
  have h13 : c.getVert 1 ≠ c.getVert 3 := by
    intro h
    have he := hc.getVert_injOn' (by simp [hlen]) (by simp [hlen]) h
    omega
  have h01 : G.Adj (c.getVert 0) (c.getVert 1) := c.adj_getVert_succ (by omega)
  have h21 : G.Adj (c.getVert 2) (c.getVert 1) := (c.adj_getVert_succ (i:=1) (by omega)).symm
  have h23 : G.Adj (c.getVert 2) (c.getVert 3) := c.adj_getVert_succ (by omega)
  have h03 : G.Adj (c.getVert 0) (c.getVert 3) := by
    have hh := (c.adj_getVert_succ (i:=3) (by omega)).symm
    simpa [←hlen] using hh
  have hbound := hG (c.getVert 0) (c.getVert 2) h02
  have hbig : 1 < (Finset.univ.filter fun w =>
      G.Adj (c.getVert 0) w ∧ G.Adj (c.getVert 2) w).card :=
    Finset.one_lt_card.mpr ⟨c.getVert 1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h01,h21⟩,
      c.getVert 3,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h03,h23⟩,h13⟩
  omega

end PEqualNP.Outside.L_meta_3754.CycleChecks

namespace PEqualNP.Outside.L_meta_3754.CycleExamples
open PEqualNP.EdgeOwnership PEqualNP.TopForm

set_option maxRecDepth 100000 in
lemma cycle8_no_four : NoFourCycle (cycle 8) := by decide +kernel

set_option maxRecDepth 100000 in
lemma cycle10_no_four : NoFourCycle (cycle 10) := by decide +kernel

lemma cycle8_no_four_walk (v : Fin 8) (c : (cycle 8).Walk v v) (hc : c.IsCycle) :
    c.length≠4 := CycleChecks.no_four_walk (cycle 8) cycle8_no_four v c hc

lemma cycle10_no_four_walk (v : Fin 10) (c : (cycle 10).Walk v v) (hc : c.IsCycle) :
    c.length≠4 := CycleChecks.no_four_walk (cycle 10) cycle10_no_four v c hc

end PEqualNP.Outside.L_meta_3754.CycleExamples
namespace PEqualNP.Outside.L_meta_3754.CycleExamples
open PEqualNP.EdgeOwnership PEqualNP.TopForm

def cycleLeaf7 : SimpleGraph (Fin 7) :=
  edgeGraph 7 [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),(0,6)]

instance : DecidableRel cycleLeaf7.Adj := by
  unfold cycleLeaf7
  infer_instance

set_option maxRecDepth 100000 in
lemma cycleLeaf7_no_four : NoFourCycle cycleLeaf7 := by decide +kernel

lemma cycleLeaf7_no_four_walk (v : Fin 7) (c : cycleLeaf7.Walk v v) (hc : c.IsCycle) :
    c.length≠4 := CycleChecks.no_four_walk cycleLeaf7 cycleLeaf7_no_four v c hc

lemma cycleLeaf7_edges : cycleLeaf7.edgeFinset.card=7 := by decide +kernel

end PEqualNP.Outside.L_meta_3754.CycleExamples
namespace PEqualNP.Outside.L_meta_3754.CycleExamples
open PEqualNP.EdgeOwnership PEqualNP.TopForm

def cycleTail8 : SimpleGraph (Fin 8) :=
  edgeGraph 8 [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),(0,6),(6,7)]

instance : DecidableRel cycleTail8.Adj := by
  unfold cycleTail8
  infer_instance

def cycleTail8Color (v : Fin 8) : Bool :=
  decide (v.val∈[1,3,5,6])

set_option maxRecDepth 100000 in
lemma cycleTail8_no_four : NoFourCycle cycleTail8 := by decide +kernel

lemma cycleTail8_no_four_walk (v : Fin 8) (c : cycleTail8.Walk v v) (hc : c.IsCycle) :
    c.length≠4 := CycleChecks.no_four_walk cycleTail8 cycleTail8_no_four v c hc

lemma cycleTail8_edges : cycleTail8.edgeFinset.card=8 := by decide +kernel

lemma cycleTail8_bipartite : ∀u v,cycleTail8.Adj u v → cycleTail8Color u≠cycleTail8Color v := by
  decide +kernel

end PEqualNP.Outside.L_meta_3754.CycleExamples
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
namespace PEqualNP.Outside.L_meta_3754.MaxFalse
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership Ledger

abbrev cycleTail8 : SimpleGraph (Fin 8) :=
  edgeGraph 8 [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),(0,6),(6,7)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cycleTail8_maxFalse_count : (maxFalseSet (graphFun cycleTail8 ∅)).card=9 := by
  decide

lemma cycleTail8_and_bound (C : Circuit) (hAO : IsAO2 8 C)
    (hc : circuitFun 8 C=graphFun cycleTail8 ∅) : 4≤C.gates.countP isAnd := by
  have h := count_bound_all hAO
  rw [hc,cycleTail8_maxFalse_count] at h
  by_contra hn
  have hle : C.gates.countP isAnd≤3 := by omega
  have hp := Nat.pow_le_pow_right (by decide : 1≤2) hle
  norm_num at hp
  omega

end PEqualNP.Outside.L_meta_3754.MaxFalse
namespace PEqualNP.Outside.L_meta_3754.CycleMinimum
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover

def isOr (g : Gate) : Bool :=
  match g.op with
  | .or => true
  | _ => false

def orSites (C : Circuit) : Finset (Fin C.gates.length) :=
  Finset.univ.filter fun k=>isOr (gateAt C k)=true

def orLabels (C : Circuit) : Finset ℕ := (orSites C).image Fin.val

lemma orSites_card (C : Circuit) : (orSites C).card=C.gates.countP isOr := by
  have heq : (fun k : Fin C.gates.length => gateAt C k)=fun k=>C.gates.get k := by
    funext k
    exact Ledger.gateAt_eq_getElem C k k.isLt
  have h := List.countP_ofFn (fun k : Fin C.gates.length => gateAt C k) isOr
  rw [heq,List.ofFn_get] at h
  simpa only [orSites,heq] using h.symm

lemma orLabels_card (C : Circuit) : (orLabels C).card=C.gates.countP isOr := by
  rw [orLabels,Finset.card_image_of_injective _ Fin.val_injective,orSites_card]

lemma counts_add (gs : List Gate)
    (h : ∀g∈gs,g.op=GateOp.and ∨ g.op=GateOp.or) :
    gs.countP MaxFalse.isAnd+gs.countP isOr=gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have ht := ih (fun a ha=>h a (List.mem_cons_of_mem g ha))
    rcases h g (by simp) with ha | ho
    · have hai : MaxFalse.isAnd g=true := by simp [MaxFalse.isAnd,ha]
      have hoi : isOr g=false := by simp [isOr,ha]
      simp [List.countP_cons,hai,hoi]
      omega
    · have hai : MaxFalse.isAnd g=false := by simp [MaxFalse.isAnd,ho]
      have hoi : isOr g=true := by simp [isOr,ho]
      simp [List.countP_cons,hai,hoi]
      omega

lemma or_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hs : CycleExamples.finiteSparse G) (hn : NoFourCycle G)
    (C : Circuit) (hAO : IsAO2 n C) (hf : circuitFun n C=graphFun G ∅) :
    G.edgeFinset.card≤C.gates.countP isOr+1 := by
  have hm : Monotone2 C := by
    intro g hg
    refine ⟨?_,(hAO.2.2 g hg).le⟩
    simpa using hAO.1 g hg
  have hdet : ∀x : Fin n → Bool,C.eval (List.ofFn x)=true ↔
      ∃u v : Fin n,G.Adj u v ∧ x u=true ∧ x v=true := by
    intro x
    change circuitFun n C x=true ↔ _
    rw [hf]
    simp [graphFun]
  have hc : ∀j g,C.gates[j]?=some g → g.op=GateOp.or → j∈orLabels C := by
    intro j g hj hg
    obtain ⟨hj,hget⟩ := List.getElem?_eq_some_iff.mp hj
    refine Finset.mem_image.mpr ⟨⟨j,hj⟩,?_,rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [Ledger.gateAt_eq_getElem C j hj,hget]
    simp [isOr,hg]
  have hb := CycleBound.edge_bound n G C (orLabels C)
    (CycleExamples.finiteSparse_set G hs) (CycleChecks.no_four_walk G hn) hm hdet hc
  rw [CycleBound.GraphInduction599.count_eq,orLabels_card] at hb
  convert hb using 1
  congr 1
  ext e
  simp

lemma cycle8_minimum (C : Circuit) (hAO : IsAO2 8 C)
    (hf : circuitFun 8 C=graphFun (CycleExamples.cycle 8) ∅) : 11≤C.size := by
  have ho := or_bound (CycleExamples.cycle 8) CycleExamples.cycle8_sparse
    CycleExamples.cycle8_no_four C hAO hf
  rw [CycleExamples.cycle8_edges] at ho
  have ha := MaxFalse.c8_and_bound C hAO hf
  have hc := counts_add C.gates hAO.1
  change 11≤C.gates.length
  omega

lemma cycle10_minimum (C : Circuit) (hAO : IsAO2 10 C)
    (hf : circuitFun 10 C=graphFun (CycleExamples.cycle 10) ∅) : 14≤C.size := by
  have ho := or_bound (CycleExamples.cycle 10) CycleExamples.cycle10_sparse
    CycleExamples.cycle10_no_four C hAO hf
  rw [CycleExamples.cycle10_edges] at ho
  have ha := MaxFalse.c10_and_bound C hAO hf
  have hc := counts_add C.gates hAO.1
  change 14≤C.gates.length
  omega

lemma cycleLeaf7_minimum (C : Circuit) (hAO : IsAO2 7 C)
    (hf : circuitFun 7 C=graphFun CycleExamples.cycleLeaf7 ∅) : 9≤C.size := by
  have ho := or_bound CycleExamples.cycleLeaf7 CycleExamples.cycleLeaf7_sparse
    CycleExamples.cycleLeaf7_no_four C hAO hf
  rw [CycleExamples.cycleLeaf7_edges] at ho
  have ha := MaxFalse.cycleLeaf7_and_bound C hAO hf
  have hc := counts_add C.gates hAO.1
  change 9≤C.gates.length
  omega

lemma cycleTail8_minimum (C : Circuit) (hAO : IsAO2 8 C)
    (hf : circuitFun 8 C=graphFun CycleExamples.cycleTail8 ∅) : 11≤C.size := by
  have ho := or_bound CycleExamples.cycleTail8 CycleExamples.cycleTail8_sparse
    CycleExamples.cycleTail8_no_four C hAO hf
  rw [CycleExamples.cycleTail8_edges] at ho
  have ha := MaxFalse.cycleTail8_and_bound C hAO hf
  have hc := counts_add C.gates hAO.1
  change 11≤C.gates.length
  omega

end PEqualNP.Outside.L_meta_3754.CycleMinimum
