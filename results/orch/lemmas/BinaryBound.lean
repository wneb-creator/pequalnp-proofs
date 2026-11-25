import Mathlib
import PEqualNP.Defs

-- Supporting proof adapted from the checked parent L_meta_2758.
-- Source revision 51ca0c7, original lines 3 through 2767.
namespace PEqualNP.Outside.R_meta_3178_52_support
namespace Binary
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace BranchGraph
variable {V : Type*} [DecidableEq V]
def containsEdge (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∃ a ∈ I,∃ b ∈ I,G.Adj a b
omit [DecidableEq V] in
lemma singleton_no_edge (G : SimpleGraph V) (w : V) : ¬ containsEdge G {w}:=by
  rintro ⟨a,ha,b,hb,hab⟩
  rw [Finset.mem_singleton] at ha hb
  subst a
  subst b
  exact G.loopless.irrefl w hab
lemma pair_contains_edge (G : SimpleGraph V) (u w : V) : containsEdge G {u,w}↔G.Adj u w:=by
  constructor
  · rintro ⟨a,ha,b,hb,hab⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.loopless.irrefl _ hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.loopless.irrefl _ hab).elim
  · intro h
    exact ⟨u,by simp,w,by simp,h⟩
def Independent (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ a ∈ S,∀ b ∈ S,¬ G.Adj a b
section FiniteGraph
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
def neighborsAfter (removed : Finset V) (u : V) : Finset V :=
  Finset.univ.filter (fun v => G.Adj u v /\ v ∉ removed)
lemma b31 {A B : Finset V} (h : A ⊆ B) (u : V) :
    neighborsAfter G B u ⊆ neighborsAfter G A u:=by
  intro v membership
  simp only [neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and] at membership ⊢
  exact ⟨membership.1,fun vIn => membership.2 (h vIn)⟩
lemma b85 {A B : Finset V} (h : A ⊆ B) {u w : V}
    (same : neighborsAfter G A u=neighborsAfter G A w) :
    neighborsAfter G B u=neighborsAfter G B w:=by
  have e (v : V) : neighborsAfter G B v=(neighborsAfter G A v).filter (· ∉ B):=by
    ext z
    simp only [neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun hz => ⟨⟨hz.1,fun zIn => hz.2 (h zIn)⟩,hz.2⟩,fun hz => ⟨hz.1.1,hz.2⟩⟩
  rw [e u,e w,same]
def TwinGroup (removed group : Finset V) : Prop :=
  ∀ u ∈ group,∀ w ∈ group,(neighborsAfter G removed u).Nonempty →
    (neighborsAfter G removed w).Nonempty -> neighborsAfter G removed u=neighborsAfter G removed w
def b106 (removed : Finset V) : Finset V :=
  Finset.univ.filter (fun v => neighborsAfter G removed v=∅)
def b24 (removed : Finset V) (root : V) : Finset V :=
  if root ∉ removed /\ (neighborsAfter G removed root).Nonempty then
    Finset.univ.filter (fun v => v ∉ removed /\ neighborsAfter G removed v=neighborsAfter G removed root)
  else ∅
def closeIsolates (removed : Finset V) : Finset V:=removed ∪ b106 G removed
def b20 (removed : Finset V) (root : V) : Finset V :=
  closeIsolates G (removed ∪ b24 G removed root)
lemma b29 (removed : Finset V) (root : V) : removed ⊆ b20 G removed root:=by
  intro u hu
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hu)
lemma b56 {removed : Finset V} (root u : V)
    (h : ¬ (neighborsAfter G removed u).Nonempty) : u ∈ b20 G removed root:=by
  have hn : ¬ (neighborsAfter G (removed ∪ b24 G removed root) u).Nonempty:=by
    intro existsNeighbor
    exact h (existsNeighbor.mono (b31 G Finset.subset_union_left u))
  have hu : u ∈ b106 G (removed ∪ b24 G removed root):=by
    simp [b106,Finset.not_nonempty_iff_eq_empty.mp hn]
  exact Finset.mem_union_right _ hu
lemma b175 [Nonempty V] {A B Q : Finset V} (smaller : A ⊆ B)
    (twins : TwinGroup G A Q) : ∃ root : V,A ∪ Q ⊆ b20 G B root:=by
  classical
  by_cases someActive : ∃ root ∈ Q,root ∉ B /\ (neighborsAfter G B root).Nonempty
  · obtain ⟨root,rootQ,rootOut,rootLive⟩:=someActive
    refine ⟨root,?_⟩
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact b29 G B root (smaller hu)
    by_cases uIn : u ∈ B
    · exact b29 G B root uIn
    by_cases live : (neighborsAfter G B u).Nonempty
    · have oldU:=live.mono (b31 G smaller u)
      have oldRoot:=rootLive.mono (b31 G smaller root)
      have same:=b85 G smaller (twins u hu root rootQ oldU oldRoot)
      have covered : u ∈ b24 G B root:=by simp [b24,rootOut,rootLive,uIn,same]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ covered)
    · exact b56 G root u live
  · let root : V:=Classical.choice inferInstance
    refine ⟨root,?_⟩
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact b29 G B root (smaller hu)
    by_cases uIn : u ∈ B
    · exact b29 G B root uIn
    exact b56 G root u (fun live => someActive ⟨u,hu,uIn,live⟩)
lemma b67 {removed : Finset V} {u : V} (out : u ∉ closeIsolates G removed) :
    (neighborsAfter G (closeIsolates G removed) u).Nonempty:=by
  have uOut : u ∉ removed:=fun h => out (Finset.mem_union_left _ h)
  have old : (neighborsAfter G removed u).Nonempty:=by
    by_contra empty
    apply out
    apply Finset.mem_union_right
    simp [b106,Finset.not_nonempty_iff_eq_empty.mp empty]
  obtain ⟨v,hv⟩:=old
  simp only [neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and] at hv
  refine ⟨v,?_⟩
  simp only [neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and]
  refine ⟨hv.1,fun dropped => ?_⟩
  rcases Finset.mem_union.mp dropped with h | h
  · exact hv.2 h
  · have witness : u ∈ neighborsAfter G removed v:=by
      simp only [neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨hv.1.symm,uOut⟩
    have none : neighborsAfter G removed v=∅:=by simpa [b106] using h
    rw [none] at witness
    exact Finset.notMem_empty _ witness
lemma b51 (removed : Finset V) :
    closeIsolates G (closeIsolates G removed)=closeIsolates G removed:=by
  apply Finset.Subset.antisymm
  · intro u hu
    rcases Finset.mem_union.mp hu with already | isolated
    · exact already
    by_contra out
    have live:=b67 G out
    have noNeighbors : neighborsAfter G (closeIsolates G removed) u=∅:=by
      simpa [b106] using isolated
    simpa [noNeighbors] using live
  · exact Finset.subset_union_left
def b60 : Finset V -> List (Finset V) -> Prop
  | _,[] => True
  | removed,group :: rest => TwinGroup G removed group /\ b60 (removed ∪ group) rest
def b13 : Finset V -> List (Finset V) -> Finset V
  | removed,[] => removed
  | removed,group :: rest => b13 (removed ∪ group) rest
def b102 : ℕ -> Finset V -> Finset V -> Prop
  | 0,start,finish => finish=start
  | k + 1,start,finish => ∃ root : V,b102 k (b20 G start root) finish
lemma b169 [Nonempty V] {A B : Finset V} (groups : List (Finset V))
    (smaller : A ⊆ B) (steps : b60 G A groups) :
    ∃ finish : Finset V,b102 G groups.length B finish /\ b13 A groups ⊆ finish:=by
  induction groups generalizing A B with
  | nil => exact ⟨B,rfl,smaller⟩
  | cons group rest ih =>
    obtain ⟨twins,next⟩:=steps
    obtain ⟨root,subset⟩:=b175 G smaller twins
    obtain ⟨finish,walk,covered⟩:=ih subset next
    exact ⟨finish,⟨root,walk⟩,covered⟩
def b19 (removed : Finset V) : Prop :=
  ∀ u v,u ∉ removed -> v ∉ removed -> ¬ G.Adj u v
omit [Fintype V] [DecidableRel G.Adj] in
lemma b178 {A B : Finset V} (subset : A ⊆ B) (noEdges : b19 G A) :
    b19 G B:=by
  intro u v uOut vOut
  exact noEdges u v (fun h => uOut (subset h)) (fun h => vOut (subset h))
lemma b134 {D : Finset V} (noEdges : b19 G (closeIsolates G D)) :
    closeIsolates G D=Finset.univ:=by
  ext u
  simp only [Finset.mem_univ,iff_true]
  by_contra out
  obtain ⟨v,hv⟩:=b67 G out
  simp only [neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and] at hv
  exact noEdges u v out hv.2 hv.1
lemma b99 {k : ℕ} {start finish : Finset V} (walk : b102 G k start finish)
    (closed : ∃ D : Finset V,start=closeIsolates G D) : ∃ D : Finset V,finish=closeIsolates G D:=by
  induction k generalizing start with
  | zero =>
    change finish=start at walk
    rw [walk]
    exact closed
  | succ k ih =>
    obtain ⟨root,after⟩:=walk
    exact ih after ⟨_,rfl⟩
lemma b58 [Nonempty V] (groups : List (Finset V))
    (twins : b60 G ∅ groups) (finished : b19 G (b13 ∅ groups)) :
    b102 G groups.length (closeIsolates G ∅) Finset.univ:=by
  obtain ⟨D,steps,subset⟩:=b169 G groups (Finset.empty_subset (closeIsolates G ∅)) twins
  have noEdges:=b178 G subset finished
  obtain ⟨A,hD⟩:=b99 G steps ⟨∅,rfl⟩
  rw [hD] at noEdges
  rwa [hD,b134 G noEdges] at steps
end FiniteGraph
end BranchGraph
namespace BranchGroupsLean
open BranchGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {m : Nat}
def bucket (label : V -> Fin m) (r : Fin m) : Finset V:=Finset.univ.filter (fun v => label v=r)
def below (label : V -> Fin m) (r : Fin m) : Finset V:=Finset.univ.filter (fun v => label v < r)
def b23 (label : V -> Fin m) (done : List (Fin m)) : Finset V :=
  Finset.univ.filter (fun v => label v ∈ done)
omit [DecidableEq V] in
@[simp] lemma coveredBy_nil (label : V -> Fin m) : b23 label []=∅:=by
  ext v
  simp [b23]
lemma b36 (label : V -> Fin m) (done : List (Fin m)) (r : Fin m) :
    b23 label (done ++ [r])=b23 label done ∪ bucket label r:=by
  ext v
  simp [b23,bucket,List.mem_append]
omit [DecidableEq V] in
lemma b98 (label : V -> Fin m) (out : Fin m) (done rest : List (Fin m)) (r : Fin m)
    (sorted : (done ++ r :: rest).Pairwise (· < ·))
    (roots : ∀ v : V,label v=out \/ label v ∈ done ++ r :: rest)
    (beforeOut : r < out) : b23 label done=below label r:=by
  have facts:=List.pairwise_append.mp sorted
  ext v
  simp only [b23,below,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro member
    exact facts.2.2 _ member r (by simp)
  · intro earlier
    rcases roots v with isOut | member
    · rw [isOut] at earlier
      exact (lt_asymm earlier beforeOut).elim
    rcases List.mem_append.mp member with doneMember | coming
    · exact doneMember
    rcases List.mem_cons.mp coming with atRoot | later
    · exact (ne_of_lt earlier atRoot).elim
    have after:=(List.pairwise_cons.mp facts.2.1).1 _ later
    exact (lt_asymm earlier after).elim
section Graph
variable (G : SimpleGraph V) [DecidableRel G.Adj]
lemma b110 (label : V -> Fin m) (out : Fin m) (roots : List (Fin m))
    (sorted : roots.Pairwise (· < ·)) (allRoots : ∀ v : V,label v=out \/ label v ∈ roots)
    (beforeOut : ∀ r ∈ roots,r < out)
    (twinAt : ∀ r ∈ roots,TwinGroup G (below label r) (bucket label r))
    (done pending : List (Fin m)) (complete : done ++ pending=roots) :
    b60 G (b23 label done) (pending.map (bucket label)):=by
  induction pending generalizing done with
  | nil => exact True.intro
  | cons r tail ih =>
    have rMember : r ∈ roots:=complete ▸ List.mem_append_right done (by simp : r ∈ r :: tail)
    have prev:=b98 label out done tail r (by simpa only [complete] using sorted)
      (fun v => by simpa only [complete] using allRoots v) (beforeOut r rMember)
    have next:=ih (done ++ [r]) (by simpa [List.append_assoc] using complete)
    refine ⟨?_,?_⟩
    · rw [prev]
      exact twinAt r rMember
    · rwa [b36] at next
lemma b96 (label : V -> Fin m) (done pending : List (Fin m)) :
    b13 (b23 label done) (pending.map (bucket label))=b23 label (done ++ pending):=by
  induction pending generalizing done with
  | nil => simp [b13]
  | cons r tail ih =>
    change b13 (b23 label done ∪ bucket label r) (tail.map (bucket label))=_
    rw [← b36,ih]
    simp [List.append_assoc]
omit [DecidableRel G.Adj] in
lemma b105 (label : V -> Fin m) (out : Fin m) (roots : List (Fin m))
    (allRoots : ∀ v : V,label v=out \/ label v ∈ roots)
    (outputIndependent : Independent G (bucket label out)) :
    b19 G (b13 ∅ (roots.map (bucket label))):=by
  rw [← coveredBy_nil label,b96,List.nil_append]
  intro u v uNot vNot
  have hu : label u=out:=(allRoots u).resolve_right (by simpa [b23] using uNot)
  have hv : label v=out:=(allRoots v).resolve_right (by simpa [b23] using vNot)
  exact outputIndependent u (by simp [bucket,hu]) v (by simp [bucket,hv])
lemma roots_required (label : V -> Fin m) (out : Fin m) (branches : Finset (Fin m)) (k : Nat)
    (allRoots : ∀ v : V,label v=out \/ label v ∈ branches)
    (beforeOut : ∀ r ∈ branches,r < out)
    (twinAt : ∀ r ∈ branches,TwinGroup G (below label r) (bucket label r))
    (outputIndependent : Independent G (bucket label out))
    (required : ∀ groups : List (Finset V),b60 G ∅ groups →
      b19 G (b13 ∅ groups) -> k ≤ groups.length) : k ≤ branches.card:=by
  let roots:=branches.sort
  have sorted : roots.Pairwise (· < ·):=List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort branches)
  have covers (v : V) : label v=out \/ label v ∈ roots:=by simpa [roots] using allRoots v
  have early (r) (member : r ∈ roots) : r < out:=beforeOut r (by simpa [roots] using member)
  have twins (r) (member : r ∈ roots) : TwinGroup G (below label r) (bucket label r) :=
    twinAt r (by simpa [roots] using member)
  have valid : b60 G ∅ (roots.map (bucket label)):=by
    simpa using b110 G label out roots sorted covers early twins [] roots rfl
  have last:=b105 G label out roots covers outputIndependent
  simpa [roots] using required (roots.map (bucket label)) valid last
end Graph
end BranchGroupsLean
namespace CircuitProof
open PEqualNP.CircuitLowerBounds
def b1 (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
lemma b42 (gs gs' : List Gate) (w : List Bool) :
    b1 (gs ++ gs') w=b1 gs' (b1 gs w):=by
  simp [b1,List.foldl_append]
lemma b61 (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool,b1 gs w=w ++ t /\ t.length=gs.length:=by
  induction gs with
  | nil => intro w; exact ⟨[],by simp [b1],rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t,ht,hl⟩:=ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t,?_,by simp [hl]⟩
    have : b1 (g :: gs) w
       =b1 gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]):=rfl
    rw [this,ht]; simp
lemma b28 (gs : List Gate) (w : List Bool) :
    (b1 gs w).length=w.length + gs.length:=by
  obtain ⟨t,ht,hl⟩:=b61 gs w
  rw [ht]; simp [hl]
lemma b41 (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (b1 gs w).getD i false=w.getD i false:=by
  obtain ⟨t,ht,_⟩:=b61 gs w
  rw [ht,List.getD_append _ _ _ _ h]
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) /\ g.inputs.length ≤ 2
end CircuitProof
namespace CircuitProof
open PEqualNP.CircuitLowerBounds
variable {n : ℕ}
lemma b33 {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j≠L.length) :
    (L ++ [S]).getD j d=L.getD j d:=by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
lemma b50 {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d=S:=by
  simp
end CircuitProof
namespace CircuitProof
open PEqualNP.CircuitLowerBounds
def NOk (g : Gate) : Prop:=Ok g /\ (g.op=GateOp.not -> g.inputs.length ≤ 1)
abbrev Stat:=Sum Bool ℕ
def Stat.val (w : List Bool) : Stat -> Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false
def Stat.Valid (m : ℕ) : Stat -> Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m
def b162 (m : ℕ) : List Stat -> Option Gate × Stat
  | [] => (none,Sum.inl true)
  | Sum.inl c :: _ => (none,Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not,[j]⟩,Sum.inr m)
def b145 (m : ℕ) : List Stat -> Option Gate × Stat
  | [] => (none,Sum.inl true)
  | [Sum.inl c] => (none,Sum.inl c)
  | [Sum.inr j] => (none,Sum.inr j)
  | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c&&d))
  | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.and,[j,k]⟩,Sum.inr m)
  | _ => (none,Sum.inl false)
def simpOr (m : ℕ) : List Stat -> Option Gate × Stat
  | [] => (none,Sum.inl false)
  | [Sum.inl c] => (none,Sum.inl c)
  | [Sum.inr j] => (none,Sum.inr j)
  | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c||d))
  | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.or,[j,k]⟩,Sum.inr m)
  | _ => (none,Sum.inl false)
def b12 (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => b145 m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => b162 m ins
  | _ => (none,Sum.inl false)
lemma b172 (op : GateOp) (hop : op=GateOp.and \/ op=GateOp.or \/ op=GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins,s.Valid w.length) :
    ((b12 op w.length ins).2).Valid (w.length + (b12 op w.length ins).1.toList.length) ∧
    ((b12 op w.length ins).2).val (b1 (b12 op w.length ins).1.toList w)
     =op.eval (ins.map (Stat.val w)):=by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
    · simp [b12,b145,Stat.Valid,Stat.val,GateOp.eval]
    · cases a <;> simp_all [b12,b145,Stat.Valid,Stat.val,GateOp.eval,b1]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [b12,b145,Stat.Valid,Stat.val,GateOp.eval,b1]
    · simp at hlen
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
    · simp [b12,simpOr,Stat.Valid,Stat.val,GateOp.eval]
    · cases a <;> simp_all [b12,simpOr,Stat.Valid,Stat.val,GateOp.eval,b1]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [b12,simpOr,Stat.Valid,Stat.val,GateOp.eval,b1]
    · simp at hlen
  · rcases ins with _ | ⟨a,l⟩
    · simp [b12,b162,Stat.Valid,Stat.val,GateOp.eval]
    · cases a <;> simp_all [b12,b162,Stat.Valid,Stat.val,GateOp.eval,b1]
def b43 (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(b12 g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (b12 g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)
def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (b43 n) acc
lemma b140 {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length=k) :
    (L ++ [S]).getD k d=S:=by
  subst h; simp
lemma b156 {α : Type} (o : Option α) : o.toList.length ≤ 1:=by
  cases o <;> simp
lemma elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length:=by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1:=ih (b43 n acc g)
    have h2 : (b43 n acc g).2.length ≤ acc.2.length + 1:=by
      simp only [b43,List.length_append]
      have:=b156 (b12 g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc=elim n gs (b43 n acc g):=rfl
    rw [h3,List.length_cons]; omega
lemma Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat,s.Valid m -> s.Valid m'
  | Sum.inl _,_ => trivial
  | Sum.inr _,hj => lt_of_lt_of_le hj h
lemma Stat.val_append (w t : List Bool) : ∀ s : Stat,s.Valid w.length →
    s.val (w ++ t)=s.val w
  | Sum.inl _,_ => rfl
  | Sum.inr _,hj => List.getD_append _ _ _ _ hj
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length=w.length /\ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (b1 acc.2 y)=w.getD i false
lemma b139 (n : ℕ) (y : List Bool) (hy : y.length=n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate),(∀ g ∈ gs,Ok g) -> Inv n y w acc →
      Inv n y (b1 gs w) (elim n gs acc):=by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (b43 n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl,hi⟩:=h
    set w':=b1 acc.2 y with hw'
    have lw' : w'.length=n + acc.2.length:=by rw [hw',b28,hy]
    set ins:=g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok:=hok g List.mem_cons_self
    have hs:=b172 g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r:=b12 g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w')=g.inputs.map fun i => w.getD i false:=by
      rw [hins,List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : b1 (acc.2 ++ r.1.toList) y=b1 r.1.toList w':=by
      rw [b42]
    obtain ⟨t,ht,htl⟩:=b61 r.1.toList w'
    refine ⟨by simp [b43,hl],?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (b1 (acc.2 ++ r.1.toList) y)=_
    rw [hnew,List.length_append,← Nat.add_assoc]
    by_cases hil : i=acc.1.length
    · subst hil
      rw [b50,hl,b50]
      exact ⟨hs.1,by rw [hs.2,hvals]⟩
    · rw [b33 _ _ _ _ hil,b33 _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1,?_⟩
      rw [ht,Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2
def isNotGate (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false
def b47 (test : GateOp -> Bool) (gs : List Gate) : ℕ :=
  gs.countP (fun g => test g.op)
lemma b157 (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (b12 op m ins).1,g.op=op:=by
  intro g hg
  cases op <;> simp only [b12] at hg
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [b145] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;>
      simp [b162] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg
lemma b174 (test : GateOp -> Bool) (gs hs : List Gate) :
    b47 test (gs ++ hs)=b47 test gs + b47 test hs:=by
  simp [b47]
lemma b151 (test : GateOp -> Bool) (g : Gate) (gs : List Gate) :
    b47 test (g :: gs)=b47 test gs + (if test g.op then 1 else 0):=by
  by_cases h : test g.op <;> simp [b47,h]
lemma b133 (test : GateOp -> Bool) (op : GateOp) (m : ℕ) (ins : List Stat) :
    b47 test (b12 op m ins).1.toList ≤ (if test op then 1 else 0):=by
  cases h : (b12 op m ins).1 with
  | none => simp [b47]
  | some g =>
    have hg : g ∈ (b12 op m ins).1:=by simp [h]
    have he:=b157 op m ins g hg
    simp [h,b151,b47,he]
lemma b167 (test : GateOp -> Bool) (n : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      b47 test (elim n gs acc).2 ≤ b47 test acc.2 + b47 test gs:=by
  induction gs with
  | nil => intro acc; simp [elim,b47]
  | cons g gs ih =>
    intro acc
    change b47 test (elim n gs (b43 n acc g)).2 ≤ _
    apply (ih (b43 n acc g)).trans
    simp only [b43,b174,b151]
    have hb:=b133 test g.op (n + acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
    omega
def nonNotCount (gs : List Gate) : ℕ :=
  gs.countP (fun g => !(isNotGate g.op))
lemma b65 (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    nonNotCount (elim n gs acc).2 ≤ nonNotCount acc.2 + nonNotCount gs :=
  b167 (fun op => !(isNotGate op)) n gs acc
end CircuitProof
namespace CircuitProof
open PEqualNP.CircuitLowerBounds
def b101 (m : ℕ) (g : Gate) : Prop :=
  (g.op=GateOp.not /\ ∃ j,j < m /\ g.inputs=[j]) ∨
  ((g.op=GateOp.and \/ g.op=GateOp.or) /\ ∃ j k,j < m /\ k < m /\ g.inputs=[j,k])
def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate),gs[p]?=some g -> b101 (m + p) g
lemma b101.nok {m : ℕ} {g : Gate} (h : b101 m g) : NOk g:=by
  rcases h with ⟨h1,j,_,h2⟩ | ⟨h1 | h1,j,k,_,_,h2⟩
  · refine ⟨⟨?_,?_⟩,?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_,?_⟩,?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_,?_⟩,?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
lemma b101.lt {m : ℕ} {g : Gate} (h : b101 m g) : ∀ a ∈ g.inputs,a < m:=by
  intro a ha
  rcases h with ⟨_,j,hj,h2⟩ | ⟨_,j,k,hj,hk,h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk
lemma b188 (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs,NOk g:=by
  intro g hg
  obtain ⟨p,hp⟩:=List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok
lemma b173 (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins,s.Valid m) :
    ∀ g ∈ (b12 op m ins).1,b101 m g:=by
  intro g hg
  cases op <;> simp only [b12] at hg
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [b145] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl,_,_,?_,?_,rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl,_,_,?_,?_,rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;> simp [b162] at hg
    subst hg
    refine Or.inl ⟨rfl,_,?_,rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg
lemma b171? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]?=some a) : k=0 /\ a ∈ o:=by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h
lemma b150 (n : ℕ) (y : List Bool) (hy : y.length=n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate),(∀ g ∈ gs,Ok g) -> Inv n y w acc →
      CleanL n acc.2 -> CleanL n (elim n gs acc).2:=by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (b1 [g] w) (b43 n acc g) :=
      b139 n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (b43 n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (b12 g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)[p]?=some g':=hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0,hmem⟩:=b171? _ _ _ hp'
      have hpl : p=acc.2.length:=by omega
      rw [hpl]
      exact b173 _ _ _ (fun s hs => by
        obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem
def b9 (n : ℕ) : List Stat:=List.ofFn (fun i : Fin n => Sum.inr i)
lemma inv_id (n : ℕ) (y : Fin n -> Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (b9 n,[]):=by
  refine ⟨by simp [b9],?_⟩
  intro i
  by_cases hlt : i < n
  · simp [b9,hlt,Stat.Valid,Stat.val,b1]
  · rw [List.getD_eq_default _ _ (by simp [b9]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial,rfl⟩
lemma b165 {α : Type} (m : ℕ) (F : Fin m -> α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d=F j:=by
  simp
lemma split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α),l[p]?=some g →
    ∃ pre post,l=pre ++ g :: post /\ pre.length=p:=by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[],l,rfl,rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre,post,rfl,rfl⟩:=ih p g h
      exact ⟨x :: pre,post,rfl,rfl⟩
lemma b190 (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs,k ∉ g.inputs) -> w.length=w'.length →
    (∀ j,j≠k -> w.getD j false=w'.getD j false) →
    ∀ j,j≠k -> (b1 gs w).getD j false=(b1 gs w').getD j false:=by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno':=hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false)=g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j=w.length
    · rw [hjl,b50,hl,b50,e]
    · rw [b33 _ _ _ _ hjl,b33 _ _ _ _ (by omega)]
      exact h j hj
end CircuitProof
namespace CircuitProof
open PEqualNP.CircuitLowerBounds
def vl {k : ℕ} (gs : List Gate) (u : Fin k -> Bool) (j : ℕ) : Bool :=
  (b1 gs (List.ofFn u)).getD j false
lemma b69 {k : ℕ} (gs : List Gate) (u : Fin k -> Bool) (j : ℕ) (h : j < k) :
    vl gs u j=u ⟨j,h⟩:=by
  unfold vl
  rw [b41 gs _ j (by simpa using h)]
  exact b165 k u false ⟨j,h⟩
lemma b104 {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k -> Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]?=some g) :
    vl gs u (k + p)=g.op.eval (g.inputs.map (vl gs u)):=by
  have hlt:=(hcl p g hp).lt
  obtain ⟨pre,post,rfl,rfl⟩:=split_at gs p g hp
  have hwl : (b1 pre (List.ofFn u)).length=k + pre.length:=by
    rw [b28]; simp
  have e : b1 (pre ++ g :: post) (List.ofFn u)
     =b1 post (b1 pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (b1 pre (List.ofFn u)).getD i false)]):=by
    rw [b42]; rfl
  have full : ∀ j,j < k + pre.length →
      (b1 (pre ++ g :: post) (List.ofFn u)).getD j false
       =(b1 pre (List.ofFn u)).getD j false:=by
    intro j hj
    rw [e,b41 _ _ j (by simp [hwl]; omega),b33 _ _ _ _ (by omega)]
  have top : (b1 (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
     =g.op.eval (g.inputs.map fun i => (b1 pre (List.ofFn u)).getD i false):=by
    rw [e,b41 _ _ _ (by simp [hwl]),b140 _ _ _ _ hwl]
  show (b1 (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
   =g.op.eval (g.inputs.map fun j => (b1 (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm
lemma vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k -> Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]?=some g) (h : ∀ a ∈ g.inputs,vl gs u a=vl gs u' a) :
    vl gs u (k + p)=vl gs u' (k + p):=by
  rw [b104 gs hcl u p g hp,b104 gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h
lemma drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k -> Bool,S.Valid (k + (elim k pre (b9 k,[])).2.length) ∧
      S.val (b1 (elim k pre (b9 k,[])).2 (List.ofFn y))
       =vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k -> Bool,vl (pre ++ g :: post) y o≠vl (pre ++ g :: post) y' o) :
    ∃ gs' o',CleanL k gs' /\ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      nonNotCount gs' ≤ nonNotCount pre + nonNotCount post ∧
      ∀ y : Fin k -> Bool,vl gs' y o'=vl (pre ++ g :: post) y o:=by
  have hok : ∀ g' ∈ pre ++ g :: post,Ok g':=fun g' hg' => (b188 _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre,Ok g':=fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post,Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k -> Bool,Inv k (List.ofFn y) (b1 pre (List.ofFn y))
      (elim k pre (b9 k,[])) :=
    fun y => b139 k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k -> Bool,(b1 pre (List.ofFn y)).length=k + pre.length:=by
    intro y; rw [b28]; simp
  have hfull : ∀ y : Fin k -> Bool,b1 (pre ++ g :: post) (List.ofFn y)
     =b1 post (b1 pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (b1 pre (List.ofFn y)).getD a false)]):=by
    intro y; rw [b42]; rfl
  have hgv : ∀ y : Fin k -> Bool,vl (pre ++ g :: post) y (k + pre.length)
     =g.op.eval (g.inputs.map fun a => (b1 pre (List.ofFn y)).getD a false):=by
    intro y
    show (b1 (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false=_
    rw [hfull,b41 _ _ _ (by simp [hwl y]),b140 _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k -> Bool,Inv k (List.ofFn y)
      (b1 pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (b1 pre (List.ofFn y)).getD a false)])
      ((elim k pre (b9 k,[])).1 ++ [S],(elim k pre (b9 k,[])).2):=by
    intro y
    obtain ⟨hl,hi⟩:=inv1 y
    refine ⟨by simp [hl],?_⟩
    intro a
    show (((elim k pre (b9 k,[])).1 ++ [S]).getD a (Sum.inl false)).Valid
        (k + (elim k pre (b9 k,[])).2.length) ∧
      (((elim k pre (b9 k,[])).1 ++ [S]).getD a (Sum.inl false)).val
        (b1 (elim k pre (b9 k,[])).2 (List.ofFn y))=_
    by_cases hal : a=(elim k pre (b9 k,[])).1.length
    · rw [hal,b50,hl,b50]
      exact ⟨(hS y).1,by rw [(hS y).2,hgv]⟩
    · rw [b33 _ _ _ _ hal,b33 _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k -> Bool,Inv k (List.ofFn y)
      (b1 (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (b9 k,[])).1 ++ [S],(elim k pre (b9 k,[])).2)):=by
    intro y
    rw [hfull]
    exact b139 k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (b9 k,[])).2 :=
    b150 k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (b9 k,[])).1 ++ [S],(elim k pre (b9 k,[])).2)).2 :=
    b150 k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (b9 k,[])).1 ++ [S],
      (elim k pre (b9 k,[])).2)).2.length + 1 ≤ (pre ++ g :: post).length:=by
    have h1 : (elim k post ((elim k pre (b9 k,[])).1 ++ [S],
        (elim k pre (b9 k,[])).2)).2.length
        ≤ (elim k pre (b9 k,[])).2.length + post.length:=elim_len k post _
    have h2 : (elim k pre (b9 k,[])).2.length ≤ 0 + pre.length :=
      elim_len k pre (b9 k,[])
    simp only [List.length_append,List.length_cons]
    omega
  have hval : ∀ y : Fin k -> Bool,
      ((elim k post ((elim k pre (b9 k,[])).1 ++ [S],
        (elim k pre (b9 k,[])).2)).1.getD o (Sum.inl false)).val
        (b1 (elim k post ((elim k pre (b9 k,[])).1 ++ [S],
          (elim k pre (b9 k,[])).2)).2 (List.ofFn y))
     =vl (pre ++ g :: post) y o:=fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (b9 k,[])).1 ++ [S],
      (elim k pre (b9 k,[])).2)).1.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y,y',hne⟩:=hnc
    apply hne
    rw [← hval y,← hval y',hst]
    rfl
  | inr j =>
    refine ⟨_,j,hc3,hlen,?_,?_⟩
    · exact (b65 k post _).trans (Nat.add_le_add_right
        (by simpa [nonNotCount] using b65 k pre (b9 k,[])) _)
    · intro y
      have h:=hval y
      rw [hst] at h
      exact h
lemma b177 (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k -> Bool,vl gs y (k + p)=vl gs y j)
    (hnc : ∃ y y' : Fin k -> Bool,vl gs y o≠vl gs y' o) :
    ∃ gs' o',CleanL k gs' /\ gs'.length + 1 ≤ gs.length /\ nonNotCount gs' ≤ nonNotCount (gs.eraseIdx p) ∧
      ∀ y : Fin k -> Bool,vl gs' y o'=vl gs y o:=by
  obtain ⟨g,hg⟩ : ∃ g,gs[p]?=some g:=⟨gs[p],List.getElem?_eq_getElem hp⟩
  obtain ⟨pre,post,rfl,rfl⟩:=split_at gs p g hg
  rw [List.eraseIdx_append_of_length_le le_rfl,Nat.sub_self,List.eraseIdx_cons_zero]
  have hcount : nonNotCount (pre ++ post)=nonNotCount pre + nonNotCount post:=by
    simp [nonNotCount]
  rw [hcount]
  apply drop_core k pre g post hcl o ((elim k pre (b9 k,[])).1.getD j (Sum.inl false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre,Ok g' :=
    fun g' h => (b188 _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1:=b139 k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1,?_⟩
  rw [(inv1.2 j).2,heq y]
  show (b1 pre (List.ofFn y)).getD j false
   =(b1 (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [b42,b41 (g :: post) (b1 pre (List.ofFn y)) j
    (by rw [b28]; simp; omega)]
end CircuitProof
namespace PetersenCutTrace
open PEqualNP.CircuitLowerBounds
open CircuitProof
def avoid {W : Type} (edge : W -> W -> Prop) (cut : W) (a b : W) : Prop :=
  edge a b /\ a≠cut /\ b≠cut
lemma b147 {W : Type} (rank : W -> Nat) (input : W -> Prop)
    (edge : W -> W -> Prop) (cut : W) (x y : W -> Bool)
    (order : ∀ a b,edge a b -> rank a < rank b)
    (localStep : ∀ b,¬ input b -> x b≠y b -> ∃ a,edge a b /\ x a≠y a)
    (sameCut : x cut=y cut) {out : W} (different : x out≠y out) :
    ∃ a,input a /\ x a≠y a /\ Relation.ReflTransGen (avoid edge cut) a out:=by
  classical
  have track : ∀ k b,rank b=k -> x b≠y b →
      ∃ a,input a /\ x a≠y a /\ Relation.ReflTransGen (avoid edge cut) a b:=by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro b hb diff
      by_cases hInput : input b
      · exact ⟨b,hInput,diff,Relation.ReflTransGen.refl⟩
      · obtain ⟨p,hp,dp⟩:=localStep b hInput diff
        have earlier : rank p < k:=(order p b hp).trans_eq hb
        obtain ⟨a,ha,da,path⟩:=ih (rank p) earlier p rfl dp
        have pOff : p≠cut:=by rintro rfl; exact dp sameCut
        have bOff : b≠cut:=by rintro rfl; exact diff sameCut
        exact ⟨a,ha,da,path.tail ⟨hp,pOff,bOff⟩⟩
  exact track (rank out) out rfl different
lemma b180 {W : Type} (rank : W -> Nat) (input : W -> Prop)
    (edge : W -> W -> Prop) (cut out : W) (x y : W -> Bool)
    (order : ∀ a b,edge a b -> rank a < rank b)
    (localStep : ∀ b,¬ input b -> x b≠y b -> ∃ a,edge a b /\ x a≠y a)
    (sameCut : x cut=y cut)
    (blocked : ∀ a,input a -> x a≠y a →
      ¬ Relation.ReflTransGen (avoid edge cut) a out) : x out=y out:=by
  by_contra different
  obtain ⟨a,ha,da,reaches⟩:=b147 rank input edge cut x y
    order localStep sameCut different
  exact blocked a ha da reaches
lemma b184 {A : Type} (w f : A -> Bool)
    (h : ∀ x y,w x=w y -> f x=f y) :
    ∃ outer : Bool -> Bool,∀ x,outer (w x)=f x:=by
  classical
  let outer (b : Bool):=if hb : ∃ a,w a=b then f (Classical.choose hb) else false
  refine ⟨outer,fun x => ?_⟩
  have hx : ∃ a,w a=w x:=⟨x,rfl⟩
  unfold outer
  rw [dite_eq_left hx]
  exact h _ _ (Classical.choose_spec hx)
def b8 {n : Nat} (gs : List Gate) (v : Fin n) : Fin (n + gs.length) :=
  v.castLE (Nat.le_add_right n gs.length)
def b5 {n : Nat} (gs : List Gate) (a b : Fin (n + gs.length)) : Prop :=
  ∃ (p : Nat) (g : Gate),gs[p]?=some g /\ b.val=n + p /\ a.val ∈ g.inputs
lemma b15 {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    {a b : Fin (n + gs.length)} (edge : b5 gs a b) : a.val < b.val:=by
  obtain ⟨p,g,hpg,hb,ha⟩:=edge
  rw [hb]
  exact (hcl p g hpg).lt _ ha
private lemma b166 {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (x y : Fin n -> Bool) (b : Fin (n + gs.length)) (notInput : ¬ b.val < n)
    (diff : vl gs x b.val≠vl gs y b.val) :
    ∃ a : Fin (n + gs.length),b5 gs a b /\ vl gs x a.val≠vl gs y a.val:=by
  let p:=b.val - n
  have hb : b.val=n + p:=by dsimp [p]; omega
  have hp : p < gs.length:=by have:=b.isLt; omega
  let g:=gs[p]
  have hpg : gs[p]?=some g:=List.getElem?_eq_getElem hp
  have differingRead : ∃ a ∈ g.inputs,vl gs x a≠vl gs y a:=by
    classical
    by_contra none
    apply diff
    rw [hb]
    exact vl_congr gs hcl x y p g hpg (fun a ha => by
      by_contra da
      exact none ⟨a,ha,da⟩)
  obtain ⟨a,ha,da⟩:=differingRead
  have ha':=(hcl p g hpg).lt a ha
  refine ⟨⟨a,by have:=b.isLt; omega⟩,⟨p,g,hpg,hb,ha⟩,da⟩
lemma b59 {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (x y : Fin n -> Bool)
    (sameCut : vl gs x cut.val=vl gs y cut.val)
    (blocked : ∀ i : Fin n,x i≠y i →
      ¬ Relation.ReflTransGen (avoid (b5 gs) cut) (b8 gs i) out) :
    vl gs x out.val=vl gs y out.val:=by
  apply b180 Fin.val (fun v => v.val < n) (b5 gs) cut out
    (fun v => vl gs x v.val) (fun v => vl gs y v.val)
  · exact fun _ _ e => b15 hcl e
  · exact b166 hcl x y
  · exact sameCut
  · intro a ha diff
    let i : Fin n:=⟨a.val,ha⟩
    have sameWire : b8 gs i=a:=Fin.ext rfl
    have di : x i≠y i:=by
      rw [b69 gs x a.val ha,b69 gs y a.val ha] at diff
      exact diff
    rw [← sameWire]
    exact blocked i di
lemma b135 {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n -> Prop) (base : Fin n -> Bool)
    (blocked : ∀ i : Fin n,group i →
      ¬ Relation.ReflTransGen (avoid (b5 gs) cut) (b8 gs i) out) :
    ∃ outer : Bool -> Bool,∀ x : Fin n -> Bool,(∀ i,¬ group i -> x i=base i) →
      outer (vl gs x cut.val)=vl gs x out.val:=by
  let Fiber:={x : Fin n -> Bool // ∀ i,¬ group i -> x i=base i}
  obtain ⟨outer,ho⟩:=b184
    (fun x : Fiber => vl gs x.val cut.val) (fun x : Fiber => vl gs x.val out.val) (by
      intro x y sameCut
      apply b59 hcl cut out x.val y.val sameCut
      intro i diff
      apply blocked i
      by_contra notGroup
      exact diff ((x.property i notGroup).trans (y.property i notGroup).symm))
  exact ⟨outer,fun x agrees => ho ⟨x,agrees⟩⟩
end PetersenCutTrace
namespace CircuitProof.Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof
def Dep {m : ℕ} (f : (Fin m -> Bool) -> Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m -> Bool,f (Function.update x p (!x p))≠f x
def Least (m : ℕ) (f : (Fin m -> Bool) -> Bool) (gs : List Gate) (o : ℕ) : Prop :=
  CleanL m gs /\ (∀ x : Fin m -> Bool,vl gs x o=f x) ∧
    ∀ (gs' : List Gate) (o' : ℕ),CleanL m gs' -> (∀ x : Fin m -> Bool,vl gs' x o'=f x) →
    nonNotCount gs' ≤ nonNotCount gs -> gs.length ≤ gs'.length
def Least.hcl {m f gs o} (h : Least m f gs o):=h.1
def Least.hev {m f gs o} (h : Least m f gs o):=h.2.1
def Least.hmin {m f gs o} (h : Least m f gs o):=h.2.2
def Reads (gs : List Gate) (p w : ℕ) : Prop:=∃ g,gs[p]?=some g /\ w ∈ g.inputs
lemma dep_nc {m : ℕ} {f : (Fin m -> Bool) -> Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m -> Bool,f x≠f y:=by
  obtain ⟨x,hx⟩:=h
  exact ⟨_,_,hx⟩
lemma reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q:=by
  obtain ⟨g,hg,hw⟩:=h
  exact (hcl q g hg).lt w hw
lemma b136 {k : ℕ} (gs : List Gate) (u : Fin k -> Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w=false:=by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [b28]; simp; omega)
lemma b149 {n : ℕ} {f : (Fin n -> Bool) -> Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n -> Bool,C.eval (List.ofFn x)=f x)
    (hnc : ∃ x y,f x≠f y) :
    ∃ gs o,CleanL n gs /\ nonNotCount gs ≤ nonNotCount C.gates /\ ∀ x,vl gs x o=f x:=by
  have hok : ∀ g ∈ C.gates,Ok g:=hfan
  set acc:=elim n C.gates (b9 n,[]) with hacc
  have hinv : ∀ y : Fin n -> Bool,
      Inv n (List.ofFn y) (b1 C.gates (List.ofFn y)) acc :=
    fun y => b139 n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n -> Bool,
      (acc.1.getD C.output (Sum.inl false)).val (b1 acc.2 (List.ofFn y))=f y:=by
    intro y
    rw [((hinv y).2 C.output).2,← hev y]
    rfl
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y,y',hne⟩:=hnc
    apply hne
    rw [← hval y,← hval y',hst]
    rfl
  | inr j =>
    refine ⟨acc.2,j,?_,?_,?_⟩
    · exact b150 n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · simpa [nonNotCount,hacc] using b65 n C.gates (b9 n,[])
    · intro y
      simpa only [hst,Stat.val,vl] using hval y
lemma b146 {n : ℕ} {f : (Fin n -> Bool) -> Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n -> Bool,C.eval (List.ofFn x)=f x)
    (hnc : ∃ x y,f x≠f y) :
    ∃ gs o,Least n f gs o /\ nonNotCount gs ≤ nonNotCount C.gates:=by
  classical
  let admissible (t : ℕ):=∃ gs o,CleanL n gs /\ nonNotCount gs ≤ nonNotCount C.gates ∧
    (∀ x,vl gs x o=f x) /\ gs.length=t
  obtain ⟨gs,o,clean,count,he⟩:=b149 C hfan hev hnc
  have existsAdmissible : ∃ t,admissible t:=⟨gs.length,gs,o,clean,count,he,rfl⟩
  obtain ⟨gs',o',hc,hb,he',hl⟩:=Nat.find_spec existsAdmissible
  refine ⟨gs',o',⟨hc,he',?_⟩,hb⟩
  intro testGates testOut testClean testEval testCost
  have lower:=Nat.find_min' existsAdmissible
    (show admissible testGates.length from
      ⟨testGates,testOut,testClean,testCost.trans hb,testEval,rfl⟩)
  exact hl.trans_le lower
lemma drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o≠k + p) (hno : ∀ q,¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k -> Bool,vl gs y o≠vl gs y' o) :
    ∃ gs' o',CleanL k gs' /\ gs'.length + 1 ≤ gs.length /\ nonNotCount gs' ≤ nonNotCount gs ∧
      ∀ y : Fin k -> Bool,vl gs' y o'=vl gs y o:=by
  obtain ⟨g,hg⟩ : ∃ g,gs[p]?=some g:=⟨gs[p],List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p:=by
    rcases hcl p g hg with ⟨_,j,hj,_⟩ | ⟨_,j,_,hj,_,_⟩ <;> omega
  let g0 : Gate:=⟨GateOp.and,[0,0]⟩
  let gs':=gs.set p g0
  have hlen : gs'.length=gs.length:=by simp [gs']
  have hget_p : gs'[p]?=some g0:=by simp [gs',hp]
  have hget_ne : ∀ r,r≠p -> gs'[r]?=gs[r]?:=by
    intro r hr
    simp [gs',Ne.symm hr]
  have hcl' : CleanL k gs':=by
    intro r g' hr'
    by_cases hrp : r=p
    · subst hrp
      rw [hget_p] at hr'
      cases hr'
      exact Or.inr ⟨Or.inl rfl,0,0,hpos,hpos,rfl⟩
    · rw [hget_ne r hrp] at hr'
      exact hcl r g' hr'
  have hagree : ∀ y : Fin k -> Bool,∀ w,w≠k + p -> vl gs' y w=vl gs y w:=by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [b69 gs' y w hwk,b69 gs y w hwk]
      · obtain ⟨r,rfl⟩ : ∃ r,w=k + r:=⟨w - k,by omega⟩
        have hrp : r≠p:=fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r:=List.getElem?_eq_none_iff.1 hr
          rw [b136 gs' y _ (by omega),b136 gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]?=some g':=by rw [hget_ne r hrp]; exact hr
          rw [b104 gs' hcl' y r g' hr',b104 gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt:=(hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g',hr,e ▸ ha⟩)
  have halias : ∀ y : Fin k -> Bool,vl gs' y (k + p)=vl gs' y 0:=by
    intro y
    rw [b104 gs' hcl' y p g0 hget_p]
    simp [g0,GateOp.eval]
  have hnc' : ∃ y y' : Fin k -> Bool,vl gs' y o≠vl gs' y' o:=by
    obtain ⟨y,y',h⟩:=hnc
    exact ⟨y,y',by rw [hagree y o ho,hagree y' o ho]; exact h⟩
  obtain ⟨gs'',o'',hc'',hl'',hcost,he''⟩ :=
    b177 k gs' hcl' o p 0 (by omega) hpos halias hnc'
  have hkeep : nonNotCount (gs'.eraseIdx p) ≤ nonNotCount gs:=by
    rw [show gs'.eraseIdx p=gs.eraseIdx p from List.eraseIdx_set_eq]
    exact (List.eraseIdx_sublist gs p).countP_le
  exact ⟨gs'',o'',hc'',by omega,hcost.trans hkeep,fun y => by rw [he'' y,hagree y o ho]⟩
section LocalSection1
variable {m : ℕ} {f : (Fin m -> Bool) -> Bool} {gs : List Gate} {o : ℕ}
lemma Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m -> Bool,f x≠f y) :
    ∃ y y' : Fin m -> Bool,vl gs y o≠vl gs y' o:=by
  obtain ⟨x,y,h⟩:=hnc
  exact ⟨x,y,by rw [L.hev,L.hev]; exact h⟩
lemma Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m -> Bool,f x≠f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m -> Bool,vl gs u (m + p)=vl gs u j:=by
  intro hall
  obtain ⟨gs',o',hc',hl',hcost,he'⟩:=b177 m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have hcost' : nonNotCount gs' ≤ nonNotCount gs :=
    hcost.trans (List.eraseIdx_sublist gs p).countP_le
  have:=L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x) hcost'
  omega
lemma Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m -> Bool,f x≠f y) (p : ℕ)
    (hp : p < gs.length) (ho : o≠m + p) : ∃ q,p < q /\ Reads gs q (m + p):=by
  by_contra hno
  have hno' : ∀ q,¬ Reads gs q (m + p):=by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q,hpq,hq⟩
    · have:=reads_lt L.hcl hq
      omega
  obtain ⟨gs',o',hc',hl',hcost,he'⟩:=drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have:=L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x) hcost
  omega
lemma Least.dep_read (L : Least m f gs o) (i : Fin m) (hd : Dep f i)
    (hnc : ∀ b : Bool,∃ x y : Fin m -> Bool,
      f (Function.update x i b)≠f (Function.update y i b)) : ∃ q,Reads gs q i:=by
  by_contra hno
  have hno' : ∀ g ∈ gs,(i : ℕ) ∉ g.inputs:=by
    intro g hg hi
    obtain ⟨q,hq⟩:=List.mem_iff_getElem?.1 hg
    exact hno ⟨q,g,hq,hi⟩
  have hoi : o≠i:=by
    intro e
    obtain ⟨x,y,hxy⟩:=hnc false
    apply hxy
    rw [← L.hev,← L.hev,e,b69 gs _ i i.isLt,b69 gs _ i i.isLt]
    simp
  obtain ⟨x,hx⟩:=hd
  apply hx
  rw [← L.hev,← L.hev]
  refine b190 i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjm : j < m
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
       =Function.update x i (!x i) ⟨j,hjm⟩ from b165 m _ false ⟨j,hjm⟩,
      show (List.ofFn x).getD j false=x ⟨j,hjm⟩ from b165 m x false ⟨j,hjm⟩]
    exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
end LocalSection1
end CircuitProof.Readers
namespace CircuitProof.RunAsm
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof
open CircuitProof.Readers
lemma pq2f_nodup {m : ℕ} {f : (Fin m -> Bool) -> Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) (hnc : ∃ x y : Fin m -> Bool,f x≠f y) {p : ℕ} {g : Gate}
    (hg : gs[p]?=some g) (hop : g.op=GateOp.and \/ g.op=GateOp.or) {a b : ℕ}
    (hin : g.inputs=[a,b]) : a≠b:=by
  rintro rfl
  have hcl:=L.hcl p g hg
  have hlt : a < m + p:=by
    rcases hcl with ⟨h1,j,_,h2⟩ | ⟨h1,j,k,hj,hk,h2⟩
    · rw [hin] at h2; simp at h2
    · rw [hin] at h2; simp at h2; omega
  have hp : p < gs.length:=(List.getElem?_eq_some_iff.1 hg).1
  refine L.no_alias hnc p hp a hlt (fun u => ?_)
  rw [b104 gs L.hcl u p g hg,hin]
  rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
end CircuitProof.RunAsm
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open CircuitProof.RunAsm
lemma b164 {n out : Nat} {f : (Fin n -> Bool) -> Bool} {gs : List Gate}
    (least : Least n f gs out) (nonconstant : ∃ x y,f x≠f y)
    (dependent : ∀ v : Fin n,Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool),∃ x y,
      f (Function.update x v b)≠f (Function.update y v b))
    (w : Nat) (amongWires : w < n + gs.length) (notOutput : w≠out) :
    ∃ p,Reads gs p w:=by
  by_cases isInput : w < n
  · let v : Fin n:=⟨w,isInput⟩
    exact least.dep_read v (dependent v) (stillNonconstant v)
  · let p:=w - n
    have wire : w=n + p:=by dsimp [p]; omega
    have pLt : p < gs.length:=by omega
    have notOut : out≠n + p:=by omega
    obtain ⟨q,_,read⟩:=least.live nonconstant p pLt notOut
    exact ⟨q,wire.symm ▸ read⟩
lemma least_gate_inputs_nodup {n out : Nat} {f : (Fin n -> Bool) -> Bool} {gs : List Gate}
    (least : Least n f gs out) (nonconstant : ∃ x y,f x≠f y) (g : Gate) (present : g ∈ gs) :
    g.inputs.Nodup:=by
  obtain ⟨slot,atSlot⟩:=List.mem_iff_getElem?.mp present
  rcases least.hcl slot g atSlot with ⟨_,a,_,args⟩ | ⟨ops,a,b,_,_,args⟩
  · simp [args]
  · have distinct:=pq2f_nodup least nonconstant atSlot ops args
    simp [args,distinct]
lemma b79 {n out : Nat} {gs : List Gate}
    {f : (Fin n -> Bool) -> Bool} (least : Least n f gs out) (nonnull : ∃ x y,f x≠f y)
    (dependent : ∀ v : Fin n,Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool),∃ x y,
      f (Function.update x v b)≠f (Function.update y v b))
    (w : Fin (n + gs.length)) (notOutput : w.val≠out) :
    ∃ (p : Nat) (g : Gate),gs[p]?=some g /\ w.val ∈ g.inputs /\ n + p < n + gs.length:=by
  obtain ⟨p,g,hit,reads⟩:=b164 least nonnull dependent stillNonconstant w.val w.isLt notOutput
  have bound:=(List.getElem?_eq_some_iff.mp hit).1
  exact ⟨p,g,hit,reads,by omega⟩
namespace PetersenCutTrace
open PEqualNP.CircuitLowerBounds
open CircuitProof CircuitProof.Readers
def b10 {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) : List (Fin (n + gs.length)) :=
  if gate : n ≤ b.val then
    let slot:=b.val - n
    have hs : slot < gs.length:=by have:=b.isLt; omega
    let g:=gs[slot]'hs
    g.inputs.attach.map fun a => ⟨a.val,by
      have atSlot : gs[slot]?=some g:=List.getElem?_eq_getElem hs
      have before:=(clean slot g atSlot).lt a.val a.property
      omega⟩
  else []
lemma b45 {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (internal : n ≤ b.val) :
    (b10 clean b).map Fin.val =
      (gs[b.val - n]'(by have:=b.isLt; omega)).inputs:=by
  simp [b10,internal,List.map_map,Function.comp_def]
lemma b111 {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (primary : b.val < n) : b10 clean b=[]:=by
  simp [b10,show ¬ n ≤ b.val by omega]
lemma b116 {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) {p : Nat} {g : Gate} (atSlot : gs[p]?=some g) (bWire : b.val=n + p) :
    (b10 clean b).map Fin.val=g.inputs:=by
  have isGate : n ≤ b.val:=by omega
  have which : b.val - n=p:=by omega
  have located:=(List.getElem?_eq_some_iff.mp atSlot).2
  simpa [which,located] using b45 clean b isGate
lemma b158 {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (a b : Fin (n + gs.length)) : a ∈ b10 clean b↔b5 gs a b:=by
  by_cases internal : n ≤ b.val
  · let slot:=b.val - n
    have hs : slot < gs.length:=by have:=b.isLt; dsimp [slot]; omega
    let g:=gs[slot]'hs
    have wire : b.val=n + slot:=by dsimp [slot]; omega
    have atSlot : gs[slot]?=some g:=List.getElem?_eq_getElem hs
    have valList : (b10 clean b).map Fin.val=g.inputs :=
      b45 clean b internal
    constructor
    · intro mem
      refine ⟨slot,g,atSlot,wire,?_⟩
      rw [← valList]
      exact List.mem_map.mpr ⟨a,mem,rfl⟩
    · rintro ⟨q,h,atQ,wireQ,inside⟩
      have same : q=slot:=by omega
      subst q
      have gateSame : h=g:=Option.some.inj (atQ.symm.trans atSlot)
      subst h
      rw [← valList] at inside
      obtain ⟨a',mem,equal⟩:=List.mem_map.mp inside
      exact (Fin.ext equal : a'=a) ▸ mem
  · have empty : b10 clean b=[]:=by simp [b10,internal]
    rw [empty]
    constructor
    · simp
    · rintro ⟨slot,g,_,wire,_⟩
      omega
lemma b137 {n out : Nat} {gs : List Gate} {f : (Fin n -> Bool) -> Bool}
    (least : Least n f gs out) (nonnull : ∃ x y,f x≠f y) (b : Fin (n + gs.length)) :
    (b10 least.hcl b).Nodup:=by
  by_cases internal : n ≤ b.val
  · apply List.Nodup.of_map Fin.val
    rw [b45 least.hcl b internal]
    exact PEqualNP.Outside.R_meta_3178_52_support.Binary.least_gate_inputs_nodup least nonnull _
      (List.getElem_mem (by have:=b.isLt; omega))
  · simp [b10,internal]
end PetersenCutTrace
namespace PetersenScratch
open PEqualNP.MetaComplexity
def b0 {n : ℕ} (i : Fin n) : DMFormula n -> ℕ
  | .lit k _ => if k=i then 1 else 0
  | .and p q => b0 i p + b0 i q
  | .or p q => b0 i p + b0 i q
def b21 {n : ℕ} (i j : Fin n) (p : DMFormula n) : Prop :=
  0 < b0 i p \/ 0 < b0 j p
def b11 {n : ℕ} (i j : Fin n) (base : Fin n -> Bool) (a b : Bool) (k : Fin n) : Bool :=
  if k=i then a else if k=j then b else base k
def b4 {n : ℕ} (i j : Fin n) (base : Fin n -> Bool) (p : DMFormula n) :
    Bool -> Bool -> Bool :=
  fun a b => p.eval (b11 i j base a b)
def binOp (conj : Bool) (a b : Bool) : Bool :=
  if conj then a&&b else a||b
noncomputable def combine {n : ℕ} (conj : Bool) (i j : Fin n) (p q : DMFormula n)
    (P Q : Bool -> Bool -> Bool) : Bool -> Bool -> Bool:=by
  classical
  exact if b21 i j p then
    if b21 i j q then fun a b => binOp conj (P a b) (Q a b) else P
    else Q
noncomputable def pairKernel {n : ℕ} (i j : Fin n) : DMFormula n -> Bool -> Bool -> Bool
  | .lit k sign => fun a b =>
    let bit:=if k=i then a else if k=j then b else false
    if sign then bit else !bit
  | .and p q => combine true i j p q (pairKernel i j p) (pairKernel i j q)
  | .or p q => combine false i j p q (pairKernel i j p) (pairKernel i j q)
private lemma b176 {n : ℕ} (p : DMFormula n) {x y : Fin n -> Bool}
    (h : ∀ k,0 < b0 k p -> x k=y k) : p.eval x=p.eval y:=by
  induction p with
  | lit k s =>
    have e:=h k (by simp [b0])
    simp [DMFormula.eval,e]
  | and p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [b0]; omega)),
      ihq (fun k hk => h k (by simp only [b0]; omega))]
  | or p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [b0]; omega)),
      ihq (fun k hk => h k (by simp only [b0]; omega))]
private lemma b107 {n : ℕ} {i j : Fin n} {base : Fin n -> Bool} {p : DMFormula n}
    (h : b0 i p=0) (a a' b : Bool) :
    b4 i j base p a b=b4 i j base p a' b:=by
  apply b176
  intro k hk
  have ne : k≠i:=by rintro rfl; omega
  simp [b11,ne]
private lemma b125 {n : ℕ} {i j : Fin n} {base : Fin n -> Bool} {p : DMFormula n}
    (h : b0 j p=0) (a b b' : Bool) :
    b4 i j base p a b=b4 i j base p a b':=by
  apply b176
  intro k hk
  have ne : k≠j:=by rintro rfl; omega
  simp [b11,ne]
def b39 (f : Bool -> Bool -> Bool) : Prop :=
  ∃ b,f false b≠f true b
private lemma b154 {op : Bool -> Bool -> Bool} {P Q : Bool -> Bool -> Bool}
    (h : b39 fun a b => op (P a b) (Q a b))
    (hQ : ∀ b,Q false b=Q true b) : b39 P:=by
  obtain ⟨b,hb⟩:=h
  exact ⟨b,fun hp => hb (by
    change op (P false b) (Q false b)=op (P true b) (Q true b)
    rw [hp,hQ])⟩
private lemma b144 {op : Bool -> Bool -> Bool} {P Q : Bool -> Bool -> Bool}
    (h : b39 fun a b => op (P a b) (Q a b))
    (hP : ∀ b,P false b=P true b) : b39 Q:=by
  obtain ⟨b,hb⟩:=h
  exact ⟨b,fun hq => hb (by
    change op (P false b) (Q false b)=op (P true b) (Q true b)
    rw [hq,hP])⟩
private lemma b73 {n : ℕ} {i j : Fin n} {base : Fin n -> Bool} {p : DMFormula n}
    (h : ¬ b21 i j p) (a b : Bool) :
    b4 i j base p a b=b4 i j base p false false:=by
  have hi : b0 i p=0:=by
    by_contra e
    exact h (Or.inl (by omega))
  have hj : b0 j p=0:=by
    by_contra e
    exact h (Or.inr (by omega))
  exact (b107 hi a false b).trans (b125 hj false b false)
private lemma b138 (conj c : Bool) (P : Bool -> Bool -> Bool)
    (h : ∃ a b a' b',binOp conj (P a b) c≠binOp conj (P a' b') c) :
    ∀ a b,binOp conj (P a b) c=P a b:=by
  cases conj <;> cases c <;> simp [binOp] at h ⊢
private lemma bin_comm (conj a b : Bool) : binOp conj a b=binOp conj b a:=by
  cases conj <;> cases a <;> cases b <;> rfl
private lemma b132 {n : ℕ} (i j : Fin n) (base : Fin n -> Bool)
    (conj : Bool) (p q : DMFormula n)
    (hi : b0 i p + b0 i q ≤ 1)
    (hj : b0 j p + b0 j q ≤ 1)
    (present : b21 i j p \/ b21 i j q)
    (dep_i : 0 < b0 i p + b0 i q →
      b39 fun a b => binOp conj (b4 i j base p a b) (b4 i j base q a b))
    (dep_j : 0 < b0 j p + b0 j q →
      b39 fun b a => binOp conj (b4 i j base p a b) (b4 i j base q a b))
    (ihp : b0 i p ≤ 1 -> b0 j p ≤ 1 -> b21 i j p →
      (0 < b0 i p -> b39 (b4 i j base p)) →
      (0 < b0 j p -> b39 fun b a => b4 i j base p a b) →
      ∀ a b,b4 i j base p a b=pairKernel i j p a b)
    (ihq : b0 i q ≤ 1 -> b0 j q ≤ 1 -> b21 i j q →
      (0 < b0 i q -> b39 (b4 i j base q)) →
      (0 < b0 j q -> b39 fun b a => b4 i j base q a b) →
      ∀ a b,b4 i j base q a b=pairKernel i j q a b)
    (a b : Bool) :
    binOp conj (b4 i j base p a b) (b4 i j base q a b) =
      combine conj i j p q (pairKernel i j p) (pairKernel i j q) a b:=by
  classical
  have pl : b21 i j p -> ∀ a b,b4 i j base p a b=pairKernel i j p a b:=by
    intro hp
    apply ihp (by omega) (by omega) hp
    · intro h
      exact b154 (dep_i (by omega)) (fun b => b107 (by omega) false true b)
    · intro h
      exact b154 (dep_j (by omega)) (fun a => b125 (by omega) a false true)
  have ql : b21 i j q -> ∀ a b,b4 i j base q a b=pairKernel i j q a b:=by
    intro hq
    apply ihq (by omega) (by omega) hq
    · intro h
      exact b144 (dep_i (by omega)) (fun b => b107 (by omega) false true b)
    · intro h
      exact b144 (dep_j (by omega)) (fun a => b125 (by omega) a false true)
  have nonconst : ∃ a b a' b',
      binOp conj (b4 i j base p a b) (b4 i j base q a b) ≠
        binOp conj (b4 i j base p a' b') (b4 i j base q a' b'):=by
    unfold b21 at present
    rcases present with (h | h) | (h | h)
    · obtain ⟨b,h⟩:=dep_i (by omega)
      exact ⟨false,b,true,b,h⟩
    · obtain ⟨a,h⟩:=dep_j (by omega)
      exact ⟨a,false,a,true,h⟩
    · obtain ⟨b,h⟩:=dep_i (by omega)
      exact ⟨false,b,true,b,h⟩
    · obtain ⟨a,h⟩:=dep_j (by omega)
      exact ⟨a,false,a,true,h⟩
  by_cases hp : b21 i j p
  · by_cases hq : b21 i j q
    · simp [combine,hp,hq,pl hp,ql hq]
    · rw [b73 hq a b]
      have hn:=nonconst
      simp_rw [b73 hq] at hn
      rw [b138 conj _ _ hn a b,pl hp]
      simp [combine,hp,hq]
  · have hq:=present.resolve_left hp
    rw [b73 hp a b,bin_comm]
    have hn:=nonconst
    simp_rw [b73 hp,bin_comm conj (b4 i j base p false false)] at hn
    rw [b138 conj _ _ hn a b,ql hq]
    simp [combine,hp]
private lemma b161 {n : ℕ} (i j : Fin n) (base : Fin n -> Bool) (p : DMFormula n)
    (hi : b0 i p ≤ 1) (hj : b0 j p ≤ 1) (present : b21 i j p)
    (dep_i : 0 < b0 i p -> b39 (b4 i j base p))
    (dep_j : 0 < b0 j p -> b39 fun b a => b4 i j base p a b) :
    ∀ a b,b4 i j base p a b=pairKernel i j p a b:=by
  induction p with
  | lit k s =>
    intro a b
    by_cases hki : k=i
    · simp [b4,pairKernel,DMFormula.eval,b11,hki]
    · have hkj : k=j:=by
        by_contra h
        simp [b21,b0,hki,h] at present
      simp [b4,pairKernel,DMFormula.eval,b11,hkj]
  | and p q ihp ihq =>
    have present' : b21 i j p \/ b21 i j q:=by
      unfold b21 at *
      simp only [b0] at present
      omega
    exact b132 i j base true p q hi hj present' dep_i dep_j ihp ihq
  | or p q ihp ihq =>
    have present' : b21 i j p \/ b21 i j q:=by
      unfold b21 at *
      simp only [b0] at present
      omega
    exact b132 i j base false p q hi hj present' dep_i dep_j ihp ihq
lemma b129 {n : ℕ} (i j : Fin n) (p : DMFormula n)
    (hi : b0 i p ≤ 1) (hj : b0 j p ≤ 1)
    (baseA baseO : Fin n -> Bool) (outerA outerO : Bool -> Bool)
    (hA : ∀ a b,outerA (b4 i j baseA p a b)=(a&&b))
    (hO : ∀ a b,outerO (b4 i j baseO p a b)=(a||b)) : False:=by
  have depAi : b39 (b4 i j baseA p):=by
    refine ⟨true,fun h => ?_⟩
    have e:=congrArg outerA h
    rw [hA,hA] at e
    cases e
  have depAj : b39 fun b a => b4 i j baseA p a b:=by
    refine ⟨true,fun h => ?_⟩
    have e:=congrArg outerA h
    rw [hA,hA] at e
    cases e
  have depOi : b39 (b4 i j baseO p):=by
    refine ⟨false,fun h => ?_⟩
    have e:=congrArg outerO h
    rw [hO,hO] at e
    cases e
  have depOj : b39 fun b a => b4 i j baseO p a b:=by
    refine ⟨false,fun h => ?_⟩
    have e:=congrArg outerO h
    rw [hO,hO] at e
    cases e
  have present : b21 i j p:=by
    left
    by_contra! h
    obtain ⟨b,hb⟩:=depAi
    exact hb (b107 (by omega) false true b)
  have stableA:=b161 i j baseA p hi hj present (fun _ => depAi) (fun _ => depAj)
  have stableO:=b161 i j baseO p hi hj present (fun _ => depOi) (fun _ => depOj)
  simp_rw [stableA] at hA
  simp_rw [stableO] at hO
  have ne : pairKernel i j p false false≠pairKernel i j p false true:=by
    intro e
    have f:=congrArg outerO e
    rw [hO,hO] at f
    cases f
  have zeros:=hA false false
  have other:=hA false true
  have one:=hA true true
  cases hk : pairKernel i j p false false <;>
    cases hl : pairKernel i j p false true <;>
    cases hm : pairKernel i j p true true <;>
    simp_all
noncomputable def edgeValue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n -> Bool) : Bool:=by
  classical
  exact decide (∃ u v,G.Adj u v /\ x u=true /\ x v=true)
private lemma b57 {n : ℕ} {G : SimpleGraph (Fin n)} {x : Fin n -> Bool}
    {u v : Fin n} (h : G.Adj u v) (hu : x u=true) (hv : x v=true) :
    edgeValue G x=true:=by
  classical
  unfold edgeValue
  exact decide_eq_true ⟨u,v,h,hu,hv⟩
private lemma b22 {n : ℕ} {G : SimpleGraph (Fin n)} {x : Fin n -> Bool}
    {u v : Fin n} (h : ¬ G.Adj u v) (active : ∀ w,x w=true -> w=u \/ w=v) :
    edgeValue G x=false:=by
  classical
  unfold edgeValue
  apply decide_eq_false
  rintro ⟨s,t,es,hs,ht⟩
  rcases active s hs with rfl | rfl <;> rcases active t ht with rfl | rfl
  · exact G.irrefl es
  · exact h es
  · exact h es.symm
  · exact G.irrefl es
private lemma b179 {n : ℕ} {G : SimpleGraph (Fin n)} {i j : Fin n}
    (h : G.Adj i j) (a b : Bool) :
    edgeValue G (b11 i j (fun _ => false) a b)=(a&&b):=by
  cases a <;> cases b
  · apply b22 (u:=i) (v:=i) G.irrefl
    intro k hk
    simp [b11] at hk
  · apply b22 (u:=j) (v:=j) G.irrefl
    intro k hk
    by_cases hki : k=i <;> by_cases hkj : k=j <;>
      simp [b11,hki,hkj] at hk ⊢
  · apply b22 (u:=i) (v:=i) G.irrefl
    intro k hk
    by_cases hki : k=i <;> by_cases hkj : k=j <;>
      simp [b11,hki,hkj] at hk ⊢
    assumption
  · exact b57 h (by simp [b11]) (by simp [b11,h.ne.symm])
private lemma b186 {n : ℕ} {G : SimpleGraph (Fin n)} {i j u v : Fin n}
    (hij : i≠j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u≠j) (hvi : v≠i) (huv : ¬ G.Adj u v) (a b : Bool) :
    edgeValue G (b11 i j (fun k => decide (k=u \/ k=v)) a b)=(a||b):=by
  have hu : b11 i j (fun k => decide (k=u \/ k=v)) a b u=true:=by
    simp [b11,hiu.ne.symm,huj]
  have hv : b11 i j (fun k => decide (k=u \/ k=v)) a b v=true:=by
    simp [b11,hvi,hjv.ne.symm]
  cases a <;> cases b
  · apply b22 huv
    intro k hk
    by_cases hki : k=i <;> by_cases hkj : k=j <;>
      simp [b11,hki,hkj] at hk
    exact hk
  · exact b57 hjv (by simp [b11,hij.symm]) hv
  · exact b57 hiu (by simp [b11]) hu
  · exact b57 hiu (by simp [b11]) hu
lemma b113 {n : ℕ} (G : SimpleGraph (Fin n)) (i j u v : Fin n)
    (hij : G.Adj i j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u≠j) (hvi : v≠i) (huv : ¬ G.Adj u v)
    (p : DMFormula n) (hi : b0 i p ≤ 1) (hj : b0 j p ≤ 1)
    (factors : ∀ base : Fin n -> Bool,∃ outer : Bool -> Bool,∀ a b,
      outer (b4 i j base p a b)=edgeValue G (b11 i j base a b)) : False:=by
  obtain ⟨outerA,ha⟩:=factors (fun _ => false)
  obtain ⟨outerO,ho⟩:=factors (fun k => decide (k=u \/ k=v))
  exact b129 i j p hi hj _ _ outerA outerO
    (fun a b => (ha a b).trans (b179 hij a b))
    (fun a b => (ho a b).trans (b186 hij.ne hiu hjv huj hvi huv a b))
end PetersenScratch
namespace PetersenCutFormula
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open CircuitProof
open PetersenScratch
def b18 {n : Nat} : DMFormula n -> DMFormula n
  | .lit i sign => .lit i (!sign)
  | .and a b => .or (b18 a) (b18 b)
  | .or a b => .and (b18 a) (b18 b)
lemma b163 {n : Nat} (p : DMFormula n) (x : Fin n -> Bool) :
    (b18 p).eval x=!(p.eval x):=by
  induction p with
  | lit i s =>
    cases s <;> cases e : x i <;> simp [b18,DMFormula.eval,e]
  | and a b iha ihb =>
    simp only [b18,DMFormula.eval,iha,ihb]
    cases a.eval x <;> cases b.eval x <;> rfl
  | or a b iha ihb =>
    simp only [b18,DMFormula.eval,iha,ihb]
    cases a.eval x <;> cases b.eval x <;> rfl
lemma b112 {n : Nat} (i : Fin n) (p : DMFormula n) :
    b0 i (b18 p)=b0 i p:=by
  induction p with
  | lit i s => rfl
  | and a b iha ihb => simp [b18,b0,iha,ihb]
  | or a b iha ihb => simp [b18,b0,iha,ihb]
def b2 {n : Nat} (fallback : Fin n) (gs : List Gate) (w : Nat) : DMFormula n :=
  if hw : w < n then
    .lit ⟨w,hw⟩ true
  else
    match gs[w - n]? with
    | none => .lit fallback true
    | some g =>
      match g.op,g.inputs with
      | .not,[a] =>
        if _ha : a < w then b18 (b2 fallback gs a) else .lit fallback true
      | .and,[a,b] =>
        if _ha : a < w then
          if _hb : b < w then .and (b2 fallback gs a) (b2 fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | .or,[a,b] =>
        if _ha : a < w then
          if _hb : b < w then .or (b2 fallback gs a) (b2 fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | _,_ => .lit fallback true
termination_by w
decreasing_by all_goals assumption
lemma b94 {n : Nat} (fallback : Fin n) (gs : List Gate) (i : Fin n) :
    b2 fallback gs i.val=.lit i true:=by
  rw [b2]
  simp [i.isLt]
private lemma b114 {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a : Nat} {g : Gate} (hg : gs[p]?=some g) (op : g.op=.not)
    (inputs : g.inputs=[a]) (ha : a < n + p) :
    b2 fallback gs (n + p)=b18 (b2 fallback gs a):=by
  have hn : ¬ n + p < n:=by omega
  have hp : n + p - n=p:=by omega
  conv_lhs => rw [b2]
  simp [hn,hp,hg,op,inputs,ha]
private lemma b115 {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]?=some g) (op : g.op=.and)
    (inputs : g.inputs=[a,b]) (ha : a < n + p) (hb : b < n + p) :
    b2 fallback gs (n + p)=.and (b2 fallback gs a) (b2 fallback gs b):=by
  have hn : ¬ n + p < n:=by omega
  have hp : n + p - n=p:=by omega
  conv_lhs => rw [b2]
  simp [hn,hp,hg,op,inputs,ha,hb]
private lemma b131 {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]?=some g) (op : g.op=.or)
    (inputs : g.inputs=[a,b]) (ha : a < n + p) (hb : b < n + p) :
    b2 fallback gs (n + p)=.or (b2 fallback gs a) (b2 fallback gs b):=by
  have hn : ¬ n + p < n:=by omega
  have hp : n + p - n=p:=by omega
  conv_lhs => rw [b2]
  simp [hn,hp,hg,op,inputs,ha,hb]
lemma b155 {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (x : Fin n -> Bool) (w : Nat) (hw : w < n + gs.length) :
    (b2 fallback gs w).eval x=vl gs x w:=by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · rw [b94 fallback gs ⟨w,hi⟩,b69 gs x w hi]
      rfl
    · obtain ⟨p,rfl⟩ : ∃ p,w=n + p:=⟨w - n,by omega⟩
      have hp : p < gs.length:=by omega
      let g:=gs[p]
      have hg : gs[p]?=some g:=List.getElem?_eq_getElem hp
      rcases hcl p g hg with ⟨op,a,ha,inputs⟩ | ⟨op | op,a,b,ha,hb,inputs⟩
      · rw [b114 fallback hg op inputs ha,b163,ih a ha (by omega),
          b104 gs hcl x p g hg]
        simp [op,inputs,GateOp.eval]
      · rw [b115 fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega),ih b hb (by omega),b104 gs hcl x p g hg]
        simp [op,inputs,GateOp.eval]
      · rw [b131 fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega),ih b hb (by omega),b104 gs hcl x p g hg]
        simp [op,inputs,GateOp.eval]
lemma b103 {n : Nat} (fallback : Fin n) (gs : List Gate) (chosen i : Fin n) :
    b0 chosen (b2 fallback gs i.val)=if i=chosen then 1 else 0:=by
  rw [b94]
  rfl
lemma b109 {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (chosen : Fin n) {p : Nat} {g : Gate} (hg : gs[p]?=some g) :
    b0 chosen (b2 fallback gs (n + p)) =
      (g.inputs.map fun a => b0 chosen (b2 fallback gs a)).sum:=by
  rcases hcl p g hg with ⟨op,a,ha,inputs⟩ | ⟨op | op,a,b,ha,hb,inputs⟩
  · simp [b114 fallback hg op inputs ha,inputs,b112]
  · simp [b115 fallback hg op inputs ha hb,inputs,b0]
  · simp [b131 fallback hg op inputs ha hb,inputs,b0]
lemma b84 {n : Nat} (fallback chosen : Fin n) {gs : List Gate}
    (hcl : CleanL n gs) {p : Nat} {g : Gate} (hg : gs[p]?=some g)
    {b : Fin (n + gs.length)} (hb : b.val=n + p)
    (parents : List (Fin (n + gs.length))) (parentsVal : parents.map Fin.val=g.inputs) :
    b0 chosen (b2 fallback gs b.val) =
      (parents.map fun a => b0 chosen (b2 fallback gs a.val)).sum:=by
  rw [hb,b109 fallback hcl chosen hg,← parentsVal,List.map_map]
  rfl
end PetersenCutFormula
namespace PetersenCutIndependent
open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutFormula PetersenCutTrace PetersenScratch
lemma b30 {n : Nat} {gs : List Gate} (fallback chosen : Fin n)
    (a : Fin (n + gs.length)) (ha : a.val < n) :
    b0 chosen (b2 fallback gs a.val) =
      if a=b8 gs chosen then 1 else 0:=by
  let i : Fin n:=⟨a.val,ha⟩
  have e : i=chosen↔a=b8 gs chosen:=by
    constructor
    · intro h
      exact Fin.ext (congrArg (fun k : Fin n => k.val) h)
    · intro h
      exact Fin.ext (congrArg (fun k : Fin (n + gs.length) => k.val) h)
  change b0 chosen (b2 fallback gs i.val)=_
  simp only [b103,e]
lemma b196 {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n -> Prop) (base : Fin n -> Bool)
    (controlled : cut=out \/ ∀ i : Fin n,group i →
      ¬ Relation.ReflTransGen (avoid (b5 gs) cut) (b8 gs i) out) :
    ∃ outer : Bool -> Bool,∀ x : Fin n -> Bool,(∀ i,¬ group i -> x i=base i) →
      outer (vl gs x cut.val)=vl gs x out.val:=by
  rcases controlled with rfl | blocked
  · exact ⟨id,fun _ _ => rfl⟩
  · exact b135 hcl cut out group base blocked
lemma b124 {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (G : SimpleGraph (Fin n)) (cut out : Fin (n + gs.length))
    (computes : ∀ x,vl gs x out.val=edgeValue G x)
    (i j u v : Fin n) (hij : G.Adj i j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u≠j) (hvi : v≠i) (huv : ¬ G.Adj u v)
    (hi : b0 i (b2 i gs cut.val) ≤ 1)
    (hj : b0 j (b2 i gs cut.val) ≤ 1)
    (controlled : cut=out \/ ∀ k : Fin n,(k=i \/ k=j) →
      ¬ Relation.ReflTransGen (avoid (b5 gs) cut) (b8 gs k) out) : False:=by
  refine b113 G i j u v hij hiu hjv huj hvi huv
    (b2 i gs cut.val) hi hj (fun base => ?_)
  obtain ⟨f,hf⟩:=b196 hcl cut out (fun k => k=i \/ k=j) base controlled
  refine ⟨f,fun a b => ?_⟩
  have agree : ∀ k,¬ (k=i \/ k=j) -> b11 i j base a b k=base k:=by
    intro k hk
    simp [b11,show k≠i from fun e => hk (Or.inl e),
      show k≠j from fun e => hk (Or.inr e)]
  unfold b4
  rw [b155 i hcl _ cut.val cut.isLt]
  exact (hf _ agree).trans (computes _)
end PetersenCutIndependent
namespace FirstBranchRoute
open Relation
variable {m : Nat} (reads : Fin m -> Fin m -> Prop) (output : Fin m)
def Branches (v : Fin m) : Prop:=∃ a b,reads v a /\ reads v b /\ a≠b
def Terminal (v : Fin m) : Prop:=v=output \/ Branches reads v
def Follow (v w : Fin m) : Prop:=reads v w /\ ¬ Terminal reads output v
lemma b72 {v a b : Fin m} (first : Follow reads output v a) (next : Follow reads output v b) :
    a=b:=by
  by_contra separate
  exact first.2 (Or.inr ⟨a,b,first.1,next.1,separate⟩)
variable (forward : ∀ {v w : Fin m},reads v w -> v < w)
variable (live : ∀ v : Fin m,v≠output -> ∃ w,reads v w)
include forward live in
lemma b81 (v : Fin m) :
    ∃ root : Fin m,Terminal reads output root /\ ReflTransGen (Follow reads output) v root:=by
  let distance (w : Fin m):=m - w.val
  induction v using (measure distance).wf.induction with
  | h v ih =>
    by_cases terminal : Terminal reads output v
    · exact ⟨v,terminal,ReflTransGen.refl⟩
    obtain ⟨next,edge⟩:=live v (fun e => terminal (Or.inl e))
    have increase:=forward edge
    have closer : distance next < distance v:=by
      dsimp [distance]
      have bounds:=next.isLt
      change v.val < next.val at increase
      omega
    obtain ⟨root,stopped,route⟩:=ih next closer
    exact ⟨root,stopped,route.head ⟨edge,terminal⟩⟩
include forward in
lemma b121 {v a b : Fin m} (terminalA : Terminal reads output a)
    (terminalB : Terminal reads output b) (routeA : ReflTransGen (Follow reads output) v a)
    (routeB : ReflTransGen (Follow reads output) v b) : a=b:=by
  let distance (w : Fin m):=m - w.val
  induction v using (measure distance).wf.induction generalizing a b with
  | h v ih =>
    rcases routeA.cases_head with h | ⟨next,edge,tailA⟩
    · subst a
      rcases routeB.cases_head with h | ⟨_,edgeB,_⟩
      · exact h
      · exact (edgeB.2 terminalA).elim
    · rcases routeB.cases_head with h | ⟨nextB,edgeB,tailB⟩
      · subst b
        exact (edge.2 terminalB).elim
      have equal:=b72 reads output edge edgeB
      subst nextB
      have increase:=forward edge.1
      have closer : distance next < distance v:=by
        dsimp [distance]
        have bounds:=next.isLt
        change v.val < next.val at increase
        omega
      exact ih next closer terminalA terminalB tailA tailB
noncomputable def first (v : Fin m) : Fin m :=
  Classical.choose (b81 reads output forward live v)
lemma first_stops (v : Fin m) : Terminal reads output (first reads output forward live v) :=
  (Classical.choose_spec (b81 reads output forward live v)).1
lemma b127 (v : Fin m) : ReflTransGen (Follow reads output) v (first reads output forward live v) :=
  (Classical.choose_spec (b81 reads output forward live v)).2
lemma b35 {v : Fin m} (stopped : Terminal reads output v) :
    first reads output forward live v=v :=
  b121 reads output forward (first_stops reads output forward live v) stopped
    (b127 reads output forward live v) ReflTransGen.refl
lemma b108 {v w : Fin m} (step : Follow reads output v w) :
    first reads output forward live v=first reads output forward live w :=
  b121 reads output forward (first_stops reads output forward live v)
    (first_stops reads output forward live w) (b127 reads output forward live v)
    ((b127 reads output forward live w).head step)
include forward in
lemma b119 {v w : Fin m} (route : ReflTransGen reads v w) : v ≤ w:=by
  induction route with
  | refl => exact le_rfl
  | tail _ edge ih => exact le_trans ih (le_of_lt (forward edge))
lemma b38 {v w : Fin m} (route : ReflTransGen (Follow reads output) v w) :
    ReflTransGen reads v w:=by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1
lemma b141 (v : Fin m) : v ≤ first reads output forward live v :=
  b119 reads forward (b38 reads output (b127 reads output forward live v))
lemma b75 {v w : Fin m} (route : ReflTransGen reads v w)
    (before : w ≤ first reads output forward live v) :
    ReflTransGen (Follow reads output) v w /\ first reads output forward live w=first reads output forward live v:=by
  induction route with
  | refl => exact ⟨ReflTransGen.refl,rfl⟩
  | tail _ edge ih =>
    have predecessorBefore:=lt_of_lt_of_le (forward edge) before
    obtain ⟨tracked,label⟩:=ih (le_of_lt predecessorBefore)
    have step : Follow reads output _ _:=⟨edge,fun stopped => by
      have self:=b35 reads output forward live stopped
      rw [self] at label
      exact (ne_of_lt predecessorBefore) label⟩
    exact ⟨tracked.tail step,(b108 reads output forward live step).symm.trans label⟩
lemma ancestor_first_le {v w : Fin m} (route : ReflTransGen reads v w)
    (stopped : Terminal reads output w) : first reads output forward live v ≤ w:=by
  by_contra tooLate
  have earlier:=lt_of_not_ge tooLate
  have same:=(b75 reads output forward live route (le_of_lt earlier)).2
  rw [b35 reads output forward live stopped] at same
  exact (ne_of_lt earlier) same
lemma b168 {v a b : Fin m} (route : ReflTransGen reads v a) (edge : reads a b)
    (bound : b ≤ first reads output forward live v) : Follow reads output a b:=by
  have earlier:=lt_of_lt_of_le (forward edge) bound
  have same:=(b75 reads output forward live route (le_of_lt earlier)).2
  refine ⟨edge,fun stopped => ?_⟩
  rw [b35 reads output forward live stopped] at same
  exact (ne_of_lt earlier) same
def Avoid (cut v w : Fin m) : Prop:=reads v w /\ v≠cut
lemma b123 (cut : Fin m) {v w : Fin m} (route : ReflTransGen (Avoid reads cut) v w) :
    ReflTransGen reads v w:=by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1
lemma b122 {v w : Fin m}
    (route : ReflTransGen (Avoid reads (first reads output forward live v)) v w) :
    w ≤ first reads output forward live v:=by
  induction route with
  | refl => exact b141 reads output forward live v
  | tail prior edge ih =>
    have label:=(b75 reads output forward live (b123 reads _ prior) ih).2
    have earlier:=lt_of_le_of_ne ih edge.2
    have following : Follow reads output _ _:=⟨edge.1,fun terminal => by
      rw [b35 reads output forward live terminal] at label
      exact (ne_of_lt earlier) label⟩
    have same:=(b108 reads output forward live following).symm.trans label
    rw [← same]
    exact b141 reads output forward live _
lemma no_avoiding_after {v w : Fin m} (after : first reads output forward live v < w) :
    ¬ ReflTransGen (Avoid reads (first reads output forward live v)) v w :=
  fun route => (not_lt_of_ge (b122 reads output forward live route)) after
include forward in
lemma b90 {source a b goal : Fin m}
    (routeA : ReflTransGen (Follow reads output) source a) (edgeA : Follow reads output a goal)
    (routeB : ReflTransGen (Follow reads output) source b) (edgeB : Follow reads output b goal) : a=b:=by
  let distance (w : Fin m):=m - w.val
  induction source using (measure distance).wf.induction generalizing a b with
  | h source ih =>
    rcases routeA.cases_head with aHere | ⟨nextA,stepA,laterA⟩
    · subst a
      rcases routeB.cases_head with bHere | ⟨next,stepB,later⟩
      · exact bHere
      have equal : next=goal:=b72 reads output stepB edgeA
      subst next
      have increasing:=b119 reads forward (b38 reads output later)
      exact (not_lt_of_ge increasing (forward edgeB.1)).elim
    · rcases routeB.cases_head with bHere | ⟨nextB,stepB,laterB⟩
      · subst b
        have equal : nextA=goal:=b72 reads output stepA edgeB
        subst nextA
        have increasing:=b119 reads forward (b38 reads output laterA)
        exact (not_lt_of_ge increasing (forward edgeA.1)).elim
      have equal:=b72 reads output stepA stepB
      subst nextB
      have increase:=forward stepA.1
      have closer : distance nextA < distance source:=by
        dsimp [distance]
        have bounds:=nextA.isLt
        change source.val < nextA.val at increase
        omega
      exact ih nextA closer laterA edgeA laterB edgeB
lemma b89 {source a b goal : Fin m}
    (bound : goal ≤ first reads output forward live source)
    (routeA : ReflTransGen reads source a) (edgeA : reads a goal)
    (routeB : ReflTransGen reads source b) (edgeB : reads b goal) : a=b:=by
  have aBound:=le_trans (le_of_lt (forward edgeA)) bound
  have bBound:=le_trans (le_of_lt (forward edgeB)) bound
  exact b90 reads output forward
    (b75 reads output forward live routeA aBound).1
    (b168 reads output forward live routeA edgeA bound)
    (b75 reads output forward live routeB bBound).1
    (b168 reads output forward live routeB edgeB bound)
lemma b54 {α : Type*} (weight : α -> Nat) (xs : List α)
    (positive : 0 < (xs.map weight).sum) : ∃ a ∈ xs,0 < weight a:=by
  induction xs with
  | nil => simp at positive
  | cons a rest ih =>
    by_cases h : 0 < weight a
    · exact ⟨a,by simp,h⟩
    have hr : 0 < (rest.map weight).sum:=by
      simp only [List.map_cons,List.sum_cons] at positive
      omega
    obtain ⟨b,hb,hbPos⟩:=ih hr
    exact ⟨b,by simp [hb],hbPos⟩
lemma b62 {α : Type*} (weight : α -> Nat) (xs : List α)
    (distinct : xs.Nodup) (small : ∀ a ∈ xs,weight a ≤ 1)
    (unique : ∀ a ∈ xs,∀ b ∈ xs,0 < weight a -> 0 < weight b -> a=b) :
    (xs.map weight).sum ≤ 1:=by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.nodup_cons] at distinct
    simp only [List.map_cons,List.sum_cons]
    by_cases h : weight a=0
    · rw [h,Nat.zero_add]
      exact ih distinct.2 (fun b hb => small b (by simp [hb]))
        (fun b hb c hc => unique b (by simp [hb]) c (by simp [hc]))
    have restZero : (rest.map weight).sum=0:=by
      by_contra some
      obtain ⟨b,hb,hbPos⟩:=b54 weight rest (by omega)
      have equal:=unique a (by simp) b (by simp [hb]) (by omega) hbPos
      exact distinct.1 (by simpa [equal] using hb)
    rw [restZero,Nat.add_zero]
    exact small a (by simp)
section Count
variable (parents : Fin m -> List (Fin m))
variable (reads_parent : ∀ a b : Fin m,reads a b↔a ∈ parents b)
variable (weight : Fin m -> Nat) (source : Fin m)
variable (other_weight : ∀ v : Fin m,v≠source -> weight v=((parents v).map weight).sum)
include forward reads_parent other_weight in
lemma b66 {v : Fin m} (positive : 0 < weight v) : ReflTransGen reads source v:=by
  revert positive
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro positive
    by_cases isSource : v=source
    · subst v
      exact ReflTransGen.refl
    rw [other_weight v isSource] at positive
    obtain ⟨a,member,hp⟩:=b54 weight (parents v) positive
    have edge:=(reads_parent a v).mpr member
    have earlier:=forward edge
    exact (ih a earlier hp).tail edge
include reads_parent other_weight in
lemma weight_before_le_one (rootWeight : weight source=1) (distinct : ∀ v,(parents v).Nodup)
    {v : Fin m} (bound : v ≤ first reads output forward live source) : weight v ≤ 1:=by
  revert bound
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro bound
    by_cases isSource : v=source
    · subst v
      exact le_of_eq rootWeight
    rw [other_weight v isSource]
    apply b62 weight (parents v) (distinct v)
    · intro a member
      have earlier:=forward ((reads_parent a v).mpr member)
      exact ih a earlier (le_trans (le_of_lt earlier) bound)
    · intro a ma b mb ha hb
      exact b89 reads output forward live bound
        (b66 reads forward parents reads_parent weight source other_weight ha)
        ((reads_parent a v).mpr ma)
        (b66 reads forward parents reads_parent weight source other_weight hb)
        ((reads_parent b v).mpr mb)
end Count
end FirstBranchRoute
namespace PetersenFirstGroup
open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutFormula PetersenCutIndependent PetersenCutTrace PetersenScratch
noncomputable def firstInputBoundary {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out -> ∃ v,b5 gs w v)
    (i : Fin n) : Fin (n + gs.length) :=
  FirstBranchRoute.first (b5 gs) out (b15 clean) live (b8 gs i)
noncomputable def firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out -> ∃ v,b5 gs w v)
    (cut : Fin (n + gs.length)) : Finset (Fin n) :=
  Finset.univ.filter fun i => firstInputBoundary clean out live i=cut
lemma b48 {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out -> ∃ v,b5 gs w v)
    (cut : Fin (n + gs.length)) (i : Fin n) :
    i ∈ firstInputGroup clean out live cut↔firstInputBoundary clean out live i=cut:=by
  simp [firstInputGroup]
lemma b130 {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out -> ∃ v,b5 gs w v)
    (w : Fin (n + gs.length)) : w ≤ out:=by
  let last : Fin (n + gs.length):=⟨n + gs.length - 1,by have:=out.isLt; omega⟩
  have top (v : Fin (n + gs.length)) : v ≤ last:=by
    change v.val ≤ n + gs.length - 1
    have:=v.isLt
    omega
  have lastOut : last=out:=by
    by_contra notOutput
    obtain ⟨v,e⟩:=live last notOutput
    exact (not_lt_of_ge (top v)) (b15 clean e)
  exact lastOut ▸ top w
lemma b17 {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out -> ∃ v,b5 gs w v)
    (distinct : ∀ w,(b10 clean w).Nodup)
    (fallback chosen : Fin n) :
    b0 chosen (b2 fallback gs (firstInputBoundary clean out live chosen).val)
      ≤ 1:=by
  let weight (a : Fin (n + gs.length)):=b0 chosen (b2 fallback gs a.val)
  have sourcePrimary : (b8 gs chosen).val < n:=chosen.isLt
  have atSource : weight (b8 gs chosen)=1:=by
    dsimp [weight]
    rw [b30 fallback chosen _ sourcePrimary,ite_eq_left rfl]
  have otherWeight : ∀ w : Fin (n + gs.length),w≠b8 gs chosen →
      weight w=((b10 clean w).map weight).sum:=by
    intro w other
    by_cases primary : w.val < n
    · simp [weight,b30 fallback chosen w primary,other,
        b111 clean w primary]
    · let p:=w.val - n
      have hp : p < gs.length:=by have:=w.isLt; dsimp [p]; omega
      have hw : w.val=n + p:=by dsimp [p]; omega
      let g:=gs[p]
      have atSlot : gs[p]?=some g:=List.getElem?_eq_getElem hp
      exact b84 fallback chosen clean atSlot hw _
        (b116 clean w atSlot hw)
  exact FirstBranchRoute.weight_before_le_one (b5 gs) out (b15 clean) live
    (b10 clean) (fun a b => (b158 clean a b).symm) weight
    (b8 gs chosen) otherWeight atSource distinct le_rfl
lemma b86 {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out -> ∃ v,b5 gs w v)
    (cut : Fin (n + gs.length)) :
    cut=out \/ ∀ k : Fin n,k ∈ firstInputGroup clean out live cut →
      ¬ Relation.ReflTransGen (avoid (b5 gs) cut) (b8 gs k) out:=by
  by_cases terminal : cut=out
  · exact Or.inl terminal
  right
  intro k member path
  have before : cut < out:=lt_of_le_of_ne (b130 clean out live cut) terminal
  have firstHere:=(b48 clean out live cut k).mp member
  have after : firstInputBoundary clean out live k < out:=by rwa [firstHere]
  have blocked:=FirstBranchRoute.no_avoiding_after (b5 gs) out
    (b15 clean) live after
  apply blocked
  change Relation.ReflTransGen (FirstBranchRoute.Avoid (b5 gs)
    (firstInputBoundary clean out live k)) (b8 gs k) out
  rw [firstHere]
  exact Relation.ReflTransGen.mono (fun _ _ e => ⟨e.1,e.2.1⟩) _ _ path
lemma b80 {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out -> ∃ v,b5 gs w v)
    (distinct : ∀ w,(b10 clean w).Nodup)
    (G : SimpleGraph (Fin n)) (computes : ∀ x,vl gs x out.val=edgeValue G x)
    (witnesses : ∀ i j,G.Adj i j -> ∃ u v,
      G.Adj i u /\ G.Adj j v /\ u≠j /\ v≠i /\ ¬ G.Adj u v)
    (cut : Fin (n + gs.length)) : BranchGraph.Independent G (firstInputGroup clean out live cut):=by
  intro i iIn j jIn adjacent
  obtain ⟨u,v,hiu,hjv,huj,hvi,huv⟩:=witnesses i j adjacent
  have iFirst:=(b48 clean out live cut i).mp iIn
  have jFirst:=(b48 clean out live cut j).mp jIn
  have iCount:=b17 clean out live distinct i i
  have jCount:=b17 clean out live distinct i j
  rw [iFirst] at iCount
  rw [jFirst] at jCount
  refine b124 clean G cut out computes i j u v adjacent hiu hjv huj hvi
    huv iCount jCount ?_
  rcases b86 clean out live cut with stopped | blocked
  · exact Or.inl stopped
  · exact Or.inr (fun k hk => blocked k (hk.elim (fun h => h.symm ▸ iIn) (fun h => h.symm ▸ jIn)))
end PetersenFirstGroup
namespace PetersenNine
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev Vertex:=Fin 9
abbrev Edges:=List (Vertex × Vertex)
def edges : Edges:=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
def edgeFun (es : Edges) (x : Vertex -> Bool) : Bool :=
  es.any (fun edge => x edge.1&&x edge.2)
lemma noLoops : ∀ e ∈ edges,e.1≠e.2:=by decide
lemma edgeFun_true (es : Edges) (x : Vertex -> Bool) :
    edgeFun es x=true↔∃ a b,(a,b) ∈ es /\ x a=true /\ x b=true:=by
  simp only [edgeFun,List.any_eq_true,Bool.and_eq_true,Prod.exists]
def graph (es : Edges) (noSelf : ∀ e ∈ es,e.1≠e.2) : SimpleGraph Vertex where
  Adj a b:=(a,b) ∈ es \/ (b,a) ∈ es
  symm:=⟨fun _ _ => Or.symm⟩
  loopless:=⟨fun v h => h.elim (fun he => noSelf (v,v) he rfl) (fun he => noSelf (v,v) he rfl)⟩
end PetersenNine
namespace PetersenGroupBFS
def b7:=Nat × (Nat -> Nat)
def b7.width (g : b7):=g.1
def b7.adjacency (g : b7):=g.2
def bit (vertex : Nat) : Nat :=
  Nat.shiftLeft 1 vertex
def b71 (g : b7) : Nat :=
  bit g.width - 1
def b3 (g : b7) (deleted vertex : Nat) : Nat :=
  Nat.land (g.adjacency vertex) (Nat.xor (b71 g) deleted)
def closeIsolates (g : b7) (deleted : Nat) : Nat :=
  (List.range g.width).foldl
    (fun mask v => if b3 g deleted v=0 then Nat.lor mask (bit v) else mask)
    deleted
def b74 (g : b7) (deleted vertex : Nat) : Nat :=
  (List.range g.width).foldl
    (fun mask v => if !(Nat.testBit deleted v) &&
        (b3 g deleted v==b3 g deleted vertex)
      then Nat.lor mask (bit v) else mask)
    0
lemma bit_at (v w : Nat) : (bit v).testBit w=decide (v=w):=by
  simp [bit,Nat.shiftLeft_eq,Nat.testBit_two_pow]
lemma b194 (g : b7) (w : Nat) :
    (b71 g).testBit w=decide (w < g.width):=by
  simp [b71,bit,Nat.shiftLeft_eq]
lemma b191 (g : b7) (deleted v w : Nat) (hw : w < g.width) :
    (b3 g deleted v).testBit w =
      ((g.adjacency v).testBit w&&!(deleted.testBit w)):=by
  simp [b3,Nat.testBit_xor,b194,hw]
private lemma b152 (vertices : List Nat) (p : Nat -> Prop) [DecidablePred p]
    (initial w : Nat) :
    (vertices.foldl (fun m v => if p v then Nat.lor m (bit v) else m) initial).testBit w =
      (initial.testBit w||(vertices.any fun v => decide (p v)&&(v==w))):=by
  induction vertices generalizing initial with
  | nil => simp
  | cons v vertices ih =>
    simp only [List.foldl_cons,List.any_cons]
    rw [ih]
    by_cases h : p v <;> simp [h,bit_at,Bool.or_assoc,Bool.beq_eq_decide_eq]
private lemma b170 (p : Nat -> Prop) [DecidablePred p] (n w : Nat) :
    ((List.range n).any fun v => decide (p v)&&(v==w)) =
      (decide (w < n)&&decide (p w)):=by
  rw [Bool.eq_iff_iff,List.any_eq_true,Bool.and_eq_true]
  simp only [List.mem_range,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
  constructor
  · rintro ⟨v,hv,hp,rfl⟩
    exact ⟨hv,hp⟩
  · rintro ⟨hw,hp⟩
    exact ⟨w,hw,hp,rfl⟩
lemma close_at (g : b7) (deleted w : Nat) :
    (closeIsolates g deleted).testBit w =
      (deleted.testBit w||(decide (w < g.width)&&decide (b3 g deleted w=0))):=by
  unfold closeIsolates
  rw [b152,b170]
lemma class_at (g : b7) (deleted v w : Nat) :
    (b74 g deleted v).testBit w =
      (decide (w < g.width) &&
        (!(deleted.testBit w)&&(b3 g deleted w==b3 g deleted v))):=by
  unfold b74
  rw [b152,b170]
  simp [Bool.beq_eq_decide_eq]
lemma b52 (width : Nat) : bit width=2 ^ width:=by
  simp [bit,Nat.shiftLeft_eq]
lemma b192 {width a b : Nat} (ha : a < bit width) (hb : b < bit width) :
    Nat.lor a b < bit width:=by
  rw [b52] at ha hb ⊢
  exact Nat.or_lt_two_pow ha hb
lemma b126 {width m w : Nat} (hm : m < bit width) (hw : width ≤ w) :
    m.testBit w=false:=by
  rw [b52] at hm
  exact Nat.testBit_lt_two_pow (hm.trans_le (Nat.pow_le_pow_right (by decide) hw))
lemma mask_ext {width a b : Nat} (ha : a < bit width) (hb : b < bit width)
    (same : ∀ w < width,a.testBit w=b.testBit w) : a=b:=by
  apply Nat.eq_of_testBit_eq
  intro w
  by_cases hw : w < width
  · exact same w hw
  · rw [b126 ha (Nat.le_of_not_gt hw),b126 hb (Nat.le_of_not_gt hw)]
lemma b64 (g : b7) (deleted v : Nat) (hd : deleted < bit g.width) :
    b3 g deleted v < bit g.width:=by
  rw [b52]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [b3,b194,Nat.not_lt_of_ge hw,b126 hd hw]
lemma b142 (g : b7) (deleted : Nat) (hd : deleted < bit g.width) :
    closeIsolates g deleted < bit g.width:=by
  rw [b52]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [close_at,Nat.not_lt_of_ge hw,b126 hd hw]
lemma b181 (g : b7) (deleted v : Nat) :
    b74 g deleted v < bit g.width:=by
  rw [b52]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [class_at,Nat.not_lt_of_ge hw]
def step (g : b7) (deleted : Nat) : List Nat :=
  deleted :: (List.range g.width).filterMap fun v =>
    if !(Nat.testBit deleted v)&&(b3 g deleted v != 0)
    then some (closeIsolates g (Nat.lor deleted (b74 g deleted v)))
    else none
def b34 (g : b7) : Nat -> List Nat
  | 0 => [closeIsolates g 0]
  | depth + 1 => ((b34 g depth).flatMap (step g)).eraseDups
lemma advance {g : b7} {depth deleted next : Nat}
    (hd : deleted ∈ b34 g depth) (hs : next ∈ step g deleted) :
    next ∈ b34 g (depth + 1):=by
  rw [b34,List.mem_eraseDups,List.mem_flatMap]
  exact ⟨deleted,hd,hs⟩
lemma stay {g : b7} {depth deleted : Nat} (hd : deleted ∈ b34 g depth) :
    deleted ∈ b34 g (depth + 1) :=
  advance hd (by simp [step])
lemma b183 {g : b7} {depth deleted vertex : Nat}
    (hd : deleted ∈ b34 g depth) (hv : vertex < g.width)
    (hlive : Nat.testBit deleted vertex=false)
    (hne : b3 g deleted vertex≠0) :
    closeIsolates g (Nat.lor deleted (b74 g deleted vertex)) ∈ b34 g (depth + 1):=by
  apply advance hd
  apply List.mem_cons_of_mem
  rw [List.mem_filterMap]
  refine ⟨vertex,List.mem_range.mpr hv,?_⟩
  simp [hlive,hne]
def petersenNine : b7 :=
  ⟨9,fun v => (#[50,69,138,276,9,385,258,36,104] : Array Nat)[v]?.getD 0⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b117 : b71 petersenNine ∉ b34 petersenNine 4:=by
  decide +kernel
end PetersenGroupBFS
namespace PetersenMaskBridge
open PetersenGroupBFS
open BranchGraph
def decode (g : b7) (mask : Nat) : Finset (Fin g.width) :=
  Finset.univ.filter (fun v => mask.testBit v.val)
@[simp] lemma mem_decode (g : b7) (mask : Nat) (v : Fin g.width) :
    v ∈ decode g mask↔mask.testBit v.val=true:=by
  simp [decode]
@[simp] lemma decode_zero (g : b7) : decode g 0=∅:=by
  ext v
  simp
@[simp] lemma decode_full (g : b7) : decode g (b71 g)=Finset.univ:=by
  ext v
  simp [b194,v.isLt]
lemma decode_or (g : b7) (a b : Nat) :
    decode g (Nat.lor a b)=decode g a ∪ decode g b:=by
  ext v
  simp [Bool.or_eq_true]
lemma b148 (g : b7) {a b : Nat} (ha : a < bit g.width) (hb : b < bit g.width)
    (same : decode g a=decode g b) : a=b:=by
  apply mask_ext ha hb
  intro w hw
  have hm : (⟨w,hw⟩ : Fin g.width) ∈ decode g a↔(⟨w,hw⟩ : Fin g.width) ∈ decode g b:=by
    rw [same]
  simp only [mem_decode] at hm
  exact Bool.eq_iff_iff.mpr hm
lemma b182 (n : Nat) : 0 < bit n:=by
  rw [b52]
  exact Nat.two_pow_pos n
lemma b185 (g : b7) : b71 g < bit g.width:=by
  unfold b71
  have:=b182 g.width
  omega
section Graph
variable (g : b7) (G : SimpleGraph (Fin g.width)) [DecidableRel G.Adj]
variable (adj : ∀ u v : Fin g.width,G.Adj u v↔(g.adjacency u.val).testBit v.val=true)
include adj in
lemma b44 (deleted : Nat) (u : Fin g.width) :
    decode g (b3 g deleted u.val)=neighborsAfter G (decode g deleted) u:=by
  ext v
  cases h : deleted.testBit v.val <;>
    simp [mem_decode,neighborsAfter,b191 g deleted u.val v.val v.isLt,adj,h]
include adj in
lemma b95 (deleted : Nat) (bound : deleted < bit g.width) (u : Fin g.width) :
    b3 g deleted u.val=0↔neighborsAfter G (decode g deleted) u=∅:=by
  constructor
  · intro h
    rw [← b44 g G adj,h,decode_zero]
  · intro h
    apply b148 g (b64 g deleted u.val bound) (b182 g.width)
    rw [b44 g G adj,h,decode_zero]
include adj in
lemma b153 (deleted : Nat) (bound : deleted < bit g.width) :
    decode g (PetersenGroupBFS.closeIsolates g deleted)=BranchGraph.closeIsolates G (decode g deleted):=by
  ext v
  simp [close_at,v.isLt,BranchGraph.closeIsolates,b106,Bool.or_eq_true,
    b95 g G adj deleted bound]
include adj in
lemma b187 (deleted : Nat) (bound : deleted < bit g.width) (root : Fin g.width)
    (outside : root ∉ decode g deleted) (live : (neighborsAfter G (decode g deleted) root).Nonempty) :
    decode g (b74 g deleted root.val)=b24 G (decode g deleted) root:=by
  have same (u : Fin g.width) : b3 g deleted u.val=b3 g deleted root.val ↔
      neighborsAfter G (decode g deleted) u=neighborsAfter G (decode g deleted) root:=by
    rw [← b44 g G adj deleted u,← b44 g G adj deleted root]
    exact ⟨congrArg (decode g),b148 g (b64 g deleted u.val bound)
      (b64 g deleted root.val bound)⟩
  ext v
  cases h : deleted.testBit v.val <;>
    simp [class_at,v.isLt,b24,outside,live,h,same,Bool.beq_eq_decide_eq]
def b83 (depth : Nat) (removed : Finset (Fin g.width)) : Prop :=
  ∃ m,m ∈ b34 g depth /\ m < bit g.width /\ decode g m=removed
include adj in
lemma b193 : b83 g 0 (BranchGraph.closeIsolates G ∅):=by
  refine ⟨PetersenGroupBFS.closeIsolates g 0,?_,
    b142 g 0 (b182 g.width),?_⟩
  · change PetersenGroupBFS.closeIsolates g 0 ∈ [PetersenGroupBFS.closeIsolates g 0]
    exact List.mem_cons_self
  · rw [b153 g G adj _ (b182 g.width),decode_zero]
include adj in
lemma b197 {depth : Nat} {removed : Finset (Fin g.width)} (root : Fin g.width)
    (rep : b83 g depth removed) (closed : BranchGraph.closeIsolates G removed=removed) :
    b83 g (depth + 1) (b20 G removed root):=by
  obtain ⟨m,hm,bounded,same⟩:=rep
  subst removed
  by_cases active : root ∉ decode g m /\ (neighborsAfter G (decode g m) root).Nonempty
  · have live : m.testBit root.val=false:=by
      cases h : m.testBit root.val
      · rfl
      · exact (active.1 ((mem_decode g m root).mpr h)).elim
    have someNeighbor : b3 g m root.val≠0:=by
      intro h
      have none:=(b95 g G adj m bounded root).mp h
      simpa [none] using active.2
    have united:=b192 bounded (b181 g m root.val)
    refine ⟨PetersenGroupBFS.closeIsolates g (Nat.lor m (b74 g m root.val)),
      b183 hm root.isLt live someNeighbor,b142 g _ united,?_⟩
    rw [b153 g G adj _ united,decode_or,b187 g G adj m bounded root active.1 active.2,
      b20]
  · have sameRemoval : b20 G (decode g m) root=decode g m:=by
      have emptyClass : b24 G (decode g m) root=∅:=ite_eq_right active
      simp only [b20,emptyClass,Finset.union_empty,closed]
    exact ⟨m,stay hm,bounded,sameRemoval.symm⟩
include adj in
lemma simulate {count depth : Nat} {start finish : Finset (Fin g.width)}
    (walk : b102 G count start finish) (initial : b83 g depth start)
    (closed : BranchGraph.closeIsolates G start=start) : b83 g (depth + count) finish:=by
  induction count generalizing depth start with
  | zero =>
    change finish=start at walk
    simpa only [walk,Nat.add_zero] using initial
  | succ count ih =>
    obtain ⟨root,next⟩:=walk
    have nextClosed : BranchGraph.closeIsolates G (b20 G start root)=b20 G start root :=
      b51 G _
    have rest:=ih next (b197 g G adj root initial closed) nextClosed
    simpa only [Nat.add_assoc,Nat.add_comm 1 count] using rest
lemma b195 {m k r : Nat} (reached : m ∈ b34 g k) (budget : k ≤ r) : m ∈ b34 g r:=by
  induction r with
  | zero =>
    have : k=0:=by omega
    simpa only [this] using reached
  | succ r ih =>
    by_cases eq : k=r + 1
    · simpa [eq] using reached
    · exact stay (ih (by omega))
include adj in
lemma b128 [Nonempty (Fin g.width)] (k : Nat) (noFinish : b71 g ∉ b34 g k)
    (groups : List (Finset (Fin g.width))) (twins : b60 G ∅ groups)
    (finished : b19 G (b13 ∅ groups)) : k < groups.length:=by
  by_contra! budget
  have walk:=b58 G groups twins finished
  obtain ⟨m,reached,bound,allGone⟩ :=
    simulate g G adj walk (b193 g G adj) (b51 G ∅)
  have equal : m=b71 g:=b148 g bound (b185 g) (by simpa using allGone)
  rw [equal,Nat.zero_add] at reached
  exact noFinish (b195 g reached budget)
end Graph
lemma petersen_nine_groups_need_five (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj]
    (adj : ∀ u v : Fin 9,G.Adj u v↔(petersenNine.adjacency u.val).testBit v.val=true)
    (groups : List (Finset (Fin 9))) (twins : b60 G ∅ groups)
    (finished : b19 G (b13 ∅ groups)) : 5 ≤ groups.length :=
  @b128 petersenNine G (inferInstance : DecidableRel G.Adj) adj
    (inferInstance : Nonempty (Fin 9)) 4 b117 groups twins finished
end PetersenMaskBridge
open PetersenNine
def b6 : SimpleGraph Vertex:=graph edges noLoops
def b37 : DecidableRel b6.Adj:=fun a b =>
  inferInstanceAs (Decidable ((a,b) ∈ edges \/ (b,a) ∈ edges))
lemma b77 (S : Finset Vertex) :
    edgeFun edges (fun i => decide (i ∈ S))=true ↔
      BranchGraph.containsEdge b6 S:=by
  constructor
  · intro h
    obtain ⟨a,b,edge,ha,hb⟩:=(edgeFun_true edges _).mp h
    exact ⟨a,of_decide_eq_true ha,b,of_decide_eq_true hb,Or.inl edge⟩
  · rintro ⟨a,ha,b,hb,adjacent⟩
    change (a,b) ∈ edges \/ (b,a) ∈ edges at adjacent
    apply (edgeFun_true edges _).mpr
    rcases adjacent with edge | edge
    · exact ⟨a,b,edge,decide_eq_true ha,decide_eq_true hb⟩
    · exact ⟨b,a,edge,decide_eq_true hb,decide_eq_true ha⟩
lemma b76 :
    ∀ a b : Vertex,b6.Adj a b ↔
      (PetersenGroupBFS.petersenNine.adjacency a.val).testBit b.val=true:=by
  letI : DecidableRel b6.Adj:=b37
  decide
lemma b53 :
    ∀ i j : Vertex,b6.Adj i j →
      ∃ u v,b6.Adj i u /\ b6.Adj j v ∧
        u≠j /\ v≠i /\ ¬ b6.Adj u v:=by
  letI : DecidableRel b6.Adj:=b37
  decide
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open scoped BigOperators
def b14 (gs : List Gate) : List Nat:=gs.flatMap Gate.inputs
def b49 (gs : List Gate) : Nat:=(gs.filter fun g => isNotGate g.op).length
lemma b46 {gs : List Gate} {slot wire : Nat} (read : Reads gs slot wire) :
    wire ∈ b14 gs:=by
  obtain ⟨g,gAt,before⟩:=read
  exact List.mem_flatMap.mpr ⟨g,List.mem_iff_getElem?.mpr ⟨slot,gAt⟩,before⟩
lemma b91 {gs : List Gate} {wire p q : Nat}
    (neq : p≠q) (first : Reads gs p wire) (second : Reads gs q wire) :
    2 ≤ (b14 gs).count wire:=by
  induction gs generalizing p q with
  | nil =>
    rcases first with ⟨g,atGate,_⟩
    simp at atGate
  | cons a rest ih =>
    simp only [b14,List.flatMap_cons,List.count_append]
    cases p with
    | zero =>
      cases q with
      | zero => exact (neq rfl).elim
      | succ q =>
        have atA : wire ∈ a.inputs:=by simpa [Reads] using first
        have later : Reads rest q wire:=by simpa [Reads] using second
        have aPos : 0 < a.inputs.count wire:=List.count_pos_iff.mpr atA
        have restPos : 0 < (b14 rest).count wire:=List.count_pos_iff.mpr (b46 later)
        simp only [b14] at restPos
        omega
    | succ p =>
      cases q with
      | zero =>
        have atA : wire ∈ a.inputs:=by simpa [Reads] using second
        have later : Reads rest p wire:=by simpa [Reads] using first
        have aPos : 0 < a.inputs.count wire:=List.count_pos_iff.mpr atA
        have restPos : 0 < (b14 rest).count wire:=List.count_pos_iff.mpr (b46 later)
        simp only [b14] at restPos
        omega
      | succ q =>
        have early : Reads rest p wire:=by simpa [Reads] using first
        have late : Reads rest q wire:=by simpa [Reads] using second
        have different : p≠q:=fun eq => neq (congrArg Nat.succ eq)
        have count:=ih different early late
        simp only [b14] at count
        omega
lemma b120 (gs : List Gate)
    (arity : ∀ g ∈ gs,g.inputs.length + (if isNotGate g.op then 1 else 0)=2) :
    (b14 gs).length + b49 gs=2 * gs.length:=by
  induction gs with
  | nil => simp [b14,b49]
  | cons g gs ih =>
    have gArity:=arity g (by simp)
    have rest:=ih (fun q hq => arity q (List.mem_cons_of_mem _ hq))
    cases h : isNotGate g.op
    · simp [h] at gArity
      simp [b14,b49,h] at rest ⊢
      omega
    · simp [h] at gArity
      simp [b14,b49,h] at rest ⊢
      omega
lemma b159 {n : Nat} {gs : List Gate} (h : CleanL n gs) :
    ∀ g ∈ gs,g.inputs.length + (if isNotGate g.op then 1 else 0)=2:=by
  intro g gMem
  obtain ⟨p,atGate⟩:=List.mem_iff_getElem?.mp gMem
  rcases h p g atGate with ⟨op,a,_,args⟩ | ⟨ops,a,b,_,_,args⟩
  · simp [op,args,isNotGate]
  · rcases ops with op | op <;> simp [op,args,isNotGate]
lemma b40 (gs : List Gate) (branches : Finset Nat)
    (twice : ∀ w ∈ branches,2 ≤ (b14 gs).count w) :
    branches.card + (b14 gs).toFinset.card ≤ (b14 gs).length:=by
  classical
  let W:=(b14 gs).toFinset
  have subset : branches ⊆ W:=by
    intro w wm
    have t:=twice w wm
    exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by omega))
  have aux : (∑ w ∈ W,if w ∈ branches then (1 : Nat) else 0)=branches.card:=by
    have same : (∑ w ∈ W,if w ∈ branches then (1 : Nat) else 0) =
        ∑ w ∈ branches,if w ∈ branches then (1 : Nat) else 0:=by
      symm
      apply Finset.sum_subset subset
      intro w _ notBranch
      simp [notBranch]
    rw [same]
    simp
  have total : (∑ w ∈ W,(b14 gs).count w)=(b14 gs).length :=
    List.sum_toFinset_count_eq_length _
  have bound : (∑ w ∈ W,((if w ∈ branches then (1 : Nat) else 0) + 1)) ≤
      ∑ w ∈ W,(b14 gs).count w:=by
    apply Finset.sum_le_sum
    intro w wIn
    by_cases b : w ∈ branches
    · simpa [b] using twice w b
    · have pos : 0 < (b14 gs).count w:=List.count_pos_iff.mpr (List.mem_toFinset.mp wIn)
      simpa [b] using pos
  rw [Finset.sum_add_distrib,aux,total] at bound
  simpa [W] using bound
lemma b160 {n out : Nat} {gs : List Gate} (clean : CleanL n gs)
    (outValid : out < n + gs.length)
    (everyNonoutputUsed : ∀ w < n + gs.length,w≠out -> ∃ p,Reads gs p w)
    (branches : Finset Nat)
    (twoReaders : ∀ w ∈ branches,∃ p q,p≠q /\ Reads gs p w /\ Reads gs q w) :
    branches.card + (n + gs.length - 1) + b49 gs ≤ 2 * gs.length:=by
  let W:=(b14 gs).toFinset
  let required:=(Finset.range (n + gs.length)).erase out
  have requiredUsed : required ⊆ W:=by
    intro w inSet
    have spec:=Finset.mem_erase.mp inSet
    obtain ⟨p,read⟩:=everyNonoutputUsed w (Finset.mem_range.mp spec.2) spec.1
    exact List.mem_toFinset.mpr (b46 read)
  have numRequired : required.card=n + gs.length - 1:=by
    change ((Finset.range (n + gs.length)).erase out).card=_
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr outValid),Finset.card_range]
  have twice : ∀ w ∈ branches,2 ≤ (b14 gs).count w:=by
    intro w mem
    obtain ⟨p,q,different,pReads,qReads⟩:=twoReaders w mem
    exact b91 different pReads qReads
  have up:=b40 gs branches twice
  have used:=Finset.card_le_card requiredUsed
  rw [numRequired] at used
  have total:=b120 gs (b159 clean)
  change n + gs.length - 1 ≤ (b14 gs).toFinset.card at used
  omega
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open PetersenCutTrace
lemma b68 {n out : Nat} {gs : List Gate}
    {f : (Fin n -> Bool) -> Bool} (least : Least n f gs out) (nonnull : ∃ x y,f x≠f y)
    (dependent : ∀ v : Fin n,Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool),∃ x y,
      f (Function.update x v b)≠f (Function.update y v b))
    (outValid : out < n + gs.length) :
    ∀ w : Fin (n + gs.length),w≠(⟨out,outValid⟩ : Fin (n + gs.length)) -> ∃ v,b5 gs w v:=by
  intro w notOutput
  have notSame : w.val≠out:=fun eq => notOutput (Fin.ext eq)
  obtain ⟨p,g,atSlot,reads,bound⟩ :=
    b79 least nonnull dependent stillNonconstant w notSame
  exact ⟨⟨n + p,bound⟩,p,g,atSlot,rfl,reads⟩
lemma b88 {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)}
    (fork : FirstBranchRoute.Branches (b5 gs) w) :
    ∃ p q,p≠q /\ Reads gs p w.val /\ Reads gs q w.val:=by
  obtain ⟨first,next,pRead,qRead,separate⟩:=fork
  obtain ⟨p,g,atP,src,ap⟩:=pRead
  obtain ⟨q,h,atQ,dst,aq⟩:=qRead
  refine ⟨p,q,?_,⟨g,atP,ap⟩,⟨h,atQ,aq⟩⟩
  intro same
  subst q
  exact separate (Fin.ext (src.trans dst.symm))
noncomputable def circuitBranchWires {n : Nat} (gs : List Gate) : Finset (Fin (n + gs.length)):=by
  classical
  exact (Finset.univ).filter fun w => FirstBranchRoute.Branches (b5 gs) w
lemma b25 {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)} :
    w ∈ circuitBranchWires gs↔FirstBranchRoute.Branches (b5 gs) w:=by
  classical
  simp [circuitBranchWires]
def b93 {V W : Type} [Fintype V] (label : V -> W) [DecidableEq W] (cut : W) : Finset V :=
  Finset.univ.filter fun v => label v=cut
def b26 {V W : Type} [Fintype V] (label : V -> W) [LinearOrder W] (cut : W) : Finset V :=
  Finset.univ.filter fun v => label v < cut
lemma b189 {V W : Type} [Fintype V] (label : V -> W) [DecidableEq W] (cut : W) (v : V) :
    v ∈ b93 label cut↔label v=cut:=by
  simp [b93]
lemma b143 {V W : Type} [Fintype V] (label : V -> W) [LinearOrder W] (cut : W) (v : V) :
    v ∈ b26 label cut↔label v < cut:=by
  simp [b26]
lemma b82 {V W : Type} [Fintype V] [DecidableEq V] [LinearOrder W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (label : V -> W) (cut : W)
    (independent : BranchGraph.Independent G (b93 label cut))
    (code : Finset V -> Bool) (decode : Bool -> Finset V -> Prop)
    (factors : ∀ I O : Finset V,(∀ i ∈ I,label i=cut) →
      (∀ i ∈ O,cut < label i) -> (BranchGraph.containsEdge G (I ∪ O)↔decode (code I) O)) :
    BranchGraph.TwinGroup G (b26 label cut) (b93 label cut):=by
  intro u uGroup v vGroup uActive vActive
  have later {x y : V} (xGroup : x ∈ b93 label cut) (edge : G.Adj x y)
      (notEarlier : y ∉ b26 label cut) : cut < label y:=by
    have ne : label y≠cut:=fun equal =>
      independent x xGroup y ((b189 label cut y).mpr equal) edge
    have notBefore : ¬ label y < cut:=fun h => notEarlier ((b143 label cut y).mpr h)
    exact lt_of_le_of_ne (le_of_not_gt notBefore) (Ne.symm ne)
  have single (x y : V) (xGroup : x ∈ b93 label cut) (yLater : cut < label y) :
      (G.Adj x y↔decode (code {x}) {y}):=by
    have g (i : V) (mem : i ∈ ({x} : Finset V)) : label i=cut:=by
      have eq : i=x:=Finset.mem_singleton.mp mem
      subst i
      exact (b189 label cut x).mp xGroup
    have h (i : V) (mem : i ∈ ({y} : Finset V)) : cut < label i:=by
      have eq : i=y:=Finset.mem_singleton.mp mem
      rwa [eq]
    simpa [BranchGraph.pair_contains_edge] using factors {x} {y} g h
  have cannot (x : V) (xGroup : x ∈ b93 label cut)
      (active : (BranchGraph.neighborsAfter G (b26 label cut) x).Nonempty) :
      code {x}≠code ∅:=by
    obtain ⟨y,neighbor⟩:=active
    simp only [BranchGraph.neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and] at neighbor
    have yLater:=later xGroup neighbor.1 neighbor.2
    have yes:=(single x y xGroup yLater).mp neighbor.1
    intro collapse
    rw [collapse] at yes
    have one:=(factors ∅ {y} (by simp) (by simpa using yLater)).mpr yes
    exact BranchGraph.singleton_no_edge G y (by simpa using one)
  have a:=cannot u uGroup uActive
  have b:=cannot v vGroup vActive
  have sameCode : code {u}=code {v}:=by
    cases hc : code ∅ <;> cases ha : code {u} <;> cases hb : code {v} <;> simp_all
  ext z
  simp only [BranchGraph.neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨edge,remains⟩
    have pos:=later uGroup edge remains
    refine ⟨(single v z vGroup pos).mpr ?_,remains⟩
    rw [← sameCode]
    exact (single u z uGroup pos).mp edge
  · rintro ⟨edge,remains⟩
    have pos:=later vGroup edge remains
    refine ⟨(single u z uGroup pos).mpr ?_,remains⟩
    rw [sameCode]
    exact (single v z vGroup pos).mp edge
namespace PetersenCutTrace
open PEqualNP.CircuitLowerBounds CircuitProof
open Relation
lemma b100 {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (x y : Fin n -> Bool) (w : Fin (n + gs.length))
    (agrees : ∀ i,ReflTransGen (b5 gs) (b8 gs i) w -> x i=y i) :
    vl gs x w.val=vl gs y w.val:=by
  revert agrees
  induction w using (measure (fun a : Fin (n + gs.length) => a.val)).wf.induction with
  | h w earlier =>
    intro agree
    by_cases input : w.val < n
    · let i : Fin n:=⟨w.val,input⟩
      have name : b8 gs i=w:=Fin.ext rfl
      have atInput : ReflTransGen (b5 gs) (b8 gs i) w:=by
        simpa only [name] using (ReflTransGen.refl : ReflTransGen (b5 gs) w w)
      have a:=agree i atInput
      simpa only [b69 gs x w.val input,b69 gs y w.val input] using a
    · let p:=w.val - n
      have pLt : p < gs.length:=by have:=w.isLt; dsimp [p]; omega
      have gateWire : w.val=n + p:=by dsimp [p]; omega
      let g:=gs[p]'pLt
      have atGate : gs[p]?=some g:=List.getElem?_eq_getElem pLt
      rw [gateWire]
      apply vl_congr gs clean x y p g atGate
      intro a inGate
      have readBefore:=(clean p g atGate).lt a inGate
      let wire : Fin (n + gs.length):=⟨a,by have:=w.isLt; omega⟩
      have read : b5 gs wire w:=⟨p,g,atGate,gateWire,inGate⟩
      apply earlier wire (show wire.val < w.val by change a < w.val; omega)
      intro i path
      exact agree i (path.tail read)
end PetersenCutTrace
open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutTrace Relation
def b55 {n : Nat} (S : Finset (Fin n)) (i : Fin n) : Bool:=decide (i ∈ S)
lemma b97 {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length),v≠out -> ∃ w,b5 gs v w)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (b5 gs) out cut) :
    let label (i : Fin n) :=
      FirstBranchRoute.first (b5 gs) out (b15 clean) live (b8 gs i)
    ∃ code : Finset (Fin n) -> Bool,∃ decode : Bool -> Finset (Fin n) -> Prop,
      ∀ I O : Finset (Fin n),
        (∀ i ∈ I,label i=cut) -> (∀ i ∈ O,cut < label i) →
        (vl gs (b55 (I ∪ O)) out.val=true↔decode (code I) O):=by
  classical
  let label (i : Fin n) :=
    FirstBranchRoute.first (b5 gs) out (b15 clean) live (b8 gs i)
  let code (I : Finset (Fin n)):=vl gs (b55 I) cut.val
  let decode (b : Bool) (O : Finset (Fin n)) :=
    ∃ J : Finset (Fin n),(∀ j ∈ J,label j=cut) /\ code J=b ∧
      vl gs (b55 (J ∪ O)) out.val=true
  refine ⟨code,decode,?_⟩
  intro I O groupI afterO
  change (∀ i ∈ I,label i=cut) at groupI
  change (∀ i ∈ O,cut < label i) at afterO
  change (_↔decode (code I) O)
  constructor
  · exact fun yes => ⟨I,groupI,rfl,yes⟩
  · rintro ⟨J,groupJ,sameCode,yes⟩
    have stable (K : Finset (Fin n)) : vl gs (b55 (K ∪ O)) cut.val=code K:=by
      apply b100 clean
      intro i ancestral
      have limit : label i ≤ cut :=
        FirstBranchRoute.ancestor_first_le (b5 gs) out (b15 clean) live ancestral terminal
      have absent : i ∉ O:=fun mem => (not_lt_of_ge limit) (afterO i mem)
      simp [b55,absent]
    have sameCut : vl gs (b55 (I ∪ O)) cut.val=vl gs (b55 (J ∪ O)) cut.val :=
      (stable I).trans (sameCode.symm.trans (stable J).symm)
    by_cases atOutput : cut=out
    · rw [atOutput] at sameCut
      exact sameCut.trans yes
    have before : cut < out:=lt_of_le_of_ne prior atOutput
    have eq:=b59 clean cut out _ _ sameCut (by
      intro i diff
      have isGroup : label i=cut:=by
        by_contra offGroup
        have notI : i ∉ I:=fun mem => offGroup (groupI i mem)
        have notJ : i ∉ J:=fun mem => offGroup (groupJ i mem)
        exact diff (by simp [b55,notI,notJ])
      intro bypass
      have groupLabel : FirstBranchRoute.first (b5 gs) out (b15 clean) live
          (b8 gs i)=cut:=isGroup
      have forbid:=FirstBranchRoute.no_avoiding_after (b5 gs) out (b15 clean) live
        (v:=b8 gs i) (w:=out) (by simpa [groupLabel] using before)
      apply forbid
      have weaker : ∀ a b,avoid (b5 gs) cut a b -> FirstBranchRoute.Avoid (b5 gs) cut a b :=
        fun _ _ h => ⟨h.1,h.2.1⟩
      have convert : ReflTransGen (FirstBranchRoute.Avoid (b5 gs) cut) (b8 gs i) out :=
        ReflTransGen.mono weaker _ _ bypass
      simpa only [groupLabel] using convert)
    rwa [eq]
open PEqualNP.CircuitLowerBounds CircuitProof
open PetersenCutTrace
lemma b87 {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length),v≠out -> ∃ w,b5 gs v w)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (computes : ∀ S : Finset (Fin n),vl gs (b55 S) out.val=true↔BranchGraph.containsEdge G S)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (b5 gs) out cut)
    (independent : BranchGraph.Independent G
      (b93 (fun i => FirstBranchRoute.first (b5 gs) out (b15 clean) live (b8 gs i)) cut)) :
    let label (i : Fin n):=FirstBranchRoute.first (b5 gs) out (b15 clean) live (b8 gs i)
    BranchGraph.TwinGroup G (b26 label cut) (b93 label cut):=by
  let label (i : Fin n):=FirstBranchRoute.first (b5 gs) out (b15 clean) live (b8 gs i)
  obtain ⟨code,decode,factors⟩:=b97 clean out live cut prior terminal
  change BranchGraph.TwinGroup G (b26 label cut) (b93 label cut)
  exact b82 G label cut independent code decode (by
    intro I O group after
    rw [← computes (I ∪ O)]
    exact factors I O group after)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open PetersenCutTrace PetersenFirstGroup
abbrev petersenF:=edgeFun edges
private lemma b78 : ∀ v : Vertex,∃ w : Vertex,
    petersenF (Function.update (fun i => decide (i=w)) v
      (!(decide (v=w))))≠petersenF (fun i => decide (i=w)):=by
  decide +kernel
lemma b63 (v : Vertex) : Dep petersenF v:=by
  obtain ⟨w,hw⟩:=b78 v
  exact ⟨fun i => decide (i=w),hw⟩
lemma b16 : ∃ x y : Vertex -> Bool,petersenF x≠petersenF y :=
  dep_nc (b63 0)
private lemma b92 : ∀ (v : Vertex) (b : Bool),
    petersenF (Function.update (fun _ => false) v b)=false ∧
    petersenF (Function.update (fun _ => true) v b)=true:=by
  decide +kernel
lemma b27 (v : Vertex) (b : Bool) :
    ∃ x y,petersenF (Function.update x v b)≠petersenF (Function.update y v b):=by
  obtain ⟨no,yes⟩:=b92 v b
  exact ⟨fun _ => false,fun _ => true,by rw [no,yes]; decide⟩
lemma b118 (x : Fin 9 -> Bool) : petersenF x=true ↔
    ∃ u v : Fin 9,b6.Adj u v /\ x u=true /\ x v=true:=by
  change PetersenNine.edgeFun PetersenNine.edges x=true↔_
  rw [PetersenNine.edgeFun_true]
  constructor
  · rintro ⟨a,b,edge,ha,hb⟩
    exact ⟨a,b,Or.inl edge,ha,hb⟩
  · rintro ⟨a,b,adjacent,ha,hb⟩
    change (a,b) ∈ PetersenNine.edges \/ (b,a) ∈ PetersenNine.edges at adjacent
    rcases adjacent with edge | edge
    · exact ⟨a,b,edge,ha,hb⟩
    · exact ⟨b,a,edge,hb,ha⟩
lemma b32 {gs : List Gate} {out : Nat} (least : Least 9 petersenF gs out) :
    out < 9 + gs.length:=by
  by_contra! after
  obtain ⟨x,y,different⟩:=least.ncv b16
  exact different ((b136 gs x out after).trans (b136 gs y out after).symm)
lemma b70 (gs : List Gate) (out : Nat) (least : Least 9 petersenF gs out)
    : 5 ≤ (circuitBranchWires (n:=9) gs).card:=by
  classical
  letI : DecidableRel b6.Adj:=b37
  have outValid:=b32 least
  let outWire : Fin (9 + gs.length):=⟨out,outValid⟩
  have live:=b68 least b16 b63 b27 outValid
  let label : Fin 9 -> Fin (9 + gs.length):=firstInputBoundary least.hcl outWire live
  let branches : Finset (Fin (9 + gs.length)):=circuitBranchWires gs
  have computes (x : Fin 9 -> Bool) : vl gs x outWire.val=PetersenScratch.edgeValue b6 x:=by
    change vl gs x out=_
    rw [least.hev,Bool.eq_iff_iff,b118]
    simp only [PetersenScratch.edgeValue,decide_eq_true_eq]
  have marked (S : Finset (Fin 9)) : vl gs (b55 S) outWire.val=true ↔
      BranchGraph.containsEdge b6 S:=by
    change vl gs (b55 S) out=true↔_
    rw [least.hev]
    exact b77 S
  have independent (r) : BranchGraph.Independent b6 (BranchGroupsLean.bucket label r) :=
    b80 least.hcl outWire live (b137 least b16)
      b6 computes b53 r
  have labels (v : Fin 9) : label v=outWire \/ label v ∈ branches:=by
    have stopped:=FirstBranchRoute.first_stops (b5 gs) outWire (b15 least.hcl) live (b8 gs v)
    rcases stopped with outLabel | fork
    · exact Or.inl outLabel
    · exact Or.inr (b25.mpr fork)
  have before (r) (member : r ∈ branches) : r < outWire:=by
    obtain ⟨a,_,path,_,_⟩:=b25.mp member
    exact lt_of_lt_of_le (b15 least.hcl path) (b130 least.hcl outWire live a)
  have twins (r) (member : r ∈ branches) : BranchGraph.TwinGroup b6
      (BranchGroupsLean.below label r) (BranchGroupsLean.bucket label r) :=
    b87 least.hcl outWire live b6 marked r
      (le_of_lt (before r member)) (Or.inr (b25.mp member)) (independent r)
  exact BranchGroupsLean.roots_required b6 label outWire branches 5 labels before twins
    (independent outWire) (PetersenMaskBridge.petersen_nine_groups_need_five b6 b76)
lemma nonNotCount_add_notCount (gs : List Gate) :
    nonNotCount gs + (gs.filter (fun g => isNotGate g.op)).length=gs.length:=by
  rw [← List.countP_eq_length_filter]
  induction gs with
  | nil => simp [nonNotCount]
  | cons g gs ih =>
    simp only [nonNotCount,List.countP_cons,List.length_cons] at ih ⊢
    cases h : isNotGate g.op <;> simp [h] <;> omega
lemma petersen_binary_lower (C : Circuit) (hfan : FanInTwo C)
    (he : ∀ x : Vertex -> Bool,C.eval (List.ofFn x)=petersenF x) :
    13 ≤ nonNotCount C.gates:=by
  obtain ⟨gs,o,least,budget⟩:=b146 C hfan he b16
  have valid:=b32 least
  have live:=b68 least b16 b63
    b27 valid
  let branches:=circuitBranchWires (n:=9) gs
  have branchLower : 5 ≤ branches.card:=b70 gs o least
  have branchBudget:=b160 least.hcl valid (fun w hw hne => by
      let wire : Fin (9 + gs.length):=⟨w,hw⟩
      obtain ⟨v,p,g,hg,_,hw'⟩:=live wire (fun h => hne (congrArg Fin.val h))
      exact ⟨p,g,hg,hw'⟩)
    (branches.image Fin.val) (fun w hw => by
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hw
      exact b88 (b25.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at branchBudget
  have countTotal:=nonNotCount_add_notCount gs
  change nonNotCount gs + b49 gs=gs.length at countTotal
  omega
end Binary

end PEqualNP.Outside.R_meta_3178_52_support

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.R_meta_3178_52_support

theorem PEqualNP.Outside.R_meta_3178_52_support : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
       x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
       x 6 && x 8 || x 8 && x 5)) →
      13 ≤ C.gates.countP (fun g => !(GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op)) := by
  intro C hfan he
  have hcomp : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = Binary.petersenF x := by
    intro x
    rw [he x]
    simp only [Binary.petersenF, Binary.PetersenNine.edgeFun, Binary.PetersenNine.edges,
      List.any_cons, List.any_nil, Bool.or_false]
    ac_rfl
  have lower := Binary.petersen_binary_lower C hfan hcomp
  have same :
      (fun g : Gate => !(GateOp.rec (motive := fun _ => Bool) false false true
        (fun _ => false) false g.op)) =
      (fun g : Gate => !(Binary.CircuitProof.isNotGate g.op)) := by
    funext g
    cases g.op <;> rfl
  rw [same]
  exact lower
