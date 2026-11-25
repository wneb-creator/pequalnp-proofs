import Mathlib
import PEqualNP.Defs
-- This two-wire lower bound is odinfree's certificate from accepted PR 5789.
namespace PEqualNP.Outside.L_meta_4528_aux
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
    exact PEqualNP.Outside.L_meta_4528_aux.Binary.least_gate_inputs_nodup least nonnull _
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
open PEqualNP.CircuitLowerBounds
abbrev Sig:=BitVec 512
def zero : Sig:=0
def one : Sig:=BitVec.allOnes 512
def neg (a : Sig) : Sig:= ~~~a
def bin (d : Bool) (a b : Sig) : Sig:=if d then a ||| b else a &&& b
def proper (a : Sig) : Prop:=a≠zero /\ a≠one
private lemma m24 (d : Bool) (a b : Sig) : bin d a b=bin d b a:=by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]
def Live (target : Sig) : Nat -> Nat -> Finset Sig -> Prop:=fun k t S =>
  ∀ (M : (Nat -> Nat -> Finset Sig -> Prop)),(proper target -> M 0 0 {target}) →
  (∀ {k t : Nat} {U : Finset Sig} {a : Sig},proper a -> neg a ∉ insert a U -> M k t (insert (neg a) U) -> M (k+1) (t+1) (insert a U)) →
  (∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool},proper a -> proper b -> a≠b -> bin d a b ∉ insert a (insert b U) -> M k t (insert (bin d a b) U) -> M (k+1) t (insert a (insert b U))) →
  M k t S
lemma Live.stop {target : Sig}  (h0 : proper target) : Live target 0 0 {target}:=fun M stop unary binary => @stop  h0
lemma Live.unary {target : Sig} {k t : Nat} {U : Finset Sig} {a : Sig} (h0 : proper a) (h1 : neg a ∉ insert a U) (h2 : Live target k t (insert (neg a) U)) : Live target (k+1) (t+1) (insert a U):=fun M stop unary binary => @unary k t U a h0 h1 (h2 M stop unary binary)
lemma Live.binary {target : Sig} {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (h0 : proper a) (h1 : proper b) (h2 : a≠b) (h3 : bin d a b ∉ insert a (insert b U)) (h4 : Live target k t (insert (bin d a b) U)) : Live target (k+1) t (insert a (insert b U)):=fun M stop unary binary => @binary k t U a b d h0 h1 h2 h3 (h4 M stop unary binary)
lemma Live.induct {target : Sig} {M : (Nat -> Nat -> Finset Sig -> Prop)} {k t S} (h : Live target k t S)
  (stop : proper target -> M 0 0 {target})
  (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig},proper a -> neg a ∉ insert a U -> Live target k t (insert (neg a) U) -> M k t (insert (neg a) U) -> M (k+1) (t+1) (insert a U))
  (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool},proper a -> proper b -> a≠b -> bin d a b ∉ insert a (insert b U) -> Live target k t (insert (bin d a b) U) -> M k t (insert (bin d a b) U) -> M (k+1) t (insert a (insert b U))) : M k t S :=
  (h (fun k t S => Live target k t S /\ M k t S)
  (fun h0 => ⟨@Live.stop target  h0,@stop  h0⟩)
  (@fun k t U a h0 h1 h2 => ⟨@Live.unary target k t U a h0 h1 h2.1,@unary k t U a h0 h1 h2.1 h2.2⟩)
  (@fun k t U a b d h0 h1 h2 h3 h4 => ⟨@Live.binary target k t U a b d h0 h1 h2 h3 h4.1,@binary k t U a b d h0 h1 h2 h3 h4.1 h4.2⟩)).2
lemma Live.recurse {target : Sig} {M : ∀ (k t : Nat) (S : Finset Sig) (proof : Live target k t S),Prop}
  (stop : ∀ (h0 : proper target),M 0 0 {target} (@Live.stop target  h0))
  (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (h0 : proper a) (h1 : neg a ∉ insert a U) (h2 : Live target k t (insert (neg a) U)) (ih : M k t (insert (neg a) U) h2),M (k+1) (t+1) (insert a U) (@Live.unary target k t U a h0 h1 h2))
  (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (h0 : proper a) (h1 : proper b) (h2 : a≠b) (h3 : bin d a b ∉ insert a (insert b U)) (h4 : Live target k t (insert (bin d a b) U)) (ih : M k t (insert (bin d a b) U) h4),M (k+1) t (insert a (insert b U)) (@Live.binary target k t U a b d h0 h1 h2 h3 h4))
  {k t S} (h : Live target k t S) : M k t S h:=by
  have r:=Live.induct (M:=fun k t S => ∀ hh : Live target k t S,M k t S hh) h
    (fun h0 _ => @stop  h0)
    (@fun k t U a h0 h1 h2 h3 _ => @unary k t U a h0 h1 h2 (h3 h2))
    (@fun k t U a b d h0 h1 h2 h3 h4 h5 _ => @binary k t U a b d h0 h1 h2 h3 h4 (h5 h4))
  exact r h
lemma Live.zeroSet {T t S} (h : Live T 0 t S) : S={T}:=by
  have hh:=h (fun k _ W => k=0 -> W={T}) (fun _ _ => rfl)
    (@fun _ _ _ _ _ _ _ e => by omega)
    (@fun _ _ _ _ _ _ _ _ _ _ _ e => by omega)
  exact hh rfl
private lemma m22 {k t S} (h : Live target k t S) : ∀ a ∈ S,proper a:=by
  induction h using Live.recurse with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
private lemma m26 {k t S} (h : Live target k t S) : t ≤ k /\ S.card+t ≤ k+1:=by
  induction h using Live.recurse with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U:=fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc:=Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U:=fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1:=Finset.card_insert_le (a:=a) (s:=insert b U)
    have h2:=Finset.card_insert_le (a:=b) (s:=U)
    exact ⟨by omega,by omega⟩
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs:=g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
def represented (w : List Sig) (v : Sig) : Prop:=v ∈ w \/ ¬proper v
private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero):=by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
private lemma m16 (a : Sig) :
    bin false a one=a /\ bin true a zero=a ∧
    bin false a zero=zero /\ bin true a one=one ∧
    bin false a a=a /\ bin true a a=a:=by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp
private lemma m70 : neg zero=one /\ neg one=zero:=by simp [neg,zero,one]
private lemma m13 {w : List Sig} {a : Sig} (h : represented w a) :
    a=zero \/ a=one \/ a ∈ w /\ proper a:=by
  by_cases hz : a=zero
  · exact Or.inl hz
  by_cases ho : a=one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)
def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w,proper a /\ z=neg a) ∨
  (∃ d a b,a ∈ w /\ b ∈ w /\ proper a /\ proper b /\ a≠b /\ z=bin d a b)
private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) \/ witness w (bin d a b):=by
  have rz : represented w zero:=Or.inr (fun h => h.1 rfl)
  have ro : represented w one:=Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩:=m16 a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩:=m16 b
  rcases m13 ha with rfl | rfl | ⟨ham,hap⟩
  · rw [m24]; cases d <;> simp_all
  · rw [m24]; cases d <;> simp_all
  rcases m13 hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z \/ witness w z) (sub : ∀ a ∈ S,a ∈ w++[z]) :
    ∃ k' t' S',k' ≤ k+1 /\ Live target k' t' S' /\ ∀ a ∈ S',a ∈ w:=by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w \/ a=z:=by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp:=m22 h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U:=S.erase (neg a)
        have ht : Live target k t (insert (neg a) U):=by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U,v ∈ w:=by
          intro v hv
          obtain ⟨hne,hm⟩:=Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U:=by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U:=S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U):=by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U,v ∈ w:=by
          intro v hv
          obtain ⟨hne,hm⟩:=Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U):=by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a≠z:=fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
def bit (i : Fin 512) (a : Sig) : Bool:=a.getLsbD i.val
private lemma m15 (i) : bit i zero=false:=by simp [bit,zero]
private lemma bit_one (i) : bit i one=true:=by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a)=!(bit i a):=by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a||bit i b else bit i a&&bit i b):=by cases d <;> simp [bit,bin]
private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false=bit i (w.getD j zero):=by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (m15 _).symm
  | some a => rfl
private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g)=g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false):=by
  obtain ⟨o,l⟩:=g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _)=(_&&_)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero)&&x) ih
  · induction l with
    | nil => exact m15 _
    | cons a l ih =>
      change bit i (bin true _ _)=(_||_)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero)||x) ih
  · cases l with
    | nil =>
      change bit i (neg zero)=!false
      rw [bit_neg,m15]
    | cons a l => exact bit_neg _ _
private lemma m47 (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)):=by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _=_
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]
abbrev Wire (R : Type):=R -> Bool
def inv {R} (a : Wire R) : Wire R:=fun r => !(a r)
def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r||b r else fun r => a r&&b r
def Constant {R} (a : Wire R) : Prop:=∃ b : Bool,a=fun _ => b
noncomputable def cost {R} (a : Wire R) : Nat:=by
  classical exact if Constant a then 1 else 0
noncomputable def mass {R} (xs : List (Wire R)) : Nat:=(xs.map cost).sum
def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop:=v ∈ pool \/ Constant v
def supply {R} (pool xs : List (Wire R)):=∀ a ∈ xs,Available pool a
def Reach {R} (roots : List (Wire R)) : Nat -> List (Wire R) -> Prop:=fun p bank =>
  ∀ (M : (Nat -> List (Wire R) -> Prop)),(M 0 roots) →
  (∀ {p : Nat} {bank : List (Wire R)} {a : Wire R},M p bank -> Available bank a -> M (p+1) (inv a :: bank)) →
  (∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool),M p bank -> Available bank a -> Available bank b -> M (p+1) (combine op a b :: bank)) →
  M p bank
lemma Reach.start {R} {roots : List (Wire R)}   : Reach roots 0 roots:=fun M start one two => @start
lemma Reach.one {R} {roots : List (Wire R)} {p : Nat} {bank : List (Wire R)} {a : Wire R} (h0 : Reach roots p bank) (h1 : Available bank a) : Reach roots (p+1) (inv a :: bank):=fun M start one two => @one p bank a (h0 M start one two) h1
lemma Reach.two {R} {roots : List (Wire R)} {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (h0 : Reach roots p bank) (h1 : Available bank a) (h2 : Available bank b) : Reach roots (p+1) (combine op a b :: bank):=fun M start one two => @two p bank a b op (h0 M start one two) h1 h2
lemma Reach.induct {R} {roots : List (Wire R)} {M : (Nat -> List (Wire R) -> Prop)} {p bank} (h : Reach roots p bank)
  (start : M 0 roots)
  (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R},Reach roots p bank -> M p bank -> Available bank a -> M (p+1) (inv a :: bank))
  (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool),Reach roots p bank -> M p bank -> Available bank a -> Available bank b -> M (p+1) (combine op a b :: bank)) : M p bank :=
  (h (fun p bank => Reach roots p bank /\ M p bank)
  (⟨@Reach.start R roots  ,@start  ⟩)
  (@fun p bank a h0 h1 => ⟨@Reach.one R roots p bank a h0.1 h1,@one p bank a h0.1 h0.2 h1⟩)
  (@fun p bank a b op h0 h1 h2 => ⟨@Reach.two R roots p bank a b op h0.1 h1 h2,@two p bank a b op h0.1 h0.2 h1 h2⟩)).2
lemma Reach.recurse {R} {roots : List (Wire R)} {M : ∀ (p : Nat) (bank : List (Wire R)) (proof : Reach roots p bank),Prop}
  (start : M 0 roots (@Reach.start R roots  ))
  (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (h0 : Reach roots p bank) (ih : M p bank h0) (h2 : Available bank a),M (p+1) (inv a :: bank) (@Reach.one R roots p bank a h0 h2))
  (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (h0 : Reach roots p bank) (ih : M p bank h0) (h2 : Available bank a) (h3 : Available bank b),M (p+1) (combine op a b :: bank) (@Reach.two R roots p bank a b op h0 h2 h3))
  {p bank} (h : Reach roots p bank) : M p bank h:=by
  have r:=Reach.induct (M:=fun p bank => ∀ hh : Reach roots p bank,M p bank hh) h
    (fun  _ => @start  )
    (@fun p bank a h0 h1 h2 _ => @one p bank a h0 (h1 h0) h2)
    (@fun p bank a b op h0 h1 h2 h3 _ => @two p bank a b op h0 (h1 h0) h2 h3)
  exact r h
def kept {α : Type} (save : Bool) (x : α) (xs : List α):=if save then x::xs else xs
def Run {R} (goal : Wire R) : Nat -> List (Wire R) -> Prop:=fun s ws =>
  ∀ (M : (Nat -> List (Wire R) -> Prop)),(M 0 [goal]) →
  (∀ {s : Nat} {xs zs : List (Wire R)},xs.Perm zs -> M s xs -> M s zs) →
  (∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool),M s (inv a :: kept save a rest) -> M (s+1) (a::rest)) →
  (∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool),M s (combine op a b :: kept ka a (kept kb b rest)) -> M (s+1) (a::b::rest)) →
  M s ws
lemma Run.stop {R} {goal : Wire R}   : Run goal 0 [goal]:=fun M stop perm one two => @stop
lemma Run.perm {R} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (h0 : xs.Perm zs) (h1 : Run goal s xs) : Run goal s zs:=fun M stop perm one two => @perm s xs zs h0 (h1 M stop perm one two)
lemma Run.one {R} {goal : Wire R} {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (h0 : Run goal s (inv a :: kept save a rest)) : Run goal (s+1) (a::rest):=fun M stop perm one two => @one s a rest save (h0 M stop perm one two)
lemma Run.two {R} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool) (h0 : Run goal s (combine op a b :: kept ka a (kept kb b rest))) : Run goal (s+1) (a::b::rest):=fun M stop perm one two => @two s a b rest op ka kb (h0 M stop perm one two)
lemma Run.induct {R} {goal : Wire R} {M : (Nat -> List (Wire R) -> Prop)} {s ws} (h : Run goal s ws)
  (stop : M 0 [goal])
  (perm : ∀ {s : Nat} {xs zs : List (Wire R)},xs.Perm zs -> Run goal s xs -> M s xs -> M s zs)
  (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool),Run goal s (inv a :: kept save a rest) -> M s (inv a :: kept save a rest) -> M (s+1) (a::rest))
  (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool),Run goal s (combine op a b :: kept ka a (kept kb b rest)) -> M s (combine op a b :: kept ka a (kept kb b rest)) -> M (s+1) (a::b::rest)) : M s ws :=
  (h (fun s ws => Run goal s ws /\ M s ws)
  (⟨@Run.stop R goal  ,@stop  ⟩)
  (@fun s xs zs h0 h1 => ⟨@Run.perm R goal s xs zs h0 h1.1,@perm s xs zs h0 h1.1 h1.2⟩)
  (@fun s a rest save h0 => ⟨@Run.one R goal s a rest save h0.1,@one s a rest save h0.1 h0.2⟩)
  (@fun s a b rest op ka kb h0 => ⟨@Run.two R goal s a b rest op ka kb h0.1,@two s a b rest op ka kb h0.1 h0.2⟩)).2
lemma Run.recurse {R} {goal : Wire R} {M : ∀ (s : Nat) (ws : List (Wire R)) (proof : Run goal s ws),Prop}
  (stop : M 0 [goal] (@Run.stop R goal  ))
  (perm : ∀ {s : Nat} {xs zs : List (Wire R)} (h0 : xs.Perm zs) (h1 : Run goal s xs) (ih : M s xs h1),M s zs (@Run.perm R goal s xs zs h0 h1))
  (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (h0 : Run goal s (inv a :: kept save a rest)) (ih : M s (inv a :: kept save a rest) h0),M (s+1) (a::rest) (@Run.one R goal s a rest save h0))
  (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool) (h0 : Run goal s (combine op a b :: kept ka a (kept kb b rest))) (ih : M s (combine op a b :: kept ka a (kept kb b rest)) h0),M (s+1) (a::b::rest) (@Run.two R goal s a b rest op ka kb h0))
  {s ws} (h : Run goal s ws) : M s ws h:=by
  have r:=Run.induct (M:=fun s ws => ∀ hh : Run goal s ws,M s ws hh) h
    (fun  _ => @stop  )
    (@fun s xs zs h0 h1 h2 _ => @perm s xs zs h0 h1 (h2 h1))
    (@fun s a rest save h0 h1 _ => @one s a rest save h0 (h1 h0))
    (@fun s a b rest op ka kb h0 h1 _ => @two s a b rest op ka kb h0 (h1 h0))
  exact r h
lemma m30 {R} (a : Wire R) (xs) : mass (a::xs)=cost a+mass xs:=by
  simp [mass]
lemma m86 {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs):=by
  cases k <;> simp [kept,m30]
lemma m75 {R} {a : Wire R} (h : Constant a) : Constant (inv a):=by
  obtain ⟨v,rfl⟩:=h
  exact ⟨!v,rfl⟩
lemma m117 {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b):=by
  obtain ⟨v,rfl⟩:=h
  obtain ⟨w,rfl⟩:=g
  cases op <;> exact ⟨_,rfl⟩
lemma m115 {R} (op) {a b : Wire R} {bank}
    (h : Constant a \/ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b):=by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false,by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true,by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false,by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true,by funext x; simp [combine]⟩
lemma m36 {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v:=by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr
lemma extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next,Reach roots q next /\ Available next (inv a) ∧
        (∀ v,Available bank v -> Available next v) /\ q+cost a ≤ p+1+cost (inv a):=by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (m75 c),fun _ h => h,by simp [cost,c,m75 c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => m36 _ h,by simp [cost,c]⟩
lemma extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next,Reach roots q next /\ Available next (combine op a b) ∧
        (∀ v,Available bank v -> Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b):=by
  classical
  by_cases c : Constant a \/ Constant b
  · refine ⟨p,bank,hp,m115 op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,m117 op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a:=fun h => c (Or.inl h)
    have cb : ¬Constant b:=fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => m36 _ h,
      by simp [cost,ca,cb]⟩
lemma m112 {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a \/ x∈xs:=by cases k <;> simp_all [kept]
lemma m150 {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next,Reach roots q next /\ Available next goal /\ q+mass ws ≤ p+s:=by
  classical
  induction h using Run.recurse generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _:=fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩:=ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩:=extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest):=by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (m112 hh)))
    obtain ⟨q,W,hW,hv,hl⟩:=ih hT ht
    have hlen:=m86 a rest save
    rw [m30] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩:=extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)):=by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases m112 hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (m112 hh))
    obtain ⟨q,W,hW,hv,hl⟩:=ih hT ht
    have hlen:=m86 a (kept kb b rest) ka
    have hlen':=m86 b rest kb
    rw [m30] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [m30,m30]
    omega
def restrictRows {R S : Type} (rows : S -> R) (a : Wire R) : Wire S :=
  fun r => a (rows r)
lemma m68 {R S : Type} (rows : S -> R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)):=by
  cases k <;> simp [kept]
lemma m121 {R S : Type} (rows : S -> R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)):=by
  induction h using Run.recurse with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,m68] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,m68] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih
lemma m29 {R S : Type} (rows : S -> R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs,Reach roots q bs -> Available bs (restrictRows rows goal) -> L ≤ q) :
    L+mass (ws.map (restrictRows rows)) ≤ p+s:=by
  obtain ⟨q,bs,hq,ht,hle⟩:=m150 nc (m121 rows h) roots hp hs
  have hqle:=hl q bs hq ht
  omega
abbrev Row:=Fin 512
def observe (a : Sig) : Wire Row:=fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
lemma m52 (f : Wire Row) (r : Row) : bit r (table f)=f r:=by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]
lemma m18 (v : Sig) : table (observe v)=v:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact m52 (observe v) ⟨j,hj⟩
lemma m41 (f : Wire Row) : observe (table f)=f:=by
  funext r
  exact m52 f r
lemma obs_neg (a : Sig) : observe (neg a)=inv (observe a):=by
  funext r
  exact bit_neg _ _
lemma obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b)=combine d (observe a) (observe b):=by
  funext r
  cases d <;> exact bit_bin _ _ _ _
lemma m113 {α β : Type} (f : α -> β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f=kept d (f a) (l.map f):=by cases d <;> rfl
lemma kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup:=by cases k <;> simp [kept,hn,ha]
lemma m28 (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset=if k then insert a l.toFinset else l.toFinset:=by
  cases k <;> simp [kept]
lemma m114 {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset=S) : Run (observe T) k (v.map observe):=by
  classical
  induction h using Live.recurse generalizing v with
  | stop hp =>
    have eq : [T].Perm v:=by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest:=(U.erase a).toList
    let save:=decide (a ∈ U)
    let tail:=kept save a rest
    have er : rest.toFinset=U.erase a:=by simp [rest]
    have hm : a ∉ rest:=by simp [rest]
    have hr : rest.Nodup:=Finset.nodup_toList _
    have ht : tail.toFinset=U:=by
      rw [show tail=kept save a rest by rfl,m28,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd:=kept_nd save a rest hr hm
    have hf : neg a ∉ tail:=by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress:=ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,m113,obs_neg] at progress
    have perm : (a::rest).Perm v:=by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest:=((U.erase a).erase b).toList
    let ka:=decide (a ∈ U)
    let kb:=decide (b ∈ U)
    let mid:=kept kb b rest
    let tail:=kept ka a mid
    have er : rest.toFinset=(U.erase a).erase b:=by simp [rest]
    have ar : a ∉ rest:=by simp [rest]
    have br : b ∉ rest:=by simp [rest]
    have hr : rest.Nodup:=Finset.nodup_toList _
    have bm:=kept_nd kb b rest hr br
    have am : a ∉ mid:=by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd:=kept_nd ka a mid bm am
    have ht : tail.toFinset=U:=by
      change (kept ka a (kept kb b rest)).toFinset=U
      rw [m28,m28,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail:=by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress:=ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,m113,m113,obs_bin] at progress
    have perm : (a::b::rest).Perm v:=by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)
lemma table_inv (f : Wire Row) : table (inv f)=neg (table f):=by
  rw [←m18 (neg (table f)),obs_neg,m41]
lemma table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g)=bin d (table f) (table g):=by
  rw [←m18 (bin d (table f) (table g)),obs_bin,m41,m41]
lemma m21 {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a):=by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false)=zero:=by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (m52 _ ⟨j,hj⟩).trans (m15 ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true)=one:=by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (m52 _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z
lemma inv_rep {w a} (ha : represented w a) :
    represented w (neg a) \/ witness w (neg a):=by
  rcases m13 ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 m70.1)
  · exact Or.inl (Or.inr fun h => h.1 m70.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
lemma m124 {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z \/ witness w z) (hs : ∀ a ∈ S,a ∈ z::w) :
    ∃ k' t' S',k' ≤ k+1 /\ Live T k' t' S' /\ ∀ a ∈ S',a ∈ w:=by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm
lemma m100 {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S,a ∈ bank.map table) :
    ∃ l v U,l ≤ p+k /\ Live T l v U /\ ∀ a ∈ U,a ∈ roots.map table:=by
  induction h using Reach.recurse generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ih ha =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩:=m124 run (inv_rep (m21 ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩:=ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ih ha hb =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩:=m124 run (bin_rep d (m21 ha) (m21 hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩:=ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
lemma m74 {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S,k ≤ p /\ Live T k t S /\ ∀ a ∈ S,a ∈ roots:=by
  have hm:=m21 hit
  rw [m18] at hm
  have mem:=hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩:=m100 h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,m18] using hs
lemma m31 {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T≠bit s T) : ∃ a ∈ S,bit r a≠bit s a:=by
  induction h using Live.recurse with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩:=ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩:=ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a=bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩
lemma m32 {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S,v ∈ roots) (r s : Row) (diff : bit r T≠bit s T)
    (isolated : ∀ v ∈ roots,v≠a -> bit r v=bit s v) : a ∈ S:=by
  obtain ⟨v,hv,hd⟩:=m31 h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))
def inputs : List Sig:=[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig:=0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def oldSeed : Sig:=0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888
def seed : Sig:=inputs.getD 0 zero ||| inputs.getD 4 zero
def sample (r : Row) (j : Fin 9):=bit r (inputs.getD j.val zero)
def edge (x : Fin 9 -> Bool) : Bool :=
  (x 0&&x 1)||(x 1&&x 2)||(x 2&&x 3)||(x 3&&x 4)||(x 4&&x 0) ||
  (x 0&&x 5)||(x 1&&x 6)||(x 2&&x 7)||(x 3&&x 8)||(x 5&&x 7) ||
  (x 6&&x 8)||(x 8&&x 5)
lemma edge_table : ∀ r : Row,bit r graph=edge (sample r):=by decide +kernel
lemma seed_table : ∀ r : Row,bit r seed=(sample r 0||sample r 4):=by decide +kernel
lemma m76 : proper graph:=by unfold proper; decide +kernel
lemma seed_nonzero : seed≠zero:=by decide +kernel
lemma m38 : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero)=inputs:=rfl
lemma sampled (r : Row) : List.ofFn (sample r)=inputs.map (bit r):=by
  rw [←m38]
  rw [List.map_ofFn]
  rfl
lemma table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false:=by
  rw [←b_read,m47 _ _ _ (fun g hg => (h g hg).1),←sampled]
  rfl
lemma m129 (gs : List Gate) (ws : List Sig) : ∃ l,execute gs ws=ws ++ l:=by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩:=ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩
def neighbor (i : Fin 9) : Nat:=[4,2,1,2,0,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row:=Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row:=Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))
def rename (f : Row -> Row) (a : Sig):=table fun r => bit (f r) a
lemma m7 (f : Row -> Row) (a : Sig) (r : Row) :
    bit r (rename f a)=bit (f r) a:=m52 _ _
lemma m14 (f : Row -> Row) (a : Sig) :
    observe (rename f a)=restrictRows f (observe a):=by funext r; exact m7 f a r
lemma rename_neg (f : Row -> Row) (a : Sig) : rename f (neg a)=neg (rename f a):=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a))=bit ⟨j,hj⟩ (neg (rename f a))
  rw [m7,bit_neg,bit_neg,m7]
lemma rename_bin (f : Row -> Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b)=bin d (rename f a) (rename f b):=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b))=bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [m7,bit_bin,bit_bin,m7,m7]
lemma rename_inj (f : Row -> Row) (onto : Function.Surjective f) :
    Function.Injective (rename f):=by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩:=onto ⟨j,hj⟩
  have he:=congrArg (bit r) h
  change bit ⟨j,hj⟩ a=bit ⟨j,hj⟩ b
  rw [m7,m7,hr] at he
  exact he
lemma m79 (f : Row -> Row) : rename f zero=zero /\ rename f one=one:=by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (m7 f zero ⟨j,hj⟩).trans ((m15 _).trans (m15 ⟨j,hj⟩).symm)
  · exact (m7 f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
lemma m90 {T k t S} (h : Live T k t S) (f : Row -> Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)):=by
  have inj:=rename_inj f onto
  obtain ⟨fz,fo⟩:=m79 f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.recurse with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f):=by
      intro hm
      obtain ⟨v,hv,eq⟩:=Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f):=by
      intro hm
      obtain ⟨v,hv,eq⟩:=Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih
lemma m63 {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T=true) (negRow : bit s T=false) :
    ∃ a ∈ S,bit r a=true /\ bit s a=false:=by
  induction h using Live.recurse with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩:=ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩
def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank,Reach (roots.map observe) p bank -> Available bank (observe T) -> L ≤ p
def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t,k ≤ cap -> ¬Live T k t S
def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row,bit r T≠bit s T /\ ∀ v ∈ roots,v≠a -> bit r v=bit s v
lemma m43 {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots,Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1):=by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩:=m74 hp h ha
  have he : roots.toFinset=S:=by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩:=essential _ hm
    exact m32 run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)
lemma m59 {v : Sig} (hv : proper v) : ¬Constant (observe v):=by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v:=by
    have avail : Available ([] : List (Wire Row)) (observe v):=Or.inr ⟨b,h⟩
    simpa only [List.map_nil,m18] using m21 avail
  exact (hr.resolve_left (by simp)) hv
lemma m137 {R} (a b : List (Wire R)) : mass (a++b)=mass a+mass b:=by
  simp [mass]
lemma m101 {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs,Constant x) :
    mass xs=xs.length:=by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha:=hc a (by simp)
    simp only [m30,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega
lemma m88 {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row -> Row) (eq : rename r T=G)
    (covered : ∀ a ∈ roots,Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles,Essential T roots a)
    (constant : ∀ a ∈ singles,Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L+singles.card):=by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩:=m74 pT hh ha
  have subS : singles ⊆ S:=by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩:=necessary a hs
    exact m32 run roots a sub i j hd hiso
  let front:=singles.toList ++ (S \ singles).toList
  have nd : front.Nodup:=by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S:=by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run':=m114 run front nd fe
  have gc : restrictRows r (observe T)=observe G:=(m14 _ _).symm.trans (congrArg observe eq)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)):=by
    intro v hv
    obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩:=List.mem_map.mp hm
    rw [←m14]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound:=m29 r run' (gc ▸ m59 pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)):=by
    simp only [front,List.map_append,m137]
    let xs:=(singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs,Constant v:=by
      intro v hv
      obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩:=List.mem_map.mp hm
      rw [←m14]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz:=m101 xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs+_
    rw [sz]
    omega
  omega
def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
lemma m39 {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset=l.toFinset.erase a:=by
  ext x
  simp [h.mem_erase_iff]
lemma enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws,∀ keep,neg a ∉ ws -> proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws,∀ b ∈ ws,∀ d ka kb,a≠b -> bin d a b ∉ ws →
      proper (bin d a b) -> (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset:=by
  classical
  intro k t hk h
  generalize he : ws.toFinset=S at h
  induction h using Live.recurse with
  | stop hp =>
    have mem : T ∈ ws.toFinset:=he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail _ =>
    have am : a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=m22 tail _ (Finset.mem_insert_self _ _)
    let keep:=decide (a ∈ U)
    have er:=m39 hn a
    have rest : (kept keep a (ws.erase a)).toFinset=U:=by
      rw [m28,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup:=by
      have na : a ∉ ws.erase a:=hn.not_mem_erase
      have nk:=kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset=insert (neg a) U:=by simp [childOne,rest]
    have sc:=(m26 tail).2
    have len : (childOne ws a keep).length ≤ cap:=by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail _ =>
    have am : a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=m22 tail _ (Finset.mem_insert_self _ _)
    let ka:=decide (a ∈ U)
    let kb:=decide (b ∈ U)
    let rest:=(ws.erase a).erase b
    have er : rest.toFinset=(ws.toFinset.erase a).erase b:=by
      rw [show rest=(ws.erase a).erase b by rfl,m39 (hn.erase _) b,
        m39 hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset=U:=by
      rw [m28,m28,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup:=(hn.erase _).erase _
    have ar : a ∉ rest:=fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest:=(hn.erase a).not_mem_erase
    have nk:=kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest:=by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup:=by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset=insert (bin d a b) U:=by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset=_
      simp [ke]
    have sc:=(m26 tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap:=by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)
def Sep (T : Sig) (width : Nat) (pos negRow : Fin width -> Row)
    (asig : Sig -> BitVec width × BitVec width) : Prop :=
  (∀ i,bit (pos i) T=true /\ bit (negRow i) T=false) ∧
  ∀ w i,(asig w).1.getLsbD i.val=bit (pos i) w ∧
    (asig w).2.getLsbD i.val=bit (negRow i) w
def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2
def covered {n} (oriented : Bool) (sig : Sig -> BitVec n × BitVec n) : List Sig -> BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws
lemma m140 {n : Nat} {oriented : Bool} {sig : Sig -> BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val=true ↔
    ∃ a ∈ ws,(column oriented (sig a)).getLsbD i.val=true:=by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]
lemma m96 {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width -> Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true -> t=0) :
    covered oriented sig ws=BitVec.allOnes width:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width:=⟨j,hj⟩
  have yes:=(correct.1 i).1
  have no:=(correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (m140 (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩:=m31 h (show bit (r i) T≠bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩:=m63 h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]
lemma m103 {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n -> Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws=BitVec.allOnes n:=by
  apply m96 h rfl correct
  intro hh
  have eq:=of_decide_eq_true hh
  have bound:=(m26 h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega
def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row -> Row) (roots : List Sig),(∀ r,bit (f r) d=true) ∧
    (∀ a ∈ raw,Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank,Reach (roots.map observe) p bank -> Available bank (restrictRows f (observe T)) -> L ≤ p
def masked (d a : Sig):=a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m:=masked d a
  m==zero||m==d||(pool.map (masked d)).any (fun v => v==m)
lemma masked_eq {f : Row -> Row} {d a b : Sig} (dom : ∀ r,bit (f r) d=true)
    (eq : masked d a=masked d b) :
    restrictRows f (observe a)=restrictRows f (observe b):=by
  funext r
  have h:=congrArg (bit (f r)) eq
  change bit (f r) a=bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using h
lemma m87 {f : Row -> Row} {d a : Sig} (dom : ∀ r,bit (f r) d=true)
    (eq : masked d a=zero) : restrictRows f (observe a)=fun _ => false:=by
  funext r
  have he:=congrArg (bit (f r)) eq
  change bit (f r) a=false
  rw [m15] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using he
lemma m106 {f : Row -> Row} {d a : Sig} (dom : ∀ r,bit (f r) d=true)
    (eq : masked d a=d) : restrictRows f (observe a)=fun _ => true:=by
  funext r
  have he:=congrArg (bit (f r)) eq
  change bit (f r) a=true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using he
def poolSupply (f : Row -> Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool,Available bank (restrictRows f (observe a))
lemma m6 {f : Row -> Row} {d a : Sig} {bank pool}
    (dom : ∀ r,bit (f r) d=true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a=true) : Available bank (restrictRows f (observe a)):=by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,m87 dom hz⟩
  · exact Or.inr ⟨true,m106 dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv
abbrev Choice:=Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1&&(c.1==2||availableB d pool c.2.2)
lemma m104 {f : Row -> Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r,bit (f r) d=true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c=true) :
    ∃ next,Reach roots (q+1) next /\ poolSupply f next (choiceVal c :: pool):=by
  have ok : availableB d pool c.2.1=true /\ (c.1==2||availableB d pool c.2.2)=true:=by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha:=m6 dom hs ok.1
  let z:=restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank):=by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2=true:=by simpa [unary] using ok.2
      have hz':=Reach.two (c.1==1) hp ha (m6 dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w)=combine b (restrictRows f v) (restrictRows f w):=by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact m36 _ (hs _ hm)
def makePool (d : Sig) (pool : List Sig) : List Choice -> Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none
lemma m61 {d : Sig} {f : Row -> Row} (dom : ∀ r,bit (f r) d=true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs=some result) :
    ∃ next,Reach roots (q+cs.length) next /\ poolSupply f next result:=by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩:=m104 dom hp hs c h
      obtain ⟨out,hr',sh'⟩:=ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction
def isMaskedConstant (d a : Sig):=masked d a==zero||masked d a==d
lemma m49 {d : Sig} {f : Row -> Row} (dom : ∀ r,bit (f r) d=true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)):=by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,m30]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)):=by
        have hh : masked d a=zero \/ masked d a=d:=by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,m87 dom hz⟩
        · exact ⟨true,m106 dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih
def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d))&&ws.all (availableB d pool)
lemma m111 {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs=some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws=true) :
    Impossible T cap ws.toFinset:=by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩:=slice
  obtain ⟨bank,hr,hs⟩:=m61 dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩:=cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)):=by
    intro v hv
    obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hm
    exact m6 dom hs (List.all_eq_true.mp all a ha)
  have b:=m29 f (m114 h ws nd rfl) nc hr coveredS lo
  have massLo:=m49 dom ws
  have hu:=ineq
  simp only [Nat.zero_add] at b
  omega
abbrev Move:=Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row:=Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig):=(m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)
lemma bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val)=bit (shifted d r) a:=by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]
lemma bool_mux (p x y : Bool) : (p&&x||!p&&y)=(if p then x else y):=by cases p <;> simp
lemma bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b)=if bit r m then bit r a else bit r b:=by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _
lemma bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a)=bit (rowMove m r) a:=by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl
def movedRow (ms : List Move) (r : Row):=ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig):=ms.foldr wordMove a
lemma m40 (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a)=bit (movedRow ms r) a:=by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
lemma m20 (ms : List Move) (a : Sig) : movedWord ms a=rename (movedRow ms) a:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (m40 ms a ⟨j,hj⟩).trans (m7 _ _ ⟨j,hj⟩).symm
def freeWord (roots : List Sig) (w : Sig):=w==zero||w==one||roots.contains w
lemma m138 {roots w} (ok : freeWord roots w=true) :
    Available (roots.map observe) (observe w):=by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext m15⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)
def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T==G&&raw.all (fun a => freeWord base (movedWord ms a))
lemma m64 {ms raw T base G} (ok : checkMap ms raw T base G=true) :
    rename (movedRow ms) T=G ∧
    ∀ a ∈ raw,Available (base.map observe) (observe (rename (movedRow ms) a)):=by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,m20] at ok
  exact ⟨ok.1,fun a ha => m138 (ok.2 a ha)⟩
lemma lower_map {ms raw T base G L} (ok : checkMap ms raw T base G=true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L:=by
  obtain ⟨eq,supp⟩:=m64 ok
  simpa using m88 pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL
lemma m110 {ms raw T base G L d} (ok : checkMap ms raw T base G=true)
    (all : movedWord ms d=one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L:=by
  obtain ⟨eq,supp⟩:=m64 ok
  have obs : restrictRows (movedRow ms) (observe T)=observe G :=
    (m14 _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←m40,all,bit_one]
  · intro a ha
    rw [←m14]
    exact supp a ha
  · rw [obs]
    exact m59 properG
  · rw [obs]
    exact hL
def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w==a||bit rs.1 w==bit rs.2 w)
lemma m98 {T roots a rs} (ok : witnessB T roots a rs=true) : Essential T roots a:=by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩
def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
lemma m35 {T raw xs} (ok : checkEssential T raw xs=true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset,Essential T raw a:=by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ha)
  exact m98 (List.all_eq_true.mp ok _ hm)
lemma m89 {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs=true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1):=by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩:=m74 properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card:=by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩:=m35 ok a ha
    exact m32 run raw a sub r s hd iso
  have bound:=(m26 run).2
  omega
def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G&&checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1==zero||movedWord ms a.1==one)
lemma lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs=true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card):=by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩:=m64 ok.1.1
  apply m88 properT properG _ eq supp _ (m35 ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh:=List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,m20] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext m15⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩
def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat):=(selected m).map Prod.snd
def vertex (m j : Nat):=if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x:=vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def cube0 : Nat -> Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat -> Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat -> Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed:=z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x:=inputs.getD j zero
    let step:=Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i:=v &&& 15
  let j:=v >>> 4
  let a:=inputs.getD i zero
  let b:=inputs.getD j zero
  let d:=(1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)
def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))
def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r:=1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def properB (T : Sig):=T != zero&&T != one
lemma m19 (T : Sig) (h : properB T=true) : proper T:=by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs:=graphPairs m hints
  properB (graphGoal m)&&checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
lemma size_of {m hints L} (h : assertSize m hints L=true) :
    Lower (vars m) (graphGoal m) L:=by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (m89 (m19 _ h.1.1) _ h.1.2 p bank hr ha)
abbrev ColumnInfo:=Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat):=m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~oldSeed else graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat -> Nat) : Bool :=
  let (z,o,q,s,L):=c
  let ms:=fixRows z o
  let free:=colFree m z o
  let G:=movedWord ms (chartGoal m)
  let xs:=supportPairs s
  let count:=(xs.map Prod.fst).toFinset.card
  properB G&&checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs&&decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))
lemma m50 {m : Nat} (c : ColumnInfo) (prior : Nat -> Nat)
    (valid : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior=true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2:=by
  obtain ⟨z,o,q,s,L⟩:=c
  let ms:=fixRows z o
  let free:=colFree m z o
  let G:=movedWord ms (chartGoal m)
  let xs:=supportPairs s
  change (((properB G&&checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one))&&_)=true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply m110 ok.1.1.2 ok.1.2 (m19 _ ok.1.1.1)
  intro p bank hr ha
  have hh:=ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (m89 (m19 _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (m19 _ ok.1.1.1) (m19 _ hh.1.1) (valid q) p bank hr ha)
def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old)&&properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
lemma relabel_of {old rep L swaps} (ok : relabelOK old rep swaps=true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L:=by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (m19 _ ok.1.1) (m19 _ ok.1.2) h
def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1==q)).map Prod.snd).getD 0
lemma m4 (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries,Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q):=by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1==q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he:=List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1==q) e=true:=List.find?_some (p:=fun a : Nat × Nat => a.1==q) (a:=e) h
    have eq : e.1=q:=beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he
abbrev BoundPool:=(Sig) × (Nat) × (Nat) × (List Sig)
abbrev BoundPool.domain (c : BoundPool) : Sig:=c.1
abbrev BoundPool.bound (c : BoundPool) : Nat:=c.2.1
abbrev BoundPool.paid (c : BoundPool) : Nat:=c.2.2.1
abbrev BoundPool.wires (c : BoundPool) : List Sig:=c.2.2.2
def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row -> Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r,bit (f r) c.domain=true) /\ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws,Reach (roots.map observe) q ws -> Available ws (restrictRows f (observe T)) -> c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank /\ poolSupply f bank c.wires /\ True
lemma m152 {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs=some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩:=by
  obtain ⟨f,roots,dom,sup,nc,prior⟩:=h
  obtain ⟨bank,hr,hs⟩:=m61 dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩
lemma m109 {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest,availableB c.domain c.wires a=true)
    (buy : if paid then choiceOK c.domain c.wires choice=true
       else availableB c.domain c.wires (choiceVal choice)=true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset:=by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩:=valid
  let ws:=choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n=c.paid+paid.toNat) : False:=by
    have covered : supply out ((ws.map observe).map (restrictRows f)):=by
      intro v hv
      obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hm
      exact zs _ ha
    have b:=m29 f (m114 run ws nd rfl) nc reach covered lo
    have cm:=m49 dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact m6 dom hs buy
    · exact m6 dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩:=m104 dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have avail:=m6 dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a=true:=known _ hm
        have point : ∀ u ∈ c.wires,Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact m6 dom point ha
      · exact Or.inr con
def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z:=choiceVal op
  let extra:=!(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires))&&(!extra||choiceOK c.domain c.wires op)
lemma m9 {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op=true) :
    Impossible T k (choiceVal op::rest).toFinset:=by
  let extra:=!(availableB c.domain c.wires (choiceVal op))
  apply m109 valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1
def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
lemma m37 {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L=some c) : ValidPool raw T c:=by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he,Option.map] at h
  | some pool =>
    rw [he] at h
    change some _=some c at h
    injection h with h
    subst c
    exact m152 slice cs he
abbrev Bits:=BitVec 768
abbrev Signals:=Bits × Bits
abbrev Decor:=Sig × Signals
def ofRows {n : Nat} (r : Fin n -> Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
lemma m8 {n : Nat} (r : Fin n -> Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val=bit (r i) v:=by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 -> Row) (a : Sig) : Signals:=(ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 -> Row) :=
  ∀ i,bit (r i) T=true /\ bit (s i) T=false
lemma pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s):=by
  exact ⟨h,fun a i => ⟨m8 _ _ _,m8 _ _ _⟩⟩
def faithful (r s : Fin 768 -> Row) (x : Decor):=x.2=pairSig r s x.1
def dneg (x : Decor) : Decor:=(neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)
lemma ofRows_neg (r : Fin 768 -> Row) (a : Sig) : ofRows r (neg a)= ~~~ofRows r a:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h:=m8 r (neg a) ⟨j,hj⟩
  rw [bit_neg,←m8 r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
lemma ofRows_bin (r : Fin 768 -> Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b)=if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h:=m8 r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←m8 r a ⟨j,hj⟩,←m8 r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
lemma m46 {r s x} (h : faithful r s x) : faithful r s (dneg x):=by
  change x.2=_ at h
  simp only [faithful,dneg,pairSig,ofRows_neg,h]
lemma m34 {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y):=by
  change x.2=_ at hx
  change y.2=_ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]
def codeDecor (op : Nat) (x y : Decor):=if op=2 then dneg x else dbin (op==1) x y
def defaultDecor : Decor:=(zero,0,0)
lemma m80 (r s) : faithful r s defaultDecor:=by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j=(ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j=bit (r ⟨j,hj⟩) zero from m8 _ _ ⟨j,hj⟩,m15]
    simp
  · change (0 : Bits).getLsbD j=(ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j=bit (s ⟨j,hj⟩) zero from m8 _ _ ⟨j,hj⟩,m15]
    simp
lemma m27 {r s ws} (all : ∀ v ∈ ws,faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor):=by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact m80 _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a:=ws.getD (bits &&& 15) defaultDecor
    let b:=ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
lemma m48 (n bits) (ws) (r s) (base : ∀ v ∈ ws,faithful r s v) :
    ∀ v ∈ decodeBank n bits ws,faithful r s v:=by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl:=List.mem_singleton.mp hz
      unfold codeDecor
      split
      · exact m46 (m27 base _)
      · exact m34 _ (m27 base _) (m27 base _)
def asRow (cols : Nat -> Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
lemma m149 : ∀ r : Row,bit r (inputs.getD 0 zero)=r.val.testBit 0:=by decide +kernel
lemma m148 : ∀ r : Row,bit r (inputs.getD 1 zero)=r.val.testBit 1:=by decide +kernel
lemma m147 : ∀ r : Row,bit r (inputs.getD 2 zero)=r.val.testBit 2:=by decide +kernel
lemma m146 : ∀ r : Row,bit r (inputs.getD 3 zero)=r.val.testBit 3:=by decide +kernel
lemma m145 : ∀ r : Row,bit r (inputs.getD 4 zero)=r.val.testBit 4:=by decide +kernel
lemma m144 : ∀ r : Row,bit r (inputs.getD 5 zero)=r.val.testBit 5:=by decide +kernel
lemma m143 : ∀ r : Row,bit r (inputs.getD 6 zero)=r.val.testBit 6:=by decide +kernel
lemma m142 : ∀ r : Row,bit r (inputs.getD 7 zero)=r.val.testBit 7:=by decide +kernel
lemma m141 : ∀ r : Row,bit r (inputs.getD 8 zero)=r.val.testBit 8:=by decide +kernel
lemma m45 : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero)=r.val.testBit j.val:=by
  intro j r
  fin_cases j
  · exact m149 r
  · exact m148 r
  · exact m147 r
  · exact m146 r
  · exact m145 r
  · exact m144 r
  · exact m143 r
  · exact m142 r
  · exact m141 r
lemma m53 (cols : Nat -> Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero)=(cols j.val).getLsbD i.val:=by
  rw [m45]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val=_
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat -> Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
lemma m99 {m j a} (h : (j,a) ∈ selected m) :
    j<9 /\ a=inputs.getD j zero:=by
  obtain ⟨v,hv,hh⟩:=List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
lemma m122 (m) (p q : Nat -> Bits) :
    ∀ a ∈ rawDecor m p q,faithful (asRow p) (asRow q) a:=by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩:=List.mem_map.mp ha
  obtain ⟨hj,rfl⟩:=m99 hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (m53 p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (m8 _ _ ⟨i,hi⟩).symm
  · exact (m53 q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (m8 _ _ ⟨i,hi⟩).symm
def liftGoal (m : Nat) (v : Nat -> Bits) : Bits :=
  let x:=fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
lemma bit_vertex (m : Nat) (v : Nat -> Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val:=by
  by_cases hh : m.testBit j.val=true
  · simpa [vertex,hh] using m53 v i j
  · simp [vertex,hh,m15]
lemma m77 (m : Nat) (v : Nat -> Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m)=(liftGoal m v).getLsbD i.val:=by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val=((if m.testBit j then v j else 0) : Bits).getLsbD i.val:=bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov:=Bits × Bits × Bits
def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1,(z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)
def takeOne (c : Cov) (a : Bits) : Bits:=c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))
private lemma cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1:=by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl
private lemma cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1:=by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private lemma add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c):=by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private lemma cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r:=by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
lemma cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v,faithful r s a) :
    (coverage d v).1=covered d (pairSig r s) (v.map Prod.fst):=by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1)=column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]
def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb
lemma m65 {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a):=List.perm_cons_erase ha
lemma m97 {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)):=by
  cases keep
  · change (coverage d (ws.erase a)).1=takeOne (coverage d ws) _
    rw [cov_perm d (m65 a ha)]
    exact (cov_one _ _).symm
  · rfl
lemma m139 {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b):=by
  have hm : b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (m65 a ha).trans (List.Perm.cons _ (m65 b hm))
lemma cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)):=by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1=takeTwo (coverage d ws) _ _
    rw [cov_perm d (m139 a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact m97 d a ha false
  · exact m97 d b hb false
  · rfl
def sameWords (a b : List Sig):=(a.all (fun x => b.contains x))&&(b.all (fun x => a.contains x))
lemma m11 {xs ys} (h : sameWords xs ys=true) : xs.toFinset=ys.toFinset:=by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩
def keyWord (v : Sig) :=
  let n:=v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig):=xs.foldl (fun v x => v+keyWord x) 0
def closeChild (pools : List BoundPool) (links : Nat -> List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws:=choiceVal op::rest
  (links (keySet ws)).any (sameWords ws)||pools.any (fun p => scalarPoolCut p k rest op)
lemma m81 {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools,ValidPool raw T p)
    (lValid : ∀ tag xs,xs ∈ links tag -> Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op=true) :
    Impossible T k (choiceVal op :: rest).toFinset:=by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [m11 ok]
    exact lValid _ _ hx
  · exact m9 (pValid _ hp) nd ok
abbrev CovPair:=Cov × Cov
def preCov (ws : List Decor) : CovPair:=(coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool):=if d then c.2 else c.1
lemma get_preCov (ws) (d : Bool) : getCov (preCov ws) d=coverage d ws:=by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb
lemma m69 {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false -> a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb:=by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact m97 d a ha ka
lemma m55 (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws:=by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
lemma m71 (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws:=by
  cases un
  · exact (m55 _ _ _).trans (m55 _ _ _)
  · exact m55 _ _ _
lemma len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false -> a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un||kb then 0 else 1):=by
  cases un
  · have hm : b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]
def movedDecor (op : Nat) (a b : Decor):=codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice:=(op,a.1,b.1)
lemma m54 (op) (a b : Decor) :
    (movedDecor op a b).1=choiceVal (movedChoice op a b):=by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
lemma m60 {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b):=by
  unfold movedDecor codeDecor
  split
  · exact m46 ha
  · exact m34 _ ha hb
abbrev NodeContext:=Nat × Nat × List Decor × CovPair × List BoundPool × (Nat -> List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links):=c
  let un:=op==2
  let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
  if len>cap then true else
    let d:=len==cap
    let rs:=restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1||ws.any (fun v => v.1==z.1) then true else
      let rest:=(opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)
def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
lemma m62 {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws,faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false -> a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools,ValidPool raw T p)
    (lv : ∀ tag xs,xs ∈ links tag -> Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb=true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset:=by
  let z:=movedDecor op a b
  let rest:=opKeep (op==2) ka kb a b ws
  let child:=z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws:=m71 _ _ _ _ _ _
  have ndc : child.Nodup:=List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1)=false:=by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩:=List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1=true:=by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2)||kb then 0 else 1))=child.length:=by
    change _=(z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz:=(m26 h).2
  change child.toFinset.card+t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap:=by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _)=true at test
  rw [leq,if_neg (by omega)] at test
  have sep:=m103 h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap:=by omega
  rw [ce] at sep
  let d:=child.length==cap
  have g : (coverage d rest).1=covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz:=m69 ha hb (op==2) ka kb d ne
  have hf:=m60 (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap)=(child.length==cap):=by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length=cap)) (pairSig r s) child=BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst)=_ at sep
  change z.2=pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768)=false:=by simp [sep]
  change (if (_ != _) then true else if !properB z.1||ws.any (fun v => v.1==z.1) then true else _)=true at test
  rw [be,pp,fr] at test
  have val:=m54 op a b
  change z.1=_ at val
  change Live T k t child.toFinset at h
  have nd':=ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact m81 pv lv nd' test k t hk h
def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op:=if d then 1 else 0
  let z:=movedDecor op a b
  let attempt:=evalMove ctx op a b z
  attempt false false&&attempt true false&&attempt false true&&attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z:=movedDecor 2 a a
  evalMove ctx 2 a a z false false&&evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false&&testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor -> Bool
  | [] => true
  | a::bs => testRow ctx a bs&&testAll ctx bs
lemma all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true:=by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm
lemma all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true \/ testPair ctx b a d=true:=by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm:=(List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail
lemma m135 {ctx a b d} (h : testPair ctx a b d=true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb=true:=by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
lemma m23 {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v↔(w=a /\ k=true) \/ w∈v:=by cases k <;> simp [kept]
lemma m105 {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k↔w∈v /\ (w≠a \/ k=true):=by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]
lemma m44 {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b:=by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩:=List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail
lemma m107 {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst /\ (v≠a.1 \/ ka=true) /\ (un=true \/ v≠b.1 \/ kb=true):=by
  have wn:=nd.of_map
  have dn:=wn.sublist (m55 ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    m105 wn,m105 dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (m44 nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (m44 nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (m44 nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
lemma m83 {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset=(childOne (ws.map Prod.fst) a.1 keep).toFinset:=by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    m107 nd ha ha,m23,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av:=List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all
lemma m78 {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
  ext v
  have av:=List.mem_map_of_mem (f:=Prod.fst) ha
  have bv:=List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    m107 nd ha hb,m23,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all
lemma m73 (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset=(childTwo v b a d kb ka).toFinset:=by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    m23,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,m24 d b a]
  tauto
lemma node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws,faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools,ValidPool raw T p)
    (lv : ∀ tag xs,xs ∈ links tag -> Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws=true) :
    Impossible T cap (ws.map Prod.fst).toFinset:=by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0:=by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset=S at h
    rw [h.zeroSet] at he
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap:=by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hv
    have hf:=m83 nd ha keep
    rw [←hf]
    exact m62 pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩:=List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩:=List.mem_map.mp hb
    have ab : a≠b:=fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d=true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
      rw [←m78 nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1=bin d a.1 b.1:=by cases d <;> rfl
      exact m62 pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (m135 test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [m73 _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (m24 d a.1 b.1 ▸ pro)
        (m24 d a.1 b.1 ▸ fresh) hh
lemma m134 (r s : Row) (h : ∀ a ∈ inputs,bit r a=bit s a) : r=s:=by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9:=⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs:=by
      rw [← m38]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (m45 i r).symm.trans ((h _ hm).trans (m45 i s))
  · have le : 512 ≤ 2^j:=by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm
def composedOK (p q : List Move):=inputs.all (fun a => movedWord p (movedWord q a)==a)
lemma m42 {p q} (h : composedOK p q=true) (r : Row) :
    movedRow q (movedRow p r)=r:=by
  apply m134
  intro a ha
  rw [←m40,←m40]
  have eq:=beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]
def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T==T)&&composedOK p p.reverse&&composedOK p.reverse p
lemma m85 {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p=true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset:=by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p):=fun r => ⟨movedRow p.reverse r,m42 ok.2 r⟩
  intro k t hk h
  have run:=m90 h (movedRow p) onto
  have goal : rename (movedRow p) T=T:=(m20 p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x)=x:=by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _=bit ⟨j,hj⟩ _
    rw [m7,m40,m42 ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p))=ws.toFinset:=by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk run
abbrev Packing:=Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat -> Nat)
def emptyPacking : Packing:=(0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat -> Nat) (pos len : Nat) :=
  let i:=pos/8192
  let shift:=pos % 8192
  let lo:=word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)
def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat -> Nat) (h : Nat) : Option (Nat × Nat) :=
  let a:=h % nb
  let sh:=packedAt data (a*sw) sw
  let row:=(h/nb+sh)%slots
  let word:=packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw))==h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none
def m2 (α : Type):=List α
def m2.leaf {α} (xs : List α) : m2 α:=xs
def m2.fork {α} (_ : Nat) (a b : m2 α) : m2 α:=List.append a b
def m2.read {α} (tree : m2 α) (i : Nat):=(show List α from tree)[i]?
def m2.values {α} (tree : m2 α) : List α:=tree
lemma m2.read_mem {α} (tree : m2 α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values:=List.mem_of_getElem? e
def Forest:=(Nat) × (Nat) × (Nat -> Bits × Bits) × (m2 ColumnInfo) × (Array (List Nat)) × (Nat -> Packing) × (Nat -> Nat -> Option (Nat × Nat))
def Forest.mask (c : Forest) : Nat:=c.1
def Forest.cap (c : Forest) : Nat:=c.2.1
def Forest.samples (c : Forest) : Nat -> Bits × Bits:=c.2.2.1
def Forest.cols (c : Forest) : m2 ColumnInfo:=c.2.2.2.1
def Forest.autos (c : Forest) : Array (List Nat):=c.2.2.2.2.1
def Forest.levels (c : Forest) : Nat -> Packing:=c.2.2.2.2.2.1
def Forest.index (c : Forest) : Nat -> Nat -> Option (Nat × Nat):=c.2.2.2.2.2.2
def wiresOf (g : Forest) :=
  let ws:=rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge:=dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
lemma m57 (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a:=by
  have base:=m122 g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩:=List.mem_map.mp ha
    exact m34 false (base w hw) (m46 (m34 false
      (m27 base 0) (m27 base 1)))
  · exact base _ ha
def targetOf (g : Forest):=chartGoal g.mask
def chartSamples (m : Nat) (v : Nat -> Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v
lemma chart_bit (m : Nat) (v : Nat -> Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m)=(chartSamples m v).getLsbD i.val:=by
  by_cases e : m=1023
  · have u:=m53 v i (0 : Fin 9)
    have w:=m53 v i (1 : Fin 9)
    have h:=m77 m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val=(v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val=(v 1).getLsbD i.val at w
    have seedEq : oldSeed=inputs.getD 0 zero &&& inputs.getD 1 zero:=by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using m77 m v i
lemma m66 {m : Nat} {p q : Nat -> Bits}
    (hp : chartSamples m p=BitVec.allOnes 768) (hq : chartSamples m q=0) :
    properPairs (chartGoal m) (asRow p) (asRow q):=by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α -> List α
  | [] => []
  | w::ws => if bits &&& 1==1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
lemma m58 {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws:=by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)
def storedDepth (_g : Forest) (depth : Nat):=depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw:=wiresOf g
  let (_,depth,_,_,_,_,_,data):=g.levels k
  let len:=10*storedDepth g depth
  let width:=len+raw.length+depth
  let recp:=packedAt data (i*width) width
  let stored:=recp &&& ((1 <<< len)-1)
  let ops:=stored
  let bank:=decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)
def getFieldV (x pos width : Nat):=(x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat -> List Choice
  | 0 => []
  | n+1 =>
    let more:=chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1==0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more
def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2
lemma m51 (g : Forest)
    (cols : ∀ ci ∈ g.cols.values,Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid=some c) :
    ValidPool (vars g.mask) (targetOf g) c:=by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply m37 _ h
    exact cols ci (g.cols.read_mem e)
def getPairs (data : Nat -> Nat) (w v : Nat) : Nat -> Nat -> List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x:=packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)
def stateSet (g : Forest) (k i : Nat):=(readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)
lemma m91 (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList,autoOK (targetOf g) (x.map swapRows)=true)
    (earlier : ∀ i < (g.levels k).1,Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair=some out) :
    Impossible (targetOf g) k out.toFinset:=by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact m85 (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))
def nodeVerified (g : Forest) (k i : Nat) :=
  let raw:=wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data):=g.levels k
  let (ops,bank,ws):=readNode g k i
  let values:=ws.map Prod.fst
  let start:=num*(10*storedDepth g depth+raw.length+depth)
  let pos:=start+num*offw+packedAt data (start+i*offw) offw
  let nr:=packedAt data pos 5
  let nl:=packedAt data (pos+5) lw
  let st:=pos+5+lw
  let rules:=(getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls:=fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup&&!(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)
lemma m33 (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values,Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList,autoOK (targetOf g) (x.map swapRows)=true)
    (prior : k>0 -> ∀ j < (g.levels (k-1)).1,Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i=true) : Impossible (targetOf g) k (stateSet g k i).toFinset:=by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN:=checked.1.1
  have hT : targetOf g ∉ stateSet g k i:=by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0:=by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset=S at h
    rw [h.zeroSet] at he
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply m48 _ _ _ _ _ (m57 g) v
    exact (m58 _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩:=List.mem_filterMap.mp hp
    exact m51 g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs:=by simpa using hx
    obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e
    exact m91 g _ names (prior (by omega)) h
def block (g : Forest) (k start : Nat) : Nat -> Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n)&&block g k start n
lemma block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true:=by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
lemma m5 {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true:=by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩
def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top,block g k 0 (g.levels k).1=true
def graphValid (g : Forest) (prior : Nat -> Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1)==BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2)==0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))
lemma forest_all (g : Forest) (top : Nat) (prior : Nat -> Nat)
    (lower : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior=true) (rows : checkedTables g top) :
    ∀ k ≤ top,∀ i < (g.levels k).1,Impossible (targetOf g) k (stateSet g k i).toFinset:=by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply m33 g 0 i (m66 geometry.1.1.1 geometry.1.1.2)
      (fun x hx => m50 _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply m33 g _ i (m66 geometry.1.1.1 geometry.1.1.2)
      (fun x hx => m50 _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)
def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1)&&sameWords (stateSet g k i) ws
lemma root_index {g top prior k i ws} (low : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws=true) : Impossible (targetOf g) k ws.toFinset:=by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←m11 idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1
lemma m17 {g prior i hints} (low : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask)=true) (hp : properB (targetOf g)=true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints)=true)
    (all : (graphPairs g.mask hints).map Prod.fst=vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1):=by
  apply m43 (m19 _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply m35 ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
lemma m10 {g prior ci hints} (low : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior=true)
    (hp : properB (targetOf g)=true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints)=true)
    (all : (graphPairs g.mask hints).map Prod.fst=vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1):=by
  apply m43 (m19 _ hp) _ (m111 (m50 ci prior low ok) [] rfl nd cut)
  intro a ha
  apply m35 ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
def Known (entries : List (Nat × Nat)):=∀ e ∈ entries,Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
lemma m0 {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2)=true) :
    Known (extendKnown old L relabels):=by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
lemma baseKnown : Known []:=by simp [Known]
def lanePlace (v : Nat) (upper : Nat):=2^769*upper+v
def combineLanes {α : Type} (f : α -> Bits) : List α -> Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat -> Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
lemma m95 (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
lemma place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v=lanePlace (a &&& b).toNat (u &&& v):=by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (m95 _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
lemma place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v=lanePlace (a ||| b).toNat (u ||| v):=by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (m95 _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
lemma place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v=lanePlace (a ^^^ b).toNat (u ^^^ v):=by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (m95 _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
lemma m93 {α} (f g : α -> Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs=combineLanes (fun x => f x &&& g x) xs:=by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
lemma m82 {α} (f g : α -> Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs=combineLanes (fun x => f x ||| g x) xs:=by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
lemma m92 {α} (f g : α -> Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs=combineLanes (fun x => f x ^^^ g x) xs:=by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
lemma broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat=combineLanes (fun _ => a) xs:=by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]
def fullMarks (r packed : Nat):=((packed+r) >>> 768) &&& r
lemma unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i)=true:=by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i:=by omega
      have ge : ¬769*(i+1)<769:=by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
lemma guardBit (a : Bits) : (a.toNat+1).testBit 768=(a==BitVec.allOnes 768):=by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim:=a.isLt
    have ne : a.toNat≠2^768-1:=by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768:=by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 8192 in
lemma mark_at {α} (f : α -> Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768):=by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1):=by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have:=(f a).isLt; omega)]
    have hi' : i < xs.length+1:=hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769:=by omega
      have di : 769*(i+1)+768-769=769*i+768:=by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)
abbrev PackedSig:=Nat × Nat
abbrev PackedCov:=Nat × Nat × Nat
def packedSig {α} (s : α -> Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α -> Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2
lemma xor_meet (a b : Bits) : a ^^^ (a &&& b)=a &&& ~~~b:=by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
lemma m12 {α} (s : α -> Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs)=combineLanes (fun x => column d (s x)) xs:=by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,m93,m92,xor_meet]
def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
lemma top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a= ~~~a:=BitVec.allOnes_xor
lemma m125 {α} (a b : α -> Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs:=by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,m92,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,m82,m93,movedDecor,codeDecor,dbin]
def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1:=fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2:=c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2
lemma m67 {α} (c : α -> Cov) (a b : α -> Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs:=by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,m93,m82,m92,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]
def contextWire (c : NodeContext) (i : Nat):=c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a:=contextWire c i
  let b:=contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a:=contextWire c i
  let b:=contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2
def onMarks {α : Type} (f : α -> Bool) (mask : Nat) : List α -> Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1==0)||f x)&&onMarks f (mask >>> 769) xs
lemma m126 {α} (f : α -> Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true:=by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0:=by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1≠0:=by
        intro he
        have at0:=congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn
abbrev Batch:=Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat):=b.2.2.2.1.getD i (0,0)
lemma m94 (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i=packedSig (fun c => (contextWire c i).2) xs:=by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]
def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero||m==p.domain||(p.wires.map (masked p.domain)).any (fun v => v==m)
lemma m25 (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x=availableMasked p (masked p.domain x):=rfl
def constantLoss (p : Decor -> Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
lemma m127 (p : Decor -> Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p+constantLoss p a keep:=by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]
lemma keptCount (p : Decor -> Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un||kb) ≤
    (opKeep un ka kb a b ws).countP p:=by
  have h1:=m127 p ws a ka
  have h2:=m127 p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega
abbrev QuickPool:=BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p:=s.1
  let un:=op==2
  let const:=fun w : Decor => isMaskedConstant p.domain w.1
  let z:=choiceVal (movedChoice op a b)
  let zm:=masked p.domain z
  let zc:=isMaskedConstant p.domain z
  let cm:=s.2.1 - constantLoss const a ka - constantLoss const b (un||kb)+zc.toNat
  let free:=zc||zm==masked p.domain a.1||zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)
lemma m72 {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true:=by
  let z:=choiceVal (movedChoice op a b)
  let const:=fun w : Decor => isMaskedConstant p.domain w.1
  let free:=isMaskedConstant p.domain z||masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest:=opKeep (op==2) ka kb a b ws
  have ck:=keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2)||kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav:=List.all_eq_true.mp all
    have ready : free=true -> availableB p.domain p.wires z=true:=by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [m25,za,←m25]
        exact hav _ ha
      · rw [m25,zb,←m25]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat:=by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true:=by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hm
      exact hav w ((m71 ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true:=by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const+if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h
def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a:=contextWire c i
  let b:=contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)
lemma m123 {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true:=by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1:=by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩:=List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hm
  have closed:=m72 (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl
def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length /\ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
lemma m102 {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true:=by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact m123 yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v):=b
  let un:=op==2
  let len:=1+(n-(if ka then 0 else 1)-(if un||kb then 0 else 1))
  if len>k then true else
    let d:=len==k
    let a:=laneWire b i
    let b':=laneWire b j
    let z:=packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov:=if d then v else u
    let mask:=fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs
lemma m133 (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true:=by
  let len:=1+(n-(if ka then 0 else 1)-(if (op==2)||kb then 0 else 1))
  let d:=len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)):=by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r:=units xs.length
    let a:=laneWire (makeBatch k n xs) i
    let b:=laneWire (makeBatch k n xs) j
    let cov:=if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs)=true at pass
    rw [if_neg small] at pass
    have chosen : cov=packedCov (fun c => getCov c.2.2.2.1 d) xs:=by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a=_:=m94 k n xs hi
    have cb : b=_:=m94 k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,m125,m12,m12,m12,chosen,m67,m82] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j=BitVec.allOnes 768
    · apply m102
      apply m126 _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f:=batchMove b xs i j op
  f false false&&f true false&&f false true&&f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false&&batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0&&batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat -> Bool
  | [] => true
  | i::js => batchRow b xs i js&&batchRows b xs js
lemma m132 (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js,j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q]))=true:=by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi:=bounds i List.mem_cons_self
    have check:=@m133 k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj':=bounds j (List.mem_cons_of_mem _ hj)
    have both:=allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true:=by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩
def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
lemma m136 {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true:=by
  have all:=m132 k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q])=xs[q].2.2.1:=by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all
def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw:=wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data):=g.levels k
  let (ops,bank,ws):=readNode g k i
  let start:=num*(10*storedDepth g depth+raw.length+depth)
  let pos:=start+num*offw+packedAt data (start+i*offw) offw
  let nr:=packedAt data pos 5
  let nl:=packedAt data (pos+5) lw
  let st:=pos+5+lw
  let rules:=(getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls:=fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)
def prelim (T : Sig) (c : NodeContext) :=
  let ws:=c.2.2.1.map Prod.fst
  decide ws.Nodup&&!(ws.contains T)
lemma m128 (g : Forest) (k i : Nat) :
    nodeVerified g k i=(prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)):=rfl
lemma makeBlock {g k start n} (h : ∀ (i : Nat),start ≤ i -> i < start+n -> nodeVerified g k i=true) :
    block g k start n=true:=by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩
def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar&&prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs:=contexts g k start n
  let b:=makeBatch k ar xs
  (List.range len).all (fun d =>
    let i:=lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
lemma m84 {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true:=by
  have ha:=List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha
lemma m120 {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true:=by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt:=List.mem_range.mp hj
  by_cases first : j<a
  · exact m84 h (lo+j) (by omega) (by omega)
  · exact m84 t (lo+j) (by omega) (by omega)
lemma cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true:=by
  let xs:=contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true:=by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok:=m84 h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)
lemma cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true:=by
  apply makeBlock
  intro i lo hi
  let xs:=contexts g k start n
  have hm : contextOf g k i ∈ xs:=by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩:=List.getElem_of_mem hm
  have one:=List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k:=by rw [e]; rfl
  have ha : xs[q].2.1=ar:=e ▸ one.1
  have hn : xs[q].2.2.1.length=ar:=by rw [e]; exact one.1
  rw [m128,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ m136 hq hb ha hn (cutsRun h)
def boxes (g : Forest) (k start n ar lo num : Nat) : Nat -> Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d /\ boxes g k start n ar (lo+num/2) (num-num/2) d
lemma boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true:=by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v:=m120 (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def cells (g : Forest) (k start n ar rows : Nat) : Nat -> Prop
  | 0 => header g k start n ar=true /\ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d /\ cells g k (start+n/2) (n-n/2) ar rows d
lemma m1 {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true:=by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v:=m5 (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
def listPieces {α} (f : α -> Bool) (xs : List α) : Nat -> Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d /\ listPieces f (xs.drop (xs.length/2)) d
lemma m3 {α f xs d} (h : @listPieces α f xs d) : xs.all f=true:=by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true:=by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def g15d3 (i : Nat) : Nat:=0xf
def g15l3 : Packing:=(1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits):=Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : m2 ColumnInfo:=(.leaf [])
def g15autos : Array (List Nat):=Array.mk [[],[33,48]]
def g15levels : Nat -> Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat -> Nat -> Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest:=⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i : Nat) : Nat:=0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat:=0x84001e90fd02fd01fa00
def g31l5 : Packing:=(3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat:=0x11a20bf
def g31l6 : Packing:=(1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits):=Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : m2 ColumnInfo:=(.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat):=Array.mk [[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat -> Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat -> Nat -> Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest:=⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits):=Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : m2 ColumnInfo:=(.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat):=Array.mk [[],[83,32]]
def g47levels : Nat -> Packing
  | _ => emptyPacking
def g47index : Nat -> Nat -> Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest:=⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits):=Array.mk [(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : m2 ColumnInfo:=(.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat):=Array.mk [[],[84]]
def g55levels : Nat -> Packing
  | _ => emptyPacking
def g55index : Nat -> Nat -> Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest:=⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits):=Array.mk [(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : m2 ColumnInfo:=(.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat):=Array.mk [[],[50,65]]
def g63levels : Nat -> Packing
  | _ => emptyPacking
def g63index : Nat -> Nat -> Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest:=⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat:=0x120ff
def g111l6 : Packing:=(1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits):=Array.mk [(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : m2 ColumnInfo:=(.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat):=Array.mk [[],[83,32]]
def g111levels : Nat -> Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat -> Nat -> Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest:=⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits):=Array.mk [(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : m2 ColumnInfo:=(.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat):=Array.mk [[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat -> Packing
  | _ => emptyPacking
def g119index : Nat -> Nat -> Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest:=⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩
def key189l7 (i : Nat) : Nat:=0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat:=0x82000f487f40bfa03fa00
def g189l6 : Packing:=(3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat:=0x1f5859bf
def g189l7 : Packing:=(1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits):=Array.mk [(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : m2 ColumnInfo:=(.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat):=Array.mk [[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat -> Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat -> Nat -> Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest:=⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits):=Array.mk [(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : m2 ColumnInfo:=(.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat):=Array.mk [[],[101,66,16]]
def g127levels : Nat -> Packing
  | _ => emptyPacking
def g127index : Nat -> Nat -> Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest:=⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index⟩
def key191l10 (i : Nat) : Nat:=0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def key191l9 (i : Nat) : Nat:=0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def key191l8 (i : Nat) : Nat:=0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def key191l7 (i : Nat) : Nat:=0x2c
def g191d6 (i : Nat) : Nat:=0x47d6448788a00
def g191l6 : Packing:=(1,4,6,0,2,0,0,g191d6)
def g191d7 (i : Nat) : Nat:=0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def g191l7 : Packing:=(28,3,6,0,2,8,0,g191d7)
def g191d8 (i : Nat) : Nat:=0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def g191l8 : Packing:=(100,2,6,5,2,12,0,g191d8)
def g191d9 (i : Nat) : Nat:=0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def g191l9 : Packing:=(12,1,6,7,2,9,0,g191d9)
def g191d10 (i : Nat) : Nat:=0x1f3c11ff
def g191l10 : Packing:=(1,0,6,4,2,0,0,g191d10)
def g191samples : Array (Bits × Bits):=Array.mk [(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : m2 ColumnInfo:=(.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat):=Array.mk [[],[84,115],[117,67,32],[116,83,32]]
def g191levels : Nat -> Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking
def g191index : Nat -> Nat -> Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none
def g191 : Forest:=⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples : Array (Bits × Bits):=Array.mk [(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : m2 ColumnInfo:=(.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat):=Array.mk [[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat -> Packing
  | _ => emptyPacking
def g251index : Nat -> Nat -> Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest:=⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits):=Array.mk [(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : m2 ColumnInfo:=(.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat):=Array.mk [[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat -> Packing
  | _ => emptyPacking
def g255index : Nat -> Nat -> Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest:=⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index⟩
def key383l12 (i : Nat) : Nat:=0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def key383l11 (i : Nat) : Nat:=0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def key383l10 (i : Nat) : Nat:=0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def key383l9 (i : Nat) : Nat:=0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def g383d8 (i : Nat) : Nat:=0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def g383l8 : Packing:=(25,4,6,0,3,8,0,g383d8)
def g383d9 (i : Nat) : Nat:=0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def g383l9 : Packing:=(91,3,6,5,3,11,0,g383d9)
def g383d10 (i : Nat) : Nat:=0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def g383l10 : Packing:=(41,2,6,7,3,12,0,g383d10)
def g383d11 (i : Nat) : Nat:=0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def g383l11 : Packing:=(6,1,6,6,3,8,0,g383d11)
def g383d12 (i : Nat) : Nat:=0x11b280e4ff
def g383l12 : Packing:=(1,0,6,3,3,0,0,g383d12)
def g383samples : Array (Bits × Bits):=Array.mk [(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : m2 ColumnInfo:=(.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat):=Array.mk [[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def g383levels : Nat -> Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking
def g383index : Nat -> Nat -> Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 17 68 7 12 5 3 (key383l9)
  | 10 => lookupWord 57 200 7 14 7 3 (key383l10)
  | 11 => lookupWord 30 108 6 13 6 3 (key383l11)
  | 12 => lookupWord 6 61 1 10 3 3 (key383l12)
  | _ => fun _ => none
def g383 : Forest:=⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma low3 : Lower (vars 3) (graphGoal 3) 1:=size_of (hints:=1) (by decide +kernel)
def maps3 : List (Nat × List Nat):=[]
def known3:=extendKnown [] 1 maps3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma valid3 : Known known3:=m0 baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma low7 : Lower (vars 7) (graphGoal 7) 2:=size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat):=[]
def known7:=extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma valid7 : Known known7:=m0 valid3 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma geom15 : graphValid g15 (boundsBefore known7)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,m3 (d:=0) ?_⟩,m3 (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s15_3_0 : block g15 3 0 1=true:=by
  apply m1 (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
lemma bl15_3 : block g15 3 0 1=true:=s15_3_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma tables15 : checkedTables g15 3:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0=true)
  · exact (rfl : block g15 1 0 0=true)
  · exact (rfl : block g15 2 0 0=true)
  · exact bl15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma low15 : Lower (vars 15) (graphGoal 15) 4 :=
  m17 (g:=g15) (i:=0) (hints:=8449) (m4 known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat):=[(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15:=extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma valid15 : Known known15:=m0 valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma low45 : Lower (vars 45) (graphGoal 45) 3:=size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat):=[]
def known45:=extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma valid45 : Known known45:=m0 valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma low51 : Lower (vars 51) (graphGoal 51) 3:=size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat):=[]
def known51:=extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma valid51 : Known known51:=m0 valid45 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma geom31 : graphValid g31 (boundsBefore known51)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,m3 (d:=1) ?_⟩,m3 (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s31_5_0 : block g31 5 0 1=true:=by
  apply m1 (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s31_5_1 : block g31 5 1 2=true:=by
  apply m1 (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
lemma bl31_5 : block g31 5 0 3=true:=(@m5 g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s31_6_0 : block g31 6 0 1=true:=by
  apply m1 (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
lemma bl31_6 : block g31 6 0 1=true:=s31_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma tables31 : checkedTables g31 6:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0=true)
  · exact (rfl : block g31 1 0 0=true)
  · exact (rfl : block g31 2 0 0=true)
  · exact (rfl : block g31 3 0 0=true)
  · exact (rfl : block g31 4 0 0=true)
  · exact bl31_5
  · exact bl31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma low31 : Lower (vars 31) (graphGoal 31) 7 :=
  m17 (g:=g31) (i:=0) (hints:=8449) (m4 known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat):=[(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31:=extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma valid31 : Known known31:=m0 valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma low47 : Lower (vars 47) (graphGoal 47) 5 :=
  m10 (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (m4 known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat):=[(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47:=extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma valid47 : Known known47:=m0 valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma low55 : Lower (vars 55) (graphGoal 55) 5 :=
  m10 (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (m4 known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat):=[(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55:=extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma valid55 : Known known55:=m0 valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma low63 : Lower (vars 63) (graphGoal 63) 8 :=
  m10 (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (m4 known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat):=[(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63:=extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma valid63 : Known known63:=m0 valid55 low63 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma geom111 : graphValid g111 (boundsBefore known63)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,m3 (d:=0) ?_⟩,m3 (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s111_6_0 : block g111 6 0 1=true:=by
  apply m1 (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
lemma bl111_6 : block g111 6 0 1=true:=s111_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma tables111 : checkedTables g111 6:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0=true)
  · exact (rfl : block g111 1 0 0=true)
  · exact (rfl : block g111 2 0 0=true)
  · exact (rfl : block g111 3 0 0=true)
  · exact (rfl : block g111 4 0 0=true)
  · exact (rfl : block g111 5 0 0=true)
  · exact bl111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma low111 : Lower (vars 111) (graphGoal 111) 7 :=
  m17 (g:=g111) (i:=0) (hints:=16785665) (m4 known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat):=[(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111:=extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma valid111 : Known known111:=m0 valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma low119 : Lower (vars 119) (graphGoal 119) 6 :=
  m10 (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (m4 known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat):=[(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119:=extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma valid119 : Known known119:=m0 valid111 low119 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma geom189 : graphValid g189 (boundsBefore known119)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,m3 (d:=1) ?_⟩,m3 (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s189_6_0 : block g189 6 0 1=true:=by
  apply m1 (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s189_6_1 : block g189 6 1 2=true:=by
  apply m1 (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
lemma bl189_6 : block g189 6 0 3=true:=(@m5 g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s189_7_0 : block g189 7 0 1=true:=by
  apply m1 (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
lemma bl189_7 : block g189 7 0 1=true:=s189_7_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma tables189 : checkedTables g189 7:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0=true)
  · exact (rfl : block g189 1 0 0=true)
  · exact (rfl : block g189 2 0 0=true)
  · exact (rfl : block g189 3 0 0=true)
  · exact (rfl : block g189 4 0 0=true)
  · exact (rfl : block g189 5 0 0=true)
  · exact bl189_6
  · exact bl189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma low189 : Lower (vars 189) (graphGoal 189) 8 :=
  m17 (g:=g189) (i:=0) (hints:=536879876) (m4 known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat):=[(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189:=extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma valid189 : Known known189:=m0 valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma low250 : Lower (vars 250) (graphGoal 250) 5:=size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat):=[]
def known250:=extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma valid250 : Known known250:=m0 valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma low127 : Lower (vars 127) (graphGoal 127) 9 :=
  m10 (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (m4 known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat):=[(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127:=extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma valid127 : Known known127:=m0 valid250 low127 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma geom191 : graphValid g191 (boundsBefore known127)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,m3 (d:=4) ?_⟩,m3 (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s191_6_0 : block g191 6 0 1=true:=by
  apply m1 (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
lemma bl191_6 : block g191 6 0 1=true:=s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s191_7_0 : block g191 7 0 13=true:=by
  apply m1 (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s191_7_1 : block g191 7 13 15=true:=by
  apply m1 (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
lemma bl191_7 : block g191 7 0 28=true:=(@m5 g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s191_8_0 : block g191 8 0 7=true:=by
  apply m1 (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s191_8_1 : block g191 8 7 61=true:=by
  apply m1 (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s191_8_2 : block g191 8 68 32=true:=by
  apply m1 (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
lemma bl191_8 : block g191 8 0 100=true:=(@m5 g191 8 0 68 32 (@m5 g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s191_9_0 : block g191 9 0 3=true:=by
  apply m1 (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s191_9_1 : block g191 9 3 9=true:=by
  apply m1 (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
lemma bl191_9 : block g191 9 0 12=true:=(@m5 g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s191_10_0 : block g191 10 0 1=true:=by
  apply m1 (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
lemma bl191_10 : block g191 10 0 1=true:=s191_10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma tables191 : checkedTables g191 10:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0=true)
  · exact (rfl : block g191 1 0 0=true)
  · exact (rfl : block g191 2 0 0=true)
  · exact (rfl : block g191 3 0 0=true)
  · exact (rfl : block g191 4 0 0=true)
  · exact (rfl : block g191 5 0 0=true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma low191 : Lower (vars 191) (graphGoal 191) 11 :=
  m17 (g:=g191) (i:=0) (hints:=536879361) (m4 known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat):=[(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191:=extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma valid191 : Known known191:=m0 valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma low251 : Lower (vars 251) (graphGoal 251) 8 :=
  m10 (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (m4 known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat):=[(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251:=extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma valid251 : Known known251:=m0 valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma low255 : Lower (vars 255) (graphGoal 255) 12 :=
  m10 (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (m4 known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat):=[(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255:=extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma valid255 : Known known255:=m0 valid251 low255 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma geom383 : graphValid g383 (boundsBefore known255)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,m3 (d:=4) ?_⟩,m3 (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s383_8_0 : block g383 8 0 23=true:=by
  apply m1 (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s383_8_1 : block g383 8 23 2=true:=by
  apply m1 (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
lemma bl383_8 : block g383 8 0 25=true:=(@m5 g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s383_9_0 : block g383 9 0 9=true:=by
  apply m1 (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s383_9_1 : block g383 9 9 75=true:=by
  apply m1 (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s383_9_2 : block g383 9 84 7=true:=by
  apply m1 (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
lemma bl383_9 : block g383 9 0 91=true:=(@m5 g383 9 0 84 7 (@m5 g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s383_10_0 : block g383 10 0 5=true:=by
  apply m1 (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s383_10_1 : block g383 10 5 16=true:=by
  apply m1 (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s383_10_2 : block g383 10 21 20=true:=by
  apply m1 (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
lemma bl383_10 : block g383 10 0 41=true:=(@m5 g383 10 0 21 20 (@m5 g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s383_11_0 : block g383 11 0 1=true:=by
  apply m1 (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s383_11_1 : block g383 11 1 5=true:=by
  apply m1 (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
lemma bl383_11 : block g383 11 0 6=true:=(@m5 g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma s383_12_0 : block g383 12 0 1=true:=by
  apply m1 (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
lemma bl383_12 : block g383 12 0 1=true:=s383_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma tables383 : checkedTables g383 12:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0=true)
  · exact (rfl : block g383 1 0 0=true)
  · exact (rfl : block g383 2 0 0=true)
  · exact (rfl : block g383 3 0 0=true)
  · exact (rfl : block g383 4 0 0=true)
  · exact (rfl : block g383 5 0 0=true)
  · exact (rfl : block g383 6 0 0=true)
  · exact (rfl : block g383 7 0 0=true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma low383 : Lower (vars 383) (graphGoal 383) 13 :=
  m17 (g:=g383) (i:=0) (hints:=12901687553) (m4 known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat):=[(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383:=extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma valid383 : Known known383:=m0 valid255 low383 (by decide +kernel)
def hashdeadl14 (i : Nat) : Nat:=0x4592c8500000000002800049a6c68a83340e9800000aa00684000000054a001bcc7001e180000682000000000000001d46a1840000003a00000001c
def hashdeadl13 (i : Nat) : Nat:=0x301a0007b2f00e0aa2992094818000e2e0000000269e056438000000000d33e40e4a200074d00000000000003b10001e0240a9bd45d962582900000000000001430001e1400000fc03b84a000614e69108a1108000810000d04c9d0000000408800000160f24180010b9d040003080001e0c000000000001997f401183740ee12000000000080d312c00102c00000000012070000000001d35000308c000a4c0001b30000000cb3800183000070f0000001abcc008002c8cc133000000000000000000000020b000000064ec0a00000f8000cc5000105d8204160001a38001c1c467309c000000a7700000016de30f80000008380b08e000d3001
def hashdeadl12 (i : Nat) : Nat:=(if i<1 then 0x7b02c3200425d610a000042a0327300000000106b33757005e04600006037d811679d009461963480703e1077f067f2582384275d80a540a20109b59b4006305d00000000ab6dfb0bf59ec084c806986b30597776440b146b100c50a956520000878e0000747c463e108bc029e7600000395ef090d06800000000f0550000d0b1e4af00000000f324d141840ca4380000000051505017000067300000e779907b0000e77730641201ea62a089a48ff0924111e9a7a041b2a180aee462f29d9b47b01eb0427030e02a5973605b9086f08d5081d04bb014363000006038c0b6d110106cc731308e0023a07fb1305601ba1839b4c088a10b88011043e427e75a600831464016903d3ba52b1ec095000ec050b011b0730478f11a0000755e331ef63db004a00a000069a91680e225f60f90092a9d0000764650a40000c591f95ac03baa33c5a1283d11871a6d2772c01c1057280f201f5012328b908232a5505e000fe02b507cf0809817c267c05c9528506d997696872194b206264030ad402d007d586d7228701d30605840f67838625a51443ce034d47ed45f704cb08730a1794e1252000070330000b56f0000b0b4000000000000a842e047609d406ae26b67b08a4de12aa0a34019000000000000b664342c50b50000c0af924dc9aa401870366002b26d00000000841e0000000060986614000000000000783ae10d980ee051d0ab4022a615808f0000a0832619a148d81500007000e007d616b032d01b483f163f00104028276b2015141030631049a027580cd0a7a05ab977802fb09ff07a97899053b0a80816e83be0790a1b809b8b460a4f0000178b0000847be03cf139a1170000b07850b3605408416262696b908af0aa7b1f5b446070d024601a42492101d496f4b4e035922127ab0000e18600008284831c00440000f031500310656013b071b045b25b4113766b5b4c6b0800008291b4888a50000000000000e38b0000225eb04d807230618425c0b097ae226f809e00000000f00d93480485e88728040000b11c3039204e9432711f445c905f004a300b97ada05680211292f09a7b1a696f3106704f19748066703f00000204d074ba20a118f025458794596091a06f000065946020913b783e342dd08c819b5b452076c21dc075e0991a4a183c3b19d7a750a68058c8379643a487b408d0523762d062b422e0b2d47fc0ac224a46231a5dca3b6069a4390000768a5433e07e0000da410b00003102090604000a010a1f88080000080d030b0c310304001300040113030203141f0c0001000232030b0801010a010007110002020208010605020401010119010b0304070203070506000210070d110100150b0a0504051d050002020b05000c0402003d0e1500260200020108040b03090500060204000d0602010100180501000001030f04 else 0xe0a0512830933085c048e216509713746026a02ec09cb040548400000268f701103ac254729fc29e8096145a39ab47552144806e00019612b7b4491ea44bc1)
def hashdeadl11 (i : Nat) : Nat:=0x5b144463e05aea749a36008e0000f05f008fc82400000000057a08357304bb42c02b0000807cd1701823000007095811411b96631031e07218223334c77b980e8010305dd000180820521064ca3ef0420000409b626cd483a833f03ac022e048a008f80a513f0000db73410f3393ca38834018881012b081c465a02c6142704300002631809700000000715300007115b00dd054b2886014000054161b183099000000000129f0870000a24110110427972915960000477d5b457113518aa01a00007134a023d08a1053002d678ef06b604a6076520f5468b025698fe62d5060c1370000e07eb793c95be02a510198285417000000000000000000005b72220ea00f9098e036e09602120000503908396112556c56084a3a211d0342f0784635707b4293308d0624205556235211962a72516903a0190235010e7765e07d5784f16feb3c248834149073d088b0134091f720f0803275f0052809446ed494b01b1b0305939136b20cf495111aba390000db890950e9807026e609a0205015880ba66b8778d4967988f077f007110cd289d0160000e278401d0000000000000000f032027400000000a08c6209804c4030102eb368a33f3b1d798e0000538a70215061a44e228300000000000000000000d01710838075e4517067406f00000000609a00003253a089a4002093b00a8125000090790000c0599583180c00000000c0411830f1160047224900000000906992725046700b000050511a67544b00000407c35bb06d0000504d3821ca470002762e0000cb1760948827b10a603b4009e06552019464444f9688a0286169097ab82524185057db2feb3d000e6303670ac01e70822426b090d664c05cf764008be03c365d6a2549347068706a71244461f086277c5780380d698dd120b27c20626037d807f403502fe1110000ea6e5071301cb0388044704f411c809595011003b20deb1a98372208b0561092820a91190049704bb03ec070670890335001a03f64504063613c50294b430832441aba46e146c8120193598c103df8314066401fd460e0745084044c100c7760b24b824f4006205b0000563070507a7c9058000000006a440000506e3040e97d006cd027646a6207807fb0450138e56fa018704e8482e0356085662f762c5b3be05eb81f1004f836000000000000000046203a6ac89692730000b034807a613d00008145702433536a79b0407805012a04e80082c50a0c0e782286421a0e4c00400004833a1491a02243880c0851202004211c6408c1835c192e081800c39681005000c04e408002001860c34c8040000000400008087400400100892c38005148410524200800478080001438126000000020022
def hashdeadl10 (i : Nat) : Nat:=0x1c05302000382d2ecf474c3a08f618409ea54931a0a2272b385214e934380040192451090d15cc0564307983441ce005970002c06068f08a82680cc070001a2c5d4a1440400018207150002808001022205d856c41e1700072d518800084a2900000a334a12801820030b1a27
def hashdeadl9 (i : Nat) : Nat:=0x202e0
def deadsamples : Array (Bits × Bits):=Array.mk [(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : m2 ColumnInfo:=(.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat):=Array.mk [[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def dead : Forest:=⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
lemma geomdead : graphValid dead (boundsBefore known383)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,m3 (d:=5) ?_⟩,m3 (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def isNotT (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false
private lemma gate_repT (w : List Sig) (g : Gate)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) /\ g.inputs.length≤2) :
    represented w (gv w g) ∨
      (if isNotT g.op then ∃ a,a∈w /\ proper a /\ gv w g=neg a
       else ∃ d a b,a∈w /\ b∈w /\ proper a /\ proper b /\ a≠b /\ gv w g=bin d a b):=by
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) \/ ∃ x,x∈w /\ proper x /\ neg a=neg x:=by
    rcases m13 ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (Or.inr fun h => h.2 m70.1)
    · exact Or.inl (Or.inr fun h => h.1 m70.2)
    · exact Or.inr ⟨a,hm,hp,rfl⟩
  have bn (d : Bool) (a b : Sig) (ha : represented w a) (hb : represented w b) :
      represented w (bin d a b) \/ ∃ d' x y,x∈w /\ y∈w /\ proper x /\ proper y /\ x≠y /\ bin d a b=bin d' x y:=by
    have bzero : ∀ v,bin false v zero=zero /\ bin true v zero=v:=fun v => ⟨(m16 v).2.2.1,(m16 v).2.1⟩
    have bone : ∀ v,bin false v one=v /\ bin true v one=one:=fun v => ⟨(m16 v).1,(m16 v).2.2.2.1⟩
    rcases m13 ha with rfl | rfl | ⟨hma,hpa⟩
    · rw [m24]
      cases d
      · exact Or.inl (Or.inr fun h => h.1 (bzero b).1)
      · rw [(bzero b).2]; exact Or.inl hb
    · rw [m24]
      cases d
      · rw [(bone b).1]; exact Or.inl hb
      · exact Or.inl (Or.inr fun h => h.2 (bone b).2)
    · rcases m13 hb with rfl | rfl | ⟨hmb,hpb⟩
      · cases d
        · exact Or.inl (Or.inr fun h => h.1 (bzero a).1)
        · rw [(bzero a).2]; exact Or.inl (Or.inl hma)
      · cases d
        · rw [(bone a).1]; exact Or.inl (Or.inl hma)
        · exact Or.inl (Or.inr fun h => h.2 (bone a).2)
      · by_cases eq : a=b
        · subst b
          cases d
          · rw [(m16 a).2.2.2.2.1]; exact Or.inl (Or.inl hma)
          · rw [(m16 a).2.2.2.2.2]; exact Or.inl (Or.inl hma)
        · exact Or.inr ⟨d,a,b,hma,hmb,hpa,hpb,eq,rfl⟩
  obtain ⟨ho,hl⟩:=hg
  rcases ho with ho | ho | ho
  · simp only [ho,isNotT,Bool.false_eq_true,ite_false]
    cases hi : g.inputs with
    | nil => exact Or.inl (Or.inr fun h => h.2 (by simp [gv,ho,hi]))
    | cons i t =>
      cases t with
      | nil => exact Or.inl (by simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(m16 _).1] using get_rep w i)
      | cons j u =>
        cases u with
        | cons _ _ => simp [hi] at hl
        | nil => simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(m16 _).1] using bn false _ _ (get_rep w i) (get_rep w j)
  · simp only [ho,isNotT,Bool.false_eq_true,ite_false]
    cases hi : g.inputs with
    | nil => exact Or.inl (Or.inr fun h => h.1 (by simp [gv,ho,hi]))
    | cons i t =>
      cases t with
      | nil => exact Or.inl (by simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(m16 _).2.1] using get_rep w i)
      | cons j u =>
        cases u with
        | cons _ _ => simp [hi] at hl
        | nil => simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(m16 _).2.1] using bn true _ _ (get_rep w i) (get_rep w j)
  · rw [Set.mem_singleton_iff] at ho
    simp only [ho,isNotT,ite_true]
    cases hi : g.inputs with
    | nil =>
      have hgv : gv w g=one:=by simp only [gv,ho,hi,List.map_nil,List.headD_nil,m70.1]
      exact Or.inl (Or.inr fun h => h.2 hgv)
    | cons i t =>
      have hgv : gv w g=neg (w.getD i zero):=by simp only [gv,ho,hi,List.map_cons,List.headD_cons]
      rw [hgv]; exact nx _ (get_rep w i)
private lemma pull_gateT {w : List Sig} {z : Sig} {k t S} (isN : Bool) (h : Live target k t S)
    (hz : represented w z ∨
      (if isN then ∃ a,a∈w /\ proper a /\ z=neg a
       else ∃ d a b,a∈w /\ b∈w /\ proper a /\ proper b /\ a≠b /\ z=bin d a b))
    (sub : ∀ a ∈ S,a ∈ w++[z]) :
    ∃ k' t' S',k' ≤ k+1 /\ t' ≤ t+isN.toNat /\ Live target k' t' S' /\ ∀ a ∈ S',a ∈ w:=by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,by cases isN <;> simp,h,?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w \/ a=z) with hu | rfl
      · exact hu
      · exact hw
    · have hp:=m22 h z hm
      rcases hz with hr | hwit
      · exact False.elim ((hr.resolve_left hw) hp)
      · cases isN with
        | true =>
          simp only [ite_true] at hwit
          obtain ⟨a,ha,hp',eq⟩:=hwit
          subst z
          let U:=S.erase (neg a)
          have ht : Live target k t (insert (neg a) U):=by simpa [U,Finset.insert_erase hm] using h
          have hu : ∀ v ∈ U,v ∈ w:=fun v hv => by
            obtain ⟨hne,hm⟩:=Finset.mem_erase.mp hv; simpa [hne] using sub v hm
          have hf : neg a ∉ insert a U:=fun hh => by
            rcases Finset.mem_insert.mp hh with eq | u
            · exact hw (eq.symm ▸ ha)
            · exact hw (hu _ u)
          exact ⟨k+1,t+1,insert a U,Nat.le_refl _,by simp,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
        | false =>
          simp only [Bool.false_eq_true,ite_false] at hwit
          obtain ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩:=hwit
          subst z
          let U:=S.erase (bin d a b)
          have ht : Live target k t (insert (bin d a b) U):=by simpa [U,Finset.insert_erase hm] using h
          have hu : ∀ v ∈ U,v ∈ w:=fun v hv => by
            obtain ⟨hne,hm⟩:=Finset.mem_erase.mp hv; simpa [hne] using sub v hm
          have hf : bin d a b ∉ insert a (insert b U):=fun hh => by
            rcases Finset.mem_insert.mp hh with eq | u
            · exact hw (eq.symm ▸ ha)
            rcases Finset.mem_insert.mp u with eq | u
            · exact hw (eq.symm ▸ hb)
            · exact hw (hu _ u)
          exact ⟨k+1,t,insert a (insert b U),Nat.le_refl _,by simp,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,by cases isN <;> simp,h,?_⟩
    intro a ha
    have hn : a≠z:=fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
private lemma extractT (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) /\ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S,k ≤ gs.length /\ t ≤ gs.countP (fun g => isNotT g.op) /\ Live target k t S /\ ∀ a ∈ S,a ∈ w:=by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hl,hs⟩:=ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl',hu',hlu,hT⟩:=pull_gateT (isNotT g.op) hl (gate_repT w g (legal g (by simp))) hs
    refine ⟨l,u,T,by simp; omega,?_,hlu,hT⟩
    simp only [List.countP_cons]
    cases h : isNotT g.op <;> simp [h] at hu' ⊢ <;> omega
def I1 (T : Sig) (cap tm : Nat) (S : Finset Sig) : Prop :=
  ∀ k t,k ≤ cap -> t ≤ tm -> ¬Live T k t S
lemma i2i1 {T cap tm S} (h : Impossible T cap S) : I1 T cap tm S :=
  fun k t hk _ => h k t hk
lemma re1 {T n tm} {ws : List Sig} (hi : I1 T n tm ws.toFinset)
    (p : List Move) (ok : autoOK T p=true) : I1 T n tm (ws.map (movedWord p.reverse)).toFinset:=by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p):=fun r => ⟨movedRow p.reverse r,m42 ok.2 r⟩
  intro k t hk ht h
  have run:=m90 h (movedRow p) onto
  have goal : rename (movedRow p) T=T:=(m20 p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x)=x:=by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _=bit ⟨j,hj⟩ _
    rw [m7,m40,m42 ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p))=ws.toFinset:=by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩; simpa only [inv] using hw
    · intro ha; exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk ht run
def child1 (tm cap len op : Nat) : Nat :=
  if len==cap||op==2||tm==0 then 0 else 1
lemma es1 {T : Sig} {cap tm : Nat} {ws : List Sig} (htm1 : tm ≤ 1) (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : tm > 0 -> ∀ a ∈ ws,∀ keep,neg a ∉ ws -> proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      I1 T (cap-1) (child1 tm cap (childOne ws a keep).length 2) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws,∀ b ∈ ws,∀ d ka kb,a≠b -> bin d a b ∉ ws →
      proper (bin d a b) -> (childTwo ws a b d ka kb).length ≤ cap →
      I1 T (cap-1) (child1 tm cap (childTwo ws a b d ka kb).length 0)
        (childTwo ws a b d ka kb).toFinset) :
    I1 T cap tm ws.toFinset:=by
  classical
  intro k t hk ht h
  generalize he : ws.toFinset=S at h
  induction h using Live.recurse with
  | stop hp =>
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  | @unary k t U a ha hf tail _ =>
    have am : a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=m22 tail _ (Finset.mem_insert_self _ _)
    let keep:=decide (a ∈ U)
    have er:=m39 hn a
    have rest : (kept keep a (ws.erase a)).toFinset=U:=by
      rw [m28,er,he]; by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup:=by
      have na : a ∉ ws.erase a:=hn.not_mem_erase
      refine List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h)),
        kept_nd keep a (ws.erase a) (hn.erase _) na⟩
    have eq : (childOne ws a keep).toFinset=insert (neg a) U:=by simp [childOne,rest]
    have sc:=(m26 tail).2
    have len : (childOne ws a keep).length ≤ cap:=by rw [←List.toFinset_card_of_nodup nd,eq]; omega
    have htm_pos : tm > 0:=by omega
    have ht' : t ≤ child1 tm cap (childOne ws a keep).length 2:=by
      unfold child1; simp; omega
    exact oneStep htm_pos a am keep fresh hz len k t (by omega) ht' (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail _ =>
    have am : a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=m22 tail _ (Finset.mem_insert_self _ _)
    let ka:=decide (a ∈ U)
    let kb:=decide (b ∈ U)
    let rest:=(ws.erase a).erase b
    have er : rest.toFinset=(ws.toFinset.erase a).erase b:=by
      rw [show rest=(ws.erase a).erase b by rfl,m39 (hn.erase _) b,m39 hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset=U:=by
      rw [m28,m28,er,he]
      ext j
      by_cases hja : j=a
      · subst j; by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka,kb,aa,bb,hab]
      · by_cases hjb : j=b
        · subst j; by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka,kb,aa,bb,hja]
        · by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka,kb,aa,bb,hja,hjb]
    have rn : rest.Nodup:=(hn.erase _).erase _
    have ar : a ∉ rest:=fun h => hn.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest:=(hn.erase a).not_mem_erase
    have nk:=kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest:=by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup :=
      List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h))),
        kept_nd ka a _ nk ax⟩
    have eq : (childTwo ws a b d ka kb).toFinset=insert (bin d a b) U:=by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset=_; simp [ke]
    have sc:=(m26 tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap:=by rw [←List.toFinset_card_of_nodup nd,eq]; omega
    have ht' : t ≤ child1 tm cap (childTwo ws a b d ka kb).length 0:=by
      unfold child1
      by_cases hlen : (childTwo ws a b d ka kb).length=cap
      · rw [←List.toFinset_card_of_nodup nd,eq] at hlen; simp [hlen]; omega
      · by_cases htm0 : tm=0
        · simp [htm0]; omega
        · have hne : ((childTwo ws a b d ka kb).length==cap||0==2||tm==0)=false:=by
            simp [beq_eq_false_iff_ne.mpr hlen,beq_eq_false_iff_ne.mpr htm0]
          rw [hne]; simp; omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) ht' (eq.symm ▸ tail)
lemma cc1s {raw T pools links k tm rest op}
    (pValid : ∀ p ∈ pools,ValidPool raw T p)
    (lValid : ∀ tag xs,xs ∈ links tag -> I1 T k tm (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op=true) :
    I1 T k tm (choiceVal op :: rest).toFinset:=by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [m11 ok]; exact lValid _ _ hx
  · exact i2i1 (m9 (pValid _ hp) nd ok)
abbrev LinkFn:=Nat -> List (List Sig)
abbrev NC1 :=
  Nat × Nat × Nat × List Decor × CovPair × List BoundPool × List QuickPool × LinkFn × LinkFn
def cw1 (c : NC1) (i : Nat) : Decor:=c.2.2.2.1.getD i defaultDecor
def em1 (c : NC1) (op : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let (cap,tm,n,ws,cov,pools,qpools,l0,l1):=c
  let un:=op==2
  let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
  if len > cap then true else
    let ct:=child1 tm cap len op
    let d:=ct==0
    if (restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1||ws.any (fun v => v.1==z.1) then true else
    if qpools.any (fun qp => fastCost qp (cap-1) a b op ka kb) then true else
      let rest:=(opKeep un ka kb a b ws).map Prod.fst
      let links:=if d then l0 else l1
      closeChild pools links (cap-1) rest (movedChoice op a b)
lemma e1s {raw T r s ws pools l0 l1 cap tm a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws,faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false -> a≠b) (hcap : 0 < cap)
    (pv : ∀ p ∈ pools,ValidPool raw T p)
    (lv0 : ∀ tag xs,xs ∈ l0 tag -> I1 T (cap-1) 0 (List.toFinset xs))
    (lv1 : ∀ tag xs,xs ∈ l1 tag -> I1 T (cap-1) 1 (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : em1 (cap,tm,ws.length,ws,preCov ws,pools,pools.map (summarizePool ws),l0,l1)
      op a b (movedDecor op a b) ka kb=true) :
    I1 T (cap-1) (child1 tm cap (moveFront ws op a b ka kb).length op)
      (moveFront ws op a b ka kb).toFinset:=by
  let z:=movedDecor op a b
  let rest:=opKeep (op==2) ka kb a b ws
  let child:=z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws:=m71 _ _ _ _ _ _
  have ndc : child.Nodup:=List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
  have val:=m54 op a b
  have fr : ws.any (fun v => v.1==z.1)=false:=by
    apply Bool.eq_false_iff.mpr; intro hh
    obtain ⟨x,hx,he⟩:=List.any_eq_true.mp hh
    exact fresh ((beq_iff_eq.mp he).symm ▸ List.mem_map_of_mem hx)
  have pp : properB z.1=true:=by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2)||kb then 0 else 1))=child.length:=by
    change _=(z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk ht h
  have hsz:=(m26 h).2
  change child.toFinset.card+t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap:=by omega
  unfold em1 at test
  change (if 1+(ws.length-_ - _) > cap then true else _)=true at test
  rw [leq,if_neg (by omega)] at test
  let ct:=child1 tm cap child.length op
  have ht0 : (ct==0)=true -> t=0:=fun hct => by have:=beq_iff_eq.mp hct; change t ≤ ct at ht; omega
  have sep:=m96 h rfl (pair_sep pairs) (ct==0) ht0
  let d:=ct==0
  have g : (coverage d rest).1=covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz:=m69 ha hb (op==2) ka kb d ne
  have hf:=m60 (faith _ ha) (faith _ hb) op
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst)=_ at sep
  change z.2=pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768)=false:=by
    rw [sep,bne_self_eq_false]
  change (if (_ != _) then true else if !properB z.1||ws.any (fun v => v.1==z.1) then true else if _ then true else _)=true at test
  rw [be,pp,fr] at test
  simp only [Bool.false_eq_true,ite_false,Bool.not_true,Bool.false_or] at test
  have nd' : (choiceVal (movedChoice op a b) :: rest.map Prod.fst).Nodup:=val ▸ ndc
  have h' : Live T k t (choiceVal (movedChoice op a b) :: rest.map Prod.fst).toFinset:=val ▸ h
  by_cases hq : (pools.map (summarizePool ws)).any (fun qp => fastCost qp (cap-1) a b op ka kb)=true
  · obtain ⟨qp,hqp,hfc⟩:=List.any_eq_true.mp hq
    obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hqp
    exact m9 (pv p hp) nd' (m72 ha hb hfc) k t hk h'
  · have hqf : (pools.map (summarizePool ws)).any (fun qp => fastCost qp (cap-1) a b op ka kb)=false :=
      Bool.eq_false_iff.mpr hq
    change (if ((pools.map (summarizePool ws)).any fun qp => fastCost qp (cap-1) a b op ka kb)=true then true else _)=true at test
    rw [hqf] at test
    simp only [Bool.false_eq_true,ite_false] at test
    by_cases hd : d=true
    · dsimp only [d,ct] at hd; rw [hd] at test; simp only [ite_true] at test
      exact cc1s pv lv0 nd' test k t hk (by have:=ht0 hd; omega) h'
    · have hdf : d=false:=Bool.eq_false_iff.mpr hd
      dsimp only [d,ct] at hdf; rw [hdf] at test; simp only [Bool.false_eq_true,ite_false] at test
      have hct1 : ct ≤ 1:=by dsimp only [ct,child1]; split_ifs <;> omega
      exact cc1s pv lv1 nd' test k t hk (by change t ≤ ct at ht; omega) h'
def tp1 (ctx : NC1) (a b : Decor) (d : Bool) : Bool :=
  let op:=if d then 1 else 0
  let z:=movedDecor op a b
  em1 ctx op a b z false false&&em1 ctx op a b z true false &&
    em1 ctx op a b z false true&&em1 ctx op a b z true true
def tr1 (ctx : NC1) (a : Decor) (bs : List Decor) : Bool :=
  let unOk:=if ctx.2.1==0 then true else
    let n:=movedDecor 2 a a
    em1 ctx 2 a a n false false&&em1 ctx 2 a a n true true
  unOk&&bs.all (fun b => tp1 ctx a b false&&tp1 ctx a b true)
def ta1 (ctx : NC1) : List Decor -> Bool
  | [] => true
  | a :: ws => tr1 ctx a ws&&ta1 ctx ws
lemma au1 {ctx} {ws : List Decor} (h : ta1 ctx ws=true) (ht : ctx.2.1 > 0) {a : Decor} (ha : a ∈ ws) (keep : Bool) :
    em1 ctx 2 a a (movedDecor 2 a a) keep keep=true:=by
  induction ws with
  | nil => cases ha
  | cons x xs ih =>
    simp only [ta1,Bool.and_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · have hr:=h.1
      simp only [tr1,Bool.and_eq_true] at hr
      have hne : (ctx.2.1==0)=false:=beq_eq_false_iff_ne.mpr (by omega)
      have hu:=hr.1
      rw [hne] at hu; simp only [Bool.false_eq_true,ite_false,Bool.and_eq_true] at hu
      cases keep <;> [exact hu.1; exact hu.2]
    · exact ih h.2 hm
lemma ab1 {ctx} {ws : List Decor} (h : ta1 ctx ws=true) {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (d : Bool) :
    tp1 ctx a b d=true \/ tp1 ctx b a d=true:=by
  induction ws with
  | nil => cases ha
  | cons x xs ih =>
    simp only [ta1,Bool.and_eq_true,tr1,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · exact False.elim (ne rfl)
    · left; cases d <;> [exact (h.1.2 b hb').1; exact (h.1.2 b hb').2]
    · right; cases d <;> [exact (h.1.2 a ha').1; exact (h.1.2 a ha').2]
    · exact ih h.2 ha' hb'
lemma tp1_at {ctx a b d} (h : tp1 ctx a b d=true) (ka kb : Bool) :
    em1 ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb=true:=by
  simp only [tp1,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> simp [h]
lemma n1s {raw T r s ws pools l0 l1 cap tm}
    (htm1 : tm ≤ 1) (pairs : properPairs T r s) (faith : ∀ w ∈ ws,faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools,ValidPool raw T p)
    (lv0 : ∀ tag xs,xs ∈ l0 tag -> I1 T (cap-1) 0 (List.toFinset xs))
    (lv1 : ∀ tag xs,xs ∈ l1 tag -> I1 T (cap-1) 1 (List.toFinset xs))
    (checks : cap=0 \/ ta1 (cap,tm,ws.length,ws,preCov ws,pools,pools.map (summarizePool ws),l0,l1) ws=true) :
    I1 T cap tm (ws.map Prod.fst).toFinset:=by
  rcases checks with rfl | checks
  · intro k t hk _ h
    have hk0 : k=0:=by omega
    subst hk0
    generalize he : (ws.map Prod.fst).toFinset=S at h
    have eqS : S={_}:=h (fun k _ S => k=0 -> S={_}) (fun _ _ => rfl)
      (fun _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn))
      (fun _ _ _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn)) rfl
    exact out (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  by_cases hc : cap=0
  · subst hc
    intro k t hk _ h
    have hk0 : k=0:=by omega
    subst hk0
    generalize he : (ws.map Prod.fst).toFinset=S at h
    have eqS : S={_}:=h (fun k _ S => k=0 -> S={_}) (fun _ _ => rfl)
      (fun _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn))
      (fun _ _ _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn)) rfl
    exact out (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  have hc' : 0 < cap:=by omega
  apply es1 htm1 nd out
  · intro htpos v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hv
    have hf:=m83 nd ha keep
    have hev:=e1s (op:=2) pairs faith nd ha ha (by simp) hc' pv lv0 lv1 pro fresh (au1 checks htpos ha keep)
    have hlenEq : (moveFront ws 2 a a keep keep).length=(childOne (ws.map Prod.fst) a.1 keep).length:=by
      have nd1 : (moveFront ws 2 a a keep keep).Nodup:=by
        unfold moveFront
        have sub:=m71 ws a a true keep keep
        exact List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
      have nd2 : (childOne (ws.map Prod.fst) a.1 keep).Nodup:=by
        unfold childOne
        have na : a.1 ∉ (ws.map Prod.fst).erase a.1:=nd.not_mem_erase
        refine List.nodup_cons.mpr ⟨fun hm => ?_,kept_nd keep a.1 _ (nd.erase _) na⟩
        rw [m23] at hm
        rcases hm with ⟨heq,_⟩ | hm
        · exact fresh (heq.symm ▸ List.mem_map_of_mem ha)
        · exact fresh (List.mem_of_mem_erase hm)
      rw [←List.toFinset_card_of_nodup nd1,←List.toFinset_card_of_nodup nd2,hf]
    rw [hf,hlenEq] at hev
    exact hev
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩:=List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩:=List.mem_map.mp hb
    have ab : a≠b:=fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a ∈ ws) (bb : b ∈ ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : tp1 (cap,tm,ws.length,ws,preCov ws,pools,pools.map (summarizePool ws),l0,l1) a b d=true) :
        I1 T (cap-1) (child1 tm cap (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length 0)
          (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
      have hf:=m78 nd aa bb ne' d ka kb
      have eq : (movedDecor (if d then 1 else 0) a b).1=bin d a.1 b.1:=by cases d <;> rfl
      have hop0 : child1 tm cap (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length (if d then 1 else 0)=child1 tm cap (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length 0:=by cases d <;> rfl
      have hev:=e1s (op:=if d then 1 else 0) pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv0 lv1
        (eq ▸ pr) (eq ▸ fr) (tp1_at test ka kb)
      have hlenEq : (moveFront ws (if d then 1 else 0) a b ka kb).length =
          (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length:=by
        have nd1 : (moveFront ws (if d then 1 else 0) a b ka kb).Nodup:=by
          unfold moveFront
          have sub:=m71 ws a b ((if d then 1 else 0)==2) ka kb
          exact List.nodup_cons.mpr ⟨fun hm => (eq ▸ fr) ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
        have nd2 : (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).Nodup:=by
          unfold childTwo
          let r0:=((ws.map Prod.fst).erase a.1).erase b.1
          have rn : r0.Nodup:=(nd.erase _).erase _
          have ar : a.1 ∉ r0:=fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have br : b.1 ∉ r0:=(nd.erase a.1).not_mem_erase
          have nk:=kept_nd kb b.1 r0 rn br
          have ax : a.1 ∉ kept kb b.1 r0:=by cases kb <;> simp [kept,ar,ne']
          refine List.nodup_cons.mpr ⟨fun hm => ?_,kept_nd ka a.1 _ nk ax⟩
          rw [m23] at hm
          rcases hm with ⟨heq,_⟩ | hm
          · exact fr (heq.symm ▸ List.mem_map_of_mem aa)
          · rw [m23] at hm
            rcases hm with ⟨heq,_⟩ | hm
            · exact fr (heq.symm ▸ List.mem_map_of_mem bb)
            · exact fr (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        rw [←List.toFinset_card_of_nodup nd1,←List.toFinset_card_of_nodup nd2,hf]
      rw [hf,hlenEq,hop0] at hev
      exact hev
    rcases ab1 checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · have hsw:=m73 (ws.map Prod.fst) nd a.1 b.1 d ka kb
      have hlenSw : (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length =
          (childTwo (ws.map Prod.fst) b.1 a.1 d kb ka).length:=by
        have ndA : (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).Nodup:=by
          unfold childTwo
          let rA:=((ws.map Prod.fst).erase a.1).erase b.1
          have rn : rA.Nodup:=(nd.erase a.1).erase b.1
          have ar : a.1 ∉ rA:=fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have br : b.1 ∉ rA:=(nd.erase a.1).not_mem_erase
          have nk:=kept_nd kb b.1 rA rn br
          have ax : a.1 ∉ kept kb b.1 rA:=by cases kb <;> simp [kept,ar,ne]
          refine List.nodup_cons.mpr ⟨fun hm => ?_,kept_nd ka a.1 _ nk ax⟩
          rw [m23] at hm; rcases hm with ⟨heq,_⟩ | hm
          · exact fresh (heq.symm ▸ List.mem_map_of_mem haW)
          · rw [m23] at hm; rcases hm with ⟨heq,_⟩ | hm
            · exact fresh (heq.symm ▸ List.mem_map_of_mem hbW)
            · exact fresh (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        have ndB : (childTwo (ws.map Prod.fst) b.1 a.1 d kb ka).Nodup:=by
          unfold childTwo
          let rB:=((ws.map Prod.fst).erase b.1).erase a.1
          have rn : rB.Nodup:=(nd.erase b.1).erase a.1
          have br : b.1 ∉ rB:=fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have ar : a.1 ∉ rB:=(nd.erase b.1).not_mem_erase
          have nk:=kept_nd ka a.1 rB rn ar
          have bx : b.1 ∉ kept ka a.1 rB:=by cases ka <;> simp [kept,br,Ne.symm ne]
          refine List.nodup_cons.mpr ⟨fun hm => ?_,kept_nd kb b.1 _ nk bx⟩
          rw [m24 d b.1 a.1] at hm
          rw [m23] at hm; rcases hm with ⟨heq,_⟩ | hm
          · exact fresh (heq.symm ▸ List.mem_map_of_mem hbW)
          · rw [m23] at hm; rcases hm with ⟨heq,_⟩ | hm
            · exact fresh (heq.symm ▸ List.mem_map_of_mem haW)
            · exact fresh (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        rw [←List.toFinset_card_of_nodup ndA,←List.toFinset_card_of_nodup ndB,hsw]
      rw [hsw,hlenSw]
      exact one b a hbW haW (Ne.symm ne) kb ka (m24 d a.1 b.1 ▸ pro) (m24 d a.1 b.1 ▸ fresh) hh
abbrev PT:=Nat × Nat × Nat × Nat × (Nat -> Nat)
def ePT : PT:=(0,0,0,0,fun _ => 0)
def dW : List Decor:=wiresOf dead
def dS : List Sig:=dW.map Prod.fst
def dcS (n : Nat) (bits : Nat) (ws : List Sig) : List Sig :=
  match n with
  | 0 => ws
  | k+1 =>
    let a:=ws.getD (bits &&& 15) zero
    let b:=ws.getD ((bits >>> 4) &&& 15) zero
    let op:=(bits >>> 8) &&& 3
    dcS k (bits >>> 10) (ws ++ [if op=2 then neg a else bin (op==1) a b])
lemma m116 (n bits : Nat) (ws : List Decor) :
    dcS n bits (ws.map Prod.fst)=(decodeBank n bits ws).map Prod.fst:=by
  induction n generalizing bits ws with
  | zero => rfl
  | succ k ih =>
    simp only [dcS,decodeBank]
    have hget : ∀ i,(ws.map Prod.fst).getD i zero=(ws.getD i defaultDecor).1:=by
      intro i
      rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_map]
      cases ws[i]? <;> rfl
    have hcode : (if ((bits >>> 8) &&& 3)=2 then neg ((ws.map Prod.fst).getD (bits &&& 15) zero)
        else bin (((bits >>> 8) &&& 3)==1) ((ws.map Prod.fst).getD (bits &&& 15) zero) ((ws.map Prod.fst).getD ((bits >>> 4) &&& 15) zero)) =
        (codeDecor ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) defaultDecor) (ws.getD ((bits >>> 4) &&& 15) defaultDecor)).1:=by
      rw [hget,hget]
      unfold codeDecor dbin dneg
      split
      · rfl
      · split <;> rfl
    rw [hcode,← List.map_singleton,← List.map_append]
    exact ih (bits >>> 10) _
lemma sLm {α β : Type} (f : α -> β) (bits : Nat) (ws : List α) :
    selectLive bits (ws.map f)=(selectLive bits ws).map f:=by
  induction ws generalizing bits with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,selectLive]
    split <;> simp [ih]
def rN (levels : Nat -> PT) (slot i : Nat) : Nat × List Decor × List Decor :=
  let raw:=dW
  let (_,depth,_,_,data):=levels slot
  let len:=10 * depth
  let width:=len+raw.length+depth
  let recp:=packedAt data (i * width) width
  let ops:=recp &&& ((1 <<< len) - 1)
  let bank:=decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)
def sS (levels : Nat -> PT) (slot i : Nat) : List Sig :=
  let (_,depth,_,_,data):=levels slot
  let len:=10 * depth
  let width:=len+dS.length+depth
  let recp:=packedAt data (i * width) width
  let ops:=recp &&& ((1 <<< len) - 1)
  selectLive (recp >>> len) (dcS depth ops dS)
lemma m119 (levels : Nat -> PT) (slot i : Nat) :
    sS levels slot i=(rN levels slot i).2.2.map Prod.fst:=by
  unfold sS rN
  rcases levels slot with ⟨num,depth,cw,offw,data⟩
  dsimp only
  have hlen : dS.length=dW.length:=by simp [dS]
  rw [hlen]
  dsimp only [dS]
  rw [m116,sLm]
def lS (levels : Nat -> PT) (slot : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (levels slot).1 then none else
    (dead.autos[pair.2]?).map fun perm => (sS levels slot pair.1).map (movedWord (perm.map swapRows).reverse)
lemma ls1s (levels : Nat -> PT) (k tm : Nat)
    (names : ∀ x ∈ dead.autos.toList,autoOK (targetOf dead) (x.map swapRows)=true)
    (earlier : ∀ i < (levels (3*k+tm)).1,I1 (targetOf dead) k tm (sS levels (3*k+tm) i).toFinset)
    {pair out} (h : lS levels (3*k+tm) pair=some out) :
    I1 (targetOf dead) k tm out.toFinset:=by
  unfold lS at h
  split at h
  · cases h
  next valid =>
    cases e : dead.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact re1 (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))
def ctx1 (levels : Nat -> PT) (idx0 idx1 : Nat -> Nat -> Option (Nat × Nat)) (k tm i : Nat) : NC1 :=
  let slot:=3 * k+tm
  let raw:=dW
  let (num,depth,cw,offw,data):=levels slot
  let (ops,bank,ws):=rN levels slot i
  let start:=num * (10 * depth+raw.length+depth)
  let pos:=start+num * offw+packedAt data (start+i * offw) offw
  let nr:=packedAt data pos 5
  let st:=pos+5
  let rules:=(getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule dead ops depth bank a b)
  let ls0:=fun tag => ((idx0 slot tag).bind (lS levels (3*(k-1)))).toList
  let ls1:=fun tag => ((idx1 slot tag).bind (lS levels (3*(k-1)+1))).toList
  (k,tm,ws.length,ws,preCov ws,rules,rules.map (summarizePool ws),ls0,ls1)
def pre1 (T : Sig) (c : NC1) : Bool :=
  let ws:=c.2.2.2.1.map Prod.fst
  decide ws.Nodup&&!(ws.contains T)
def nv1 (levels : Nat -> PT) (idx0 idx1 : Nat -> Nat -> Option (Nat × Nat)) (k tm i : Nat) : Bool :=
  let c:=ctx1 levels idx0 idx1 k tm i
  pre1 (targetOf dead) c&&(if k=0 then true else ta1 c c.2.2.2.1)
lemma nv1s (levels : Nat -> PT) (idx0 idx1 : Nat -> Nat -> Option (Nat × Nat)) (k tm i : Nat)
    (htm1 : tm ≤ 1) (samples : properPairs (targetOf dead) (asRow fun j => (dead.samples j).1) (asRow fun j => (dead.samples j).2))
    (cols : ∀ ci ∈ dead.cols.values,Slice (vars dead.mask) (targetOf dead) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ dead.autos.toList,autoOK (targetOf dead) (x.map swapRows)=true)
    (prior0 : k > 0 -> ∀ j < (levels (3*(k-1))).1,I1 (targetOf dead) (k-1) 0 (sS levels (3*(k-1)) j).toFinset)
    (prior1 : k > 0 -> ∀ j < (levels (3*(k-1)+1)).1,I1 (targetOf dead) (k-1) 1 (sS levels (3*(k-1)+1) j).toFinset)
    (checked : nv1 levels idx0 idx1 k tm i=true) :
    I1 (targetOf dead) k tm (sS levels (3*k+tm) i).toFinset:=by
  rw [m119]
  simp only [nv1,pre1,ctx1,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] at checked
  have hN:=checked.1.1
  have hT : targetOf dead ∉ (rN levels (3*k+tm) i).2.2.map Prod.fst:=checked.1.2
  by_cases h0 : k=0
  · subst k
    intro k' t' hk' _ h
    have hk0 : k'=0:=by omega
    subst k'
    generalize he : ((rN levels (3*0+tm) i).2.2.map Prod.fst).toFinset=S at h
    have eqS : S={_}:=h (fun k _ S => k=0 -> S={_}) (fun _ _ => rfl)
      (fun _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn))
      (fun _ _ _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn)) rfl
    exact hT (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  apply n1s (raw:=vars dead.mask) htm1 samples _ hN hT _ _ _ (Or.inr (by simpa only [h0,ite_false] using checked.2))
  · intro v hv
    apply m48 _ _ _ _ _ (m57 dead) v
    exact (m58 _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩:=List.mem_filterMap.mp hp
    exact m51 dead cols h
  · intro tag xs hx
    have e : ((idx0 (3*k+tm) tag).bind (lS levels (3*(k-1))))=some xs:=by simpa using hx
    obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e
    have h0' : 3*(k-1)=3*(k-1)+0:=by omega
    rw [h0'] at h
    exact ls1s levels (k-1) 0 names (by simpa [←h0'] using prior0 (by omega)) h
  · intro tag xs hx
    have e : ((idx1 (3*k+tm) tag).bind (lS levels (3*(k-1)+1)))=some xs:=by simpa using hx
    obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e
    exact ls1s levels (k-1) 1 names (prior1 (by omega)) h
def bk1 (levels : Nat -> PT) (idx0 idx1 : Nat -> Nat -> Option (Nat × Nat)) (k tm start : Nat) : Nat -> Bool
  | 0 => true
  | n+1 => nv1 levels idx0 idx1 k tm start&&bk1 levels idx0 idx1 k tm (start+1) n
lemma bk1_at {levels idx0 idx1 k tm start n} (h : bk1 levels idx0 idx1 k tm start n=true)
    (i : Nat) (lo : start ≤ i) (hi : i < start+n) : nv1 levels idx0 idx1 k tm i=true:=by
  induction n generalizing start with
  | zero => omega
  | succ n ih =>
    simp only [bk1,Bool.and_eq_true] at h
    by_cases eq : i=start
    · exact eq ▸ h.1
    · exact ih h.2 (by omega) (by omega)
lemma m130 {levels idx0 idx1 k tm start a b}
    (ha : bk1 levels idx0 idx1 k tm start a=true)
    (hb : bk1 levels idx0 idx1 k tm (start+a) b=true) :
    bk1 levels idx0 idx1 k tm start (a+b)=true:=by
  induction a generalizing start with
  | zero => simpa [bk1] using hb
  | succ a ih =>
    simp only [bk1,Nat.succ_add,Bool.and_eq_true] at ha ⊢
    exact ⟨ha.1,ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm 1] using hb)⟩
lemma mkB1 {levels idx0 idx1 k tm start n}
    (h : ∀ i,start ≤ i -> i < start+n -> nv1 levels idx0 idx1 k tm i=true) :
    bk1 levels idx0 idx1 k tm start n=true:=by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [bk1,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i lo hi => h i (by omega) (by omega))⟩
def chk1 (c : NC1) (i j op : Nat) (ka kb : Bool) : Bool :=
  let a:=cw1 c i
  let b:=cw1 c j
  em1 c op a b (movedDecor op a b) ka kb
def cf1 (c : NC1) (d un ka kb : Bool) (op i j : Nat) : Bits :=
  let a:=cw1 c i
  let b:=cw1 c j
  restCov (getCov c.2.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2
def fb1 (c : NC1) (i j op : Nat) (ka kb : Bool) : Bool :=
  let (cap,tm,n,ws,_,pools,qpools,l0,l1):=c
  let a:=ws.getD i defaultDecor
  let b:=ws.getD j defaultDecor
  let un:=op==2
  let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
  let ct:=child1 tm cap len op
  let z1:=choiceVal (movedChoice op a b)
  if !properB z1||ws.any (fun v => v.1==z1) then true else
  if qpools.any (fun qp => fastCost qp (cap-1) a b op ka kb) then true else
    let rest:=(opKeep un ka kb a b ws).map Prod.fst
    let links:=if ct==0 then l0 else l1
    closeChild pools links (cap-1) rest (movedChoice op a b)
lemma fb1s {c i j op ka kb}
    (hlen : ¬(1+(c.2.2.1 - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1)) > c.1))
    (h : fb1 c i j op ka kb=true) :
    chk1 c i j op ka kb=true:=by
  rcases c with ⟨cap,tm,n,ws,cov,pools,qpools,l0,l1⟩
  dsimp only [chk1,em1,cw1]
  dsimp only at hlen
  rw [if_neg hlen]
  dsimp only [fb1] at h
  have hz1 : (movedDecor op (ws.getD i defaultDecor) (ws.getD j defaultDecor)).1 =
      choiceVal (movedChoice op (ws.getD i defaultDecor) (ws.getD j defaultDecor)) :=
    m54 op _ _
  set len:=1+(n - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1))
  set ct:=child1 tm cap len op
  set d:=ct==0
  by_cases hcomb : ((restCov (getCov cov d) (column d (ws.getD i defaultDecor).2) (column d (ws.getD j defaultDecor).2) (op==2) ka kb ||| column d (movedDecor op (ws.getD i defaultDecor) (ws.getD j defaultDecor)).2) != BitVec.allOnes 768)=true
  · simp only [hcomb,ite_true]
  · simp only [hcomb,ite_false,hz1]
    exact h
def mkBt1 (k n : Nat) (xs : List NC1) : Batch :=
  (k,n,units xs.length,
    (List.range n).map (fun i => packedSig (fun c => (cw1 c i).2) xs),
    packedCov (fun c => c.2.2.2.2.1.1) xs,
    packedCov (fun c => c.2.2.2.2.1.2) xs)
lemma lw1_at (k n : Nat) (xs : List NC1) {i : Nat} (h : i < n) :
    laneWire (mkBt1 k n xs) i=packedSig (fun c => (cw1 c i).2) xs:=by
  simp [laneWire,mkBt1,List.getD_eq_getElem?_getD,h]
def bmv1 (b : Batch) (tm : Nat) (xs : List NC1) (i j op : Nat) (ka kb : Bool) : Bool :=
  let (k,n,r,_,u,v):=b
  let un:=op==2
  let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
  if len > k then true else
    let d:=child1 tm k len op==0
    let a:=laneWire b i
    let b':=laneWire b j
    let z:=packedOp (r * (BitVec.allOnes 768).toNat) op a b'
    let cov:=if d then v else u
    let mask:=fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fb1 c i j op ka kb) mask xs
lemma bmv1a (k tm n : Nat) (xs : List NC1) {i j op : Nat} {ka kb}
    (hi : i < n) (hj : j < n) {q : Nat} (hq : q < xs.length)
    (budget : xs[q].1=k) (ht : xs[q].2.1=tm) (arity : xs[q].2.2.1=n)
    (pass : bmv1 (mkBt1 k n xs) tm xs i j op ka kb=true) :
    chk1 xs[q] i j op ka kb=true:=by
  let len:=1+(n - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1))
  let d:=child1 tm k len op==0
  have eval : chk1 xs[q] i j op ka kb =
      if len > k then true else if cf1 xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else fb1 xs[q] i j op ka kb:=by
    rcases hxq : xs[q] with ⟨cap,tmm,nn,ws,cov,pools,qpools,l0,l1⟩
    rw [hxq] at budget ht arity
    dsimp only at budget ht arity
    subst budget ht arity
    unfold chk1 em1 cf1 fb1 cw1
    dsimp only [len,d]
    have hz1 : (movedDecor op (ws.getD i defaultDecor) (ws.getD j defaultDecor)).1 =
        choiceVal (movedChoice op (ws.getD i defaultDecor) (ws.getD j defaultDecor)):=m54 op _ _
    rw [hz1]
  by_cases small : len > k
  · simp [eval,small]
  · let r:=units xs.length
    let a:=laneWire (mkBt1 k n xs) i
    let b:=laneWire (mkBt1 k n xs) j
    let cov:=if d then packedCov (fun c : NC1 => c.2.2.2.2.1.2) xs
               else packedCov (fun c : NC1 => c.2.2.2.2.1.1) xs
    change (if len > k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r * (BitVec.allOnes 768).toNat) op a b))) xs)=true at pass
    rw [if_neg small] at pass
    have chosen : cov=packedCov (fun c => getCov c.2.2.2.2.1 d) xs:=by
      dsimp only [cov]; cases d <;> rfl
    have ca : a=_:=lw1_at k n xs hi
    have cb : b=_:=lw1_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,m125,m12,m12,m12,chosen,m67,m82] at pass
    by_cases hit : cf1 xs[q] d (op==2) ka kb op i j=BitVec.allOnes 768
    · have hlenq : ¬(1+(xs[q].2.2.1 - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1)) > xs[q].1):=by
        rw [budget,arity]; exact small
      apply fb1s hlenq
      apply m126 _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
def bp1 (b : Batch) (tm : Nat) (xs : List NC1) (i j op : Nat) : Bool :=
  let f:=bmv1 b tm xs i j op
  f false false&&f true false&&f false true&&f true true
def br1 (b : Batch) (tm : Nat) (xs : List NC1) (i : Nat) (js : List Nat) : Bool :=
  let unOk:=if tm==0 then true else
    bmv1 b tm xs i i 2 false false&&bmv1 b tm xs i i 2 true true
  unOk&&js.all (fun j => bp1 b tm xs i j 0&&bp1 b tm xs i j 1)
def brs1 (b : Batch) (tm : Nat) (xs : List NC1) : List Nat -> Bool
  | [] => true
  | i :: js => br1 b tm xs i js&&brs1 b tm xs js
lemma brs1a (k tm n : Nat) (xs : List NC1) {q : Nat} (hq : q < xs.length)
    (budget : xs[q].1=k) (ht : xs[q].2.1=tm) (arity : xs[q].2.2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js,j < n) (allRows : brs1 (mkBt1 k n xs) tm xs js=true) :
    ta1 xs[q] (js.map (cw1 xs[q]))=true:=by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [brs1,Bool.and_eq_true,br1,List.all_eq_true] at allRows
    simp only [List.map_cons,ta1,tr1,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi:=bounds i List.mem_cons_self
    have check:=@bmv1a k tm n xs
    have hun : (if xs[q].2.1==0 then true else
        em1 xs[q] 2 (cw1 xs[q] i) (cw1 xs[q] i) (movedDecor 2 (cw1 xs[q] i) (cw1 xs[q] i)) false false &&
        em1 xs[q] 2 (cw1 xs[q] i) (cw1 xs[q] i) (movedDecor 2 (cw1 xs[q] i) (cw1 xs[q] i)) true true)=true:=by
      rw [ht]
      cases htm : (tm==0)
      · simp only [Bool.false_eq_true,ite_false,Bool.and_eq_true]
        have h1:=allRows.1.1
        simp only [htm,Bool.false_eq_true,ite_false,Bool.and_eq_true] at h1
        exact ⟨check hi hi hq budget ht arity h1.1,check hi hi hq budget ht arity h1.2⟩
      · simp
    refine ⟨⟨hun,?_⟩,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj':=bounds j (List.mem_cons_of_mem _ hj)
    have both:=allRows.1.2 j hj
    have opCheck (d : Bool) (pass : bp1 (mkBt1 k n xs) tm xs i j (if d then 1 else 0)=true) :
        tp1 xs[q] (cw1 xs[q] i) (cw1 xs[q] j) d=true:=by
      simp only [bp1,Bool.and_eq_true] at pass
      simp only [tp1,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget ht arity pass.1.1.1,check hi hj' hq budget ht arity pass.1.1.2⟩,
        check hi hj' hq budget ht arity pass.1.2⟩,check hi hj' hq budget ht arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩
def rb1 (k tm n : Nat) (xs : List NC1) : Bool :=
  brs1 (mkBt1 k n xs) tm xs (List.range n)
lemma rb1a {k tm n} {xs : List NC1} {q} (hq : q < xs.length)
    (hb : xs[q].1=k) (ht : xs[q].2.1=tm) (ha : xs[q].2.2.1=n) (hn : xs[q].2.2.2.1.length=n)
    (pass : rb1 k tm n xs=true) : ta1 xs[q] xs[q].2.2.2.1=true:=by
  have all:=brs1a k tm n xs hq hb ht ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (cw1 xs[q])=xs[q].2.2.2.1:=by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [cw1,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all
def ctxs1 (levels : Nat -> PT) (idx0 idx1 : Nat -> Nat -> Option (Nat × Nat)) (k tm start n : Nat) : List NC1 :=
  ((List.range n).map (start+·)).map (ctx1 levels idx0 idx1 k tm)
def cc1 (levels : Nat -> PT) (idx0 idx1 : Nat -> Nat -> Option (Nat × Nat)) (k tm start n ar : Nat) : Bool :=
  let xs:=ctxs1 levels idx0 idx1 k tm start n
  xs.all (fun c => c.2.2.1==ar&&pre1 (targetOf dead) c) &&
  let b:=mkBt1 k ar xs
  (List.range ar).all (fun i => br1 b tm xs i (List.range' (i+1) (ar - (i+1))))
lemma cb1 {levels idx0 idx1 k tm start n ar}
    (h : cc1 levels idx0 idx1 k tm start n ar=true) :
    bk1 levels idx0 idx1 k tm start n=true:=by
  unfold cc1 at h
  rw [Bool.and_eq_true] at h
  let xs:=ctxs1 levels idx0 idx1 k tm start n
  have hrun : rb1 k tm ar xs=true:=by
    have go (lo num : Nat) (eq : lo+num=ar) :
        brs1 (mkBt1 k ar xs) tm xs (List.range' lo num)=true:=by
      induction num generalizing lo with
      | zero => rfl
      | succ num ih =>
        simp only [List.range'_succ,brs1,Bool.and_eq_true]
        refine ⟨?_,ih (lo+1) (by omega)⟩
        have ok:=List.all_eq_true.mp h.2 lo (List.mem_range.mpr (by omega))
        simpa only [show ar - (lo+1)=num by omega] using ok
    unfold rb1; rw [List.range_eq_range']; exact go 0 ar (by omega)
  apply mkB1
  intro i lo hi
  have hm : ctx1 levels idx0 idx1 k tm i ∈ xs:=by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i - start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩:=List.getElem_of_mem hm
  have one:=List.all_eq_true.mp h.1 _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k:=by rw [e]; rfl
  have ht : xs[q].2.1=tm:=by rw [e]; rfl
  have ha : xs[q].2.2.1=ar:=e ▸ one.1
  have hn : xs[q].2.2.2.1.length=ar:=by rw [e]; exact one.1
  simp only [nv1,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ rb1a hq hb ht ha hn hrun
def cs1 (levels : Nat -> PT) (idx0 idx1 : Nat -> Nat -> Option (Nat × Nat)) (k tm start n ar : Nat) : Nat -> Prop
  | 0 => cc1 levels idx0 idx1 k tm start n ar=true
  | d+1 => cs1 levels idx0 idx1 k tm start (n / 2) ar d /\ cs1 levels idx0 idx1 k tm (start+n / 2) (n - n / 2) ar d
lemma k1 {levels idx0 idx1 k tm start n ar}
    (h : cc1 levels idx0 idx1 k tm start n ar=true) :
    cs1 levels idx0 idx1 k tm start n ar 0:=h
lemma csb1 {levels idx0 idx1 k tm start n ar d}
    (h : cs1 levels idx0 idx1 k tm start n ar d) :
    bk1 levels idx0 idx1 k tm start n=true:=by
  induction d generalizing start n with
  | zero => exact cb1 h
  | succ d ih =>
    have v:=m130 (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
lemma f1_all (levels : Nat -> PT) (idx0 idx1 : Nat -> Nat -> Option (Nat × Nat)) (top : Nat)
    (prior : Nat -> Nat)
    (lo : ∀ m,Lower (vars m) (graphGoal m) (prior m))
    (valid : graphValid dead prior=true)
    (tabs : ∀ k ≤ top,∀ tm ≤ 1,bk1 levels idx0 idx1 k tm 0 (levels (3*k+tm)).1=true) :
    ∀ k ≤ top,∀ tm ≤ 1,∀ i < (levels (3*k+tm)).1,I1 (targetOf dead) k tm (sS levels (3*k+tm) i).toFinset:=by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at valid
  have pairs:=m66 valid.1.1.1 valid.1.1.2
  have cols : ∀ ci ∈ dead.cols.values,Slice (vars dead.mask) (targetOf dead) (subcube ci.1 ci.2.1) ci.2.2.2.2 :=
    fun ci hc => m50 ci prior lo (valid.1.2 ci hc)
  have names:=valid.2
  intro k
  induction k with
  | zero =>
    intro hk tm htm i hi
    have hb:=tabs 0 hk tm htm
    exact nv1s levels idx0 idx1 0 tm i htm pairs cols names
      (fun h => False.elim (Nat.lt_irrefl 0 h))
      (fun h => False.elim (Nat.lt_irrefl 0 h))
      (bk1_at hb i (Nat.zero_le i) (by simpa using hi))
  | succ k ih =>
    intro hk tm htm i hi
    have hb:=tabs (k+1) hk tm htm
    exact nv1s levels idx0 idx1 (k+1) tm i htm pairs cols names
      (fun _ j hj => ih (by omega) 0 (by decide) j hj)
      (fun _ j hj => ih (by omega) 1 (by decide) j hj)
      (bk1_at hb i (Nat.zero_le i) (by simpa using hi))
def pL24F (i : Nat) : Nat:=0x3b649c6549302e95348200
def pL24 : PT:=(1,7,7,3,pL24F)
def pL27F (i : Nat) : Nat:=0xb003405c30005801a27a2bc60400005ba6c00d180009948568a1aca78869645f332e2924120083fe6e350daa6290401a7f0ca605514c120803ef8262902a4c0a610061bf6e9c62e95348200db6ce32605d2a690401f749524c0ba54d20803ee92a4982a6c0a410065db32d5254d8244200fba4a9a40c1aa488401f7615148183549108038f6b68c0aa3552610061ef715b4486aa4c200
def pL27 : PT:=(12,6,7,8,pL27F)
def pH0_27F (i : Nat) : Nat:=0x100b80
def pH0_27 (h : Nat) : Option (Nat × Nat):=lookupWord 1 3 2 9 1 4 pH0_27F h
def pL28F (i : Nat) : Nat:=0x1e000f8003e000f8003e000f800204af000bc0010003400a0161f8003e000f970675e554c4333aaa81209005fb0758c24c5214c200eea45b966a9aa4904015f48db5cd535492080355e350e3142c0a41006adc6a1c52858148200d5e8d438650b0290401eb61a854981545208035bc38ed294290a41006b78329875c52148200b770eb19498a4290401e3d1a8605314c120803d6c304a9302a8a21007af0609326053144200
def pL28 : PT:=(13,6,7,8,pL28F)
def pL30F (i : Nat) : Nat:=0x2c01a05c302e00d1030c94b0c0c00416a5158d8800205a2c02098760108ca7008402da6c2745718170004160446e058028402ed3600d1812000c0c8c005d1606401c8018002200c001100209b88708c8af8018009c02be10000817ea291b01490c0031c00020d4830332908018009a28c0200ac4010002232908018028800c014460c1329080200088010004d14661c1024f4503702a019d0e007001e02e0050067a281b81578c007800e837017002818fd17cd80a806400403341b80b801400ae04007c004045036024029f18018d0e007006e02e005812015f8c00c6870038037017002405f01002800780b800c014e0c00fc05c005410f45b45b29b06f36e0ee00400801779b7075075837a2f002005fcdbd1783b800a0bfe6c007c0dc0058dc8bf8968618448338167f97dc7bf7ae7a977474b7226ed6d06b365a65564463f5e65e15b85a757e5615445335164f94e84d74ba4914804033863092d424b1da18d14c0e7082041000c7fda86d53148200f7f1815453048200e7eda36095244200c7fda86d53244200c7fdb86953244200b7f9c854d2044200f7798554d2044200f7d98354d2044200f7e920549814c200c7fdba2e95348200b6fdc62e95348200f7d9302e95348200a7fcca6c55348200f7d93054d8148200c7fd85aeda344200c7fd52aeda344200c7fd83aeda244200c7fd53aeda24420097fccb54d8244200f3dd8354d8244200b7edc254d8244200f76d5254d8244200a7fdca60d5244200f7e92060d5244200c7fdba6153244200e7f581546aa4c200a7fdc5486aa4c200c7fdb560eaa48200a7fdc854eaa48200e7dd8354eaa48200c7fd836c6aa48200c7fd536c6aa48200e3fd8360aaa44200e7ed8254aaa44200a7fdc84caaa44200a7fdc54caaa44200e7ed824caaa4420087fecc6e9834420087fecc6e9824420087fecc6e9324420087fdc1aeda84820087fdc8aeda34420087fdc5aeda344200c7bdc4aeda34420087fdc2aeda344200c7bdb4606aa4c200c7bdb4546aa4c200c7bdb4486aa4c200c7f5b1606aa48200
def pL30 : PT:=(49,5,7,12,pL30F)
def pH0_30F (i : Nat) : Nat:=0x4b00859028063024013889b9100400883683806584ba3e81f24f841850064b8e08546118000
def pH0_30 (h : Nat) : Option (Nat × Nat):=lookupWord 7 22 5 12 4 4 pH0_30F h
def pL31F (i : Nat) : Nat:=(if i<3 then (if i<1 then 0xafe9c220da244200aff1c120da2442008ff9cb14da244200aff1c114da244200c7f8c96e98244200cef8c66e982442008ff8cb69d82442008ff8cb68d82442008ff9cb69482442008ff9cb68c8244200c7f8c96e95244200cdf8c76e952442008ff9cb6a15244200cdf9ba2dd52442008ff9cb6a05244200cbf9b86a05244200cef9a86d85244200cfb9a86d05244200cfb9a66d052442008ff9cb68c5244200cef9b668c5244200cfd9b368c5244200cff1a86c45244200cff1a36c452442008ff9cb6a132442008ff9cb6953244200cbf9ca6e032442008ff9cb6a03244200cbf9b86a03244200cdf9a86dc3244200cef9a86d83244200cbf9b86983244200cdf9b76983244200cf79ca6d43244200cf79a86d43244200cf79a66d43244200df71c16d432442008ff9cb6943244200cbf9b86943244200cdf9b76943244200cef9b66943244200cf79b56943244200cfb9a86d03244200cfb9a66d03244200cfb9a56d03244200cff1a86c43244200cff1a66c43244200cff1a56c4324420097f8c96e1714420097f9c22e5514420097f8c96e1514420097f8c96dd5144200c7f8b968d5144200b7f1c22e55144200b7f0c96e15144200cff0cb6a15144200eef0c66a15144200ef70c56a15144200b7f0c96dd5144200b7f0c96d95144200f770b95955144200ef71a85955144200ef71a75955144200fe71865955144200fe71765955144200b7f0c96cd51442009ff1cb20d5144200aff1ca20d5144200bdf1c720d5144200bef1c620d5144200bf71c520d5144200bfb1c420d5144200bfe1c220d5144200b7f0c96c95144200aff1ca2095144200bf71c52095144200fe71655895144200f770b95495144200ef71a85495144200fd70c75495144200bf71c65495144200ff61825495144200ff617254951442009ff1cb0c95144200aff1ca0c95144200bbf1c80c95144200bdf1c70c95144200bef1c60c95144200bf71c50c95144200bfb1c40c9514420097f8c96e131442008ff9cb6a1314420097f8c96dd314420097f8c96d531442008ff9cb6953144200d7f0b9545314420097f8c96e121442008ff9cb6a1214420097f8c96d521442008ff9cb69521442008ff9cb68d214420087fdcb6953244200e7e9a35492044200f769535492044200f7e1c25452044200ebe9825498144200ebe9824c98144200ebf1826055144200ef715260551442008ff8cb6093144200cbf9b86093144200efc9824c93144200cff1b56053144200ebf1826053144200efd13260531442008ff9cb61521442008ff9cb60d21442008ff9cb54d2144200cff1b84c521442008ef9c62e953482008ef9c62e951482008df9c72e931482008ef9c62e93148200bde1c72852148200bfc1c32852148200afe0ca5c52148200f749535493048200f761525452044200 else (if i<2 then 0xcfd9b368c5148200cfe9a86c85148200adf9c72e93148200aef9c62e931482008ff9c82e931482008ff9c52e931482008ff8cb6a131482008ff8cb6993148200cfd8cb68d3148200efd0c168d3148200cfe8ba5493148200df69b55493148200cff0ba6053148200ebf1a86053148200efd1a360531482008ff9cb6a03148200cbf9b86a03148200cfe9a86c831482009fe9cb5483148200df69b5548314820097f8c96e1214820097f8c96d52148200efd1a34c52148200ffc1324c52148200b7e8c96e12148200b7e8c96a12148200b7e8c96d52148200d7e8c96d52148200dde8c76d521482009fe9cb2152148200afe9ca2152148200bde9c72152148200bee9c62152148200bfa9c42152148200bfc9c32152148200bfe1c121521482009fe9cb20d2148200afe9ca20d2148200bde9c720d2148200bee9c620d2148200bf69c520d2148200bfa9c420d2148200bfe1c120d21482009fe9cb14d2148200bfe1c114d2148200efe1a52852148200bfe1c32852148200efe1a32852148200fde1a75c52148200fde1875c52148200efe1a65c52148200fde1765c52148200dfe1b55c521482009fe9cb5452148200efe0ca4c52148200bfe1c74c52148200efe1a64c52148200ffc1a34c52148200ffc1634c5214820087fdc52e93148200e3f9a86053048200a7f8ca5453048200b7d9c54c53048200f7d1814c53048200a7f8c96dda844200af78c56dda844200cef9b72d9a844200a7f8c96d5a844200cef8b66d5a844200cf79b52d5a844200a7f8c96cda844200cef8b66cda844200cef8b62cda844200cfd9b32cda844200a7f8c96c9a844200cef8b66c9a844200cfe9b22c9a844200a7f8c96d9a544200a7f8c96cda544200c7f8b96cda544200a7f8c96c9a544200cfd9ca6cc8544200cfe9ca6c88544200a7f8c96e1a344200cbf9b82e1a344200a7f8c96dda344200afe8c26dda3442008ff8cb61da344200a7f8c96d5a344200cf79b52d5a3442008ff9cb215a344200adf9c7215a344200aef9c6215a344200afd9c3215a344200afe9c2215a344200aff1c1215a344200cfe9b22c9a344200c7f8c96e98344200cef8c66e98344200cef9a76d88344200cf79ca6d48344200cf79a76d48344200df71c16d48344200cfb9a76d08344200cfe9ca6c88344200cfe9a76c88344200cff1a76c483442008ff8cb6a163442008ff8cb69d6344200c7f8c96e953442008ff8cb6a153442008ff8cb69d53442008ff9cb6a05344200cff1a86c45344200a7f8c96e1a244200a7f8c96d5a2442008ff9cb215a244200adf9c7215a244200aef9c6215a244200afb9c4215a244200afd9c3215a244200afe9c2215a244200aff1c1215a2442008ff9cb20da244200adf9c720da244200aef9c620da244200af79c520da244200afb9c420da244200 else 0xafe9c2215a348200aff1c1215a348200cff1b12c5a348200cdf9a86dca348200cef9a86d8a348200cdf9b7698a348200cdf9b7694a348200cef9b6694a3482008ff9c52e98348200cef9a76d88348200cf79ca6d48348200cf79a76d48348200df69c26d48348200cfb9a76d08348200cfe9a76c88348200cff1ca6c48348200cff1a76c48348200dfe1c26c483482008ff9c82e973482008ff9c52e97348200cdf8ba61d73482008ff9c82e963482008ff9c52e963482008ff8cb6a16348200bef0c16996348200aef9c62e953482008ff9c82e953482008ff8cb699534820097f9c12e5824820097f8c96e1524820097f8c96d95248200b7e8c96e15248200b7e8c96a15248200dde9b82dd5248200b7e8c96d95248200bfe0c16995248200bf69c32955248200fd69875d55248200b7e8c96cd5248200dde8b72cd5248200bde9c728d5248200bee9c628d5248200bf69c528d52482009fe9cb20d5248200afe9ca20d5248200bde9c720d5248200bee9c620d5248200bf69c520d5248200bfa9c420d5248200bfe1c120d52482009fe8cb5cd5248200afe8ca54d5248200ef68ca54d5248200bf69c754d5248200fd68b754d5248200ef69a754d5248200ff48b354d5248200ff498354d5248200ff497354d5248200b7e8c96c55248200dde8b76c552482008ff9cb6a1324820097f8c96d9324820097f8c96d532482008ff9ca6e0a148200cdf9a86dca148200cef9a86d8a148200cf79a86d4a148200df69c26d4a148200cbf9b8694a148200cdf9b7694a148200cef9b6694a148200cfb9a86d0a148200cfb9a56d0a148200cfd9a86cca148200cfd9a56cca148200cbf9b868ca148200cdf9b768ca148200cef9b668ca148200cf79b568ca148200dbe9b8548a148200dde9b7548a148200dee9b6548a148200df69b5548a148200dfa9b4548a148200dfc9b3548a148200efe152684a1482008ff9c52e981482008ff9c32e98148200cbf8cb6a18148200e3f8c96a18148200ebf0c16a18148200cef9ba2d98148200eaf9a82d98148200b3f8c96098148200ebe9a85498148200cff1ba2858148200ebf1a82858148200bef1c62858148200bf71c52858148200bfd1c32858148200cfb9a76d081482008ff9cb68c8148200cdf9b768c8148200cfd9b368c8148200cfe9a36c881482009fe9cb5488148200cfe9ba5488148200dde9b75488148200df69b55488148200dfa9b454881482008ff9c82e971482008ff9c52e971482008ff9c32e97148200cdf8ba61d7148200ebf1a860561482008ff9c82e951482008ff9c32e95148200fd68c75495148200df69b75495148200ef69a75495148200ff60c15495148200cff0ba6055148200ebf1a86055148200ff61526055148200ff61525c551482008ff9cb6a051482008ff9cb68c5148200)) else (if i<5 then (if i<4 then 0xfa798761565582009ef8cb59583582009ef8cb61d63582009ef8cb6156358200cef8ba6d95358200baf8c86d953582008ff8cb69d82582009ef8cb59582582009ef8cb58d8258200fad98358d8258200cdf9ba2dd5258200cbf9ca6e03258200cf79ca6d43258200de79c66d43258200daf9b85943258200dcf9b75943258200de79b55943258200deb9656d03258200cff1ca6c43258200def1c66c43258200def1656c43258200beb9c41496158200baf9c80c96158200bcf9c70c96158200be79c50c96158200beb9c40c96158200bef1c10c96158200faf1826056158200fe71655c551582008ff8cb69d3158200fed1634c5215820097f9c82e5634c200d7d9532e5634c20097f9c22e5634c20097f8c96dd634c2008ff8cb699824c200cfd9ba2cd824c200bf99c42cd824c200bfd1c12cd824c20097f8c96d9324c200cef9ba2d9814c200d7d9c32e5514c20097f9c22e5514c20097f8c96d9514c200d7d8b96cd514c20097f9c82e5314c20097f8c96e1314c20097f8c96dd314c20097f8c96d5314c200b7d9c82e5314c200b7d8c96e1314c200bdd9c72e1314c200b7d8c96dd314c200bfc8c26dd314c200b7d8c96d5314c200d7d8b96d5314c200d7d8c96d5314c200b7d8c9695314c200bbd9c82c9314c200bdd9c72c9314c200bed9c62c9314c200bf59c52c9314c2009fd8cb609314c200afd9ca209314c200bfd1c1209314c2009fd9cb149314c200afd9ca149314c200bed9c6149314c200bfd1c1149314c200f7d0b9605314c200fbd0b8605314c200fed0c6605314c200fbd186605314c200dfd1b5605314c200fbd182605314c2009fd9cb545314c200b7d8c9545314c20097f8c96d5214c200dfd1b84c5214c200efd1a64c5214c200ffc0c24c5214c200ffc1624c5214c200cbf9ca6e0214c200cf79ca6d4214c200df59c36d4214c2009fd9cb54c214c200cfd9ba54c214c200dbd9b854c214c200ddd9b754c214c200ded9b654c214c200df59b554c214c200aff0c16d9a848200aef9c62cda848200cfd9b32cda848200a7f8c96c5a848200adf9c72c5a848200afb9c42c5a848200cff1b12c5a84820097f8c96e987482008ff9c52e987482008ff9c32e98748200cff1a82c5a648200cff1a72c5a6482008ff8cb61da648200cff0b32c5a648200aff0c1699a548200cef9a86d8a548200cfb9a86d0a548200cfb9a66d0a5482008ff9c32e98548200cfd9ca6cc8548200cff1ca6c48548200dfe1c26c485482008ff9c82e965482008ff9c32e96548200bef0c16996548200aff0c1699a348200aef9c6295a348200cbf9b82e1a3482008ff8cb61da348200a7f8c96d9a348200aff0c16d9a348200a7f8c96d5a348200cf79b52d5a3482008ff9cb215a348200adf9c7215a348200aef9c6215a348200afd9c3215a348200 else 0x1e000f0007800219213211dc004086e0017000437f8005c001e00086285b7000c2db800418bc00208ee001700043d403380061b2011c0030f500ce001804004e030dc700140270186e3800801178bc00342202f010031008a06014013f5ff45f36f18f026816804017805005c027affa2f9b78c7872edacb66ed7eb5b6d50b52ed3ab4a6d18b41ecf6b366cc8b2deca6b256c84b1cec62b146c40b0bec1eb036bfcafaebdaaf26bb8ae6eb8aad86b50acfeb2eac76b0cabeeadeab36abcaa7ea8ea9f6a60a93ea3ea8b6a1ca7fe9eea7769cca6ee9aaa666988a5de966a556944a4ce922a3e68dca32e8baa27688ca1ee86aa196854a10e832a0868109ffe7e29f167b49ebe79e9e067649d4e7429c967149c0e6f29b866c49ace6a29a4668099be65e9936630987e60297c65e0970e5a69656584959e55694e6528945e50693d64e4931e4aa9296494920e466915645090ce4168fe63d08e9e38a8e163748d8e3468ca630c8bee2ea8b362bc8aae29a89f626c896e24a88e621c882e1fa87a61cc86ee1aa866617c85ae15a8526138849e11684160f483be0de83360b0824e08281c6060810e03280860107ffdfee7f45fc07ebdf927dd5f4c7cedf2a7c35efc7badece7af5eac7a6de8a79e5e68795de3a7875e0077bddd27705da4761dd6a7535d30747dd0e73f5cec736dcca7315cb4728dc927205c70717dc4270f5c2c706dc0a6fb5bdc6f2dbba6e75b806d8db466cd5b186c1daf66b95ad46adda9a6a25a78699da566915a34685da1267a59cc66ed99e6635970651d92a646590863dd8e663258a0620d87e6185850609d8165fe57e85f2d7ae5e7578c5ded76a5d357245c4d7025bc56e05b3d6be5a8569059fd66e597564c58ed61e58355fc57ad5da57255b8569d58a55e556854fd52e54154f4538d4d253354b0521d45e51053d04e3d32a4ba52a84a5d27a497524c48ed236489520847dd1f247851d0472d1ba46a518c45ed15e453513c44dd12644250f8436d0d642e509c41fd05640e5010402cffa3f74fcc3eecfaa3e64f883ddcf663d24f2c3c6cefe3bb4edc3afce963a14e74398ce523904e30387ce023794dd4370cdb23684d9035ccd563514d28345cd0633d4ce4334ccb63294c9431acc5a30f4c20300cbe62f54bb82e6cb7e2d84b442c6caf22b54ab82a3ca722954a4428cca2228149f4278c9d227049b0267c9822594954250c91a23f48e0233c8be22b489c21fc86e2174840208c81e20347fc1fac7da1ef47ac1e6c78a1de475c1d2c73a1ca47181c1c6f61b646c81aac69a19f466c196c64a18e4628182c5fa17a45d8171c5b6169457c15ac55a14f452c146c4fe13b44d012cc47210643e40eec3aa0e643880ddc3420c943140bdc2e60b542ac0a3c2720954244086c1f20724188054c12a02240009ef8cb61d6558200) else (if i<6 then 0x7931c0020700078002019c00204ae0015e2f000b8003c0016c5e001700078003c00108ee001700078003c001e000862f000b8003c001e0008477000b8003c001e000804700080142002100108038401c3c0010070f00041c0010070c437000812b8005c001e000f00040438005c001e000f00078003c001086e00170007800210dc002886e00105486cf000f8003c0010d9e001003878002131c0020010800878003c001e000f0007800378bc00204ae0015e2f000b8002f8bc002e000be2f000ae638005731c002b98e0015cc7000b8003c001e000f00078003c0010700078003c0010050f00078002905c0020700056d83c0011b8e001700078003c001098e00154c7000820b8004105c002e0008027000b8003c001e000f0004317800410dc002e000f00078003c001e000f0004367800400f5082e001816f000b80021b3c002e00084c7000820aa638006105c002e000f00078003c0010c9e00105c8417000f86b800400d9e001700043d420b8007c001082e0017000420b8004105c002e000f000400420021082e0010040097000c014200a10050803878003c001082e001700078003c001e000f00078002105c002e000f00078003c001e000f00078002f8bc002e000f00040201238007c0010cb082e001f00078003c0010004700082082e78006010025c0030b9e00102281b00c00700300103580001527c63cd80bb43ac08a0c8432011653e31800001604802e729f1800db022baff9b006f0378c140042185c0020c2e00100087800200010dcc7000b800200010f0004000210010dcc000880042d31c002e0008008400021e1ae0017000586800440098e00164c7000b2638004009931c003c98e00100864c7000c00021e1ae001700078003c001e000f00078003c00108ee00105b7000b8002c340022e000f00042db800411cd6dc0030010800878003c001e000f00078002009c002008e001700078003c001e000f00040138004011c002e000804700080043c001e000f00078002131c0020010f00043142db8007c0010b6e001002700082f38004d6dc002e00084c7000aa638004009c002086e001043700082d8263800618a131c0036b6e00105b70008012adb8006d6dc0020bce001700078003c0016b6e001700078003c001e000f00078002009c0026b6e00170007800210cd6dc003086e0010437000800420141001080086a600044014100308617000830b800400030801840b03c0010a9e0017000780020061e0008087000b8003c001e000f000780020061008e00170006013800401410a9e001700078003c001e000f00040238005c001e000f00078003c001001085b04c7000c00420021098e00100184004216dc0020010862f000826380040be08a06c0300025906006800f4570ee02f183b877a2f0178c100b40b080c7c0 else 0x7000780023bfc002e0008eff00081c001e000f00078003c001682e001700078003c001e000f00078003c001e000f00078003c001e000f00078003c001e000f00042e78005c00103a0b9e0018318403c202610010f0005a602c35c002e00080085a63800400210130f4c0008803420c61001080087a60004401a10050f00040143c001005080684034200a1e000f00078003c00102308ee0018417000b8003c001082e00170007800201a10700078003c001e000f00040143d30002208ee001700041c001698e00134c7000b8003c001004e001700078003c001e000ddb7000b8002f3010010f00078002f6c10010862f000b8002b6dc002e000f00042df8005b8bc002e000f00040338005c001698e001700078003c001e000f00076638005b31c0020700040043c35c0020010802638005931c002c98e00100464c7000c0432638)))
def pL31 : PT:=(513,5,7,14,pL31F)
def pH0_31F (i : Nat) : Nat:=0x80200cf05403509506f0a00c00
def pH0_31 (h : Nat) : Option (Nat × Nat):=lookupWord 2 8 4 12 4 4 pH0_31F h
def pH1_31F (i : Nat) : Nat:=0x806a0001ba0b212614a2401ba1001a01aa03c1861680520801b80fc0cec401a011400
def pH1_31 (h : Nat) : Option (Nat × Nat):=lookupWord 5 21 5 12 4 4 pH1_31F h
def pL33F (i : Nat) : Nat:=(if i<1 then 0xbb4762be1be9b00d8047408cd98c0c060010083408cd848100386168a405a004020d020070c230480040231820660df01068101800a01644080bfa2b0e05802cc090025456304180502b3958409012a29102017120400e049a290890010083224812020c0080880101880220001380c0aca09211021e300100a706a05800088015d5fe8bcd815f29e3004f8706700e014308016808e8bcd815f29e3004f8706700e014308016827047c628701000e01409001482404602a0201000604400a012023e300100570602000c0880150600bfd15a2c456530a58342280cc0801736c1d801e0b417029e6cc1a1140660400ba2e0058096bf17d94c228530438c41860c01b9b302005d1707600885f68acd994b1861c02003805002a01c09d8c00800e017001c0402be3000009805300f0100043135f0bfd1622b29853c618700ee6d81806b02805802603c04001062d7c37c5fe6d0d994829e30c3807745c0c03581402c0140101802fb4588bcd994c296310618740e01b801c0200881601dcd806e06c0080c417fa2b4588aca614f1801dcd98340480d8090160080610bfd1594c29e30c620c30e81d01003736c05801e0bdafc5fe6ccda1b029e30c620c30e81d01003745c058022049afc5fe6ccda1b32985203ba2c0400dc6301600782901c1beaff45e6c0bb8c016c0dc0b00302f82405206433745e6dc6287706c05801817f9480ce8bcdb8c70ea0d80b002814f45e6c1bf8c70e01981b81600505fe8bcdb94f1861c03303702c00a0bfca404745e6dc63876066058015ca783010e8bcdb07702c0089c74cf25eb2c495fca664d12168e2467a2f115d896441a1c10af844c162022fbf7c73dcde84f1c77b3b15d12e0b6bbb38d8f6c1e5d5ac055069c34a823f916e7e13801984c0854f2528f946762b211486d82860d002e8003bfedd30298401dff689814c200effaa4c0a610077fdba54d20803bfe5d2a690401dff6c55348200effaa6d0a410077fda360520803bfea9b0290401dff6e98344200effb06d12210077fdba60910803bfedab0488401dff6958244200effb66c12210077fda360910803bfea9b0488401dff6e95244200effb66a92210077fda354910803bfec1aa488401dff6e93244200effb6a992210077fda54c910803bfec2a6488401dff60eaa48200effaa7552410057febb68530802bff5db50904019ffaeda848200affd76d1a410057febb68d108033ff5db46884019ff606aa4c200cffaa3552610067fd21aa9308033fed4554904019ff68eaa48200eff261552410067fd83aa9208033fea9d54904019ff606aa48200cffa63552410067fd83aa9108033fec1554884019ff54aaa44200cffa65552210047febb6a1208023ff5db46884011ffaeda2442008ffb71552410047fdb3aa9208023fed8d54904011ef6d2aa4c200 else 0x111736e30034029413810a6dc608106300a72b088a11345a6d860cd158c0130284000d058050603004013056404e02002d36631408069c)
def pL33 : PT:=(54,4,7,13,pL33F)
def pH0_33F (i : Nat) : Nat:=0xc7c1f209f4e800c5c0c00c4031324003141a241b00c509c00c4031c2a003100c4031405dd15301c031b01108f00c4031504d023375f81d900403100c7c435449c996014031009a09800c402500c4031f00803100c740000c744100c681200c7c56c063d68e05a006304688e9040031707003100c403100c4031756111300c4031e00e518715c03100c48da67a200ec05080d012042100a2a99248c03100c4031c5200310078031e49492000c581a5023c2200c4c2417640317168031103ec19708201500c5182c65b08d0014085020000504080020a14000000c0800004006
def pH0_33 (h : Nat) : Option (Nat × Nat):=lookupWord 24 116 7 14 6 4 pH0_33F h
def pL34F (i : Nat) : Nat:=(if i<8 then (if i<4 then (if i<2 then (if i<1 then 0x8530802f7cdb042984017de6d4214c200bfb36610a610067f8b96a1208035fcd4150904013fe2e98748200bfe162d3241006ff0b1699208027fcdd30c904013fe6e97648200bdf36c52a41006f79a529520802fdcda14a904013fe2e985482009ff37442a41005df9b721520802f7cdb10a904017ee6d08548200bfb36642a41005fe9b221520802ff8d890a904013fe2e96548200ddf34cb2a41005df9b728d20802f7cdb14690401bf668ca3482009ff374c1a41004ff8ba60d208027fcdd1069040177e6dc8348200bdf36c41a41005f79b520d20802fdcda106904017fa6c88348200bfe36241a41004ff9ba5cd208027fc5d2e690401b7e69d73482009ff374b1a41004ff8ba58d2080377cd32c6904013fe2e953482009ff37429a41005fe9b214d20802bfc5cb0490401f7a2dd5248200dfd34ea9241007f68a554920803fb4baaa490401fda54d5248200b7f37050a41005df9b728520802f7cdb142904017de6d4a148200bf736850a41005fd9b3285208037f8d0942904013fe2e98148200d7f350c0a41004ff9ba20520802efcdb902904017ee6d08148200bfd36440a41004ff8ba5c5208036fcd3ae290401bbe69961482009ff174a8a41007f6952545208027fcdd0a2904017fa6c851482009ff17498a41006fd9a34c5208027fcdd062904017fa6c83148200dfd34c90a41005fe9b548520803ff050a4290401ff85c52148200ffc26290a410047fcba54d208023fe5d262904019fe6a13048200efb2a6982410077e9524c120803bec98a6090401bbe2d9a8442009ff374c3a21004ff9ba619108027fcdd2ec884019fe2e5a5442009ff37442a21005df9b721510802f7cdb10a884017ee6d08544200bfb36642a21005fe9b221510802ff8d890a884013fe6e96544200cff172d1a21004ff9ba60d108027fcdd1068840177e6dc8344200bdf36c41a21005f79b520d10802fdcda106884017fa6c88344200bfe36241a21004ff9ba5cd108027fcdd2c6884013fe6e953442009ff37429a21005ff1b114d108027fcdd304884013fe6e882442009ff374b9221004ff9ba589108027fcdd2a4884013fe6e85244200bdf36c29221005fb9b414910802ff8d88a4884013fe6e932442009ff37419221005bf9b80c910802efcdb864884017be6d83244200bef36a19221005fb9b40c910802ff8d8864884015fe2e55144200efe172a8a21006ff1a8545108037f8d3aa288401fdc5955144200fee2a4a8a210057f8b94c5108023fedd306884011ff6e982442008ffb74992210067f9a348110803bf4a924088401dfc54520442009ff37099221006fe9824c9108035fcc130288401bfc60551442009ff37098a21004ff9b54c5108037ec9926288401bfc60531442009ff37090a21004ff9b5485108027fcd9a4288401bfc4c52144200 else 0x1bfe6897144200fbf2e4b8a21005ff9b8545108037fcd42a2884017fe6dd5144200dff34ea8a21006ff9a3545108037fcd12a288401fde5495144200ffe302a8a21007ff17154510803ff8dc2a288401ffc6a15144200ffe36ea8a21007ff1a754510803ff8c3aa288401ffc6d95144200ffe30ca8a21007ff17654510803ff8c2aa288401ffc5955144200ffe366a8a21007ff1a354510803ff8c1aa288401ffc20d5144200ffe2e6a8a21007ff16354510803ff8a9aa288401ffc6c95144200ffe344a8a21007ff18254510803ff8412a288401ffc5c95144200ffe2c4a8a21007ff15254510803ff8992a288401ffc0c95144200bff37098a21006ff9a84c510802ffcdba6288401bfe69d3144200bff36a98a21006ff9a54c5108037fcd126288401ff64c93144200ffe30298a21007ff1514c510802ffcdc24288401bfe6a12144200bff36e90a21006ff9a748510802ffcdaa4288401bfe6952144200bff36690a21006ff9a348510803ff8b8a4288401ffc5452144200ffe26290a210067fda868d108033fedc346884019ff6d5a344200cffb64d1a210057fdba60d108033fed4344884019ff695a244200cffb46d12210067fdb8689108033fed9b44884019ff6e98244200affb74c12210067fda5609108033fed1b04884019ff6e95244200affb74a92210067fda354910803bf6c12a4884015ff6e93244200affb6a992210067fda54c910803bfcdc24088401dfe6a12044200eff36a902210077f9a548110803bfcc2a4088401dfe6cd2044200eff346902210077f98348110803bfca9a4088401bfe6cd8244200dff362c1221006ff9b84c9108037fcdaa6488401bfe6c53244200dff36ac0a21006ff9b3605108037fcd930288401bfe5498144200dff264c0a21006ff9b3545108037fcd92a288401bfe6095144200dff264a8a21006ff9b84c5108037fcdaa6288401bfe6c93144200dff30498a21006ff9524c5108037fcdc24288401bfe6d52144200dff30a90a21006ff9b3485108037fcc1a4288401bfe54d2144200fcf30ab2ac10057f8b968d60803b7c5cac6b0401fb660d6358200bdf36ca9ac1004ff9ba14d60802f7cdb0a6b04013fe6e85258200bdf36c292c1005fb9b4149608027fcdd064b04016fe6e03258200bbf36e192c1005ef9b60c960802fbcda864b04017ee6d03258200bfe362192c1006df9a75c560803f78c0ac2b04017be6d95158200fcf2caa8ac1005ef9b64c560803f6cb1a62b04019fe2e5a64c2009ff374bb2610057f8b958d308027fcdd104984013fe6e8814c200bbf36e40a61005fd9b320530802bfc5caa2984013fe6e8514c200bfb36628a610057f8b94c530803bec5ca6298401bf6699314c200bfb36a98a61007fd1814c530803fe898a42984013fe6e8214c200b7f37010a61005df9b7) else (if i<3 then 0xad1a21006ff88568d108037fcbab4688401bfe595a344200dff364d1a21006ff8b268d108037fcdd306884017fe6e98344200dff350c1a21006ff9a760d108037fcd330688401bfe68d8344200bff37441a21005ff9b720d108037fcd3906884017fe6d48344200bff36441a21005ff9b120d10802ffcdd2e6884017fe6e17344200dff350b9a21007df9875cd108037fcd32e688401bfe68d7344200bff370b1a21006ff9a858d10802ffcdbac688401bfe69d6344200fdf30cb1a21006ff9a558d108037fcd1ac688401ff660d6344200dff374a9a21005ff9ba54d108037fc5d2a6884017fe6e15344200dff350a9a21005ff9b754d108037fcd3aa6884017fe6d95344200dff34ca9a21007f798554d108037fcd1aa688401ff660d5344200ffb2e6a9a21005ff9b814d108037fcd40a6884017fe6d85344200dff34c29a21005ff9b214d108037fcd434488401bfe69da244200dff34ad1221006ff9a3689108037fcdc34488401bfe6dda244200dff30ed1221006ff9b6689108037fcc334488401bfe5d9a244200dff36ad1221006ff985689108037fc42b4488401bfe5d5a244200dff2cad1221006ff9b3689108037fcc1b4488401bfe20da244200dff2e6d1221006ff963689108037fca9b4488401bfe14da244200dff374c1221005ff9ba609108037fc5d30488401bfe6a18244200dff34ec1221007bf987609108037fcd330488401bfe6958244200dff346c1221007bf983609108037fcd1304884017fe6d48244200dff34a41221005ff9b3209108037fcd1904884017fe6e97244200bff370b9221006ff9a85c9108037fcd32e488401bfe6957244200dff346b9221007df9735c910802ffcdc2c488401bfe6a16244200bff36eb1221006ff9a758910803f7cbb2c488401bfe6956244200fdf2cab1221006ff9a358910803f7cb1ac488401bfe6896244200ffd304b1221006ff9ba54910802ffcdd2a4884017fe6e15244200dff350a9221005ff9b754910803efc5baa4884017fe6d95244200dff34ca9221007f7975549108037fcd1aa488401fde54d5244200dff344a9221007fe98254910803ff4b92a4884017fe6e05244200dff35029221005ff9b6149108037fcd30a4884017fe6cc5244200dff34629221006ff9ba4c910802ffcdd264884017fe6e13244200dff35099221005ff9b74c9108037fcd3a64884017fe6d93244200dff34c99221005ff9b54c9108037fcd2a6488401bfe68d3244200ffb2e699221006ff9a24c910803ff4c1264884017fe6e03244200dff35019221005ff9b60c9108037fcd3064884017fe6d43244200dff34a19221006ff9a7605108037fcd2b0288401bfe68d8144200dff344c0a21007bf98260510802ffcdc2e288401bfe6a17144200fbf30eb8a21006ff9a55c5108037fcd1ae2884 else 0x8037fcd3aa2904017fe6d95148200dff34ca8a41007f79a554520803fbcb2aa290401bfe68d5148200ffd364a8a41007fe95254520803fbca92a290401ffc6055148200ffe2e2a8a41005ff9b8145208037fcd40a2904017fe6cc5148200dff34628a41006ff9ba4c520802ffcdd26290401bfe2e93148200bff37098a41006ff9a84c520802ffcdba6290401bfe69d3148200bff36c98a41006ff9a64c520802ffcdaa6290401ff668d3148200dff34698a41007fd9634c520803ff4a926290401ff64c93148200ffe30298a41005ff9b80c5208037fcd4062904017fe6dc3148200dff34e18a41005ff9b50c520803ff4a9062904017fe6e12148200dff35090a41005ff9b6485208037fcd3242904017fe6d52148200bff36690a41006ff9a348520803ff4c124290401ffa5892148200ffd2a490a41007fe93248520803ff898a4290401ffa6e12148200ffd35090a41007fe9b748520803ff4d3a4290401ffa61d2148200ffd36c90a41007fe9a648520803ff4c324290401ffa5d92148200ffd36a90a41007fe9a548520803ff4c2a4290401ffa2152148200ffd2ea90a41007fe96548520803ff4d9a4290401ffa68d2148200ffd30690a41007fe88348520803ff4b9a4290401ffa58d2148200ffd2a690a41007fe85348520803ff4c0a4290401ffa5c52148200ffd2a290a41007fe931485208033fed8b50904019ff6a1a348200cffb4ad1a410057fdba54d208033fed4342904019ff68da148200cffb74c0a410057fdba605208039fed4302904015ff6e93148200affb6a98a410077f9b04c520803bfcdc26090401dfe6a13048200eff36a982410077f9a54c120803bfcd8a6090401dfe6853048200eff302982410077f9514c1208037fcdbb5088401bfe6d9a844200dff36ad4221006ff8b56a1108037fcd9b5088401bfe2cda844200dff364d4221006ff8b26a1108037fcd434e88401bfe2e1a744200dff166d3a21005ff9ba61d108037fc5d30e88401bfe6a18744200dff30ed3221006ff9a761910802ffcdc2ec88401bfe6a17644200fbf30ebb221006ff9a8695108037fcd3b4a88401bfe6d9a544200dff2ecd2a21006ff9b3695108037fcd934a88401bfe6e98544200bff374c2a21006ff9a8615108037fcd3b0a88401efe61d8544200dff34cc2a21005ff9b321510802ffcd910a884017fe6e97544200bff370baa21006ff9a85d510803efcc3aea88401bfe6997544200bff370b2a21006ff9a859510802ffcdbaca88401bfe69d6544200fdf30cb2a21007ef97659510803fbcc2aca88401dfe2e5a344200dff350d1a21006ff9a768d108037fcd2b4688401bfe6e1a344200dff170d1a21006ff9b768d108037fcc3b4688401bfe6d9a344200dff30cd1a21006ff97668d108037fcdab4688401bfe2d5a344200dff3)) else (if i<6 then (if i<5 then 0xe595a348200dff362d1a41006ff8b168d20802ffcdc14690401bfe6a0a348200bff36c51a41006ff9a628d20802ffcda94690401bfe694a348200dff374c1a41005ff9ba60d208037fcd3b0690401bfe6998348200dff346c1a41005ff9ba20d20802ffcdb90690401bfe69c8348200bff36a41a41005ff9b220d20802ffcd8906904017fe6e97348200bff370b9a41007df9a75cd20803efcc3ae690401bfe6997348200dff346b9a41005ff9ba58d208037fc5d2c6904017fe6e16348200dff350b1a41005ff9b758d208037fcd3ac690401fbe6996348200fdf30cb1a41006ff9a358d20803fecc1ac690401bfe6e95348200bff374a9a41006ff8ba54d20802ffcdc2a6904017fe6dd5348200dff34ea9a41005ff9b654d208037fcd32a690401fde6155348200dff346a9a41007fd98354d20803fecb9aa6904017fe6e85348200bff37029a41005ff9b614d208037fcd30a6904017fe6c85348200bff36229a41006ff9a6609208037fcd1b0490401efe60d8248200bff370b1241006ff9a858920803f7cb2ac490401bfe68d6248200fdf2c6b1241007fe98258920802ffcdc2a4904017fe6d95248200dff34ca9241006ff9a354920803fbca9aa490401ffa6095248200ffd2c4a9241007fe9b854920803ff45c2a490401ffa6a15248200ffd150a9241007fe9b754920803ff4d3aa490401ffa61d5248200ffd36ca9241007fe9a654920803ff4c32a490401ffa5d95248200ffd30aa9241007fe96554920803ff4d9aa490401ffa2cd5248200ffd346a9241007fe8a354920803ff4c1aa490401ffa20d5248200ffd2e6a9241007fe96354920803ff4a9aa490401ffa6c55248200ffd162a9241005ff9b84c9208037fcd4264904017fe6d93248200dff34c99241005ff9b54c920803ff4c126490401ffa5493248200dff350d0a41006ff9a7685208037fcd334290401bfe695a148200dff346d0a41007fe95268520802ffcdc14290401bfe6a0a148200bff36a50a41006ff9a528520802ffcd994290401bfe68ca148200ffd2a450a41006ff9ba60520802ffcdd30290401efe6a18148200dff350c0a41006ff9a760520803f7c5b30290401efe6198148200dff346c0a41007bf98260520803ff4a930290401ffc2858148200bff36e40a41006ff9a720520802ffcda902904017fe6cc8148200dff34640a41007fe95220520802ffcdd2e2904017fe6e17148200dff350b8a41007df9a75c520803efcc3ae290401bfe6997148200fbf2ecb8a41006ff9a35c520803ff4a92e2904017fe6e96148200bff370b0a41006ff9a858520802ffcdbac290401bfe69d6148200fdf34cb0a41006ff9a358520803f7cb12c290401ffa5496148200ffe302b0a41006ff9ba54520802ffcdd2a2904017fe6e15148200dff350a8a41005ff9b75452 else 0xa61006ff9a65c530803efcbb2e298401f7e5c9714c200bff374b0a61005ff9b858530802ffcdbac298401bfe69d614c200fdf2c4b0a61007ff181585308037fcdd2a2984017fe6e9514c200eff172a8a61005ff9b6545308037fcd32a298401ff66cd514c200ffe302a8a61007ff17154530802ffcdd0a2984017fe6cc514c200bff36428a61005ff9b84c530802ffcdba6298401bfe69d314c200bff36c98a61006ff9a64c530802ffcdaa6298401ff660d314c200ffb2e698a61007fd9634c530803feca9a6298401ff64c9314c200ffe30298a61007fd9b84c530803fec5c26298401ff66a1314c200ffb36e98a61007fd9a74c530803fecc3a6298401ff66d9314c200ffb34c98a61007fd9864c530803fecbb26298401ff66d5314c200ffb16a98a61007fd9a54c530803fecbaa6298401ff6595314c200ffb36498a61007fd8b24c530803fecd126298401ff6609314c200ffb10498a61007fd9724c530803fecb126298401ff6549314c200ffb0a498a61007fd9814c530803fecb8a6298401ff6545314c200dff37490a61005ff9ba48530802ffcdc242984017fe6dd214c200dff34e90a61005ff9b6485308037fcd3242984017fe6d5214c200bff36690a61007fd95348530803ff4b124298401ffc5c5214c200ffe26290a61007fd93148530802ffcdd042984017fe6e0214c200bff36a10a61005ff9b308530803feca9842984019ff6a1a14c200cffb4ad0a610067fda268530802bfedd30298401dfe2e5a848200dff36cd4241006ff9b36a1208037fc59b5090401bfe6c5a848200dff162d4241005ff9b52a120802ffcd995090401bfe6a1a748200bff374c3a41006ff8ba61d208037fcd434c90401bfe69da648200ffe162d3241006ff987699208037fc5ab4c90401bfe2cda648200bff374c3241006ff9a761920802ffcdd2ec904017fe6e17648200dff350bb241007df9875d9208037fcd434a90401bfe2a1a548200fbf16ed2a41006ff9a7695208037fcd334a904017fe6e0a548200dff35052a41005ff9b6295208037fcd314a904017fe6cca548200dff374c2a41005ff9ba615208037fcd3b0a90401efe61d8548200dff34cc2a41005ff9ba21520802ffcd990a904017fe6c88548200bff36242a41005ff9ba5d520802ffcdc2ea90401f7e61d7548200dff34cbaa41005ff9ba59520802ffcdc2ca904017fe6dd6548200dff34eb2a41007ef9a659520803f7cc32ca90401fbe5d96548200fef30ab2a41006ff9a868d208037fc5434690401bfe69da348200dff34cd1a41006ff9a568d208037fc52b4690401bfe6e1a348200dff170d1a41006ff9b768d208037fcc3b4690401bfe6d9a348200dff30cd1a41006ff97668d208037fcdab4690401bfe2d5a348200dff30ad1a41006ff88568d208037fcbab4690401bf) else (if i<7 then 0xffcdc2a6b04017fe6dd5358200fdf36ca9ac1007f798554d60803f7cb2aa6b0401ff660d5358200ffb2e6a9ac1007ef96354d60802ffcdc0a6b04017fe6c85358200bff36229ac1006ff9ba609608037fc5d304b0401bfe69d8258200f7f30ec12c1007ef96560960803dfcc1b04b0401fbe58d8258200bff370b92c1007ef9655c960803efcb9ae4b0401fbe58d7258200dff374a92c1005ff9b854960802ffcdbaa4b0401f7e2dd5258200fef2eaa92c1007ef96554960803f7cb1aa4b0401fde54d5258200ffd304a92c1007fe97254960802ffcdc0a4b04017fe6cc5258200fdf2c6292c1005ff9b1149608037fcdd264b04017fe6e13258200bff36e992c1006ff9a74c960802ffcdaa64b0401fbe5953258200ffb2e6992c1007ef9634c960803ff4c1264b04017fe6e03258200bff36a192c1007ef9650c960802ffcd8864b0401efe6098158200bff370b8ac1007df9875c560803f7cb2ae2b0401fbe58d7158200fbf2e4b8ac1007ef98758560803f7cc2ac2b0401fbe5d56158200fdf306b0ac1007ef97358560803f7ca9ac2b0401fbe14d6158200fdf304b0ac1007ef97258560803f7ca92c2b0401fbe1496158200fdf264b0ac1007ef832585608037fcdd2a2b04017fe6e15158200bff36ea8ac1006ff9a754560803f7cdb2a2b0401fbe5955158200fdf2c6a8ac1007f795254560803ff8c0aa2b0401ffc5c55158200dff37498ac1005ff9b84c560802ffcdba62b0401bfe69d3158200fdf36c98ac1005ff9b54c560803f7cb2a62b0401fbe58d3158200ffb26498ac1007ff1814c5608037fcdd242b04017fe6e12158200bff36e90ac1006ff9a748560802ffcdaa42b0401fbe5952158200bff36690ac1007ef96348560803ff8b8a42b0401ffc4c52158200eff172d3261006ff9a7699308037fc5ab4c98401bfe2c9a64c200bff374bb261005ff9b758d308037fcd3ac698401ff65cd634c200dff350d1261006ff9a7689308037fcd334498401bfe6e9824c200bff374c1261006ff8ba609308037fcd330498401ff62cd824c200bff37441261005ff9b320930802ffcd8904984017fe6e9724c200dff34cb9261007df9735c930802ffcdd2c4984017fe6e1624c200bff36eb1261006ff9a758930803f7cbb2c498401fbe58d624c200ffd304b1261005ff9b84c930802ffcdba6498401bfe69d324c200bff36c99261006ff9a64c930803fecb9a6498401ffa609324c200eff172d0a61006ff9a8685308037fcd3b4298401bfe699a14c200dff34ad0a61006ff9a2685308037fcdd302984017fe6e9814c200dff34ec0a61007ef8b660530803dfcc330298401efe609814c200bff37440a61005ff9b7205308037fcd3902984017fe6d4814c200bff36640a61005ff9b220530802ffcdd2e2984017fe6e1714c200fbf30eb8 else 0x31b0c5b059b019afadaf41aea9ae11ad21ac89ac1dab85ab19aaadaa41a9a9a911a879a80da749a685a5eda529a491a3f9a335a29da205a16da0d5a0699ffd9f659ea19ddd9d719d059c6d9ba99b3d9ad19a6599f999b999219889981d9785971996ad964195d5956994fd949193f9938d92f5923191999101903d8fd18f398e758ddd8d458cd98c418ba98ae58a4d89b5894988dd887187d986e9865185e58521845d83f18301829581fd8191812580b980217f897ef17e857dc17d557cbd7c517bb97b217a8979f1795978c1785577bd775176e57679760d757574dd744573d9736d72a97211714d70b570496fdd6eed6e556dbd6cf96c356b9d6b316a996a5969c1692968bd67f9673566716605654164d5643d63a56365632562e56279620d61cd613560f560b5607560355f9d5f315e6d5e2d5ded5dad5d415ca95c695c295bbd5b255ab95a2159e159755909589d58055799572d56955629556554f9548d5421538952f1522d51954eed4d794c054a91491d47514609443d42f541ad40393ec53bc53a5138853711343d321930a52da52a4d2905273925c52451225921111f451d791b811b151a7d1a111979190d187517dd1745168115e9157d14e51479140d13751309129d125d1199110110690ffd0f910f250eb90d9d0cad0be90aa109b1081106f50529035d0190ffc4fda0fbd4fa08f810f618f44cf388f2f0f258f1c0f128f038ef74ee2cedc0eb44e8c8e6a4e530e498e21ce024df8cdef4de30dd98dc7cdb34d8e4d6c0d4c8d2a4d080ce04cd98cd2ccc10caf4c9acc838c6f0c5d4c53cc420c2d8c088bebcbcc4bb24b92cb6dcb510b3c8b2d8b1e8b0ccb034ae68acf4aa78a880a688a490a31ca1249f589e109c9c9bd89a909948985896e494949320925c9114907c8fb88e9c8d808c388b1c89d4888c871885fc8564844883b0826880f47f807e907d747cb07c187ad079b4786c77247608751873d0728871f07158703c6f206e306be069bc67f065f86400620860c05fa45e5c5d145cd45b085968579c562854885314514850004f684dc84b78498047884590441c427c40583f103dc83c283a88394037a03658351033c8322830e02f402dcc2cb02ae4297027fc26b4251423a02258213c20a4200c1f481eb01dc01cfc1c381a6c187416a81508131010ec0f4c0e040cbc0b740a000860071805d0045c02e8014800037fc59b4eb0401bfe2e98758200dff374c2ac1007bf98761560802ffcdc2eab0401f7e61d7558200fdf30eb2ac1007ef98559560803f7c59acab0401fbe2c96558200dff374c1ac1007ef96560d60802ffcdc2e6b0401f7e61d7358200fdf2cab9ac1007ef98758d60803f7c5aac6b0401fbe6156358200fdf2eab1ac1007ef98358d60803f7cb9ac6b0401fbe2c96358200dff374a9ac1006ff8ba54d60802))) else (if i<12 then (if i<10 then (if i<9 then 0x1af32af23af1a2f10af01aef82eeeaee52edbaeccaebdaeb42ea7ee9e6e94ee85ee7c6e6d6e63ee5a6e50ee44ae386e2c2e22ae192e126e0bae04edf8adec6de5addc2dd2adc92dbcedb36da9eda06d942d8aad7e6d74ed68ad5f2d502d43ed34ed28ad21ed186d096d056cf92cf52cee6cdf6cdb6cd76cd36ccf6cc32cbf2cbb2cb46ca82c992c952c912c8d2c866c7fac78ec6cac65ec5f2c586c4eec3fec33ac276c1b2c0eec02abf92bf52bebabe22bd5ebcc6bc02bb3eba7ab9b6b94ab6ceb47eb1d6b036afcaaf32ae9aae5aadeeadaead16ac7eabbaab22aab6a9f2a92ea896a7a6a70ea6a2a60aa572a4daa442a3aaa33ea27aa20ea176a0b29fc29f569f169e7e9de69d4e9ce29c769bde9b469a5699be9926988e97f6978a96f2965a959694fe946693ce930a927291da914290aa8fe68f7a8e8a8d9a8caa8c128b7a8b0e8a4a898688ee882a876686ce866285ca85068442837e82e6827a820e81ce8136809e80067f9a7f2e7e967dfe7d0e7c767bde7b1a7a8279ea795278ba7822775e769a75d674e673f6735e72f2725a71ee712a70926fce6f366e726dda6d426caa6c6a6bfe6b3a6a7669b2691a68ae681667aa671266a6663a65a264de644663da62ea622661ba614e60b6601e5f5a5e6a5dfe5d925d265c365b725aae5a16597e591258a6583a57fa578e56f6568a561e558655465506549a542e53c2535652925252521251d25166512650e6504e4fe24f764f0a4eca4e064d9a4cd64c3e4ba64ae24a1e495a489647fe4792475246ba464e45b6451e44de44724406439a43024212417a40b63fc63f2e3ec23e563dbe3d263cba3c4e3b8a3b4a3ade3a1a398238ea3852378e36f6363235c6355a34c2342a339232fa3262319e310630c630022f962f2a2e922e262d8e2cf62c5e2b9a2b022a6a29d2296628fa280a279e2706269a262e25c2252a24be242623ba232222e2221e218620ee20561fea1f521eba1e221de21d4a1cde1c721c061b6e1ad61a6a1a2a1992192618ba1822178a171e1686161a1556143a137612de12721206119a110210c210560fbe0f7e0f3e0e7a0db60d760d360cf60c8a0c1e0b5a0b1a0ada0a6e0a0209c2098208ea085207ba072205ae033200b5ff15fd75fbd5fa61f8c1f7d1f631f4bdf3f9f285f0b9ef19ed4debadea65e86de751e6b9e621e5b5e549e4b1e471e405e399e2a9e23de1d1e139e0f9e035df9ddf05de6ddda9dd3ddc79dbb5db49dab1da19d981d915d8a9d811d779d70dd675d5ddd545d505d46dd3a9d33dd2a5d20dd149d0b1cfc1cf29ce91cdf9cd61cc71cb81cabdca25c9b9c921c889c7c5c701c63dc5d1c565c4cdc409c345c255c1bdc151c0b9c021bf89bef1be59bdc1bd29bc65bbcdbb35ba9dba05b96db8d5b811b7a5b70db649b5b1b519b481b3e9b351b28db1c9b1 else 0x754fa02dd0c08f011a9c0083aa7d0169dfd0d808d4e1ac0093aa7d016e8ec046a70d60041d53e80b4d48a9c35a6347686c00a1be3144c08e16e21b001c0aa1a02231923145b8b61538684c086c00902237c648c516e2d85480411c21b0161ac00d192338fa6b6d5263847686c0586b002c5b8f4d8baa4c708e3bfa1b0161ac00b1d5b14fa6b631c238efe86c0586b002f629f4d6daa7431a0c05801024b629f4d6daa4c7602c358012045016c53e9adb54e1ad3063847686c00c1be2d85489819221b001c6f8c51522605b886c0071be324628b716d8684c086c0091922dc168a90082384361ac0093aa0b4410a9c3423b001c648c516e2d85489913023b0024e40b713203002086c0071be2d85489819223b001c6f8c51522605b88ec0071be324628b716c2644c08ec0093902dc4c80c00821b001c5b9c80186184360235386b0024e400c30c21811e0235380107204100cc3461b00180a8df1923145b8b61538684c60051c816e03002086c0586b0020e400c30c218c7602c358010720c700c30d80b0d60038b73906380618610d80b0d60049c831c030c3086c0586b0020e400c30c218d0602c007391868c700c30d800c4dd0d02d18394340b461d86c8a9c004152367000c1d40205b0130016010d905b80084dc0aa1a022400357fa2f36e53c6287706c0580141bc00d5fe8bcdb94f18e1d41b016005801ebfd179b729e3143a83602c00a003d7fa2f36e53c6187506c04905e0ac05c04ebfd179b329e31c3b012c1682b0140300275fe8bcd994f18e1d4199b1462eb616c2a74c09810580122486feb6d3123b62e003ec550c21a41082d6d800e0b46fec59522a75b6003ec518a2a74c098d6c21b00206fec518bad85b69813021b002762eb690420b4c286c0075be37f4c48e11dadb001f628c5153a604c08ed6d801037f5b0b6d30260476c5c0081bfb1462eb616c2a74c098c009d8ba604488ed6d21b001f50f350b350474fdb4f174eab4e3f4d7b4d3b4ccf4c374bcb4b074a9b4a5b49ef49af49434903483f47a7473b46a34663459f450744c7445b4397432b42bf41fb4137409f3fdb3f433f033e973e2b3d933d273cbb3bf73b8b3b1f3adf3a47395738bf385337e7372336b7364b35df357334af3417337f32e7324f318b30f3305b2f972f572eeb2e7f2e132d232c5f2bf32b2f2ac329ff296728a3280b27732707269b265b25ef25af254324d7246b242b23bf2353231322a7226721a3210b20471fdb1f431eab1e3f1dd31d0f1ca31bdf1aef1a5719bf19271863179f1707166f162f156b14d3143b137712df124711af10eb10530fbb0e9f0e070d6f0d030c970bd30b0f0a1f090307e7077b06e306a3060b059f0507046f03d7033f027b01e3014b005aff96fea6fe0efd4afcb2fc1afb82fa92fa26f962f872f7daf742f652f536f4) else (if i<11 then 0xd18610c60b0030e40c8dbe6e35b6a9c1d868c1186c00b16e2e36f9c8d8baa70761a30c218c1600602ddbe723629b8d6d83b0d18610c60b003008a0edbe723629b8d6daa70d698304208c360070650c220c203057145b89901820b001adb00c30581b0d60035f4f8a0b7cc0b7371800e316db0a9130238410b9c0081be2a44c08e1042e7001c5b84a35386806600302f094030612811a1a3520330018648b71323a806082c00705e77c6f8c918a2dc5b08ec0c6a70d082c00d192354fa6b6d1d818d4e1ad0580142dc611d5d8a77f4760635386b4160059d5d8a7d35b023c0c6a74160048e23abb14fa6b63bf818d4e1ad0580160bd031d5d8a7d35b1a915386b4c68ed05801a0b4eaec53e9adb4760635386b0028648a913230806082c0071523d5410b9c00519263b0d00cc00516e128c761a019800c04b0d00c18651923145b8b61538684c082c00a11c3245b8991be0304160040123be37c648c516e2d85498e11d81b0d082c00e192338fa6b6d5263847606c35a0b002c5b8f4d8baa4c708e3bf81b0d682c00b1d5b14fa6b631c238efe06c35a0b002f629f4d6daa4d0606d058010049036c53e9adb54e1ad3063b4160058f6d8a7d35b6a931c23b0361ac00a1be2d85489819220b001c470b7b8a2646280c10580102386c8c9c0041be314548981042e7001c6488e1322d806082c00711c3d5410b9c0051922dc470991520304160040121be324628b716c6a45498e11d86841600681240c754430a9c3463b00226406543418480be0304a953869e2e0038a91b380060bc2500cc0041aa0202c40678b800c2180405880d86b0018251b801181b0d182c0071926e30d008305800c2dc25008c0d868c1600384a3700230361a305800e128dc02301086b03182c0080946e30d008305800c030c160018821922dc4c80cc00617220b000cef8c916e26406182c00719277cdc00cc0d868c160041df37008c0601cc0c60b0020061b8c3460b0014410b7b8b8680660030821b232300107a9b8c0031922dc4102305a033001c4302d0101610360030c916e6a44c80c305800e754dc086019868c160038c916e2644100cc0060242e44161ac0051922dcc700cc3460b001c04a06371868c7182c0071726e3000e0361ac003012128041b8305800c32c0400980cf17001804c06c34033001437037018023aff45e6d4a78c50ec0dc0b003424837011d7fa2f36e53c6287606a0580180b800b5fe8bcdb94f18a1d81b8128188080280afaff45e6cca78c606e04b05e0ae11013ebfd179b329e3143b812c0880801a017aff45e6dca78c606604b0edf146161af302f3001c5b0a91302386ce0030c5152260470b710d800e37c5489811c2dc43600382d08041922dc1688e10d808d4e1ac00a1927d016e8ed0d808d4e1ac00916e754169dfd1da1b011a9c358014 else 0x36d8004ad843600184bc0023900304360021c5c00210d800405700094c086c003018013000c0480c0098008618026001d0e2bed16a2b36a6cca694b18a3043983506006005ed7fa2f36e53c63830030028ebfd179b329e31c1801801475fe8bcdb94f1860c00c00a0a2936252460832040060051419a2b36652c618700c20c00c00aa8302d630c38061060027a0cd7da2b36652c60061060060054d159b329630c38060013b5f68acd994b18018004fd179b729e3004f0160000e828a4d89491821c81001801400100e0b6aff45e314603320ea1d4180373665380b004008861e8a8a79b602e3180033212f958e8bcd81571802780b00007515f28a4d88c10e40800c00a0008070480bd2fd5fe6d4da9482961dd1701718a0d80201840382f6be97fa2e0ea5380b8c600e6cc2be5149b1292308100180140070021680215fcbf43a07745c0400994f18c000039b506880100e0b40925fabfcda9b32925343807745a0c01b8c602c010026d159b30e057c63010013b4566cc3883004057c6005602002a6bed159b30e653c6301001402d61c41994f1801580800a004001009d179b30ea0c41994f18c04b6bed159b02be31808009dafb4566c0108302be3002b010015008002013a2b2961dcda83718c04a0100040235fe6cc3ba2d06653c63012d4760012b6505800624b000962892c0035058005ad954e001eb651d8007ad94360018d858b2db0010494b6c00351d8004b1543600182dc0021258004b7d5b6001aa9c00250d8005800236162886c004112adb000d62889c0031138004227000844e001089c00296c2d8750f7d05800c3d75b0b90020dca3d45c8b706e496c2d87161a1efa0b001cef8f516fa0b00146f8c51522604708616e20b0024ef8a911c2df4160030df18bad85489811c218410b7c00a3bfb7f628a9d31a38430b7d058015b7ce46c5d6c6a41198610da0b00286f8c5d6c2a44c08e10c2085be0050e2391b175b636d53868c308631da0b0030e40c8dbfadb54e1a31c61b4160051dfdbfb1754e9811c2185be82c00a1b1b7ce46c5d6d868c718610da0b002f6f9c8d8a6835b6a930c218c7682c00b113b7ce46c5d6daa70d18e30d80142086c8c9c0040743d7000e410f5c00305a3df000e410f5c0030752087be1ac0051ea2e40083720df152260430b7105800e8681f08090221be720628b716c2a70d09830c21841600701104437c648c516e2d854e1a130218c1082c00e19232cef8df371adb54e0ec35a18c1600601141c6e30d18210477f00200721a002302237c648c516e2d8110a9c3426043182105801c045071d537023854e1ad3060841600581543404468680a81118821ef86b00120761ac00311c042070f7c35800c2384481002a83b0d60038111be720628b716c2a70761a30c218c160068f6391b14dc6b6d5383b0)) else (if i<14 then (if i<13 then 0x335380042dc1d600180451d8006011436001e0008c900980063246aab6c00435380042dc1d60018b700980062dc610b6c00416e013000c5b8c216c2a70014d4a04c003352813000cdb4b6c003434010008cefbb6b3063b0015e29c5b3063b0014d4d9831d8008edb0d6001e1ac00278b86b000c64c98c00307cedb0d60020b71e926300105b8dd931800986b000b0d60010ea93180062a411c98c0041923564c60020b71842da4c6002815c35800786b00095b298c00336c663000d5b08ec00319238b000c5b83ac0031bea63000c08e02c00300832562e00208e193800601154e00180450d800604501600199830d80063240260018c919cadb0010c760010b7075800771462a98c00416e013000c5b8b6c00316e013000c5b8b6c00331c813000c5b82d16d80096d85b298c00436d2db000d4c6001198c002c0010098004adb000864804c0031922a7000c5b8043beadb00145b83ac00331d80042a54c60019a9c00235380040130008472b6c00316e0b7000c5b88ec0030098004031db186c00478a030c3600200c30d8006e6006186c004018edb000c2580cc00319203062e00203c01980062dc0660018b70198006f1406600180cc00201980043240660018b70182db00100ab98019800803300080660010c901980062dc060b6c004019800403300095b60011b6c002c00156c21b000c64886c00330d80042dc1d600182dc002531800461b0008066001004c00210d8004013000843298c00309780043240260018c9190adb00105b83ac0031920b7000c648c8531800861b00085b804c00316e2f05b60020b700980062dc5e6001986c00216e0b7000cc3404c00316e2f14c600240431d80076d80660019b6c00258b80047170008021c5c0031b17155b0a9c005192013000c57e0010b700871700105b83ab8b800861b00086c5c553021b0014c360015c501980066a70008d4e001004c00210cadb000c5b80cc00310c2df000c02600108653008f00114c600101533180060130008492b6c003192013000c64892c00316e013000c5b892c003008717000c49600129810d800661b000806600118ec00201980042195b60018b701980062185be00180cc00210d80043246fdb6c00405b6db000c6fdb65318008032db6001804c00236d800571462ab6905800a010416001dc505b800771462a98c004b8a03241600200410580066db00095b0a9c003c0011922a7000c54a98c003019800401041402c0040eced8d4e00204b05a6a70011db600107676c6a7001016e00104b3538006364d4e001e000e000e000804c002009800580026a5cc6001e000e000e000e0008043538006f1700080480c00980098003800380020130008023c5c003c001c00136d8004ad8476001986c00219223b000f000447600100cc00200980046380260019a9c002 else 0x41202560018d9c00278b80040f0d4e001e000e0008eac0021858004f170008436001012352e6300130007000700046ce0016000e00085878b800621b000832e00108ec002c00116e2394160021c5c00231cb7e4760020123538006030c16001bc501860b0011db00c3058008f1406182c004730030c160020090198006023000b000404032c00378b8004088046001b9804780078002adb0008db6001008c002b6c20b000c6484ab6c20b001470482c0033042e64160020f6b6ca6041600280890580076db000adb60010c9019800620864e001808c00201180042094c023c004c0010978004324041b6c004196327000c04048c003304327000c658b910580086085ce0018c9196a6300106ce00103cc00216e023000c5b8b8c00316e023000c5b8b8c0030100f3000c5b8b853180080201e6001e0009b61703d7001162e0011c5c0020106db000c16e0010c901180060b46ce00180816f80060b45c882c004010163000cc10b9c00305aa63000c16e00102dc00201016043206c00535380046a46ce001808c0021058004023000841298c0035318004054cc6001882c0020106db000f0004040c910d800812864e00180816f80062e4416001808c00201004b000d4c082c0033042e7000f000404012c00331d80040230008416001008193800620864e001808c002c00136d20b000c41600103cc00216e20b000ce2c06c00302b8004a60416001982c002078032416002058012f1406482c00630404a41600200880d8006edb0008c1600104bc00209060b000f00041e600103c371800780038002025e280cc0040b0f14c160026000e000e0008b9c00202b8004049cc182c004c001c00101980042e7000b00070004063b6c00301860b000c06082c00301860b000fa2f36e53c63870076040051438afb45a8acda9b329a52c628c10e00e01400ba8735fabed16a2b36a6c4a58c51821c01c02801775fe8bcda94f18a1c01c028014b4566cca58c30e01801e810014b5f68acd994b1801801e810014f45e6dca78c70ec0d80001a0a29362524608700c00f40800a40400ba040340294af94526c4a48c00c00f40800a40415fe6cca78c745a1c03500440a0160144044d159b606057c600280144066bfd179b10e057c6009805002ac0cd7da2b3640cca78c005002980cd7da2b3621cca78c01300a0054d7da2b3604581815f18604005203015f18026c0a000013810010015aff4565381b8c736a1cc097cda87606e31d141719e2bb6c0030ecedb000ddb60010c2c00276ce63000f0005db60010bcc002b8a77ce2bb6c00519380043270008db1a9c003c001b8a3155b60020b707580062dc7a60018b700980062dc6e8b6c0043bb80040b5db1a9c00478a0b4d4e00202dc00216e0b7000dcc02dc00378a0b7000d5b60011b6c00256c2a7000c648eac0) else (if i<15 then 0xd800660831022c00430413b000c1f022d3060b0014c1022d31800860809698905800a0434c40ec00476d800408c476001862044e60c16002e00084e73060b001300041f600103e045868c16002e000e000e000e000822c3460b0013000700040ae00100404623b00100961a30408b00170007000700045ce0013c5c0020478004089db182c004045800408b00094c6001015c358006040db69811d800a32408698c0041922254c60020b7021a6300105b8895318008040e2e98c00402ba63000f0004c1698c00330da63000c0869841d8008224c16001811c1d86b0010082dfd31800804154e98c004023a61076002023c002a0457da2d4566d4d994d2901ec1a83102e30005d409afd5f68b5159b536252c1a83102e30005b409afd5f68b5159b5366534a407906205c6300001794526c4a51171801fc1a81001486100220f0edb000c32b98c003c00176d800580020c80460018220118007714251c5c004b8a6a7000c62e0015b63be6db0012db1c536d80080f00660018b718a6da4160028b705b80062df00083c182c00316e12b000c2f182c00316e023000c5b8ddc0033bb800477ee29a9c004b8b8004160256001bc538a6a70011db5c536c6a7001404600160008b701180062dc0660018220118006b170008e2e0010c909580066a562e0018ea36c3d541600282fc0d800602147600182f40d8006021416001858c002192023000cd48d5c00316e3554160021c530580062dc0460018b701180063085b8a9c0040100f3000cd48b7c0033522df000cdb0f5c0033bf660c76002598c00278a716cc18ec00576c6dacc18ec00578a6a6cc18ec005047663000c32e1ac003c358004141e2e1ac0041923164c60023b6c3580062dc7a498c00416e3764c60023c5c35800786b000875498c00315208e4c60020c91ab26300105b8c293180080570d6001e1ac002011800580022dc0460018b701980060c8046001bc5c0025318004194cc60018c90958006388db0f5505800a37d4c6001812c0d800602064ac5c00411c327000c042a9c00302481b000c04282c0030a0663000c6480810d800802024486c00431c3264360020b719d219416002dc518aa62436002998305800623b00085b808c00316f80042dc04086c00416e12b000c0403c31d80086385be001db616ca630010db0f5c00358aa63000ce2998c003c001011800432404086c0040942a46ce0020083be2df00105ba82c00331d80042a54c60019a9c002352367000c096001008c0020102df000c470b75058008049036001808c00216e37cdb282c0051bea60c76002008c0020f180056d85b600180807980076d85b298c0040100f0c7086c00536d80047170008e2e0010b7b8a2a5416002dc5152a6300100408680d8009714d4e00183c3538006f1700081960011a9c002c0010b1800 else 0x2df000b00075b60011a9c00216e0e85b60021a9c00216f80040e8ef8a9c004c0010658005ad94c60018f5c00216e0e85b600218ec002c0013bf800580023d7000b00041d1df11d80080e8c760018b7c0025bea63000f00045b83a16d80082dc1d6001e0008f5c00256c0e8d4e0020f5c0023538004ad81d18ec00416e0e85b60020b712580060b45ba82c004d6ca0b000f00045be001186c00216e77f000cc360010b7c00216e0e85b60020b7c00230d80058002b154160018b70747145b60028b707580062bf0008c3600103ab8a2a70012e2e001186c00235380046a700085b83a16d80082485be0018b704780062245be001a9850580062dc1d0b6c00416e0eb000c5b892c00316e0e8e2e0026000986c002125800463b00085b83a5bfadb00141d0b755380082df0008448b750580082e700085b83a16d80082e641600183a17320b00101d482c00317320b000c5c60010b8c002c001171800580022df00085be0010b8c002c00178b80042df000b00045be001600083a16c3df00105b83ac00305a2e46ce00202dc00256c0b7000c5b83ac00317380043df0008d483a1b38008a6300081d0b61ef80082dc1d186905800a2dc41600183a90580060e85be0018b707520b00101d08e90580082e641600183a1ef800780022dc1d0b6c00416e0eb000c448c9c00316e0e8e2e00203a17380062dc1d600183a17380066181d0c9c00430c0eb000c1121a0023b6c714db398b31800c2df0d6001e1a16f800786b000b4c60015b616ca630010db022d31800877dcc59830d800af14e2b98b3061b0019db1b6731660c36003298c0020cb86b000f00045ba98c003d31800404b0d6001812d3180062274c6001850c3580062dc64298c004021a63000f0d182c00316e0434c08ec00516e0434c60020b7178a60436002986d3180060434c08ec00436da63000c32e98c0030a1a63000ce41c553021b00174c60010b753021b00101169830d21b001408698c003434044008cefb98b3060b0015e29c5731660c160033b636ce62cc182c006352e62cc182c005731660c3182c00556ca63000cdb61ac0031923dadb298c0051c1a63000cc1698c003305a63000c08e1ac00302032562e98c0051043254c023c005021a63000c08e9841d80082274c6001e1a30d8006324081b6d31800a60b4c60018b7196a60416002982d31800660b4c600183ec3580062dc08698c00416e0434c60020b7170a630010c1698c00336da63000d4c600161ac002d300b442dc08698c00416e0b54c600202dc002353a63000cd4e98c00302386b000c08e9841d80082274c60019b6d318007a60c360018c953020b00101f698c00316ea6041600269881))))
def pL34 : PT:=(1106,4,7,16,pL34F)
def pH0_34F (i : Nat) : Nat:=0x319589e20445800a227e498b96e40f10ab1dd00c696bfaae80d2b300316b718185bba98e60b403100c615870a742c00c5dd300c403100c595400c5828906ac0b825c43052b4031b2024216095a99702781cd06f82f0a4141900c602320bbc2b3978c00e08200304d0000890c0
def pH0_34 (h : Nat) : Option (Nat × Nat):=lookupWord 15 56 6 14 6 4 pH0_34F h
def pH1_34F (i : Nat) : Nat:=(if i<1 then 0x680300080518c4a07f51cc100804020100804020100804020100804c014e074f411700807808cb15ff41b9807a040b8d04f245d9f03cb4078614680201b116402015115402014060c0201c03d00201200d80201008040201008040201008040201f070c0470e01014098e056c02014079300d7316fb018fb0635c174603b181e2f03c00201c07078464008040201008040201f01cc0201008040201008040201901f8c16b700940201b029cc112f16cf41a5004fd01f48037802017013802010080402010080601e00080600d2a01d2000a00806815100804020126306406d0080480c350722412e511c50029617550119940604156008074c1a3206081540022b0023906864063700910000116f78083008040201d0424803b105f8020100805c03d00807c14a00805c057104b44076e05cac4c33035a811fd043200c9606a280f6a045784fe00805441a00804400dd0676c0a06168fc1324049741dd204ee81a26171a45c0008040201d05ffc49cc07e701e60080701a40080701577059f41b3406eb80490080480b53152084a490480003e00804041e008040201704c6406600807800400807017db01140201d1497815c7028402010080740710080540fd00805c431000fc40f930639411bf07c50571c02fec1403405f81aea066c8582f040341889060380e7500d3407cf03e800cee0794c0be1039b41e18024c046e606078021c02940201008040201f052fc1b8916d8c12b0028c020140451018b00805c08b3028a80e87430401696064ec0cc0080600267070101aca00d641020080401b70080780c7d05e980c8302f40201d00bf01e7f00ca81ece00f080ed50648804b00804c450606280201a206981297018002010080402010080581d5c05640201e0027c0eec021581d1b1175446f0080441b6008040201008040201e128d81d9f0758020100806810de02a2020001186c1d000807c1f7b0254c49800805c4ff00806800e300cf4008307fb81cdc406701580080481857058c801f2032b85818021b80e5e07ce80823059341a6c02518149707ec050490468c07d902c80202803010020240003c050000e00c0101800010000380000000074000280003c00004000140000c000000000002004000140102c00004120740b0240200c0301c06000000100200413010010000d00401008020600000c0000005008020000100007000000000101803000060040200c06000060240301801000050000101805004010080b0040300000008000000801c000180700003008000200200007000000000008c030100300400004040000001409038000040102001000010240c00809000050240005c03008000080000c09008010180300c030080a0000602800080010000501c0101c040040103c0809000004000100000402024130100b0042103002 else (if i<2 then 0x74033e8128d02f2c150503000201104cc80ac0080581840080541d47036901ab4004e40c4402ec02010080402011007402010080781bd008040201008040201907c280480080701c4e15d98090812388161f03cdc068a000dc0aa0043e01a70080402010080402010080401070080604f0008054469d0733c01200807406bc102bc1ea008040201100c4c1010080402010080680e400804c01600807416da067002017042b40209048f400500806c139104b0008e411ac0201a0441007510715013e70154c04731168c178c05eec14d2064681ff2053c02012043841870080402011017f00eb008040201008040201a002c0201008070462400a140e200804c15d2050b013d2023cc4ef304e204410080402010080402010080700d3008050092e05e7009c704c2841c1059a04eea041900af00806446a008064052c0779c121203c441ad913c9c04a0080402010065198c0d0135c17c304584146d02cc02016118f4105b03700201a050c0201c010e41700080741ee00806804c0080440b65036dc05d00659809600806419ac01ab4017402d201040057e41a9215cbc0220080680d4401c800f50080680ff8042c02010080402010080604a5c03aac1c2b03400201c07d6c195008040079f11580201008058058008040201008040201a036300810080501da000e541764115dc467703080201e01dc0201b05550574006cb4190b10500201d07a7c1eb903eec0c600807c5bcb11b00201a0277048f20618c0ddc103e8cc2504db000150152cc00b110b813780220442400806c0199052200e3f06f944684006c02014040c0201007e00201902b40201f05c402017057a81240037c856fd07bfc1c6f02e80201706fdc0447071c0201008040201d0510020190667411100806801e00805814c008040201e00300201a02b802010080402018058802010080402014003c02016032cc080700e080b100805c05100804020100806c0cd0080402010080681b1800600201b02c3a0c0301ee402a50347816a008040201c90614168d01040201008070507200180201007c9414700805405ce04ea0134e01184135806c080672044f450c0074a014e701b0c02d40187c500a014e002e70499819f2001dc122e076d81b540421c1532128341526075fc042906a9044b503fa4160e05b2c4a20080400fc905b80201a0385409e505d4020141258020100807808db01c1c0b9b01b841dfb430901cae073dc1fa9000bc1270080784520080601183078c020100805c15aa1199409fb1601418200804857ec014002019104405bb0080402018073b809ac01a40201405140201008040201008040201008040201607254091c07b541af905cfc197a0633c0a4c029ac4a10047400c511160806fe0265805b5025ec05e411208476b00468056d160c02010080402010080 else 0x11c6030701897009f803ab05dc020150194802b107f081bbb007081cb3018802019068301dcb013d81f6008064453504a9c0155021380ef4126a809b9205dc01050190c0a9403e00201806f00201006d0c08700806c0ab008060037002240201b01640201401fc0201b04bd007a00806040bd068e8141f02de00d500804c16f91488c01af03800201c0168c165700b3019e2125781d8b03a68198704780201d0366c0f))
def pH1_34 (h : Nat) : Option (Nat × Nat):=lookupWord 207 868 10 18 10 4 pH1_34F h
def pL36F (i : Nat) : Nat:=0x57f29cdb0ec6006d140c80122fe5383045a2e6d8c41d81400ad7c5fca70e02345cdb1881b0280162fe5387009a2e6d8c60d01400aa2b70d200dffaa9208027feaa4c2009ffaa9208027feaa44200
def pL36 : PT:=(4,3,7,9,pL36F)
def pH0_36F (i : Nat) : Nat:=0x1c09806c01b020401b006c01b006c01b482801b6800407402401b006c805e038429006c01b006c01b006c004806c01b006c487aa1601b200201b006c01b006c01b581401b006c01b006ce0680182c9806d0084a1c801581e804006c01b083668e006c01b006c01b006c01b006c801f02201b006c01b006c01b006c01b28a8044e00e4438220040000000080020c004
def pH0_36 (h : Nat) : Option (Nat × Nat):=lookupWord 11 76 7 14 6 4 pH0_36F h
def pL37F (i : Nat) : Nat:=(if i<2 then (if i<1 then 0x9e6d2799fcb38665eac9418e9b15661b2c1c181cb0025ecebbf9731addc5abeb4a1641ac06574eabe1542aa4e5352a4d944da7f64eb69ba1326a5bc4a42921921da3fa46968c01132a21042d6845903da0303fa27d50f709e6e3c0a7620e809c98385e6e28d869a9034766658ca098ec30de6040bb596f82c925730a9894e6293650009d59338257648588ea913021ca421880e8fc81ebe3c507508e241b6234d065b8c3a178e2d785848ab414aa28284c68910112620583db87620e061a9031385be0abe13b0246841a074e0d2016f8276041a069009d80d200d20003ff9a858200ffe69d60803ff98758200ffe69560803ff98558200ffe5d560803ff9a358200ffe60d60803ff97358200ffe54d60803ff85358200ffe68960803ff98258200ffe5c960803ff95258200ffe14960803ff93258200ffe0c960803ff98158200ffe5c560803ff95158200ffe4c560803ff92158200ffe69930803ff9764c200ffe58d30803ff9a24c200ffe60930803ff8824c200ffe5c930803ff9624c200ffe4c930803ff9a14c200ffe60530803ff8814c200ffe5c530803ff9614c200ffe54530803ff8514c200ffe4c530803ff9214c200ffe085308037fda14c200dff60530803ff9a848200ffe2a120803ff9a748200ffe61d20803ff9a648200ffe61920803ff97648200ffe69520803ff8a548200ffe61520803ff88548200ffe5d520803ff96548200ffe68d20803ff8a348200ffe60d20803ff88348200ffe5cd20803ff96348200ffe54d20803ff85348200ffe60920803ff96248200ffe54920803ff93248200ffe68520803ff8a148200ffe60520803ff88148200ffe5c520803ff96148200ffe54520803ff85148200ffe4c520803ff83148200ffe485208037fda848200dff68d208037fd5348200dff685208037fd8148200dff4c520803ff9a844200ffe69d10803ff98744200ffe61910803ff97644200ffe69510803ff98544200ffe21510803ff97544200ffe59510803ff9a344200ffe60d10803ff88344200ffe5cd10803ff96344200ffe54d10803ff85344200ffe68910803ff98244200ffe20910803ff97244200ffe58910803ff95244200ffe14910803ff93244200ffe0c910803ff98144200ffe5c510803ff95144200ffe4c510803ff92144200dff68d108037fd8344200dff689108037fd8244200dff549108037fd3244200bfe69d60803ef96558200fbe58d60803ef96158200bfe69930803fd9314c200bfe6a120802ff9a748200bfe69920802ff9a348200ffa54920803fe921482009ff6a1208037f93048200bfe6a110802ff9a744200bfe69910802ff9a544200bfe68d10802ff9a244200ffc545108027fda3442009ff689108037f92044200bfe60910802ff93244200bfe60510802ff95144200bfe4c510802ff92144200 else 0xc57f45cdb29c630e8190280180882c06819afe8b9b6538c21d032050034767143a6a58e6180480a1a801425bbe1d352c730c024050d400a3240437db6ad9a9aa58ea3986a19c520a0286a0083e8e2874d4d52c751cc350c5c4350031dd7143a6a6a963a8e61a862e21a801816874c730c024050d40083a804716c56dab677da963a8e61a8620a0286a0083aafa3be16c04d4c350022dfada8ea1a027561a80105bbbee287454b1d4730d431710d400c77dc50e9a96180480a1a801271008e2d8adb56cd4d52efb1cc350c414050d4010b15f4adaa977e866388280a1a80166499c023bf6fb6d5b35354b8ac730d43105014350044b777dc50e9a9aa48e61a86868b88018023bf6fb8b62b6d5b352c730d4310501435003dd56382d809a986a0038121d018024050d4007011c5b15b6ad9a9aa58ea39df6188280a1a801ee43e8ef818414050d4008b7eb6aa68e721c56188280a1a80165bbbee2874d4d52c751c434345c400c011dfb7dc5366c56dab663a8e6a58620a0286a00839006404d4c35001892011dfb7dc5b15b6ad9a9aa58e6188280a1a8020e431c0610501435001c76715a963986010b886a004896ef97016b1cc30084143500282d63986010b886882801008bbee2b525c30c0243441400a0240c010b886882800e00809afe8b9b6538c21d83405002c0458a0457f45cdb29c610ec1a02801806009afe8b9b6538c61c83405002c610120457f45cdb29c630e41a028018022b1026bfa2e6c94e318720d01400c011128135fd1736ca7184390680a0060ba6f952471b2e41eee2c355c400b109df7543af15a93de1a2e20053be1d78ac71ef0d17100203a3d3c586b982e18280106f9524378b471ef0d37100240ef14226e21a60a003be85491d64104eff8bdb435cc50d0030df238c912882ed9d586b983228680181e1bedb15247590411ef0d37143400c048df2a6c820bc5eda1ae618ea1a0060b0033abe2f6cd4c35cc400902406033c56e21a60a0042bfa2e6d94e318740d81400908b5fd1736ca71843a06c0923b16cfa1524710ceff8b5c43541400c12cdf2a48e365c8ae21aa0a005074433e9e2c35cc17141400937dd52382d21bc56a6b886a8280166f9524378ac75710d50500240937ca90308e72186ae21aa0a0058041d3aa16809e2f6cd4c35cc400bd7f45cdb29c610ec1a028012066bfa2e6d94e318720d01400a03004d7f45cdb29c630e41a02555254d1c6fd8b5b5304350500289237ea9b16b6a608e21a82801554953471bf62d314356c41400a0b4dfa3ab62a698a1ac520a0055be6fd5362d6c4750d4c10500288937ea9a628ead886b148280151df2389c6648c0b155a26cc48487ab0c9a145c204833703da03cbfd47eaefac9f1abdd67a8af2f9e1bbbb076b6eb01d1cb9da727ee309c27b7a06e1edae9b0ab5a26) else (if i<3 then 0x2e2004992ef8745cb5354b8b0d31d4730d431710039df7143a2e61a63a8e61a862e1a960a006bbee2874d4d525cb0d431710d31cc1400d77dc50e9a9aa61a63a8e2e4b861982801aefb8ad4c34c3304114008776df714c56d9a9aa48e83a1a61a8660a82801e1f3bee2b5211434c350c473054136d00341277dc56d9a98698208a004844e2d8adb56cd4d524741d0d3bec330541400f722c57d2b6aa60e869df61982a0a0065bf5b55307434e438ac330541400b2dcbc089dfb7dc5b15a9aa48e83a1a6d98660a828022093bee2b6cd48440810d0d11cc330541400e77dc56d9a96182286a004044e2d8adb1ef5b3535491d07434c350cefb050042c56e2b6aa42383a1aa19df60a00599265844efdbedb56cd4d524741d0d30d4338ac14011b7ec5aa60e86a866e200405a113bf6fb8b62b6d5b11d07434c350cd4b050042df756c56e2b683a1aa19a960a005822efb8adb3521130d430204143447305003889089dfb7dc5b15b6ad9a9aa48e83a1a6198280216fb9162b715b55211c1d0d30cc1400c1980108b5fd1736ca71883b0640a006044bb444afe8b9b6538c41d8320500300877fc5ed9a963a06869828014253e90d0190014487161a12a002992041bedb56cd4d52c751c6450d0d30541400f0f1f4f15b66a58e81a1a6e20053e86fb8b62b6cd4d52c751c4340d0d30541400f776df6d8b66a6a963a8e3221a60a82801a2c3bee2f8bdb010d4b1d03434c1400c129a98680c800a75010e2d8adb56cefb52c751c4340d0d305414010756c57d2b677e8e81a1a6a582a0a0065bf5b51cea9910d3054140092dcc2021dfb7dc5b14a963a8e21a0686982a09b68022093bfe2f6cd4810c740d0d305002c4a63a1a0320029c40438b62b6d5b35354bbec710d03434c15050042c57d2b6aa5df81a1a63982a0a00599267010efdbedb56cd4d52474346430541400f2dc0877edf716c56a6a92388681a1a60a826da008010efdbee2d8adb56cd4b1c4340d0d30541400fb7dd5b16b663a066a61a60a828016308106f990db56cd4d52c751c43434c1505003c3c77edf6d8c86a6a963a8e21a1a60a82801c2c3bf6fb6d5b01054b1d471910d3054110d003c1277edf6dab66a6a90208e3221a21982a0a0078120640d0d010c14007129b88680860a003010e2d8adb1ef5b35354b1d4710d03434413bec140116e00c81a1a77d82800e64996043bf6fb6d5b35354b1d4743441191003edfb16a9a3a06869b8801016810efdbee2d8adb56cc751c4340d0d352c14010755b803206869a960a004010efdbee2d8adb56cd4d524340d0d31cc1400f6e00c81a1a63982800e048190d010411904330500242e0580157f45cdb29c630e81b02801817003afe8b9b6538c21d03605002c310235fd17364a71843a06c0a005819afe8b9b6538c61d03205002876034 else 0x74715a96618e6183a2e4b780142ebbed4b30c730c1d1725bc00a324b70e8f437eb66a6a98698ea3986a19c560a828022213bee2b30c730c1d1730024b73a83a3d1c5b15df6a6b68698ea3986a1982a0a00896f6fd6ceac34c751cc350cc15050031df715a9661860e8b980105b9c41d1e8e2d8ad4d530d3bec756cc350cc15050044c92dcce0e9dfb7eb66a6a9869c563986a1982a0a00896e1d3bf6fb8b62d6d0d352c730d4330541400f2dedf756c5ada1a6a58e61a8660a82801a1e3bee2b52cc31c1d1705cc00a2dc3a3d1c5b15a9aa61a63a8e77d86ad982a0a00816f6fd6d54c3547390e2b0cc15050030b70e9dfb7dc5366c5ada1a63a8e6a58660a8280205bdbee458b5b43547352c330541400c2dc920e9dfb7dc5b16b66a6a98698e61982a0a00816f6fb9162d6d54c34c730cc150500303aaa61aa628e3de86))
def pL37 : PT:=(153,3,7,15,pL37F)
def pH0_37F (i : Nat) : Nat:=0x2ee38020c0c3016033c728809d069c1b3ad100ac76e89e2288815161ce65c2d028e144900400dac2d00d8036206003600d803600db19e00d8036d05e01e00d969c301842060d4036462c03600d803600d803600d803650bd00f00d9aa7408803687adc1d00db8264041419c08403657d003600d8ae700d9425f0454ab709c0368250c2800db2df50c26ab80c403620d0036807c41414b94a300d803677c381600dbc0bf0a600746d282ed0c80369ba409300d80366034036908c99f00d9dcd00d803690aa82ce2a242400db82be7bc0001a043850210a01001400118000000014000040018d
def pH0_37 (h : Nat) : Option (Nat × Nat):=lookupWord 26 118 7 14 6 4 pH0_37F h
def pH1_37F (i : Nat) : Nat:=(if i<3 then (if i<1 then 0x3665077a011486c7480452803f9e099e457be00014056fe0bab4180b0390008a5407d280a5804520008ba02b201c680452417080114b418d00452008a5006ec022900452b014e60864022900452008a400c6d04fe60112008a40114b0143c30ea31723c068b01d5d0162707f4011484018804525052ec03a9415800102a03280114941dce0220103320114802110026330074002af821b501c6f01edc439080cb603df907c8c0400c17390bc4e02d4e070ac0ec1805750354e0544022900017d21de0114ac1c2c48dd008a46021080024027a700864099640e8c84128046e011480229730e7008a480c58022900452c004ee093802292009e502db40094022928310744300114a85c58045201293a0284407080452f02b6c0901c12a40345008a480aa4405ef843de02ae20fb7c22168410800c0008c54041004529030e0114840efe82e98078b00942c06268b292160ee028205af88bb4008a580c2f44e35920a008a4e045dc4dd8045290680203cc0229004523042400b5280bc80452008a40114ac178e035a00000000000002004090040000000201300600004006020018098070000000100402201814000004044038050000080380000a0040980600002800000000004060090080000a01d00201c0000000000002000000004018050020000000000a00c0200102000c060110140000000001404000800000000030060100000000e002004018070080100380000e014010030040080300400000003800030010020200000000000b000000008000000180a00500c0100280100a000008050000000000b0000840100002e0100380000200c008020360000500000000c010000000140600a0260280100200a0700000400c0040000201000001003008014020060040500480001a0000280b01c008018000000000080600801004000016000000030000000000a00c0340000900000c04800002000008110000280000800800002806000000000040000040183000000402801008000000100140740701200002c000010080000000000002c04001000000000010000240001b002000000030100000280900201801000006034008040000400c80200a000028000060180000400601c000000100000180b00201c0000a006000028030080080000003a0100400e00600c03002000008058000060000280400202803802000000000000020180180d00c008010010000200280000001405003004004020080000300280000602000000000000008000000140000002e0000a80a04a0080001000002001801000008070130040000a0000020840580b00e004010000020000001e02c0000081100e040000010020040200e004008008360000040080300200c0080100e0180000d000014008000000180100b00800c0180002000c0780700008800800 else (if i<2 then 0x23580c27017e004529058440a5180bb00452305ec01149009d2027d1012480bc8c1e3f03bc40518c0581c156a81caf00e7c27c581a5d00b58087360fd3c0eab810d607f300a540116382a10047162732c1a72824a607e5610ca086eb0166903d4a0e2bc1d8e0b8fd07e2009696c768005c80505e06e00093c8bc0c060d54378a877700c5004ea01149c1db480bcd010720eec022900452008a401148022900033f14920114a81f800452507a86062a087370b99802de011498049c0370002720114a81c3b840f008a40114802295092f4027120b6c0229004523051a609c081a900452008a401148022900452008a401148802680452008a5205bac088f02d3008a5009c5014d8020870672201e5403370288e02d360794022918086071bc0114a510800268f02d801149c01ce8424b04d6c1104022900452601306066280f9080e9b044c2064d0147a810f705eaa0b7002296822d704b2c000802296012c008a4011480229004520056880334022900452902cf0014940a9804529060fe094802297ba1a902ef40908022900452008a4c0dd0022900452008a401148001a8023d5075e0114b80a3701e1008a5e0f8402290006f008a4011480229602cd8107060e20022978346008a58c3a002290035d2013620c6541bcd83dbb00bb605ed81e1100f4008a562c34022900452f1262a0de80229183cb5067dc0a4fc0d7980de507076101204b1b0401c0368c2de4022900452008a4a107c022950bb8700d2a020141761822b80026011480229701dba17124224541c5f8305600686231641fd901b22000b80bfb8205d8251008a4600a04032180558104b204b8022900452401f880e7c0229608023002060e58809e682cf008a401148022900452008a4c023c02295000e91697403bac1f98831e40752e43b941a2780c9a04bda02ec822680452e10e820f8bcc0600452a065801148022960400008a5a0ce96c75004527076940876c19690b6b008a420cb8003420393e023b66828022900452001b820b30400f581e24102201148014d001f11269a0114801cc804522066801148022970aeb34428c0110022958367008a52269580b900452a06a760dc8405b0085fe08380114a45c1804526006d8088c0229004187029aa01f80229004528013801148c1d5182aca035120cca016ba002c008a5801d1c01bf83cfd0292e0b58022900452008a4a0acc022900452008a40114802290818da173542df201cb80452305a300b008037201bfc0611801240165600c7008a44043b01067833b805da8075fc1a68041400724804ddc0a2da20ab04cd60fd80218283fd804fc0114a005f3801a008a502eac8208b8362008a40236d057ce9217008a40114b0024004527024401148ac7300452008a40114802290833ff06c98013c022900452a06bc8034802294 else 0x380be7c42c9037b917920114940b1e0103008a48043002295010a701b0a05c4022930358200a0303aa81a568286f078d8017fc0be20413008a401149418bc031f008a40114b40b9d03e6901a8601f7403680452008a40114b409400452008a401148022960072008a580c754139b80fa40472c0afd003800452008a40114a013a00452700140114b81ace042ff0310011480229202131025624034022950827c04740114985dcb02c4406982278bc1014838c012d880a29c86f004523036a4011881d1f0a5b704aa0114a400600452b06478035504592005a008a5a0cd700d0009b2117760114a01be08adba1758011480214f042e615af40e900229201c9e019c601d4022948325a06854046002290019d008a5e05eac09a80452008a4c03f441c080452c083b28832c096b0095008a4a0fdc01bf600aa30044a25d98102082d9f12fe80c09009da803d701200114802294a047940900114ac05280bbd9030c00a01401850024008a4a83774808004520018de0045c22200452008a401148003da81ee008a520aa84060b0434a06c3a07edc01038ae5e03d8a0de1807300452f03a74639b8163a8846607d001149c20d9000d008a5a06e5015380452b0640011481c6e8045280309c03640229301b77010b40abc022900452c01b460da9053f90236008a4011480229180d0002522060a0052028e1008a4a095f0130804521047c011480229018ec008a401148022900452008a40114a81f280452008a401148022960bb59058c01148022900452008a401148022900452008a5426a4022950253803780114b818e1005bb0031021040229581e6f044e0114800fb80452008a40114a41cdd0105b05ee60976410088419b04ac421da45ceb808e4025e0283fc0360827c6015f01032c187202a0b000c0112e049c602835053d602b7454308365d0033e07d9015ee84206049180ca9c0d1e813ec08800110c04b76809f20738c2054007400452a01e460554022900452008a401148022900452600f9a044c02291813d1108680d5c04da200f9805e9e10a14523e008dd0682e09ca01ffc88e6008a40114880e630ba0141ca80ea0807c601cba06520114802290880a008a422b2ac0cfb804e507bb4050d41bb002b1403e1806c002291a00fd308d60c8b410e00452008a421125c1c49803e008a5e2b08022908ae74035601148400e88a69021c5e26ac022940230903bd00c0002291043f008a480c2805830045216424403c1853200168008a5c0d1e0465300e0d13a7c0e9e816d281dd2026660be80229403bf0002a011480229380d69022a22d9141930045210663e0f2801d000452008a5c27d285b428970d04760114b00f1e83cd81013e024441f1c0059401f740fb2c47558816008a4e0cbc8023d8351b048b0026b815f1826f1043780a41420d289b6)) else (if i<4 then 0xe28120c821fd00ac011480229589c4008a46883b805710221008a401149c155a0890d1205c0ce00223a82647028f0109fa876b03fc00855210ddc1cd50415008a5c0a2f815720384008a5c0d7c022900452c02ba80826c1ad80452b085a0114802291026e20875200b5017c00452008a4a072004c1b80b2915e8011480229603d71032aa00c80229002c5008a5608bf8521804523035c0114900a7f02d84023ca016040f4804524000001148022900452008a462950401e00452f039de0504022970174603b801148022900452008a5206b50004e829c505972069d804ea00969074a8684c4123103cca0400200ac022900452f019e01148022900452008a4011496c78400d3f07a60114bc5e100452008a4804924178582e4b172420dfc022948099008a401148022900452e05ca0114804a1804524073001148022908260008a500c54022900452008a4e0669407b80452da417a0dd78054580ff2120820480c17378314414ec01148c11ab837d40692a2ce98227a0386c05a542c2e05f478b9f008a40114904e7e013600170a057945bb30377e017e0114944c260299008a5103b6c0ba80452b06780114ac04a000cae02804102b01fac01065084ae07f5802a48291c039ee02c6c2077811f21383a008c81b460808c086ae018f287828089e031d42ef84083980a9a03f5e06cf80ea1ba0b4031e2098b0486102c360667e254fc0bf90b8a203cfa041281eb28b51b0260025d001dd603b79041f0055b4211d0bd18160940a250228a8007c073aa01e3c0b5d81785042a62c6e813c301fe902cb20972803170328b04b00114b452b102843080c01148c05c80452008a4011498206d803b316e0a07fc02297023c7038ec0ba1401ff0125a05be421ae84e6f0426008a4407368142982a8a0591c057385dfc81c0f01d8c02d2c084f03731003800553421e004522119e0114b808dcb214003b40114a806400452a401bc27e8022900452d04140114802290045240742011480229004524012ec0765810580452008a4802c3414e80452c028500bbc022900452707ce00cdb00a660829008a4011480229389d2f178be0b7b421880150016c32108400cf08197a048980d8005d2a03da0118822439015d80452008a401148022900452d043040528c5a400452216b40114941e0004521045240fac05d88818b421c201148c065b82d5c080a01149021c0045242427201940229681e0c13c16210ac15c90327a41e3c10f8811438203506d82089241e2001f8201c96069505d0903b2e03f200850c49b682e20048e01148022900452008a40114802290838f5059c01148022900452307a42c03b45b910042b052401148022900452c05c20114802291807f008a40114802296827fe069ea022cc045001644037b00dc780d300452008a40114a418c604164072 else (if i<5 then 0xa1804525b1ce011480229601c52100fa0bf58108804521049801148022938b05701e2e2ea0022970116716ce01024c030e8b98107bd003b44098c01f3008a420eb802295826ca01c4600e0810b0017e008a46114342240045280043a1139020b9a20b008a460da6016ec80db008a4408a8022900452008a5c0f04807580452008a5806300229004520085601148022938077216e2a0f7044e380452e03248019c022900452008a4ce84c022920b0ab1824011480229004524005da24f4022900452513da609e401d1390e9010060114802291821a008a4e0efb80688817db074de03760181f8126008a5c0c13c223782bc7088be08ce001558148b0184c069241aa00452008a40114bc1b580452401980114bc5baf90f5008a420101c0ad00452500f4e06e90124b0243f129b20f8185c468016606df60bb8022928810008a420c9181c168bcec0167201da587358071008a4c10cc022908b8e4105ce0ad605bd403efd06600114900c8282e04151d6039c40046825b008a520878022960a1d1011001149004620041008a5a0f2005529019c0018140f4600cd804520022020bed412790152a02bf6084141ae004525040f60d40022900452008a4c09a6808cd0185102b00114bc14738277006dce0db40229582325040c002de84f700452008a500f0e04d0a08d1b047f4482d40e0b8313674220114a406180452f0469a035d010bf81d0008a4e07b744eae8161008a5624ff14085830dc04ed6838c022900452c07a1a2403c112804528028801148022900452008a52439ec1e7710ea903ad4060d007f48029108068253ec175f820e10144a2ea681c71aa1d008a401149682400452d0312011480229289570030140145c15d00452307b180450022950026307aaa012c022940402008a420e0002291820500690c05c3420f782e35020240c86419bf01c410547a012ac051d826a104976039581cf58b5c900d401149005318408d127c0114a01ff383ada106d225e4022958281013cc0114b01cac826df038740ac84188c820d607d201148022958363b037c01148022900452b010ea0ee280f580452008a4011480229782c9703d00114b5c7b3221c5119601148022900452103eb20bcf8160809b8e151e0114b0566b8298008a4011480229383b5008a5a00504009480f5a02540114802295000311765a0605c5b600452008a4a05648029e89f8008a5a088941d6780e3f080e01148022900452008a42093402290045210210a2d1c02290030cb00bc01149c1aa80452a003660206c03598394703de403bd81d9d0a74c0549604c80153481b63056dc0fe08151002d0917bc80c3e82266027b008a40003dc0e9001e4331d500caf8091c01ac603532037c809f80452a06adc0bfc02296090ac085960a5901f54829fd0268e00bec1f76844a00760e0a else 0x40c8a014ea079360cf40229281a18125c01148022900452b045c01148022900452008a54042c44ae8045270098a0f64022938312d054b2047000d8a801f008a40002e812f80452008a5e10ec805d109ce008a40114ac09080452008a40114841)))
def pH1_37 (h : Nat) : Option (Nat × Nat):=lookupWord 460 1930 11 19 11 4 pH1_37F h
def pL40F (i : Nat) : Nat:=0x54a390cf4e2ad8741a5c0014df54a184482e2ed8359847001622afd166d298c03a0d020029bea94732105c5db06b3086002ebf459b4a6310e034080096f8e9528e0221b8ab80d20800b0257e8b3694c621d06010014a9472198ab64c208008a66317496a450ac13400ffcb0401ff930802ffa61007fe48200bfe90401ff910802ffa21003fe44200
def pL40 : PT:=(8,2,7,10,pL40F)
def pH0_40F (i : Nat) : Nat:=0x1002400404013c08048060100200400
def pH0_40 (h : Nat) : Option (Nat × Nat):=lookupWord 2 11 4 11 3 4 pH0_40F h
def pH1_40F (i : Nat) : Nat:=0x706c01751058705ed0203059b003d05ca116308974438406506e704bb118010e9088f07d708cf1787024f0189044b08ef054e0609071f01e021eb06d5065a0009050d01b1083d056f0670099117b46084031107992440099b0764040307eb176b02351740063f07a00990099d2238808c11062062170c114a094c0143061a31f700a008b0208104f807bd410d093b0339032f072a221106ad04ca047501a30755045c02c0099f02500999027a019805ba097f07cc76e50360012102bd207f103700e50915030206b205a8005e0084041d078209060392001a17f50660099105100992017b022d1797080f16db05df04d810b6010b0860043e101702a407f3077703f0048502d4710a098f05210739084a004803c816e8544c046a04e004986102070a01c5029010f50424062e02e7096b100502f5013b03aa082c074d069d0090108616f800fe4475708c66ed08fb03b9b205104203d417ed02100950068d053a08db181f04a3038f17ab91fc016000700353a20500c706fd03e61777026a064a00d9092a0347087b01d600ba0153037501fa011505532203119d057902851719002c006e08a105fb085108100051703010c010107022700040327010851010617001420381c060b205015115a4923000201000b0700030509112300000d03045203000b20040c0b0c0e02000529000313
def pH1_40 (h : Nat) : Option (Nat × Nat):=lookupWord 69 214 8 16 8 4 pH1_40F h
def pL : Nat -> PT
  | 24 => pL24
  | 27 => pL27
  | 28 => pL28
  | 30 => pL30
  | 31 => pL31
  | 33 => pL33
  | 34 => pL34
  | 36 => pL36
  | 37 => pL37
  | 40 => pL40
  | _ => ePT
def p0 : Nat -> Nat -> Option (Nat × Nat)
  | 27 => pH0_27
  | 30 => pH0_30
  | 31 => pH0_31
  | 33 => pH0_33
  | 34 => pH0_34
  | 36 => pH0_36
  | 37 => pH0_37
  | 40 => pH0_40
  | _ => fun _ => none
def p1 : Nat -> Nat -> Option (Nat × Nat)
  | 31 => pH1_31
  | 34 => pH1_34
  | 37 => pH1_37
  | 40 => pH1_40
  | _ => fun _ => none
abbrev b27:=bk1 pL p0 p1
abbrev bm27 (k tm s a b : Nat):=@m130 pL p0 p1 k tm s a b
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c24_0 : b27 8 0 0 1=true:=by
  apply csb1 (ar:=9) (d:=0)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
lemma a24 : b27 8 0 0 1=true:=c24_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c27_0 : b27 9 0 0 12=true:=by
  apply csb1 (ar:=10) (d:=0)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
lemma a27 : b27 9 0 0 12=true:=c27_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c28_0 : b27 9 1 0 13=true:=by
  apply csb1 (ar:=9) (d:=1)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
lemma a28 : b27 9 1 0 13=true:=c28_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c30_0 : b27 10 0 0 12=true:=by
  apply csb1 (ar:=10) (d:=0)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c30_12 : b27 10 0 12 37=true:=by
  apply csb1 (ar:=11) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
lemma a30 : b27 10 0 0 49=true:=(bm27 10 0 0 12 37 c30_0 c30_12)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c31_0 : b27 10 1 0 9=true:=by
  apply csb1 (ar:=9) (d:=0)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c31_9 : b27 10 1 9 48=true:=by
  apply csb1 (ar:=10) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c31_57 : b27 10 1 57 48=true:=by
  apply csb1 (ar:=10) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c31_105 : b27 10 1 105 48=true:=by
  apply csb1 (ar:=10) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c31_153 : b27 10 1 153 48=true:=by
  apply csb1 (ar:=10) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c31_201 : b27 10 1 201 48=true:=by
  apply csb1 (ar:=10) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c31_249 : b27 10 1 249 48=true:=by
  apply csb1 (ar:=10) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c31_297 : b27 10 1 297 48=true:=by
  apply csb1 (ar:=10) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c31_345 : b27 10 1 345 48=true:=by
  apply csb1 (ar:=10) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c31_393 : b27 10 1 393 48=true:=by
  apply csb1 (ar:=10) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c31_441 : b27 10 1 441 48=true:=by
  apply csb1 (ar:=10) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c31_489 : b27 10 1 489 24=true:=by
  apply csb1 (ar:=10) (d:=1)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
lemma a31 : b27 10 1 0 513=true:=(bm27 10 1 0 249 264 (bm27 10 1 0 105 144 (bm27 10 1 0 9 96 c31_0 (bm27 10 1 9 48 48 c31_9 c31_57)) (bm27 10 1 105 48 96 c31_105 (bm27 10 1 153 48 48 c31_153 c31_201))) (bm27 10 1 249 144 120 (bm27 10 1 249 48 96 c31_249 (bm27 10 1 297 48 48 c31_297 c31_345)) (bm27 10 1 393 48 72 c31_393 (bm27 10 1 441 48 24 c31_441 c31_489))))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c33_0 : b27 11 0 0 1=true:=by
  apply csb1 (ar:=9) (d:=0)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c33_1 : b27 11 0 1 6=true:=by
  apply csb1 (ar:=10) (d:=0)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c33_7 : b27 11 0 7 20=true:=by
  apply csb1 (ar:=11) (d:=1)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c33_27 : b27 11 0 27 27=true:=by
  apply csb1 (ar:=12) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
lemma a33 : b27 11 0 0 54=true:=(bm27 11 0 0 7 47 (bm27 11 0 0 1 6 c33_0 c33_1) (bm27 11 0 7 20 27 c33_7 c33_27))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_0 : b27 11 1 0 48=true:=by
  apply csb1 (ar:=10) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_48 : b27 11 1 48 48=true:=by
  apply csb1 (ar:=10) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_96 : b27 11 1 96 48=true:=by
  apply csb1 (ar:=10) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_144 : b27 11 1 144 48=true:=by
  apply csb1 (ar:=10) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_192 : b27 11 1 192 4=true:=by
  apply csb1 (ar:=10) (d:=0)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_196 : b27 11 1 196 48=true:=by
  apply csb1 (ar:=11) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_244 : b27 11 1 244 48=true:=by
  apply csb1 (ar:=11) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_292 : b27 11 1 292 48=true:=by
  apply csb1 (ar:=11) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_340 : b27 11 1 340 48=true:=by
  apply csb1 (ar:=11) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_388 : b27 11 1 388 48=true:=by
  apply csb1 (ar:=11) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_436 : b27 11 1 436 48=true:=by
  apply csb1 (ar:=11) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_484 : b27 11 1 484 48=true:=by
  apply csb1 (ar:=11) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_532 : b27 11 1 532 48=true:=by
  apply csb1 (ar:=11) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_580 : b27 11 1 580 48=true:=by
  apply csb1 (ar:=11) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_628 : b27 11 1 628 48=true:=by
  apply csb1 (ar:=11) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_676 : b27 11 1 676 48=true:=by
  apply csb1 (ar:=11) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_724 : b27 11 1 724 48=true:=by
  apply csb1 (ar:=11) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_772 : b27 11 1 772 48=true:=by
  apply csb1 (ar:=11) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_820 : b27 11 1 820 48=true:=by
  apply csb1 (ar:=11) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_868 : b27 11 1 868 48=true:=by
  apply csb1 (ar:=11) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_916 : b27 11 1 916 48=true:=by
  apply csb1 (ar:=11) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_964 : b27 11 1 964 48=true:=by
  apply csb1 (ar:=11) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_1012 : b27 11 1 1012 48=true:=by
  apply csb1 (ar:=11) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c34_1060 : b27 11 1 1060 46=true:=by
  apply csb1 (ar:=11) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
lemma a34 : b27 11 1 0 1106=true:=(bm27 11 1 0 532 574 (bm27 11 1 0 244 288 (bm27 11 1 0 144 100 (bm27 11 1 0 48 96 c34_0 (bm27 11 1 48 48 48 c34_48 c34_96)) (bm27 11 1 144 48 52 c34_144 (bm27 11 1 192 4 48 c34_192 c34_196))) (bm27 11 1 244 144 144 (bm27 11 1 244 48 96 c34_244 (bm27 11 1 292 48 48 c34_292 c34_340)) (bm27 11 1 388 48 96 c34_388 (bm27 11 1 436 48 48 c34_436 c34_484)))) (bm27 11 1 532 288 286 (bm27 11 1 532 144 144 (bm27 11 1 532 48 96 c34_532 (bm27 11 1 580 48 48 c34_580 c34_628)) (bm27 11 1 676 48 96 c34_676 (bm27 11 1 724 48 48 c34_724 c34_772))) (bm27 11 1 820 144 142 (bm27 11 1 820 48 96 c34_820 (bm27 11 1 868 48 48 c34_868 c34_916)) (bm27 11 1 964 48 94 c34_964 (bm27 11 1 1012 48 46 c34_1012 c34_1060)))))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c36_0 : b27 12 0 0 3=true:=by
  apply csb1 (ar:=10) (d:=0)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c36_3 : b27 12 0 3 1=true:=by
  apply csb1 (ar:=11) (d:=0)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
lemma a36 : b27 12 0 0 4=true:=(bm27 12 0 0 3 1 c36_0 c36_3)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c37_0 : b27 12 1 0 30=true:=by
  apply csb1 (ar:=10) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c37_30 : b27 12 1 30 48=true:=by
  apply csb1 (ar:=11) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c37_78 : b27 12 1 78 48=true:=by
  apply csb1 (ar:=11) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c37_126 : b27 12 1 126 27=true:=by
  apply csb1 (ar:=11) (d:=2)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
lemma a37 : b27 12 1 0 153=true:=(bm27 12 1 0 78 75 (bm27 12 1 0 30 48 c37_0 c37_30) (bm27 12 1 78 48 27 c37_78 c37_126))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c40_0 : b27 13 1 0 1=true:=by
  apply csb1 (ar:=9) (d:=0)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma c40_1 : b27 13 1 1 7=true:=by
  apply csb1 (ar:=10) (d:=0)
  simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
lemma a40 : b27 13 1 0 8=true:=(bm27 13 1 0 1 7 c40_0 c40_1)
lemma tables2758 : ∀ k ≤ 13,∀ tm ≤ 1,b27 k tm 0 (pL (3*k+tm)).1=true:=by
  intro k hk tm ht; interval_cases k <;> interval_cases tm
  · exact (rfl : b27 0 0 0 0=true)
  · exact (rfl : b27 0 1 0 0=true)
  · exact (rfl : b27 1 0 0 0=true)
  · exact (rfl : b27 1 1 0 0=true)
  · exact (rfl : b27 2 0 0 0=true)
  · exact (rfl : b27 2 1 0 0=true)
  · exact (rfl : b27 3 0 0 0=true)
  · exact (rfl : b27 3 1 0 0=true)
  · exact (rfl : b27 4 0 0 0=true)
  · exact (rfl : b27 4 1 0 0=true)
  · exact (rfl : b27 5 0 0 0=true)
  · exact (rfl : b27 5 1 0 0=true)
  · exact (rfl : b27 6 0 0 0=true)
  · exact (rfl : b27 6 1 0 0=true)
  · exact (rfl : b27 7 0 0 0=true)
  · exact (rfl : b27 7 1 0 0=true)
  · exact a24
  · exact (rfl : b27 8 1 0 0=true)
  · exact a27
  · exact a28
  · exact a30
  · exact a31
  · exact a33
  · exact a34
  · exact a36
  · exact a37
  · exact (rfl : b27 13 0 0 0=true)
  · exact a40
def wt27 : Nat -> Nat -> Nat -> Row × Row
  | 0,1,0 => (⟨2,by decide⟩,⟨3,by decide⟩)
  | 0,1,1 => (⟨1,by decide⟩,⟨3,by decide⟩)
  | 0,1,2 => (⟨2,by decide⟩,⟨6,by decide⟩)
  | 0,1,3 => (⟨4,by decide⟩,⟨12,by decide⟩)
  | 0,1,4 => (⟨1,by decide⟩,⟨17,by decide⟩)
  | 0,1,5 => (⟨1,by decide⟩,⟨33,by decide⟩)
  | 0,1,6 => (⟨2,by decide⟩,⟨66,by decide⟩)
  | 0,1,7 => (⟨4,by decide⟩,⟨132,by decide⟩)
  | 0,1,8 => (⟨8,by decide⟩,⟨264,by decide⟩)
  | 0,2,0 => (⟨20,by decide⟩,⟨21,by decide⟩)
  | 0,2,1 => (⟨1,by decide⟩,⟨3,by decide⟩)
  | 0,2,2 => (⟨9,by decide⟩,⟨13,by decide⟩)
  | 0,2,3 => (⟨4,by decide⟩,⟨12,by decide⟩)
  | 0,2,4 => (⟨1,by decide⟩,⟨17,by decide⟩)
  | 0,2,5 => (⟨1,by decide⟩,⟨33,by decide⟩)
  | 0,2,6 => (⟨2,by decide⟩,⟨66,by decide⟩)
  | 0,2,7 => (⟨4,by decide⟩,⟨132,by decide⟩)
  | 0,2,8 => (⟨8,by decide⟩,⟨264,by decide⟩)
  | 0,3,0 => (⟨10,by decide⟩,⟨11,by decide⟩)
  | 0,3,1 => (⟨1,by decide⟩,⟨3,by decide⟩)
  | 0,3,2 => (⟨2,by decide⟩,⟨6,by decide⟩)
  | 0,3,3 => (⟨5,by decide⟩,⟨13,by decide⟩)
  | 0,3,4 => (⟨1,by decide⟩,⟨17,by decide⟩)
  | 0,3,5 => (⟨1,by decide⟩,⟨33,by decide⟩)
  | 0,3,6 => (⟨2,by decide⟩,⟨66,by decide⟩)
  | 0,3,7 => (⟨4,by decide⟩,⟨132,by decide⟩)
  | 0,3,8 => (⟨8,by decide⟩,⟨264,by decide⟩)
  | 0,4,0 => (⟨16,by decide⟩,⟨17,by decide⟩)
  | 0,4,1 => (⟨1,by decide⟩,⟨3,by decide⟩)
  | 0,4,2 => (⟨2,by decide⟩,⟨6,by decide⟩)
  | 0,4,3 => (⟨4,by decide⟩,⟨12,by decide⟩)
  | 0,4,4 => (⟨1,by decide⟩,⟨17,by decide⟩)
  | 0,4,5 => (⟨1,by decide⟩,⟨33,by decide⟩)
  | 0,4,6 => (⟨2,by decide⟩,⟨66,by decide⟩)
  | 0,4,7 => (⟨4,by decide⟩,⟨132,by decide⟩)
  | 0,4,8 => (⟨8,by decide⟩,⟨264,by decide⟩)
  | 0,5,0 => (⟨32,by decide⟩,⟨33,by decide⟩)
  | 0,5,1 => (⟨1,by decide⟩,⟨3,by decide⟩)
  | 0,5,2 => (⟨2,by decide⟩,⟨6,by decide⟩)
  | 0,5,3 => (⟨4,by decide⟩,⟨12,by decide⟩)
  | 0,5,4 => (⟨1,by decide⟩,⟨17,by decide⟩)
  | 0,5,5 => (⟨1,by decide⟩,⟨33,by decide⟩)
  | 0,5,6 => (⟨2,by decide⟩,⟨66,by decide⟩)
  | 0,5,7 => (⟨4,by decide⟩,⟨132,by decide⟩)
  | 0,5,8 => (⟨8,by decide⟩,⟨264,by decide⟩)
  | 0,6,0 => (⟨80,by decide⟩,⟨81,by decide⟩)
  | 0,6,1 => (⟨1,by decide⟩,⟨3,by decide⟩)
  | 0,6,2 => (⟨2,by decide⟩,⟨6,by decide⟩)
  | 0,6,3 => (⟨4,by decide⟩,⟨12,by decide⟩)
  | 0,6,4 => (⟨1,by decide⟩,⟨17,by decide⟩)
  | 0,6,5 => (⟨1,by decide⟩,⟨33,by decide⟩)
  | 0,6,6 => (⟨257,by decide⟩,⟨321,by decide⟩)
  | 0,6,7 => (⟨4,by decide⟩,⟨132,by decide⟩)
  | 0,6,8 => (⟨8,by decide⟩,⟨264,by decide⟩)
  | 0,7,0 => (⟨130,by decide⟩,⟨131,by decide⟩)
  | 0,7,1 => (⟨1,by decide⟩,⟨3,by decide⟩)
  | 0,7,2 => (⟨2,by decide⟩,⟨6,by decide⟩)
  | 0,7,3 => (⟨4,by decide⟩,⟨12,by decide⟩)
  | 0,7,4 => (⟨1,by decide⟩,⟨17,by decide⟩)
  | 0,7,5 => (⟨1,by decide⟩,⟨33,by decide⟩)
  | 0,7,6 => (⟨2,by decide⟩,⟨66,by decide⟩)
  | 0,7,7 => (⟨5,by decide⟩,⟨133,by decide⟩)
  | 0,7,8 => (⟨8,by decide⟩,⟨264,by decide⟩)
  | 0,8,0 => (⟨258,by decide⟩,⟨259,by decide⟩)
  | 0,8,1 => (⟨1,by decide⟩,⟨3,by decide⟩)
  | 0,8,2 => (⟨2,by decide⟩,⟨6,by decide⟩)
  | 0,8,3 => (⟨4,by decide⟩,⟨12,by decide⟩)
  | 0,8,4 => (⟨1,by decide⟩,⟨17,by decide⟩)
  | 0,8,5 => (⟨1,by decide⟩,⟨33,by decide⟩)
  | 0,8,6 => (⟨2,by decide⟩,⟨66,by decide⟩)
  | 0,8,7 => (⟨4,by decide⟩,⟨132,by decide⟩)
  | 0,8,8 => (⟨9,by decide⟩,⟨265,by decide⟩)
  | 9,1,0 => (⟨2,by decide⟩,⟨3,by decide⟩)
  | 9,1,1 => (⟨4,by decide⟩,⟨6,by decide⟩)
  | 9,1,2 => (⟨2,by decide⟩,⟨6,by decide⟩)
  | 9,1,3 => (⟨4,by decide⟩,⟨12,by decide⟩)
  | 9,1,4 => (⟨1,by decide⟩,⟨17,by decide⟩)
  | 9,1,5 => (⟨1,by decide⟩,⟨33,by decide⟩)
  | 9,1,6 => (⟨2,by decide⟩,⟨66,by decide⟩)
  | 9,1,7 => (⟨4,by decide⟩,⟨132,by decide⟩)
  | 9,1,8 => (⟨8,by decide⟩,⟨264,by decide⟩)
  | 9,2,0 => (⟨20,by decide⟩,⟨21,by decide⟩)
  | 9,2,1 => (⟨1,by decide⟩,⟨3,by decide⟩)
  | 9,2,2 => (⟨2,by decide⟩,⟨6,by decide⟩)
  | 9,2,3 => (⟨4,by decide⟩,⟨12,by decide⟩)
  | 9,2,4 => (⟨1,by decide⟩,⟨17,by decide⟩)
  | 9,2,5 => (⟨1,by decide⟩,⟨33,by decide⟩)
  | 9,2,6 => (⟨2,by decide⟩,⟨66,by decide⟩)
  | 9,2,7 => (⟨4,by decide⟩,⟨132,by decide⟩)
  | 9,2,8 => (⟨8,by decide⟩,⟨264,by decide⟩)
  | 9,3,0 => (⟨10,by decide⟩,⟨11,by decide⟩)
  | 9,3,1 => (⟨1,by decide⟩,⟨3,by decide⟩)
  | 9,3,2 => (⟨2,by decide⟩,⟨6,by decide⟩)
  | 9,3,3 => (⟨4,by decide⟩,⟨12,by decide⟩)
  | 9,3,4 => (⟨1,by decide⟩,⟨17,by decide⟩)
  | 9,3,5 => (⟨1,by decide⟩,⟨33,by decide⟩)
  | 9,3,6 => (⟨2,by decide⟩,⟨66,by decide⟩)
  | 9,3,7 => (⟨4,by decide⟩,⟨132,by decide⟩)
  | 9,3,8 => (⟨8,by decide⟩,⟨264,by decide⟩)
  | 9,4,0 => (⟨16,by decide⟩,⟨17,by decide⟩)
  | 9,4,1 => (⟨1,by decide⟩,⟨3,by decide⟩)
  | 9,4,2 => (⟨2,by decide⟩,⟨6,by decide⟩)
  | 9,4,3 => (⟨4,by decide⟩,⟨12,by decide⟩)
  | 9,4,4 => (⟨8,by decide⟩,⟨24,by decide⟩)
  | 9,4,5 => (⟨1,by decide⟩,⟨33,by decide⟩)
  | 9,4,6 => (⟨2,by decide⟩,⟨66,by decide⟩)
  | 9,4,7 => (⟨4,by decide⟩,⟨132,by decide⟩)
  | 9,4,8 => (⟨8,by decide⟩,⟨264,by decide⟩)
  | 9,5,0 => (⟨32,by decide⟩,⟨33,by decide⟩)
  | 9,5,1 => (⟨1,by decide⟩,⟨3,by decide⟩)
  | 9,5,2 => (⟨2,by decide⟩,⟨6,by decide⟩)
  | 9,5,3 => (⟨4,by decide⟩,⟨12,by decide⟩)
  | 9,5,4 => (⟨1,by decide⟩,⟨17,by decide⟩)
  | 9,5,5 => (⟨128,by decide⟩,⟨160,by decide⟩)
  | 9,5,6 => (⟨2,by decide⟩,⟨66,by decide⟩)
  | 9,5,7 => (⟨4,by decide⟩,⟨132,by decide⟩)
  | 9,5,8 => (⟨8,by decide⟩,⟨264,by decide⟩)
  | 9,6,0 => (⟨80,by decide⟩,⟨81,by decide⟩)
  | 9,6,1 => (⟨1,by decide⟩,⟨3,by decide⟩)
  | 9,6,2 => (⟨2,by decide⟩,⟨6,by decide⟩)
  | 9,6,3 => (⟨4,by decide⟩,⟨12,by decide⟩)
  | 9,6,4 => (⟨1,by decide⟩,⟨17,by decide⟩)
  | 9,6,5 => (⟨1,by decide⟩,⟨33,by decide⟩)
  | 9,6,6 => (⟨2,by decide⟩,⟨66,by decide⟩)
  | 9,6,7 => (⟨4,by decide⟩,⟨132,by decide⟩)
  | 9,6,8 => (⟨8,by decide⟩,⟨264,by decide⟩)
  | 9,7,0 => (⟨130,by decide⟩,⟨131,by decide⟩)
  | 9,7,1 => (⟨1,by decide⟩,⟨3,by decide⟩)
  | 9,7,2 => (⟨2,by decide⟩,⟨6,by decide⟩)
  | 9,7,3 => (⟨4,by decide⟩,⟨12,by decide⟩)
  | 9,7,4 => (⟨1,by decide⟩,⟨17,by decide⟩)
  | 9,7,5 => (⟨1,by decide⟩,⟨33,by decide⟩)
  | 9,7,6 => (⟨2,by decide⟩,⟨66,by decide⟩)
  | 9,7,7 => (⟨4,by decide⟩,⟨132,by decide⟩)
  | 9,7,8 => (⟨8,by decide⟩,⟨264,by decide⟩)
  | 9,8,0 => (⟨258,by decide⟩,⟨259,by decide⟩)
  | 9,8,1 => (⟨1,by decide⟩,⟨3,by decide⟩)
  | 9,8,2 => (⟨2,by decide⟩,⟨6,by decide⟩)
  | 9,8,3 => (⟨4,by decide⟩,⟨12,by decide⟩)
  | 9,8,4 => (⟨1,by decide⟩,⟨17,by decide⟩)
  | 9,8,5 => (⟨1,by decide⟩,⟨33,by decide⟩)
  | 9,8,6 => (⟨2,by decide⟩,⟨66,by decide⟩)
  | 9,8,7 => (⟨4,by decide⟩,⟨132,by decide⟩)
  | 9,8,8 => (⟨8,by decide⟩,⟨264,by decide⟩)
  | _,_,_ => (⟨0,by decide⟩,⟨0,by decide⟩)

def neg0 : Sig:=neg (inputs.getD 0 zero)
def w27 (a j : Nat) : Sig:=bin true (if a=0 then inputs.getD 0 zero else neg0) (inputs.getD j zero)
def fb27 : List Sig:=inputs ++ [neg0]
def fm27 (a j : Nat) : List Sig:=inputs ++ [neg0,w27 a j]
def nb27 : List Sig:=(inputs.erase (inputs.getD 0 zero)) ++ [neg0]
def ne27 (a j : Nat) : List Sig:=(inputs.erase (inputs.getD 0 zero)) ++ [neg0,w27 a j]

lemma edge_eq_petersen2758 (x : Fin 9 -> Bool) :
    edge x=Binary.PetersenNine.edgeFun Binary.PetersenNine.edges x:=by
  unfold edge Binary.PetersenNine.edgeFun Binary.PetersenNine.edges
  simp [List.any_cons,List.any_nil,Bool.or_assoc]

lemma wit2758_other_ok :
    ([0,9] : List Nat).all (fun a =>
      ([1,2,3,4,5,6,7,8] : List Nat).all (fun j =>
        ([1,2,3,4,5,6,7,8] : List Nat).all (fun i =>
          let p:=wt27 a j i
          (bit p.1 graph != bit p.2 graph) &&
          (fm27 a j).all (fun w => w == inputs.getD i zero||bit p.1 w == bit p.2 w))))=true:=by
  decide +kernel

lemma wit2758_zero_ok :
    ([0,9] : List Nat).all (fun a =>
      ([1,2,3,4,5,6,7,8] : List Nat).all (fun j =>
        let p:=wt27 a j 0
        (bit p.1 graph != bit p.2 graph) &&
        (fm27 a j).all (fun w => w == inputs.getD 0 zero||w == neg0||bit p.1 w == bit p.2 w)))=true:=by
  decide +kernel

lemma validCol2758 (ci : ColumnInfo) (hmem : dead.cols.values.contains ci=true) :
    ValidPool (vars 511) graph ⟨subcube ci.1 ci.2.1,ci.2.2.2.2,0,vars 511⟩:=by
  have hgd:=geomdead
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true] at hgd
  have hslice:=m50 ci (boundsBefore known383) (m4 known383 valid383) (hgd.1.2 ci (List.contains_iff_mem.mp hmem))
  have htgt : chartGoal dead.mask=graph:=by decide +kernel
  rw [htgt] at hslice
  exact m37 (cs:=[]) hslice rfl

lemma cp27 (ci : ColumnInfo) (head : Sig) (rest : List Sig)
    (hmem : dead.cols.values.contains ci=true)
    (heq : choiceVal (0,head,head)=head)
    (hnd0 : decide (head :: rest).Nodup=true)
    (hcut : scalarPoolCut ⟨subcube ci.1 ci.2.1,ci.2.2.2.2,0,vars 511⟩ 13 rest (0,head,head)=true) :
    Impossible graph 13 (head :: rest).toFinset:=by
  have hvp:=validCol2758 ci hmem
  have hnd : (choiceVal (0,head,head) :: rest).Nodup:=by
    rw [heq]; exact of_decide_eq_true hnd0
  have himp:=m9 hvp hnd hcut
  rwa [heq] at himp

lemma r27 (idx : Nat) (hi : idx < 8) :
    I1 graph 13 1 (sS pL 40 idx).toFinset:=by
  have hall:=f1_all pL p0 p1 13 (boundsBefore known383)
    (m4 known383 valid383) geomdead tables2758 13 (by decide) 1 (by decide) idx hi
  have htgt : targetOf dead=graph:=by decide +kernel
  rwa [htgt] at hall

lemma pk27 : autoOK graph ((dead.autos.getD 1 []).map swapRows)=true:=by decide +kernel

lemma npb27 : Impossible graph 13 (inputs.getD 0 zero :: inputs.erase (inputs.getD 0 zero)).toFinset :=
  cp27 (16,0,495,0,13) (inputs.getD 0 zero) (inputs.erase (inputs.getD 0 zero)) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma nbb27 : Impossible graph 13 (neg0 :: inputs).toFinset :=
  cp27 (1,0,510,0,12) neg0 inputs (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma nnb27 : I1 graph 13 1 nb27.toFinset:=by
  have h:=r27 0 (by decide)
  have hs : sameWords (sS pL 40 0) nb27=true:=by decide +kernel
  rwa [m11 hs] at h

lemma nbw27 (a j : Nat) (ha : a ∈ ([0,9] : List Nat)) (hj : j ∈ ([1,2,3,4,5,6,7,8] : List Nat)) :
    Impossible graph 13 (w27 a j :: neg0 :: inputs).toFinset:=by
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at ha hj
  rcases ha with rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact cp27 (1,0,510,0,12) _ (neg0 :: inputs) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma npw27 (a j : Nat) (ha : a ∈ ([0,9] : List Nat)) (hj : j ∈ ([1,2,3,4,5,6,7,8] : List Nat)) :
    I1 graph 13 1 (w27 a j :: inputs).toFinset:=by
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at ha hj
  rcases ha with rfl | rfl
  · rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h:=r27 1 (by decide)
      have hs : sameWords (sS pL 40 1) (w27 0 1 :: inputs)=true:=by decide +kernel
      rwa [m11 hs] at h
    · have h:=r27 3 (by decide)
      have hs : sameWords (sS pL 40 3) (w27 0 2 :: inputs)=true:=by decide +kernel
      rwa [m11 hs] at h
    · have h:=r27 5 (by decide)
      have hs : sameWords (sS pL 40 5) (w27 0 3 :: inputs)=true:=by decide +kernel
      rwa [m11 hs] at h
    · exact i2i1 (cp27 (16,0,495,0,13) (w27 0 4) inputs (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    · have h:=re1 (r27 1 (by decide)) ((dead.autos.getD 1 []).map swapRows) pk27
      have hs : sameWords ((sS pL 40 1).map (movedWord ((dead.autos.getD 1 []).map swapRows).reverse)) (w27 0 5 :: inputs)=true:=by decide +kernel
      rwa [m11 hs] at h
    · exact i2i1 (cp27 (64,0,447,0,13) (w27 0 6) inputs (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    · exact i2i1 (cp27 (128,0,383,0,13) (w27 0 7) inputs (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    · have h:=re1 (r27 3 (by decide)) ((dead.autos.getD 1 []).map swapRows) pk27
      have hs : sameWords ((sS pL 40 3).map (movedWord ((dead.autos.getD 1 []).map swapRows).reverse)) (w27 0 8 :: inputs)=true:=by decide +kernel
      rwa [m11 hs] at h
  · rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact i2i1 (cp27 (1,0,510,0,12) _ inputs (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

lemma nne27 (a j : Nat) (ha : a ∈ ([0,9] : List Nat)) (hj : j ∈ ([1,2,3,4,5,6,7,8] : List Nat)) :
    I1 graph 13 1 (ne27 a j).toFinset:=by
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at ha hj
  rcases ha with rfl | rfl
  · rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h:=r27 2 (by decide)
      have hs : sameWords (sS pL 40 2) (ne27 0 1)=true:=by decide +kernel
      rwa [m11 hs] at h
    · have h:=r27 4 (by decide)
      have hs : sameWords (sS pL 40 4) (ne27 0 2)=true:=by decide +kernel
      rwa [m11 hs] at h
    · have h:=r27 6 (by decide)
      have hs : sameWords (sS pL 40 6) (ne27 0 3)=true:=by decide +kernel
      rwa [m11 hs] at h
    · have himp:=cp27 (17,0,494,0,11) (w27 0 4) nb27 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      have hs : sameWords (w27 0 4 :: nb27) (ne27 0 4)=true:=by decide +kernel
      rw [m11 hs] at himp; exact i2i1 himp
    · have h:=re1 (r27 2 (by decide)) ((dead.autos.getD 1 []).map swapRows) pk27
      have hs : sameWords ((sS pL 40 2).map (movedWord ((dead.autos.getD 1 []).map swapRows).reverse)) (ne27 0 5)=true:=by decide +kernel
      rwa [m11 hs] at h
    · have h:=r27 7 (by decide)
      have hs : sameWords (sS pL 40 7) (ne27 0 6)=true:=by decide +kernel
      rwa [m11 hs] at h
    · have h:=re1 (r27 7 (by decide)) ((dead.autos.getD 1 []).map swapRows) pk27
      have hs : sameWords ((sS pL 40 7).map (movedWord ((dead.autos.getD 1 []).map swapRows).reverse)) (ne27 0 7)=true:=by decide +kernel
      rwa [m11 hs] at h
    · have h:=re1 (r27 4 (by decide)) ((dead.autos.getD 1 []).map swapRows) pk27
      have hs : sameWords ((sS pL 40 4).map (movedWord ((dead.autos.getD 1 []).map swapRows).reverse)) (ne27 0 8)=true:=by decide +kernel
      rwa [m11 hs] at h
  · have k9 : ∀ j : Nat, choiceVal (0,w27 9 j,w27 9 j)=w27 9 j -> (w27 9 j :: nb27).Nodup -> scalarPoolCut (subcube 1 0,12,0,vars 511) 13 nb27 (0,w27 9 j,w27 9 j)=true -> sameWords (w27 9 j :: nb27) (ne27 9 j)=true -> I1 graph 13 1 (ne27 9 j).toFinset:=fun j h1 h2 h3 h4 => i2i1 ((m11 h4) ▸ cp27 (1,0,510,0,12) (w27 9 j) nb27 (by decide +kernel) h1 (decide_eq_true h2) h3)
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact k9 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact k9 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact k9 3 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact k9 4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact k9 5 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact k9 6 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact k9 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact k9 8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

lemma same_on_live {T k t S} (h : Live T k t S) (r1 r2 : Row)
    (hs : ∀ v ∈ S,bit r1 v=bit r2 v) : bit r1 T=bit r2 T:=by
  induction h using Live.recurse with
  | stop => exact hs _ (Finset.mem_singleton_self _)
  | unary _ _ _ ih =>
    apply ih; intro v hv; simp only [Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · simp only [bit_neg,hs _ (Finset.mem_insert_self _ _)]
    · exact hs _ (Finset.mem_insert_of_mem hv)
  | binary _ _ _ _ _ ih =>
    apply ih; intro v hv; simp only [Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · simp only [bit_bin,hs _ (Finset.mem_insert_self _ _),
        hs _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))]
    · exact hs _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv))

lemma kill2758 {a j : Nat} (ha : a ∈ ([0,9] : List Nat)) (hj : j ∈ ([1,2,3,4,5,6,7,8] : List Nat))
    {k t S} (hk : k ≤ 13) (ht : t ≤ 1) (h : Live graph k t S) (sub : ∀ v ∈ S,v ∈ fm27 a j) : False:=by
  have hother : ∀ i : Fin 9,i.val ≠ 0 -> inputs.getD i.val zero ∈ S:=by
    intro i hi
    have hiMem : i.val ∈ ([1,2,3,4,5,6,7,8] : List Nat):=by simp; omega
    have h0:=List.all_eq_true.mp wit2758_other_ok a ha
    have h1:=List.all_eq_true.mp h0 j hj
    have hh:=List.all_eq_true.mp h1 i.val hiMem
    simp only [Bool.and_eq_true,bne_iff_ne] at hh
    have h2:=List.all_eq_true.mp hh.2
    exact m32 h _ _ sub (wt27 a j i.val).1 (wt27 a j i.val).2 hh.1 (fun w hw hn => by
      have ha':=h2 w hw
      have hne : (w == inputs.getD i.val zero)=false:=beq_eq_false_iff_ne.mpr hn
      rw [hne] at ha'; simp only [Bool.false_or] at ha'; exact beq_iff_eq.mp ha')
  have hzero : inputs.getD 0 zero ∈ S ∨ neg0 ∈ S:=by
    by_contra hneither
    push Not at hneither
    have h0:=List.all_eq_true.mp wit2758_zero_ok a ha
    have hh:=List.all_eq_true.mp h0 j hj
    simp only [Bool.and_eq_true,bne_iff_ne] at hh
    have h2:=List.all_eq_true.mp hh.2
    have hsub : ∀ v ∈ S,bit (wt27 a j 0).1 v=bit (wt27 a j 0).2 v:=by
      intro v hv
      have ha':=h2 v (sub v hv)
      have hn1 : (v == inputs.getD 0 zero)=false:=beq_eq_false_iff_ne.mpr (fun e => hneither.1 (e ▸ hv))
      have hn2 : (v == neg0)=false:=beq_eq_false_iff_ne.mpr (fun e => hneither.2 (e ▸ hv))
      rw [hn1,hn2] at ha'; simp only [Bool.false_or] at ha'; exact beq_iff_eq.mp ha'
    exact hh.1 (same_on_live h _ _ hsub)
  by_cases h0 : inputs.getD 0 zero ∈ S
  · have haveIn : inputs.toFinset ⊆ S:=by
      intro v hv
      have hm:=List.mem_toFinset.mp hv
      rw [← m38,List.mem_ofFn] at hm
      obtain ⟨i,rfl⟩:=hm
      by_cases hi : i.val=0
      · rw [hi]; exact h0
      · exact hother i hi
    by_cases h9 : neg0 ∈ S
    · by_cases h10 : w27 a j ∈ S
      · have eqS : S=(w27 a j :: neg0 :: inputs).toFinset:=by
          apply Finset.Subset.antisymm
          · intro v hv
            have hm:=sub v hv
            simp only [fm27,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hm
            rcases hm with hm | rfl | rfl <;> simp [*]
          · intro v hv
            simp only [List.toFinset_cons,Finset.mem_insert] at hv
            rcases hv with rfl | rfl | hv
            · exact h10
            · exact h9
            · exact haveIn hv
        exact nbw27 a j ha hj k t hk (eqS ▸ h)
      · have eqS : S=(neg0 :: inputs).toFinset:=by
          apply Finset.Subset.antisymm
          · intro v hv
            have hm:=sub v hv
            simp only [fm27,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hm
            rcases hm with hm | rfl | rfl
            · simp [hm]
            · simp
            · exact False.elim (h10 hv)
          · intro v hv
            simp only [List.toFinset_cons,Finset.mem_insert] at hv
            rcases hv with rfl | hv
            · exact h9
            · exact haveIn hv
        exact nbb27 k t hk (eqS ▸ h)
    · by_cases h10 : w27 a j ∈ S
      · have eqS : S=(w27 a j :: inputs).toFinset:=by
          apply Finset.Subset.antisymm
          · intro v hv
            have hm:=sub v hv
            simp only [fm27,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hm
            rcases hm with hm | rfl | rfl
            · simp [hm]
            · exact False.elim (h9 hv)
            · simp
          · intro v hv
            simp only [List.toFinset_cons,Finset.mem_insert] at hv
            rcases hv with rfl | hv
            · exact h10
            · exact haveIn hv
        exact npw27 a j ha hj k t hk ht (eqS ▸ h)
      · have eqS : S=(inputs.getD 0 zero :: inputs.erase (inputs.getD 0 zero)).toFinset:=by
          apply Finset.Subset.antisymm
          · intro v hv
            have hm:=sub v hv
            simp only [fm27,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hm
            rcases hm with hm | rfl | rfl
            · by_cases hv0 : v=inputs.getD 0 zero
              · subst hv0; simp
              · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ ((List.mem_erase_of_ne hv0).mpr hm))
            · exact False.elim (h9 hv)
            · exact False.elim (h10 hv)
          · intro v hv
            simp only [List.toFinset_cons,Finset.mem_insert] at hv
            rcases hv with rfl | hv
            · exact h0
            · exact haveIn (List.mem_toFinset.mpr (List.mem_of_mem_erase (List.mem_toFinset.mp hv)))
        exact npb27 k t hk (eqS ▸ h)
  · have h9 : neg0 ∈ S:=hzero.resolve_left h0
    have hnd : inputs.Nodup:=of_decide_eq_true (by decide +kernel : decide inputs.Nodup=true)
    have hbaseSub : (inputs.erase (inputs.getD 0 zero)).toFinset ⊆ S:=by
      intro v hv
      have hm:=List.mem_toFinset.mp hv
      have hm':=List.mem_of_mem_erase hm
      have hne0 : v ≠ inputs.getD 0 zero:=fun e => hnd.not_mem_erase (e ▸ hm)
      rw [← m38,List.mem_ofFn] at hm'
      obtain ⟨i,rfl⟩:=hm'
      exact hother i (fun hi => hne0 (by rw [hi]))
    by_cases h10 : w27 a j ∈ S
    · have eqS : S=(ne27 a j).toFinset:=by
        apply Finset.Subset.antisymm
        · intro v hv
          have hm:=sub v hv
          simp only [fm27,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hm
          rcases hm with hm | rfl | rfl
          · have hne : v ≠ inputs.getD 0 zero:=fun e => h0 (e ▸ hv)
            exact List.mem_toFinset.mpr (List.mem_append_left _ ((List.mem_erase_of_ne hne).mpr hm))
          · exact List.mem_toFinset.mpr (List.mem_append_right _ (by simp))
          · exact List.mem_toFinset.mpr (List.mem_append_right _ (by simp))
        · intro v hv
          have hm:=List.mem_toFinset.mp hv
          simp only [ne27,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hm
          rcases hm with hm | rfl | rfl
          · exact hbaseSub (List.mem_toFinset.mpr hm)
          · exact h9
          · exact h10
      exact nne27 a j ha hj k t hk ht (eqS ▸ h)
    · have eqS : S=nb27.toFinset:=by
        apply Finset.Subset.antisymm
        · intro v hv
          have hm:=sub v hv
          simp only [fm27,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hm
          rcases hm with hm | rfl | rfl
          · have hne : v ≠ inputs.getD 0 zero:=fun e => h0 (e ▸ hv)
            exact List.mem_toFinset.mpr (List.mem_append_left _ ((List.mem_erase_of_ne hne).mpr hm))
          · exact List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_singleton_self _))
          · exact False.elim (h10 hv)
        · intro v hv
          have hm:=List.mem_toFinset.mp hv
          simp only [nb27,List.mem_append,List.mem_singleton] at hm
          rcases hm with hm | rfl
          · exact hbaseSub (List.mem_toFinset.mpr hm)
          · exact h9
      exact nnb27 k t hk ht (eqS ▸ h)

lemma noPair2758 (a b : Nat) (ha : a ∈ ([0,9] : List Nat)) (hb : b < 10)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C) (hsz : C.size ≤ 13)
    (hno : ∀ x : Fin 9 -> Bool,
      let x9:=List.ofFn x ++ [!x 0]
      C.eval (x9 ++ [x9.getD a false||x9.getD b false])=edge x) : False:=by
  let g0 : Gate:=⟨.not,[0]⟩
  let g1 : Gate:=⟨.or,[a,b]⟩
  let Cfull : Circuit:=⟨g0 :: g1 :: C.gates,C.output⟩
  have hfanFull : PEqualNP.MetaComplexity.FanInTwo Cfull:=by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨by simp [g0],by simp [g0]⟩
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨by simp [g1],by simp [g1]⟩
      · exact legal g hg
  have hstep (x : Fin 9 -> Bool) :
      Cfull.eval (List.ofFn x) =
        (let x9:=List.ofFn x ++ [!x 0]; C.eval (x9 ++ [x9.getD a false||x9.getD b false])):=by
    simp only [Circuit.eval,Circuit.wires,Cfull,List.foldl_cons,g0,g1,GateOp.eval,
      List.map_cons,List.map_nil,List.headD,List.any_cons,List.any_nil,id,Bool.or_false]
    have h0 : (List.ofFn x).getD 0 false=x 0:=by
      rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp
    rw [h0]
  have hcomp : ∀ x : Fin 9 -> Bool,Cfull.eval (List.ofFn x)=Binary.PetersenNine.edgeFun Binary.PetersenNine.edges x:=by
    intro x; rw [hstep x]; exact (hno x).trans (edge_eq_petersen2758 x)
  have hlow:=Binary.petersen_binary_lower Cfull hfanFull hcomp
  have hnn : Binary.CircuitProof.nonNotCount Cfull.gates=1 + Binary.CircuitProof.nonNotCount C.gates:=by
    change List.countP (fun q => !Binary.CircuitProof.isNotGate q.op) (g0 :: g1 :: C.gates) =
      1 + List.countP (fun q => !Binary.CircuitProof.isNotGate q.op) C.gates
    rw [List.countP_cons,List.countP_cons]
    have h0 : (!Binary.CircuitProof.isNotGate g0.op)=false:=rfl
    have h1 : (!Binary.CircuitProof.isNotGate g1.op)=true:=rfl
    rw [h0,h1]; simp; omega
  rw [hnn] at hlow
  have hbound:=Binary.nonNotCount_add_notCount C.gates
  change Binary.CircuitProof.nonNotCount C.gates + (C.gates.filter fun q => Binary.CircuitProof.isNotGate q.op).length=C.gates.length at hbound
  have hfeq : (fun q : Gate => isNotT q.op)=(fun q : Gate => Binary.CircuitProof.isNotGate q.op):=by
    funext q; cases q.op <;> rfl
  have hcntEq : C.gates.countP (fun q => isNotT q.op)=(C.gates.filter fun q => Binary.CircuitProof.isNotGate q.op).length:=by
    rw [List.countP_eq_length_filter,hfeq]
  have hlen : C.gates.length ≤ 13:=hsz
  have ht1 : C.gates.countP (fun q => isNotT q.op) ≤ 1:=by omega
  have hbit_neg0 (r : Row) : bit r neg0=!(sample r 0):=by simp only [neg0,bit_neg,sample]; rfl
  have hgetD_x9 (r : Row) (idx : Nat) (hidx : idx < 10) :
      ((List.ofFn (sample r) ++ [!sample r 0]).getD idx false)=bit r (if idx < 9 then inputs.getD idx zero else neg0):=by
    by_cases h9 : idx < 9
    · rw [if_pos h9,List.getD_eq_getElem?_getD,List.getElem?_append_left (by simp [h9]),List.getElem?_ofFn]
      simp [h9,sample]
    · have hi9 : idx=9:=by omega
      subst hi9
      rw [if_neg (by omega),List.getD_eq_getElem?_getD,List.getElem?_append_right (by simp)]
      simp [hbit_neg0]
  let wa : Sig:=if a=0 then inputs.getD 0 zero else neg0
  let wb : Sig:=if b < 9 then inputs.getD b zero else neg0
  let w : Sig:=bin true wa wb
  let bank : List Sig:=inputs ++ [neg0,w]
  have ha_eq : wa=(if a < 9 then inputs.getD a zero else neg0):=by
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at ha
    rcases ha with rfl | rfl <;> simp [wa]
  have goalEq : (execute C.gates bank).getD C.output zero=graph:=by
    apply BitVec.eq_of_getLsbD_eq
    intro m hm
    let r : Row:=⟨m,hm⟩
    change bit r ((execute C.gates bank).getD C.output zero)=bit r graph
    rw [← b_read,m47 _ _ _ (fun g hg => (legal g hg).1)]
    have hmap : bank.map (bit r) =
        (List.ofFn (sample r) ++ [!sample r 0]) ++
        [(List.ofFn (sample r) ++ [!sample r 0]).getD a false ||
         (List.ofFn (sample r) ++ [!sample r 0]).getD b false]:=by
      have ha10 : a < 10:=by simp only [List.mem_cons,List.mem_nil_iff,or_false] at ha; rcases ha with rfl | rfl <;> omega
      simp only [bank,List.map_append,List.map_cons,List.map_nil,← sampled,hbit_neg0,w,bit_bin,ite_true]
      rw [hgetD_x9 r a ha10,hgetD_x9 r b hb,← ha_eq]; rfl
    rw [hmap]
    exact (hno (sample r)).trans (edge_table r).symm
  have out:=get_rep (execute C.gates bank) C.output
  rw [goalEq] at out
  have targetIn:=out.resolve_right (fun hn => hn m76)
  obtain ⟨k,t,S,hk,ht,run,hs⟩:=extractT C.gates bank legal m76 targetIn
  by_cases hb0 : b=0
  · subst hb0
    have hsub : ∀ v ∈ S,v ∈ fm27 0 1:=by
      intro v hv
      have hm:=hs v hv
      simp only [bank,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hm
      rcases hm with hm | rfl | rfl
      · exact List.mem_append_left _ hm
      · exact List.mem_append_right _ (by simp)
      · have hp:=m22 run w hv
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at ha
        rcases ha with rfl | rfl
        · have hw0 : w=inputs.getD 0 zero:=by decide +kernel
          rw [hw0]; exact List.mem_append_left _ (by decide +kernel : inputs.getD 0 zero ∈ inputs)
        · have hw1 : w=one:=by decide +kernel
          rw [hw1] at hp; exact False.elim (hp.2 rfl)
    exact kill2758 (by simp) (by simp) (hk.trans hlen) (ht.trans ht1) run hsub
  · by_cases hb9 : b=9
    · subst hb9
      have hsub : ∀ v ∈ S,v ∈ fm27 0 1:=by
        intro v hv
        have hm:=hs v hv
        simp only [bank,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hm
        rcases hm with hm | rfl | rfl
        · exact List.mem_append_left _ hm
        · exact List.mem_append_right _ (by simp)
        · have hp:=m22 run w hv
          simp only [List.mem_cons,List.mem_nil_iff,or_false] at ha
          rcases ha with rfl | rfl
          · have hw1 : w=one:=by decide +kernel
            rw [hw1] at hp; exact False.elim (hp.2 rfl)
          · have hw9 : w=neg0:=by decide +kernel
            rw [hw9]; exact List.mem_append_right _ (by simp)
      exact kill2758 (by simp) (by simp) (hk.trans hlen) (ht.trans ht1) run hsub
    · have hbm : b ∈ ([1,2,3,4,5,6,7,8] : List Nat):=by simp; omega
      have hblt : b < 9:=by omega
      have hw_eq : w=w27 a b:=by simp only [w,wa,wb,if_pos hblt,w27]
      have hsub : ∀ v ∈ S,v ∈ fm27 a b:=by
        intro v hv; simpa only [bank,hw_eq,fm27] using hs v hv
      exact kill2758 ha hbm (hk.trans hlen) (ht.trans ht1) run hsub

end PEqualNP.Outside.L_meta_4528_aux

open PEqualNP.Outside.L_meta_4528_aux
theorem PEqualNP.Outside.L_meta_4528 : ∀ (x1 : Fin (9 : ℕ)), x1 = (1 : Fin (9 : ℕ)) ∨ x1 = (6 : Fin (9 : ℕ)) → ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 x1]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro j _ C basis small
  by_contra none
  push Not at none
  apply PEqualNP.Outside.L_meta_4528_aux.noPair2758 0 j.val (by simp) (by omega) C basis small
  intro x
  have pin (i : Fin 9) : (List.ofFn x ++ [!x 0]).getD i.val false = x i := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp), List.getElem?_ofFn]
    simp
  change C.eval ((List.ofFn x ++ [!x 0]) ++ [((List.ofFn x ++ [!x 0]).getD 0 false) || (List.ofFn x ++ [!x 0]).getD j.val false]) = edge x
  rw [show 0 = (0 : Fin 9).val by rfl, pin, pin]
  exact none x
