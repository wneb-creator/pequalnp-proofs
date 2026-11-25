import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_5012
abbrev Z0 :=@Finset.mem_filter
abbrev Z1 :=@decide_eq_true_eq
abbrev Z2 :=@Finset.mem_sdiff
abbrev Z3 :=@Finset.mem_singleton
abbrev Z4 :=@Finset.mem_union
abbrev Z5 :=@Finset.mem_inter
abbrev Z6 :=@Finset.mem_insert
abbrev Z7 :=@Finset.mem_univ
abbrev Z8 :=@List.getD_eq_getElem?_getD
abbrev Z9 :=@Finset.mem_range
abbrev Z10 :=@List.mem_cons
abbrev Z11 :=@List.not_mem_nil
abbrev Z12 :=@Bool.and_eq_true
abbrev Z13 :=@Bool.or_eq_true
abbrev Z14 :=@Bool.eq_false_iff
abbrev Z15 :=@List.map_cons
abbrev Z16 :=@List.map_nil
abbrev Z17 :=@List.length_append
abbrev Z18 :=@Finset.mem_product
abbrev Z19 :=@Finset.mem_image
abbrev Z20 :=@Finset.card_empty
abbrev Z24 :=@Finset.card_insert_of_notMem
abbrev Z25 :=@Finset.not_nonempty_iff_eq_empty
namespace N5
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo
lemma z019 {α:Type} [DecidableEq α] {A B:Finset α} (h:A⊆ B):
  (B \ A).card=B.card - A.card:=by
 rw [Finset.card_sdiff,Finset.inter_eq_left.mpr h]
lemma z065 (gs:List Gate) (acc:List Bool):
  (gs.foldl (fun w g=>w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) acc).length=
   acc.length+gs.length:=by
 induction gs generalizing acc with
 | nil=>simp
 | cons g gs ih=>
  simp only [List.foldl_cons,ih,Z17,List.length_cons,List.length_nil]
  omega
lemma z064 (gs:List Gate) (acc:List Bool) (i:ℕ) (hi:i < acc.length):
  (gs.foldl (fun w g=>w++[g.op.eval (g.inputs.map fun k=>w.getD k false)]) acc).getD i false=
   acc.getD i false:=by
 induction gs generalizing acc with
 | nil=>rfl
 | cons g gs ih=>
  simp only [List.foldl_cons]
  have hlt:i < (acc++[g.op.eval (g.inputs.map fun k=>acc.getD k false)]).length:=by
   simp only [Z17,List.length_singleton];omega
  rw [ih _ hlt]
  simp only [Z8,List.getElem?_append_left hi]
lemma z063 (gs:List Gate) (acc:List Bool) (j:ℕ) (hj:j < gs.length)
  (q9a:∀ k∈ gs[j].inputs,k < acc.length+j):
  (gs.foldl (fun w g=>w++[g.op.eval (g.inputs.map fun k=>w.getD k false)]) acc).getD
    (acc.length+j) false=
   gs[j].op.eval (gs[j].inputs.map fun k=>
    (gs.foldl (fun w g=>w++[g.op.eval (g.inputs.map fun m=>w.getD m false)]) acc).getD
     k false):=by
 induction gs generalizing acc j with
 | nil=>cases hj
 | cons g gs ih=>
  cases j with
  | zero=>
   simp only [Nat.add_zero,List.foldl_cons,List.getElem_cons_zero] at q9a ⊢
   set acc':=acc++[g.op.eval (g.inputs.map fun k=>acc.getD k false)]
   have q5v:acc.length < acc'.length:=by
    simp only [acc',Z17,List.length_singleton];omega
   rw [z064 gs acc' acc.length q5v]
   have qg6:acc'.getD acc.length false=g.op.eval (g.inputs.map fun k=>acc.getD k false):=by
    simp only [acc',Z8,List.getElem?_append_right (le_refl _),
     Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
   rw [qg6]
   congr 1
   apply List.map_congr_left
   intro k hk
   have hka:k < acc.length:=q9a k hk
   have qns:k < acc'.length:=by omega
   rw [z064 gs acc' k qns]
   simp only [acc',Z8,List.getElem?_append_left hka]
  | succ j'=>
   simp only [List.foldl_cons,List.getElem_cons_succ]
   set acc':=acc++[g.op.eval (g.inputs.map fun k=>acc.getD k false)]
   have qg7:acc'.length=acc.length+1:=by
    simp only [acc',Z17,List.length_singleton]
   have hj':j' < gs.length:=by simp only [List.length_cons] at hj;omega
   have q92:acc.length+(j'+1)=acc'.length+j':=by omega
   rw [q92]
   apply ih acc' j' hj'
   intro k hk
   have hbk:=q9a k (by simpa using hk)
   omega
lemma z137 (C:Circuit) (x:List Bool):
  (C.wires x).length=x.length+C.gates.length:=
 z065 C.gates x
lemma z144 {n:ℕ} (C:Circuit) (x:Fin n→ Bool) (i:ℕ) (hi:i < n):
  wval C x i=x ⟨i,hi⟩:=by
 unfold wval Circuit.wires
 have hlt:i < (List.ofFn x).length:=by simp [hi]
 rw [z064 C.gates (List.ofFn x) i hlt]
 simp [Z8,hi]
lemma z070 {n:ℕ} (C:Circuit) (j:ℕ) (x:Fin n→ Bool):
 gateVal n C j x=wval C x (n+j):=rfl
lemma z143 {n:ℕ} (C:Circuit) (x:Fin n→ Bool) {w:ℕ} (hw:n+C.gates.length≤ w):
  wval C x w=false:=by
 unfold wval
 rw [Z8]
 have q5v:(C.wires (List.ofFn x)).length=n+C.gates.length:=by
  rw [z137,List.length_ofFn]
 rw [List.getElem?_eq_none (by omega)]
 rfl
lemma z068 {C:Circuit} {j:ℕ} (hj:j < C.gates.length):
  gateAt C j=C.gates[j]:=by
 unfold gateAt
 simp [Z8,hj]
lemma z069 {C:Circuit} {j:ℕ} (hj:j < C.gates.length):
  gateAt C j∈ C.gates:=by
 rw [z068 hj];exact List.getElem_mem hj
lemma z071 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) {j:ℕ} (hj:j < C.gates.length):
  (gateAt C j).inputs=[opnd C j 0,opnd C j 1]:=by
 have q5v:(gateAt C j).inputs.length=2:=hAO.2.2 _ (z069 hj)
 unfold opnd
 match h:(gateAt C j).inputs with
 | [a,b]=>simp
 | []=>rw [h] at q5v;simp at q5v
 | [_]=>rw [h] at q5v;simp at q5v
 | _::_::_::_=>rw [h] at q5v;simp at q5v
lemma z105 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) {j:ℕ} (hj:j < C.gates.length) (b:Fin 2):
  opnd C j b∈ (gateAt C j).inputs:=by
 rw [z071 hAO hj]
 fin_cases b <;> simp
lemma z104 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) {j:ℕ} (hj:j < C.gates.length) (b:Fin 2):
  opnd C j b < n+j:=
 hAO.2.1 j hj _ (z105 hAO hj b)
lemma z141 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (x:Fin n→ Bool)
  {j:ℕ} (hj:j < C.gates.length):
  wval C x (n+j)=(gateAt C j).op.eval [wval C x (opnd C j 0),wval C x (opnd C j 1)]:=by
 unfold wval Circuit.wires
 have q5v:(List.ofFn x).length=n:=List.length_ofFn
 have q9a:∀ k∈ C.gates[j].inputs,k < (List.ofFn x).length+j:=by
  intro k hk;rw [q5v,← z068 hj] at *;exact hAO.2.1 j hj k hk
 have h:=z063 C.gates (List.ofFn x) j hj q9a
 rw [q5v] at h
 rw [h,← z068 hj,z071 hAO hj]
 simp
lemma z140 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (x:Fin n→ Bool)
  {j:ℕ} (hj:j < C.gates.length) (hop:(gateAt C j).op=GateOp.and):
  wval C x (n+j)=(wval C x (opnd C j 0) && wval C x (opnd C j 1)):=by
 rw [z141 hAO x hj,hop];simp [GateOp.eval]
lemma z142 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (x:Fin n→ Bool)
  {j:ℕ} (hj:j < C.gates.length) (hop:(gateAt C j).op=GateOp.or):
  wval C x (n+j)=(wval C x (opnd C j 0) || wval C x (opnd C j 1)):=by
 rw [z141 hAO x hj,hop];simp [GateOp.eval]
lemma z138 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C):
  ∀ w < n+C.gates.length,wval C (fun _:Fin n=>true) w=true:=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih=>
  intro hw
  by_cases hwn:w < n
  ·rw [z144 C _ w hwn]
  ·have hj:w - n < C.gates.length:=by omega
   have q0f:w=n+(w - n):=by omega
   rw [q0f]
   have hop:=hAO.1 _ (z069 hj)
   have h0:opnd C (w - n) 0 < w:=by have:=z104 hAO hj 0;omega
   have h1:opnd C (w - n) 1 < w:=by have:=z104 hAO hj 1;omega
   have hv0:=ih _ h0 (by omega)
   have hv1:=ih _ h1 (by omega)
   rcases hop with q17 | hor
   ·rw [z140 hAO _ hj q17,hv0,hv1];rfl
   ·rw [z142 hAO _ hj hor,hv0,hv1];rfl
lemma z059 (n:ℕ) (gs:List Gate) (acc:List (List ℕ)):
  (gs.foldl (coneStep n) acc).length=acc.length+gs.length:=by
 induction gs generalizing acc with
 | nil=>simp
 | cons g gs ih=>
  simp only [List.foldl_cons,ih,coneStep,Z17,List.length_cons,List.length_nil]
  omega
lemma z058 (n:ℕ) (gs:List Gate) (acc:List (List ℕ)) (i:ℕ) (hi:i < acc.length):
  (gs.foldl (coneStep n) acc).getD i []=acc.getD i []:=by
 induction gs generalizing acc with
 | nil=>rfl
 | cons g gs ih=>
  simp only [List.foldl_cons]
  have hlt:i < (coneStep n acc g).length:=by
   simp only [coneStep,Z17,List.length_singleton];omega
  rw [ih _ hlt]
  simp only [coneStep,Z8,List.getElem?_append_left hi]
lemma z025 (n:ℕ) (C:Circuit):(cones n C).length=C.gates.length:=by
 unfold cones;rw [z059];simp
lemma z057 (n:ℕ) (gs:List Gate) (acc:List (List ℕ)) (j:ℕ) (hj:j < gs.length):
  (gs.foldl (coneStep n) acc).getD (acc.length+j) []=
   (gs[j].inputs.filter (fun w=>decide (n≤ w∧ w < n+(acc.length+j)))).flatMap
    (fun w=>(w - n)::(gs.foldl (coneStep n) acc).getD (w - n) []):=by
 induction gs generalizing acc j with
 | nil=>cases hj
 | cons g gs ih=>
  cases j with
  | zero=>
   simp only [Nat.add_zero,List.foldl_cons,List.getElem_cons_zero]
   set acc':=coneStep n acc g
   have q5v:acc.length < acc'.length:=by
    simp only [acc',coneStep,Z17,List.length_singleton];omega
   rw [z058 n gs acc' acc.length q5v]
   have qg6:acc'.getD acc.length []=
     (g.inputs.filter (fun w=>decide (n≤ w∧ w < n+acc.length))).flatMap
      (fun w=>(w - n)::acc.getD (w - n) []):=by
    simp only [acc',coneStep,Z8,List.getElem?_append_right (le_refl _),
     Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
   rw [qg6]
   apply List.flatMap_congr
   intro w hw
   simp only [List.mem_filter,Z1] at hw
   have hwn:w - n < acc.length:=by omega
   have qjo:w - n < acc'.length:=by omega
   rw [z058 n gs acc' (w - n) qjo]
   simp only [acc',coneStep,Z8,List.getElem?_append_left hwn]
  | succ j'=>
   simp only [List.foldl_cons,List.getElem_cons_succ]
   set acc':=coneStep n acc g
   have qg7:acc'.length=acc.length+1:=by
    simp only [acc',coneStep,Z17,List.length_singleton]
   have hj':j' < gs.length:=by simp only [List.length_cons] at hj;omega
   have q92:acc.length+(j'+1)=acc'.length+j':=by omega
   rw [q92]
   exact ih acc' j' hj'
lemma z080 {n:ℕ} {C:Circuit} {i j:ℕ} (h:InCone n C i j):j < C.gates.length:=by
 by_contra hge
 unfold InCone at h
 rw [Z8,List.getElem?_eq_none (by rw [z025];omega)] at h
 simp at h
lemma z078 {n:ℕ} {C:Circuit} {i j:ℕ} (hj:j < C.gates.length):
  InCone n C i j↔
   ∃ w∈ (gateAt C j).inputs,n≤ w∧ w < n+j∧ (i=w - n∨ InCone n C i (w - n)):=by
 unfold InCone cones
 have h:=z057 n C.gates [] j hj
 simp only [List.length_nil,Nat.zero_add] at h
 rw [h,← z068 hj]
 simp only [List.mem_flatMap,List.mem_filter,Z1,Z10]
 constructor
 ·rintro ⟨w,⟨hw1,hw2,hw3⟩,hw4⟩;exact ⟨w,hw1,hw2,hw3,hw4⟩
 ·rintro ⟨w,hw1,hw2,hw3,hw4⟩;exact ⟨w,⟨hw1,hw2,hw3⟩,hw4⟩
lemma z079 {n:ℕ} {C:Circuit} {i j:ℕ}:InCone n C i j→ i < j:=by
 induction j using Nat.strong_induction_on with
 | ind j ih=>
  intro h
  have hj:=z080 h
  rw [z078 hj] at h
  rcases h with ⟨w,_,hnw,qfz,rfl | q0c⟩
  ·omega
  ·have:=ih (w - n) (by omega) q0c;omega
lemma z062 (n:ℕ) (gs:List Gate) (acc:List (List ℕ)):
  (gs.foldl (orStep n) acc).length=acc.length+gs.length:=by
 induction gs generalizing acc with
 | nil=>simp
 | cons g gs ih=>
  simp only [List.foldl_cons,ih,orStep,Z17,List.length_cons,List.length_nil]
  omega
lemma z061 (n:ℕ) (gs:List Gate) (acc:List (List ℕ)) (i:ℕ) (hi:i < acc.length):
  (gs.foldl (orStep n) acc).getD i []=acc.getD i []:=by
 induction gs generalizing acc with
 | nil=>rfl
 | cons g gs ih=>
  simp only [List.foldl_cons]
  have hlt:i < (orStep n acc g).length:=by
   simp only [orStep,Z17,List.length_singleton];omega
  rw [ih _ hlt]
  simp only [orStep,Z8,List.getElem?_append_left hi]
lemma z118 (n:ℕ) (C:Circuit):(orSets n C).length=C.gates.length:=by
 unfold orSets;rw [z062];simp
lemma z060 (n:ℕ) (gs:List Gate) (acc:List (List ℕ)) (j:ℕ) (hj:j < gs.length):
  (gs.foldl (orStep n) acc).getD (acc.length+j) []=
   (acc.length+j)::(match gs[j].op with
    | GateOp.or=>
     (gs[j].inputs.filter (fun w=>decide (n≤ w∧ w < n+(acc.length+j)))).flatMap
      (fun w=>(gs.foldl (orStep n) acc).getD (w - n) [])
    | _=>[]):=by
 induction gs generalizing acc j with
 | nil=>cases hj
 | cons g gs ih=>
  cases j with
  | zero=>
   simp only [Nat.add_zero,List.foldl_cons,List.getElem_cons_zero]
   set acc':=orStep n acc g
   have q5v:acc.length < acc'.length:=by
    simp only [acc',orStep,Z17,List.length_singleton];omega
   rw [z061 n gs acc' acc.length q5v]
   have qg6:acc'.getD acc.length []=
     acc.length::(match g.op with
      | GateOp.or=>
       (g.inputs.filter (fun w=>decide (n≤ w∧ w < n+acc.length))).flatMap
        (fun w=>acc.getD (w - n) [])
      | _=>[]):=by
    simp only [acc',orStep,Z8,List.getElem?_append_right (le_refl _),
     Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
    cases g.op <;> rfl
   rw [qg6]
   congr 1
   cases g.op
   ·rfl
   ·apply List.flatMap_congr
    intro w hw
    simp only [List.mem_filter,Z1] at hw
    have hwn:w - n < acc.length:=by omega
    have qjo:w - n < acc'.length:=by omega
    rw [z061 n gs acc' (w - n) qjo]
    simp only [acc',orStep,Z8,List.getElem?_append_left hwn]
   ·rfl
   ·rfl
   ·rfl
  | succ j'=>
   simp only [List.foldl_cons,List.getElem_cons_succ]
   set acc':=orStep n acc g
   have qg7:acc'.length=acc.length+1:=by
    simp only [acc',orStep,Z17,List.length_singleton]
   have hj':j' < gs.length:=by simp only [List.length_cons] at hj;omega
   have q92:acc.length+(j'+1)=acc'.length+j':=by omega
   rw [q92]
   exact ih acc' j' hj'
lemma z114 {n:ℕ} {C:Circuit} {w g:ℕ} (h:OrReaches n C w g):
  w - n < C.gates.length:=by
 by_contra hge
 unfold OrReaches at h
 rw [Z8,List.getElem?_eq_none (by rw [z118];omega)] at h
 simp at h
lemma z111 {n:ℕ} {C:Circuit} {j g:ℕ} (hj:j < C.gates.length):
  OrReaches n C (n+j) g↔
   g=j∨ ((gateAt C j).op=GateOp.or∧
    ∃ w∈ (gateAt C j).inputs,n≤ w∧ w < n+j∧ OrReaches n C w g):=by
 unfold OrReaches orSets
 have h:=z060 n C.gates [] j hj
 simp only [List.length_nil,Nat.zero_add] at h
 rw [Nat.add_sub_cancel_left,h,← z068 hj]
 constructor
 ·rintro ⟨_,q23⟩
  rw [Z10] at q23
  rcases q23 with rfl | q23
  ·exact Or.inl rfl
  ·cases hop:(gateAt C j).op
   ·rw [hop] at q23;simp at q23
   ·rw [hop] at q23
    rw [List.mem_flatMap] at q23
    rcases q23 with ⟨w,hw,hwg⟩
    rw [List.mem_filter] at hw
    simp only [Z1] at hw
    exact Or.inr ⟨rfl,w,hw.1,hw.2.1,hw.2.2,⟨hw.2.1,hwg⟩⟩
   ·rw [hop] at q23;simp at q23
   ·rw [hop] at q23;simp at q23
   ·rw [hop] at q23;simp at q23
 ·rintro (rfl | ⟨hop,w,hw,hnw,qfz,hwg⟩)
  ·exact ⟨Nat.le_add_right n _,List.mem_cons_self⟩
  ·refine ⟨Nat.le_add_right n j,List.mem_cons_of_mem j ?_⟩
   rw [hop,List.mem_flatMap]
   exact ⟨w,List.mem_filter.mpr ⟨hw,by simp [hnw,qfz]⟩,hwg.2⟩
lemma z112 {n:ℕ} {C:Circuit} {w g:ℕ} (hw:w < n):¬ OrReaches n C w g:=
 fun h=>by have:=h.1;omega
lemma z113 {n:ℕ} {C:Circuit} {w g:ℕ} (h:OrReaches n C w g):g≤ w - n:=by
 have hnw:n≤ w:=h.1
 have hj:w - n < C.gates.length:=z114 h
 obtain ⟨k,hk⟩:∃ k,w=n+k:=⟨w - n,by omega⟩
 subst hk
 rw [Nat.add_sub_cancel_left] at hj ⊢
 clear hnw
 induction k using Nat.strong_induction_on with
 | ind k ih=>
  rw [z111 hj] at h
  rcases h with rfl | ⟨_,u,_,hnu,qjp,hug⟩
  ·exact le_refl _
  ·have hlt:u - n < k:=by omega
   have q1d:u=n+(u - n):=by omega
   rw [q1d] at hug
   have:=ih (u - n) hlt hug (by omega)
   omega
lemma z115 {n:ℕ} {C:Circuit} {j:ℕ} (hj:j < C.gates.length):
  OrReaches n C (n+j) j:=
 (z111 hj).mpr (Or.inl rfl)
lemma z116 {n:ℕ} {C:Circuit} {w j g:ℕ}
  (h1:OrReaches n C w j) (h2:OrReaches n C (n+j) g):OrReaches n C w g:=by
 have hnw:n≤ w:=h1.1
 have hwn:w - n < C.gates.length:=z114 h1
 obtain ⟨k,rfl⟩:∃ k,w=n+k:=⟨w - n,by omega⟩
 rw [Nat.add_sub_cancel_left] at hwn
 clear hnw
 induction k using Nat.strong_induction_on with
 | ind k ih=>
  rw [z111 hwn] at h1
  rcases h1 with rfl | ⟨hop,u,hu,hnu,qjp,huj⟩
  ·exact h2
  ·rw [z111 hwn]
   refine Or.inr ⟨hop,u,hu,hnu,qjp,?_⟩
   have q1d:u=n+(u - n):=by omega
   rw [q1d] at huj ⊢
   exact ih (u - n) (by omega) huj (by omega)
lemma z117 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (x:Fin n→ Bool)
  {w g:ℕ} (h:OrReaches n C w g) (hg:gateVal n C g x=true):wval C x w=true:=by
 have hnw:n≤ w:=h.1
 have hwn:w - n < C.gates.length:=z114 h
 obtain ⟨k,rfl⟩:∃ k,w=n+k:=⟨w - n,by omega⟩
 rw [Nat.add_sub_cancel_left] at hwn
 clear hnw
 induction k using Nat.strong_induction_on with
 | ind k ih=>
  rw [z111 hwn] at h
  rcases h with rfl | ⟨hop,u,hu,hnu,qjp,hug⟩
  ·exact hg
  ·rw [z142 hAO x hwn hop,Z13]
   rw [z071 hAO hwn] at hu
   have q1d:u=n+(u - n):=by omega
   rw [q1d] at hug
   have hvu:=ih (u - n) (by omega) hug (by omega)
   rw [← q1d] at hvu
   simp only [Z10,Z11,or_false] at hu
   rcases hu with rfl | rfl
   ·exact Or.inl hvu
   ·exact Or.inr hvu
lemma z095 {n:ℕ} (C:Circuit) (u v:Fin n):
  u∈ orIn n C v.val↔ u=v:=by
 unfold orIn
 simp only [Z0,Z7,true_and]
 constructor
 ·rintro (heq | ⟨k,_,q0q,_,_⟩)
  ·exact Fin.ext heq
  ·exact absurd q0q (z112 v.isLt)
 ·rintro rfl;exact Or.inl rfl
lemma z107 {n:ℕ} {C:Circuit} {j:ℕ} (hj:j < C.gates.length)
  (q17:(gateAt C j).op=GateOp.and):orIn n C (n+j)=∅:=by
 ext u
 simp only [orIn,Z0,Z7,true_and,Finset.notMem_empty,iff_false,not_or]
 refine ⟨by have:=u.isLt;omega,?_⟩
 rintro ⟨k,hk,q0q,hor,_⟩
 rw [z111 hj] at q0q
 rcases q0q with rfl | ⟨qmb,_⟩
 ·rw [q17] at hor;cases hor
 ·rw [q17] at qmb;cases qmb
lemma z108 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) {j:ℕ} (hj:j < C.gates.length)
  (hor:(gateAt C j).op=GateOp.or):
  orIn n C (n+j)=orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1):=by
 ext u
 simp only [Z4,orIn,Z0,Z7,true_and]
 constructor
 ·rintro (hu | ⟨k,hk,q0q,q3d,huk⟩)
  ·omega
  ·rw [z111 hj] at q0q
   rcases q0q with rfl | ⟨_,w,hw,hnw,qfz,hwk⟩
   ·rw [z071 hAO hj] at huk
    simp only [Z10,Z11,or_false] at huk
    rcases huk with h0 | h1
    ·exact Or.inl (Or.inl h0)
    ·exact Or.inr (Or.inl h1)
   ·rw [z071 hAO hj] at hw
    simp only [Z10,Z11,or_false] at hw
    rcases hw with rfl | rfl
    ·exact Or.inl (Or.inr ⟨k,hk,hwk,q3d,huk⟩)
    ·exact Or.inr (Or.inr ⟨k,hk,hwk,q3d,huk⟩)
 ·rintro ((h0 | ⟨k,hk,hwk,q3d,huk⟩) | (h1 | ⟨k,hk,hwk,q3d,huk⟩))
  ·right
   refine ⟨j,hj,z115 hj,hor,?_⟩
   rw [z071 hAO hj,h0];simp
  ·right
   refine ⟨k,hk,(z111 hj).mpr (Or.inr ⟨hor,opnd C j 0,z105 hAO hj 0,hwk.1,
    z104 hAO hj 0,hwk⟩),q3d,huk⟩
  ·right
   refine ⟨j,hj,z115 hj,hor,?_⟩
   rw [z071 hAO hj,h1];simp
  ·right
   refine ⟨k,hk,(z111 hj).mpr (Or.inr ⟨hor,opnd C j 1,z105 hAO hj 1,hwk.1,
    z104 hAO hj 1,hwk⟩),q3d,huk⟩
lemma z110 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (x:Fin n→ Bool)
  {w:ℕ} {u:Fin n} (hu:u∈ orIn n C w) (hx:x u=true):wval C x w=true:=by
 unfold orIn at hu
 simp only [Z0,Z7,true_and] at hu
 rcases hu with rfl | ⟨k,hk,q0q,q3d,huk⟩
 ·rw [z144 C x u.val u.isLt];exact hx
 ·apply z117 hAO x q0q
  rw [z070,z142 hAO x hk q3d,Z13]
  rw [z071 hAO hk] at huk
  simp only [Z10,Z11,or_false] at huk
  rcases huk with h0 | h1
  ·left;rw [← h0,z144 C x u.val u.isLt];exact hx
  ·right;rw [← h1,z144 C x u.val u.isLt];exact hx
lemma z109 {n:ℕ} {C:Circuit} {w k:ℕ} (h:OrReaches n C w k):
  orIn n C (n+k)⊆ orIn n C w:=by
 intro u hu
 unfold orIn at hu ⊢
 simp only [Z0,Z7,true_and] at hu ⊢
 rcases hu with hu | ⟨m,hm,hkm,qaw,hum⟩
 ·omega
 ·exact Or.inr ⟨m,hm,z116 h hkm,qaw,hum⟩
def z036 (n j r w:ℕ):ℕ:=
 if w=n+j then r else if n+j < w then w - 1 else w
def z026 (n:ℕ) (C:Circuit) (j r:ℕ):Circuit:=
 {gates:=(C.gates.eraseIdx j).map (fun g=>{g with inputs:=g.inputs.map (z036 n j r)})
  output:=z036 n j r C.output}
lemma z030 (n:ℕ) (C:Circuit) {j:ℕ} (hj:j < C.gates.length) (r:ℕ):
  (z026 n C j r).gates.length=C.gates.length - 1:=by
 simp [z026,List.length_eraseIdx,hj]
lemma z028 {n:ℕ} {C:Circuit} {j r i:ℕ}
  (hj:j < C.gates.length) (hi:i < j):
  gateAt (z026 n C j r) i=
   {(gateAt C i) with inputs:=(gateAt C i).inputs.map (z036 n j r)}:=by
 have hi':i < (z026 n C j r).gates.length:=by rw [z030 n C hj r];omega
 rw [z068 hi',z068 (by omega)]
 simp only [z026,List.getElem_map]
 rw [List.getElem_eraseIdx_of_lt (by rw [List.length_eraseIdx,if_pos hj];omega) hi]
lemma z027 {n:ℕ} {C:Circuit} {j r i:ℕ}
  (hj:j < C.gates.length) (hji:j≤ i) (hi:i < C.gates.length - 1):
  gateAt (z026 n C j r) i=
   {(gateAt C (i+1)) with inputs:=(gateAt C (i+1)).inputs.map (z036 n j r)}:=by
 have hi':i < (z026 n C j r).gates.length:=by rw [z030 n C hj r];omega
 rw [z068 hi',z068 (by omega)]
 simp only [z026,List.getElem_map]
 rw [List.getElem_eraseIdx_of_ge (by rw [List.length_eraseIdx,if_pos hj];omega) hji]
lemma z029 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) {j r:ℕ}
  (hj:j < C.gates.length) (hr:r < n+j):IsAO2 n (z026 n C j r):=by
 refine ⟨?_,?_,?_⟩
 ·intro g hg
  simp only [z026,List.mem_map] at hg
  rcases hg with ⟨g0,hg0,rfl⟩
  exact hAO.1 g0 (List.mem_of_mem_eraseIdx hg0)
 ·intro i hi w hw
  rw [z030 n C hj r] at hi
  by_cases hij:i < j
  ·rw [z028 hj hij] at hw
   simp only [List.mem_map] at hw
   rcases hw with ⟨u,hu,rfl⟩
   have qjq:u < n+i:=hAO.2.1 i (by omega) u hu
   unfold z036
   rw [if_neg (by omega),if_neg (by omega)]
   exact qjq
  ·rw [z027 hj (by omega) hi] at hw
   simp only [List.mem_map] at hw
   rcases hw with ⟨u,hu,rfl⟩
   have qjq:u < n+(i+1):=hAO.2.1 (i+1) (by omega) u hu
   unfold z036
   split_ifs <;> omega
 ·intro g hg
  simp only [z026,List.mem_map] at hg
  rcases hg with ⟨g0,hg0,rfl⟩
  simp only [List.length_map]
  exact hAO.2.2 g0 (List.mem_of_mem_eraseIdx hg0)
lemma z032 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) {j r i:ℕ}
  (hj:j < C.gates.length) (hi:i < j) (b:Fin 2):
  opnd (z026 n C j r) i b=z036 n j r (opnd C i b):=by
 unfold opnd
 rw [z028 hj hi,z071 hAO (by omega)]
 fin_cases b <;> rfl
lemma z031 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) {j r i:ℕ}
  (hj:j < C.gates.length) (hji:j≤ i) (hi:i < C.gates.length - 1) (b:Fin 2):
  opnd (z026 n C j r) i b=z036 n j r (opnd C (i+1) b):=by
 unfold opnd
 rw [z027 hj hji hi,z071 hAO (by omega)]
 fin_cases b <;> rfl
lemma z033 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (x:Fin n→ Bool)
  {j r:ℕ} (hj:j < C.gates.length) (hr:r < n+j)
  (heq:wval C x r=wval C x (n+j)):
  ∀ w < n+C.gates.length,wval (z026 n C j r) x (z036 n j r w)=wval C x w:=by
 have q4x:=z029 hAO hj hr
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih=>
  intro hw
  by_cases hwn:w < n
  ·have hdw:z036 n j r w=w:=by unfold z036;rw [if_neg (by omega),if_neg (by omega)]
   rw [hdw,z144 _ x w hwn,z144 _ x w hwn]
  ·by_cases hwj:w=n+j
   ·subst hwj
    have hdw:z036 n j r (n+j)=r:=by unfold z036;simp
    have hdr:z036 n j r r=r:=by unfold z036;rw [if_neg (by omega),if_neg (by omega)]
    have h1:=ih r hr (by omega)
    rw [hdr] at h1
    rw [hdw,h1,heq]
   ·by_cases hlt:w < n+j
    ·have hk:w - n < j:=by omega
     have hdw:z036 n j r w=n+(w - n):=by
      unfold z036;rw [if_neg hwj,if_neg (by omega)];omega
     have q0f:w=n+(w - n):=by omega
     rw [hdw]
     conv_rhs=>rw [q0f]
     have hk':w - n < (z026 n C j r).gates.length:=by rw [z030 n C hj r];omega
     rw [z141 q4x x hk',z141 hAO x (by omega)]
     have hg:=z028 (n:=n) (r:=r) hj hk
     rw [z032 hAO hj hk 0,z032 hAO hj hk 1]
     have h0:=ih (opnd C (w - n) 0) (by have:=z104 hAO (by omega:w - n < C.gates.length) 0;omega) (by have:=z104 hAO (by omega:w - n < C.gates.length) 0;omega)
     have h1:=ih (opnd C (w - n) 1) (by have:=z104 hAO (by omega:w - n < C.gates.length) 1;omega) (by have:=z104 hAO (by omega:w - n < C.gates.length) 1;omega)
     rw [h0,h1,hg]
    ·have hgt:n+j < w:=by omega
     have hk:w - n - 1 < C.gates.length - 1:=by omega
     have hjk:j≤ w - n - 1:=by omega
     have hdw:z036 n j r w=n+(w - n - 1):=by
      unfold z036;rw [if_neg hwj,if_pos hgt];omega
     have q0f:w=n+(w - n - 1+1):=by omega
     rw [hdw]
     conv_rhs=>rw [q0f]
     have hk':w - n - 1 < (z026 n C j r).gates.length:=by rw [z030 n C hj r];omega
     rw [z141 q4x x hk',z141 hAO x (by omega)]
     have hg:=z027 (n:=n) (r:=r) hj hjk hk
     rw [z031 hAO hj hjk hk 0,z031 hAO hj hjk hk 1]
     have h0:=ih (opnd C (w - n - 1+1) 0) (by have:=z104 hAO (by omega:w - n - 1+1 < C.gates.length) 0;omega) (by have:=z104 hAO (by omega:w - n - 1+1 < C.gates.length) 0;omega)
     have h1:=ih (opnd C (w - n - 1+1) 1) (by have:=z104 hAO (by omega:w - n - 1+1 < C.gates.length) 1;omega) (by have:=z104 hAO (by omega:w - n - 1+1 < C.gates.length) 1;omega)
     rw [h0,h1,hg]
lemma z034 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (x:Fin n→ Bool)
  {j r:ℕ} (hj:j < C.gates.length) (hr:r < n+j)
  (hle:wval C x (n+j)=true→ wval C x r=true):
  ∀ w < n+C.gates.length,wval C x w=true→ wval (z026 n C j r) x (z036 n j r w)=true:=by
 have q4x:=z029 hAO hj hr
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih=>
  intro hw q10
  by_cases hwn:w < n
  ·have hdw:z036 n j r w=w:=by unfold z036;rw [if_neg (by omega),if_neg (by omega)]
   rw [hdw,z144 _ x w hwn];rw [z144 _ x w hwn] at q10;exact q10
  ·by_cases hwj:w=n+j
   ·subst hwj
    have hdw:z036 n j r (n+j)=r:=by unfold z036;simp
    have hdr:z036 n j r r=r:=by unfold z036;rw [if_neg (by omega),if_neg (by omega)]
    have h1:=ih r hr (by omega) (hle q10)
    rw [hdr] at h1
    rw [hdw]
    exact h1
   ·by_cases hlt:w < n+j
    ·have hk:w - n < j:=by omega
     have hdw:z036 n j r w=n+(w - n):=by
      unfold z036;rw [if_neg hwj,if_neg (by omega)];omega
     have q0f:w=n+(w - n):=by omega
     rw [hdw];rw [q0f] at q10
     have hk':w - n < (z026 n C j r).gates.length:=by rw [z030 n C hj r];omega
     have hg:=z028 (n:=n) (r:=r) hj hk
     have qg8:opnd C (w - n) 0 < w:=by have:=z104 hAO (by omega:w - n < C.gates.length) 0;omega
     have qg9:opnd C (w - n) 1 < w:=by have:=z104 hAO (by omega:w - n < C.gates.length) 1;omega
     rcases hAO.1 _ (z069 (by omega:w - n < C.gates.length)) with q17 | hor
     ·rw [z140 hAO x (by omega) q17,Z12] at q10
      rw [z140 q4x x hk' (by rw [hg];exact q17),Z12]
      rw [z032 hAO hj hk 0,z032 hAO hj hk 1]
      exact ⟨ih _ qg8 (by omega) q10.1,ih _ qg9 (by omega) q10.2⟩
     ·rw [z142 hAO x (by omega) hor,Z13] at q10
      rw [z142 q4x x hk' (by rw [hg];exact hor),Z13]
      rw [z032 hAO hj hk 0,z032 hAO hj hk 1]
      exact q10.imp (ih _ qg8 (by omega)) (ih _ qg9 (by omega))
    ·have hgt:n+j < w:=by omega
     have hk:w - n - 1 < C.gates.length - 1:=by omega
     have hjk:j≤ w - n - 1:=by omega
     have hdw:z036 n j r w=n+(w - n - 1):=by
      unfold z036;rw [if_neg hwj,if_pos hgt];omega
     have q0f:w=n+(w - n - 1+1):=by omega
     rw [hdw];rw [q0f] at q10
     have hk':w - n - 1 < (z026 n C j r).gates.length:=by rw [z030 n C hj r];omega
     have hg:=z027 (n:=n) (r:=r) hj hjk hk
     have qg8:opnd C (w - n - 1+1) 0 < w:=by have:=z104 hAO (by omega:w - n - 1+1 < C.gates.length) 0;omega
     have qg9:opnd C (w - n - 1+1) 1 < w:=by have:=z104 hAO (by omega:w - n - 1+1 < C.gates.length) 1;omega
     rcases hAO.1 _ (z069 (by omega:w - n - 1+1 < C.gates.length)) with q17 | hor
     ·rw [z140 hAO x (by omega) q17,Z12] at q10
      rw [z140 q4x x hk' (by rw [hg];exact q17),Z12]
      rw [z031 hAO hj hjk hk 0,z031 hAO hj hjk hk 1]
      exact ⟨ih _ qg8 (by omega) q10.1,ih _ qg9 (by omega) q10.2⟩
     ·rw [z142 hAO x (by omega) hor,Z13] at q10
      rw [z142 q4x x hk' (by rw [hg];exact hor),Z13]
      rw [z031 hAO hj hjk hk 0,z031 hAO hj hjk hk 1]
      exact q10.imp (ih _ qg8 (by omega)) (ih _ qg9 (by omega))
lemma z035 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (x:Fin n→ Bool)
  {j r:ℕ} (hj:j < C.gates.length) (hr:r < n+j):
  ∀ w < n+C.gates.length,w≠ n+j→ (n≤ w→ ¬ InCone n C j (w - n))→
   wval (z026 n C j r) x (z036 n j r w)=wval C x w:=by
 have q4x:=z029 hAO hj hr
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih=>
  intro hw hwj hnc
  by_cases hwn:w < n
  ·have hdw:z036 n j r w=w:=by unfold z036;rw [if_neg (by omega),if_neg (by omega)]
   rw [hdw,z144 _ x w hwn,z144 _ x w hwn]
  ·have qmc:¬ InCone n C j (w - n):=hnc (by omega)
   have q3v:∀ b:Fin 2,opnd C (w - n) b≠ n+j∧
     (n≤ opnd C (w - n) b→ ¬ InCone n C j (opnd C (w - n) b - n)):=by
    intro b
    have hk:w - n < C.gates.length:=by omega
    have q23:=z105 hAO hk b
    have hlt:=z104 hAO hk b
    constructor
    ·intro heq;apply qmc;rw [z078 hk]
     exact ⟨opnd C (w - n) b,q23,by omega,hlt,Or.inl (by omega)⟩
    ·intro hnu hin;apply qmc;rw [z078 hk]
     exact ⟨opnd C (w - n) b,q23,hnu,hlt,Or.inr hin⟩
   by_cases hlt:w < n+j
   ·have hk:w - n < j:=by omega
    have hdw:z036 n j r w=n+(w - n):=by
     unfold z036;rw [if_neg hwj,if_neg (by omega)];omega
    have q0f:w=n+(w - n):=by omega
    rw [hdw]
    conv_rhs=>rw [q0f]
    have hk':w - n < (z026 n C j r).gates.length:=by rw [z030 n C hj r];omega
    rw [z141 q4x x hk',z141 hAO x (by omega)]
    have hg:=z028 (n:=n) (r:=r) hj hk
    rw [z032 hAO hj hk 0,z032 hAO hj hk 1]
    have h0:=ih (opnd C (w - n) 0) (by have:=z104 hAO (by omega:w - n < C.gates.length) 0;omega)
     (by have:=z104 hAO (by omega:w - n < C.gates.length) 0;omega) (q3v 0).1 (q3v 0).2
    have h1:=ih (opnd C (w - n) 1) (by have:=z104 hAO (by omega:w - n < C.gates.length) 1;omega)
     (by have:=z104 hAO (by omega:w - n < C.gates.length) 1;omega) (q3v 1).1 (q3v 1).2
    rw [h0,h1,hg]
   ·have hgt:n+j < w:=by omega
    have hk:w - n - 1 < C.gates.length - 1:=by omega
    have hjk:j≤ w - n - 1:=by omega
    have hdw:z036 n j r w=n+(w - n - 1):=by
     unfold z036;rw [if_neg hwj,if_pos hgt];omega
    have q0f:w=n+(w - n - 1+1):=by omega
    have q92:w - n=w - n - 1+1:=by omega
    rw [hdw]
    conv_rhs=>rw [q0f]
    have hk':w - n - 1 < (z026 n C j r).gates.length:=by rw [z030 n C hj r];omega
    rw [z141 q4x x hk',z141 hAO x (by omega)]
    have hg:=z027 (n:=n) (r:=r) hj hjk hk
    rw [z031 hAO hj hjk hk 0,z031 hAO hj hjk hk 1]
    have h0:=ih (opnd C (w - n - 1+1) 0)
     (by have:=z104 hAO (by omega:w - n - 1+1 < C.gates.length) 0;omega)
     (by have:=z104 hAO (by omega:w - n - 1+1 < C.gates.length) 0;omega)
     (by rw [← q92];exact (q3v 0).1) (by rw [← q92];exact (q3v 0).2)
    have h1:=ih (opnd C (w - n - 1+1) 1)
     (by have:=z104 hAO (by omega:w - n - 1+1 < C.gates.length) 1;omega)
     (by have:=z104 hAO (by omega:w - n - 1+1 < C.gates.length) 1;omega)
     (by rw [← q92];exact (q3v 1).1) (by rw [← q92];exact (q3v 1).2)
    rw [h0,h1,hg]
lemma z073 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] (x:Fin n→ Bool):
  graphFun G ∅ x=true↔ ∃ u v:Fin n,G.Adj u v∧ x u=true∧ x v=true:=by
 unfold graphFun;simp
lemma z075 {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (v:Fin n):
  graphFun G ∅ (fun w=>decide (w=v))=false:=by
 rw [Z14,ne_eq,z073]
 rintro ⟨a,b,hab,ha,hb⟩
 simp only [Z1] at ha hb
 subst ha;subst hb
 exact G.loopless.irrefl _ hab
lemma z074 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] (u v:Fin n):
  graphFun G ∅ (pairInput u v)=true↔ G.Adj u v:=by
 rw [z073]
 constructor
 ·rintro ⟨a,b,hab,ha,hb⟩
  unfold pairInput at ha hb
  simp only [Z1] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  ·exact absurd hab (G.loopless.irrefl _)
  ·exact hab
  ·exact hab.symm
  ·exact absurd hab (G.loopless.irrefl _)
 ·intro huv
  exact ⟨u,v,huv,by simp [pairInput],by simp [pairInput]⟩
lemma z120 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (hne:∃ u v:Fin n,G.Adj u v):
  n≤ C.output∧ C.output < n+C.gates.length:=by
 obtain ⟨u,v,huv⟩:=hne
 have qmd:∀ x,wval C x C.output=graphFun G ∅ x:=fun x=>congrFun hL.2.1 x
 constructor
 ·by_contra hlt
  push Not at hlt
  have h1:=qmd (fun w=>decide (w=⟨C.output,hlt⟩))
  rw [z144 C _ C.output hlt,z075] at h1
  simp at h1
 ·by_contra hge
  push Not at hge
  have h1:=qmd (pairInput u v)
  rw [z143 C _ hge,(z074 u v).mpr huv] at h1
  cases h1
lemma z088 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (hne:∃ u v:Fin n,G.Adj u v):
  ∀ j < C.gates.length,InOutputCone n C j:=by
 have ⟨u,_,_⟩:=hne
 have hn0:0 < n:=Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt
 have q9b:=z120 hL hne
 intro j hj
 refine ⟨hj,?_⟩
 by_contra q8o
 push Not at q8o
 have hr:0 < n+j:=by omega
 let C':=z026 n C j 0
 have q4x:=z029 hL.1 hj hr
 have q6z:circuitFun n C'=graphFun G ∅:=by
  funext x
  change wval C' x C'.output=graphFun G ∅ x
  rw [← congrFun hL.2.1 x]
  exact z035 hL.1 x hj hr C.output q9b.2 q8o.1 (fun _=>q8o.2 q9b.1)
 have hsz:=hL.2.2 C' q4x q6z
 simp only [Circuit.size,C',z030 n C hj 0] at hsz
 omega
lemma z090 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (hne:∃ u v:Fin n,G.Adj u v)
  {j r:ℕ} (hj:j < C.gates.length) (hr:r < n+j):
  ¬ ∀ x:Fin n→ Bool,wval C x r=wval C x (n+j):=by
 have q9b:=z120 hL hne
 intro heq
 let C':=z026 n C j r
 have q4x:=z029 hL.1 hj hr
 have q6z:circuitFun n C'=graphFun G ∅:=by
  funext x
  change wval C' x C'.output=graphFun G ∅ x
  rw [← congrFun hL.2.1 x]
  exact z033 hL.1 x hj hr (heq x) C.output q9b.2
 have hsz:=hL.2.2 C' q4x q6z
 simp only [Circuit.size,C',z030 n C hj r] at hsz
 omega
lemma z089 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (hne:∃ u v:Fin n,G.Adj u v)
  {a:ℕ} (ha:a < C.gates.length) (q17:(gateAt C a).op=GateOp.and) (b:Fin 2):
  ¬ ∀ x:Fin n→ Bool,wval C x (opnd C a b)=true→ graphFun G ∅ x=true:=by
 have q9b:=z120 hL hne
 intro q9c
 set r:=opnd C a b
 have hr:r < n+a:=z104 hL.1 ha b
 let C':=z026 n C a r
 have q4x:=z029 hL.1 ha hr
 have q6z:circuitFun n C'=graphFun G ∅:=by
  funext x
  change wval C' x C'.output=graphFun G ∅ x
  cases hFx:graphFun G ∅ x
  ·have hrx:wval C x r=false:=by
    cases h:wval C x r
    ·rfl
    ·have:=q9c x h;rw [hFx] at this;cases this
   have hax:wval C x (n+a)=false:=by
    rw [z140 hL.1 x ha q17]
    fin_cases b
    ·change wval C x (opnd C a 0)=false at hrx;rw [hrx];rfl
    ·change wval C x (opnd C a 1)=false at hrx;rw [hrx,Bool.and_false]
   have hcx:wval C x C.output=false:=by
    change circuitFun n C x=false;rw [congrFun hL.2.1 x];exact hFx
   change wval (z026 n C a r) x (z036 n a r C.output)=false
   rw [z033 hL.1 x ha hr (by rw [hrx,hax]) C.output q9b.2,hcx]
  ·have hcx:wval C x C.output=true:=by
    change circuitFun n C x=true;rw [congrFun hL.2.1 x];exact hFx
   change wval (z026 n C a r) x (z036 n a r C.output)=true
   apply z034 hL.1 x ha hr _ C.output q9b.2 hcx
   intro hax
   rw [z140 hL.1 x ha q17,Z12] at hax
   fin_cases b
   ·exact hax.1
   ·exact hax.2
 have hsz:=hL.2.2 C' q4x q6z
 simp only [Circuit.size,C',z030 n C ha r] at hsz
 omega
lemma z081 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {w:ℕ} (hw:w < n):
  ¬ ∀ x:Fin n→ Bool,wval C x w=true→ graphFun G ∅ x=true:=by
 intro h
 have:=h (fun i=>decide (i=⟨w,hw⟩)) (by rw [z144 C _ w hw];simp)
 rw [z075] at this
 cases this
lemma z091 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (hne:∃ u v:Fin n,G.Adj u v)
  {h:ℕ} (hh:h < C.gates.length) (hor:(gateAt C h).op=GateOp.or)
  (hnb:¬ BelowF G C h) (b:Fin 2):
  ¬ ∀ x:Fin n→ Bool,wval C x (opnd C h b)=true→ graphFun G ∅ x=true:=by
 intro q9c
 apply q01
 refine ⟨h,hh,b,z088 hL hne h hh,hor,hnb,q9c,?_⟩
 refine ⟨fun _=>true,z138 hL.1 (opnd C h b) (by have:=z104 hL.1 hh b;omega)⟩
lemma z119 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) {h:ℕ} (hh:h < C.gates.length)
  (hor:(gateAt C h).op=GateOp.or) (hb:BelowF G C h) (b:Fin 2):
  n≤ opnd C h b∧ opnd C h b - n < C.gates.length∧ BelowF G C (opnd C h b - n):=by
 have hwb:∀ x,wval C x (opnd C h b)=true→ graphFun G ∅ x=true:=by
  intro x hwx
  apply hb x
  rw [z070,z142 hL.1 x hh hor,Z13]
  fin_cases b
  ·exact Or.inl hwx
  ·exact Or.inr hwx
 have hge:n≤ opnd C h b:=by
  by_contra hlt;push Not at hlt;exact z081 hlt hwb
 have hlt:opnd C h b < n+h:=z104 hL.1 hh b
 refine ⟨hge,by omega,?_⟩
 intro x hx
 apply hwb x
 rw [z070] at hx
 rwa [show n+(opnd C h b - n)=opnd C h b by omega] at hx
lemma z098 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit} {k:ℕ}:
  k∈ tops G C↔ k < C.gates.length∧ (gateAt C k).op=GateOp.and∧ BelowF G C k:=by
 letI:DecidableEq GateOp:=gateOpDecEq
 unfold tops gatesWhere;rw [Z0,Z9]
lemma z097 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit} {k:ℕ}:
  k∈ orT G C↔ k < C.gates.length∧ (gateAt C k).op=GateOp.or∧ BelowF G C k:=by
 letI:DecidableEq GateOp:=gateOpDecEq
 unfold orT gatesWhere;rw [Z0,Z9]
lemma z096 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit} {k:ℕ}:
  k∈ orN G C↔ k < C.gates.length∧ (gateAt C k).op=GateOp.or∧ ¬ BelowF G C k:=by
 letI:DecidableEq GateOp:=gateOpDecEq
 unfold orN gatesWhere;rw [Z0,Z9]
lemma z094 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit} {k:ℕ}:
  k∈ junk G C↔ k < C.gates.length∧ (gateAt C k).op=GateOp.and∧ ¬ BelowF G C k:=by
 unfold junk gatesWhere
 rw [Z0,Z9]
 unfold IsDirtyAnd IsDirty BelowF
 constructor
 ·rintro ⟨hk,q17,_,x,hgx,hfx⟩
  refine ⟨hk,q17,fun hb=>?_⟩
  have:=hb x hgx;rw [hfx] at this;cases this
 ·rintro ⟨hk,q17,hnb⟩
  push Not at hnb
  rcases hnb with ⟨x,hgx,hfx⟩
  refine ⟨hk,q17,hk,x,hgx,?_⟩
  cases h:graphFun G ∅ x
  ·rfl
  ·exact absurd h hfx
lemma z013 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (hne:∃ u v:Fin n,G.Adj u v)
  {k m:ℕ} (hk:k < C.gates.length) (hbk:BelowF G C k)
  (hm:m < C.gates.length) (q60:n+k∈ (gateAt C m).inputs):
  m∈ orT G C:=by
 have hwb:∀ x,wval C x (n+k)=true→ graphFun G ∅ x=true:=hbk
 rw [z071 hL.1 hm] at q60
 simp only [Z10,Z11,or_false] at q60
 obtain ⟨b,hb⟩:∃ b:Fin 2,opnd C m b=n+k:=by
  rcases q60 with h0 | h1
  ·exact ⟨0,h0.symm⟩
  ·exact ⟨1,h1.symm⟩
 rcases hL.1.1 _ (z069 hm) with q17 | hor
 ·exfalso
  exact z089 hL hne hm q17 b (by rw [hb];exact hwb)
 ·rw [z097]
  refine ⟨hm,hor,?_⟩
  by_contra hnb
  exact z091 hL q01 hne hm hor hnb b (by rw [hb];exact hwb)
lemma z121 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
  {C:Circuit} (hL:IsLeastAO G C) (hne:∃ u v:Fin n,G.Adj u v):
  C.output - n∈ tops G C ∪ orT G C:=by
 have q9b:=z120 hL hne
 have hk:C.output - n < C.gates.length:=by omega
 have hb:BelowF G C (C.output - n):=by
  intro x hx
  rw [z070,show n+(C.output - n)=C.output by omega] at hx
  rw [← congrFun hL.2.1 x];exact hx
 rw [Z4,z098,z097]
 rcases hL.1.1 _ (z069 hk) with q17 | hor
 ·exact Or.inl ⟨hk,q17,hb⟩
 ·exact Or.inr ⟨hk,hor,hb⟩
lemma z038 {n:ℕ} {C:Circuit} {k j:ℕ} (h:InCone n C k j):
  ∃ m < C.gates.length,n+k∈ (gateAt C m).inputs:=by
 induction j using Nat.strong_induction_on with
 | ind j ih=>
  have hj:=z080 h
  rw [z078 hj] at h
  rcases h with ⟨w,hw,hnw,qfz,rfl | q0c⟩
  ·exact ⟨j,hj,by rwa [show n+(w - n)=w by omega]⟩
  ·exact ih (w - n) (by omega) q0c
lemma z133 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (hne:∃ u v:Fin n,G.Adj u v):
  (tops G C).card≤ (orT G C).card+1:=by
 have q9b:=z120 hL hne
 have q32:=z121 hL hne
 have q4y:Disjoint (tops G C) (orT G C):=by
  rw [Finset.disjoint_left]
  intro k hk1 hk2
  rw [z098] at hk1;rw [z097] at hk2
  rw [hk1.2.1] at hk2;cases hk2.2.1
 let S:=((tops G C ∪ orT G C).erase (C.output - n)).image (fun k=>n+k)
 let T:=(orT G C ×ˢ (Finset.univ:Finset (Fin 2))).image (fun p=>opnd C p.1 p.2)
 have q0c:S⊆ T:=by
  intro w hw
  simp only [S,Z19,Finset.mem_erase,Z4] at hw
  rcases hw with ⟨k,⟨qd0,q3w⟩,rfl⟩
  have q0d:k < C.gates.length:=by
   rcases q3w with h | h
   ·exact (z098.mp h).1
   ·exact (z097.mp h).1
  have qjr:BelowF G C k:=by
   rcases q3w with h | h
   ·exact (z098.mp h).2.2
   ·exact (z097.mp h).2.2
  have qjs:=z088 hL hne k q0d
  have hin:InCone n C k (C.output - n):=by
   rcases qjs.2 with heq | ⟨_,hin⟩
   ·exfalso;apply qd0;omega
   ·exact hin
  obtain ⟨m,hm,q60⟩:=z038 hin
  have qc4:=z013 hL q01 hne q0d qjr hm q60
  rw [z071 hL.1 hm] at q60
  simp only [Z10,Z11,or_false] at q60
  simp only [T,Z19,Z18,Z7,and_true]
  rcases q60 with h0 | h1
  ·exact ⟨(m,0),qc4,h0.symm⟩
  ·exact ⟨(m,1),qc4,h1.symm⟩
 have qga:S.card=(tops G C).card+(orT G C).card - 1:=by
  rw [Finset.card_image_of_injective _ (fun a b h=>by omega),
   Finset.card_erase_of_mem q32,Finset.card_union_of_disjoint q4y]
 have qme:T.card≤ 2 * (orT G C).card:=by
  calc T.card≤ (orT G C ×ˢ (Finset.univ:Finset (Fin 2))).card:=Finset.card_image_le
   _=(orT G C).card * 2:=by simp
   _=2 * (orT G C).card:=Nat.mul_comm _ _
 have hle:=Finset.card_le_card q0c
 rw [qga] at hle
 omega
lemma z024 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C):
  C.size=(tops G C).card+(orT G C).card+(junk G C).card+(orN G C).card:=by
 have hU:Finset.range C.gates.length=tops G C ∪ orT G C ∪ junk G C ∪ orN G C:=by
  ext k
  simp only [Z4,Z9,z098,z097,z094,z096]
  constructor
  ·intro hk
   rcases hL.1.1 _ (z069 hk) with q17 | hor
   ·by_cases hb:BelowF G C k
    ·exact Or.inl (Or.inl (Or.inl ⟨hk,q17,hb⟩))
    ·exact Or.inl (Or.inr ⟨hk,q17,hb⟩)
   ·by_cases hb:BelowF G C k
    ·exact Or.inl (Or.inl (Or.inr ⟨hk,hor,hb⟩))
    ·exact Or.inr ⟨hk,hor,hb⟩
  ·rintro (((⟨hk,_⟩ | ⟨hk,_⟩) | ⟨hk,_⟩) | ⟨hk,_⟩) <;> exact hk
 have hd1:Disjoint (tops G C) (orT G C):=by
  rw [Finset.disjoint_left];intro k h1 h2
  rw [z098] at h1;rw [z097] at h2;rw [h1.2.1] at h2;cases h2.2.1
 have hd2:Disjoint (tops G C ∪ orT G C) (junk G C):=by
  rw [Finset.disjoint_left];intro k h1 h2
  rw [z094] at h2;simp only [Z4,z098,z097] at h1
  rcases h1 with h1 | h1 <;> exact h2.2.2 h1.2.2
 have hd3:Disjoint (tops G C ∪ orT G C ∪ junk G C) (orN G C):=by
  rw [Finset.disjoint_left];intro k h1 h2
  rw [z096] at h2;simp only [Z4,z098,z097,z094] at h1
  rcases h1 with (h1 | h1) | h1
  ·exact h2.2.2 h1.2.2
  ·exact h2.2.2 h1.2.2
  ·rw [h1.2.1] at h2;cases h2.2.1
 change C.gates.length=_
 rw [← Finset.card_range C.gates.length,hU,
  Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,
  Finset.card_union_of_disjoint hd1]
lemma z023 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (hne:∃ u v:Fin n,G.Adj u v) (x:Fin n→ Bool):
  circuitFun n C x=true↔ ∃ a∈ tops G C,gateVal n C a x=true:=by
 have q9b:=z120 hL hne
 have q32:=z121 hL hne
 constructor
 ·intro hcx
  have qnt:∀ k,k∈ tops G C ∪ orT G C→ gateVal n C k x=true→
    ∃ a∈ tops G C,gateVal n C a x=true:=by
   intro k
   induction k using Nat.strong_induction_on with
   | ind k ih=>
    intro hk hvk
    rw [Z4] at hk
    rcases hk with qnu | q93
    ·exact ⟨k,qnu,hvk⟩
    ·rw [z097] at q93
     rw [z070,z142 hL.1 x q93.1 q93.2.1,Z13] at hvk
     rcases hvk with h0 | h1
     ·obtain ⟨hge,hlt,hbf⟩:=z119 hL q93.1 q93.2.1 q93.2.2 0
      have qd1:opnd C k 0 - n < k:=by have:=z104 hL.1 q93.1 0;omega
      have q23:opnd C k 0 - n∈ tops G C ∪ orT G C:=by
       rw [Z4,z098,z097]
       rcases hL.1.1 _ (z069 hlt) with q17 | hor
       ·exact Or.inl ⟨hlt,q17,hbf⟩
       ·exact Or.inr ⟨hlt,hor,hbf⟩
      exact ih _ qd1 q23 (by rw [z070,show n+(opnd C k 0 - n)=opnd C k 0 by omega];exact h0)
     ·obtain ⟨hge,hlt,hbf⟩:=z119 hL q93.1 q93.2.1 q93.2.2 1
      have qd1:opnd C k 1 - n < k:=by have:=z104 hL.1 q93.1 1;omega
      have q23:opnd C k 1 - n∈ tops G C ∪ orT G C:=by
       rw [Z4,z098,z097]
       rcases hL.1.1 _ (z069 hlt) with q17 | hor
       ·exact Or.inl ⟨hlt,q17,hbf⟩
       ·exact Or.inr ⟨hlt,hor,hbf⟩
      exact ih _ qd1 q23 (by rw [z070,show n+(opnd C k 1 - n)=opnd C k 1 by omega];exact h1)
  apply qnt (C.output - n) q32
  rw [z070,show n+(C.output - n)=C.output by omega]
  exact hcx
 ·rintro ⟨a,ha,hva⟩
  rw [z098] at ha
  rw [congrFun hL.2.1 x]
  exact ha.2.2 x hva
lemma z103 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (hne:∃ u v:Fin n,G.Adj u v)
  {g1 g2:ℕ} (q00:∀ k,k∈ junk G C↔ k=g1∨ k=g2):
  ∀ w < n+C.gates.length,
   (∀ k,w=n+k→ ¬ BelowF G C k)→
   ∀ x:Fin n→ Bool,
    wval C x w=true↔
     (∃ u∈ orIn n C w,x u=true)∨
     (OrReaches n C w g1∧ gateVal n C g1 x=true)∨
     (OrReaches n C w g2∧ gateVal n C g2 x=true):=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih=>
  intro hw hnb x
  by_cases hwn:w < n
  ·constructor
   ·intro hwx
    left
    refine ⟨⟨w,hwn⟩,(z095 C _ _).mpr rfl,?_⟩
    rwa [z144 C x w hwn] at hwx
   ·rintro (⟨u,hu,hxu⟩ | ⟨hr,_⟩ | ⟨hr,_⟩)
    ·have huw:u=⟨w,hwn⟩:=(z095 C u ⟨w,hwn⟩).mp hu
     subst huw;rw [z144 C x w hwn];exact hxu
    ·exact absurd hr (z112 hwn)
    ·exact absurd hr (z112 hwn)
  ·have hk:w - n < C.gates.length:=by omega
   have q0f:w=n+(w - n):=by omega
   have q5w:¬ BelowF G C (w - n):=hnb (w - n) q0f
   rcases hL.1.1 _ (z069 hk) with q17 | hor
   ·have q23:w - n∈ junk G C:=z094.mpr ⟨hk,q17,q5w⟩
    rw [q00] at q23
    constructor
    ·intro hwx
     rcases q23 with h1 | h2
     ·right;left
      refine ⟨?_,?_⟩
      ·rw [q0f,h1];exact z115 (by omega)
      ·rw [z070,← h1,← q0f];exact hwx
     ·right;right
      refine ⟨?_,?_⟩
      ·rw [q0f,h2];exact z115 (by omega)
      ·rw [z070,← h2,← q0f];exact hwx
    ·rintro (⟨u,hu,_⟩ | ⟨hr,hvg⟩ | ⟨hr,hvg⟩)
     ·rw [q0f,z107 hk q17] at hu;simp at hu
     ·exact z117 hL.1 x hr hvg
     ·exact z117 hL.1 x hr hvg
   ·have qc5:∀ b:Fin 2,∀ m,opnd C (w - n) b=n+m→ ¬ BelowF G C m:=by
     intro b m hm hbm
     exact z091 hL q01 hne hk hor q5w b (by rw [hm];exact hbm)
    have q80:opnd C (w - n) 0 < w:=by have:=z104 hL.1 hk 0;omega
    have q58:opnd C (w - n) 1 < w:=by have:=z104 hL.1 hk 1;omega
    have ih0:=ih (opnd C (w - n) 0) q80 (by omega) (qc5 0) x
    have ih1:=ih (opnd C (w - n) 1) q58 (by omega) (qc5 1) x
    rw [q0f,z142 hL.1 x hk hor,Z13,ih0,ih1,
     z108 hL.1 hk hor]
    have q59:∀ g,g=g1∨ g=g2→
      (OrReaches n C (n+(w - n)) g↔
       OrReaches n C (opnd C (w - n) 0) g∨ OrReaches n C (opnd C (w - n) 1) g):=by
     intro g hg
     have qjt:g≠ w - n:=by
      intro heq
      have hgj:g∈ junk G C:=(q00 g).mpr hg
      rw [heq,z094] at hgj
      rw [hor] at hgj;cases hgj.2.1
     rw [z111 hk]
     constructor
     ·rintro (heq | ⟨_,u,hu,_,_,hug⟩)
      ·exact absurd heq qjt
      ·rw [z071 hL.1 hk] at hu
       simp only [Z10,Z11,or_false] at hu
       rcases hu with rfl | rfl
       ·exact Or.inl hug
       ·exact Or.inr hug
     ·rintro (h0 | h1)
      ·exact Or.inr ⟨hor,opnd C (w - n) 0,z105 hL.1 hk 0,h0.1,z104 hL.1 hk 0,h0⟩
      ·exact Or.inr ⟨hor,opnd C (w - n) 1,z105 hL.1 hk 1,h1.1,z104 hL.1 hk 1,h1⟩
    rw [q59 g1 (Or.inl rfl),q59 g2 (Or.inr rfl)]
    constructor
    ·rintro ((⟨u,hu,hxu⟩ | ⟨h1,hg1⟩ | ⟨h2,hg2⟩) | (⟨u,hu,hxu⟩ | ⟨h1,hg1⟩ | ⟨h2,hg2⟩))
     ·exact Or.inl ⟨u,Finset.mem_union_left _ hu,hxu⟩
     ·exact Or.inr (Or.inl ⟨Or.inl h1,hg1⟩)
     ·exact Or.inr (Or.inr ⟨Or.inl h2,hg2⟩)
     ·exact Or.inl ⟨u,Finset.mem_union_right _ hu,hxu⟩
     ·exact Or.inr (Or.inl ⟨Or.inr h1,hg1⟩)
     ·exact Or.inr (Or.inr ⟨Or.inr h2,hg2⟩)
    ·rintro (⟨u,hu,hxu⟩ | ⟨h1 | h1,hg1⟩ | ⟨h2 | h2,hg2⟩)
     ·rcases Z4.mp hu with h0 | h1
      ·exact Or.inl (Or.inl ⟨u,h0,hxu⟩)
      ·exact Or.inr (Or.inl ⟨u,h1,hxu⟩)
     ·exact Or.inl (Or.inr (Or.inl ⟨h1,hg1⟩))
     ·exact Or.inr (Or.inr (Or.inl ⟨h1,hg1⟩))
     ·exact Or.inl (Or.inr (Or.inr ⟨h2,hg2⟩))
     ·exact Or.inr (Or.inr (Or.inr ⟨h2,hg2⟩))
lemma z102 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
  (h4:NoFourCycle G) {a b w1 w2:Fin n} (hab:a≠ b)
  (ha1:G.Adj a w1) (hb1:G.Adj b w1) (ha2:G.Adj a w2) (hb2:G.Adj b w2):w1=w2:=by
 by_contra hne
 have hle:=h4 a b hab
 have q0c:({w1,w2}:Finset (Fin n))⊆ Finset.univ.filter (fun w=>G.Adj a w∧ G.Adj b w):=by
  intro w hw
  simp only [Z6,Z3] at hw
  simp only [Z0,Z7,true_and]
  rcases hw with rfl | rfl
  ·exact ⟨ha1,hb1⟩
  ·exact ⟨ha2,hb2⟩
 have q18:=Finset.card_le_card q0c
 rw [Finset.card_pair hne] at q18
 omega
lemma z132 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hAO:IsAO2 n C) {a:ℕ} (ha:a∈ tops G C)
  {u v:Fin n} (hu:u∈ side (n:=n) C a 0) (hv:v∈ side (n:=n) C a 1):
  G.Adj u v:=by
 rw [z098] at ha
 have q10:gateVal n C a (pairInput u v)=true:=by
  rw [z070,z140 hAO _ ha.1 ha.2.1,Z12]
  exact ⟨z110 hAO _ hu (by simp [pairInput]),
   z110 hAO _ hv (by simp [pairInput])⟩
 exact (z074 u v).mp (ha.2.2 (pairInput u v) q10)
lemma z129 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hAO:IsAO2 n C) (h4:NoFourCycle G) {a:ℕ} (ha:a∈ tops G C \ centreless G C):
  (side (n:=n) C a 0).Nonempty∧ (side (n:=n) C a 1).Nonempty∧
   ((side (n:=n) C a 0).card=1∨ (side (n:=n) C a 1).card=1):=by
 rw [Z2] at ha
 have qmf:(side (n:=n) C a 0).Nonempty:=by
  rw [Finset.nonempty_iff_ne_empty]
  intro h0;exact ha.2 (Z0.mpr ⟨ha.1,Or.inl h0⟩)
 have qgb:(side (n:=n) C a 1).Nonempty:=by
  rw [Finset.nonempty_iff_ne_empty]
  intro h1;exact ha.2 (Z0.mpr ⟨ha.1,Or.inr h1⟩)
 refine ⟨qmf,qgb,?_⟩
 by_contra qb1
 push Not at qb1
 have hc0:1 < (side (n:=n) C a 0).card:=by
  have:=Finset.Nonempty.card_pos qmf;omega
 have hc1:1 < (side (n:=n) C a 1).card:=by
  have:=Finset.Nonempty.card_pos qgb;omega
 obtain ⟨u1,hu1,u2,hu2,qd2⟩:=Finset.one_lt_card.mp hc0
 obtain ⟨v1,hv1,v2,hv2,qnv⟩:=Finset.one_lt_card.mp hc1
 exact qnv (z102 h4 qd2
  (z132 hAO ha.1 hu1 hv1) (z132 hAO ha.1 hu2 hv1)
  (z132 hAO ha.1 hu1 hv2) (z132 hAO ha.1 hu2 hv2))
lemma z139 {n:ℕ} (gs1 gs2:List Gate) (o1 o2:ℕ) (x:Fin n→ Bool)
  {w:ℕ} (hw:w < n+gs1.length):
  wval ⟨gs1++gs2,o2⟩ x w=wval ⟨gs1,o1⟩ x w:=by
 unfold wval Circuit.wires
 rw [List.foldl_append]
 have q5v:w < (gs1.foldl (fun w g=>w++[g.op.eval (g.inputs.map fun i=>w.getD i false)])
   (List.ofFn x)).length:=by
  rw [z065,List.length_ofFn];exact hw
 exact z064 gs2 _ w q5v
def z008 (n:ℕ) (gs:List Gate):List ℕ→ List Gate × ℕ
 | []=>(gs,0)
 | [w]=>(gs,w)
 | w::w2::ws=>
  let res:=z008 n gs (w2::ws)
  (res.1++[⟨GateOp.or,[w,res.2]⟩],n+res.1.length)
lemma z011 (n:ℕ) (gs:List Gate) (ws:List ℕ):
  ∃ extra:List Gate,(z008 n gs ws).1=gs++extra:=by
 match ws with
 | []=>exact ⟨[],by simp [z008]⟩
 | [w]=>exact ⟨[],by simp [z008]⟩
 | w::w2::ws=>
  obtain ⟨extra,heq⟩:=z011 n gs (w2::ws)
  refine ⟨extra++[⟨GateOp.or,[w,(z008 n gs (w2::ws)).2]⟩],?_⟩
  simp only [z008,heq,List.append_assoc]
lemma z010 (n:ℕ) (gs:List Gate) (ws:List ℕ) (hne:ws≠ []):
  (z008 n gs ws).1.length=gs.length+(ws.length - 1):=by
 match ws with
 | []=>exact absurd rfl hne
 | [w]=>simp [z008]
 | w::w2::ws=>
  have ih:=z010 n gs (w2::ws) (by simp)
  simp only [z008,Z17,List.length_cons,List.length_nil] at ih ⊢
  omega
lemma z009 {n:ℕ} {gs:List Gate} (hAO:IsAO2 n ⟨gs,0⟩)
  (ws:List ℕ) (hne:ws≠ []) (hws:∀ w∈ ws,w < n+gs.length):
  IsAO2 n ⟨(z008 n gs ws).1,0⟩∧
   (z008 n gs ws).2 < n+(z008 n gs ws).1.length:=by
 match ws with
 | []=>exact absurd rfl hne
 | [w]=>
  simp only [z008]
  exact ⟨hAO,hws w (by simp)⟩
 | w::w2::ws=>
  have ⟨q4x,qnw⟩:=z009 hAO (w2::ws) (by simp) (fun u hu=>hws u (by simp [hu]))
  have qju:gs.length≤ (z008 n gs (w2::ws)).1.length:=by
   rw [z010 n gs (w2::ws) (by simp)];omega
  have qjv:w < n+(z008 n gs (w2::ws)).1.length:=by have:=hws w (by simp);omega
  simp only [z008]
  set gs':=(z008 n gs (w2::ws)).1
  set w':=(z008 n gs (w2::ws)).2
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  ·intro g hg
   simp only [List.mem_append,List.mem_singleton] at hg
   rcases hg with hg | rfl
   ·exact q4x.1 g hg
   ·exact Or.inr rfl
  ·intro j hj u hu
   simp only [Z17,List.length_singleton] at hj
   by_cases hlt:j < gs'.length
   ·have q4a:gateAt ⟨gs'++[⟨GateOp.or,[w,w']⟩],0⟩ j=gateAt ⟨gs',0⟩ j:=by
     rw [z068 (by simp;omega),z068 hlt]
     simp [List.getElem_append_left hlt]
    rw [q4a] at hu
    exact q4x.2.1 j hlt u hu
   ·have qjw:j=gs'.length:=by omega
    subst qjw
    have q4a:gateAt ⟨gs'++[⟨GateOp.or,[w,w']⟩],0⟩ gs'.length=⟨GateOp.or,[w,w']⟩:=by
     rw [z068 (by simp)]
     simp
    rw [q4a] at hu
    simp only [Z10,Z11,or_false] at hu
    rcases hu with rfl | rfl
    ·exact qjv
    ·exact qnw
  ·intro g hg
   simp only [List.mem_append,List.mem_singleton] at hg
   rcases hg with hg | rfl
   ·exact q4x.2.2 g hg
   ·rfl
  ·simp only [Z17,List.length_singleton];omega
lemma z012 {n:ℕ} {gs:List Gate} (hAO:IsAO2 n ⟨gs,0⟩) (x:Fin n→ Bool)
  (ws:List ℕ) (hne:ws≠ []) (hws:∀ w∈ ws,w < n+gs.length):
  wval ⟨(z008 n gs ws).1,0⟩ x (z008 n gs ws).2=
   decide (∃ w∈ ws,wval ⟨gs,0⟩ x w=true):=by
 match ws with
 | []=>exact absurd rfl hne
 | [w]=>
  simp only [z008,List.mem_singleton,exists_eq_left]
  cases wval ⟨gs,0⟩ x w <;> rfl
 | w::w2::ws=>
  have qd3:=z009 hAO (w2::ws) (by simp) (fun u hu=>hws u (by simp [hu]))
  have ih:=z012 hAO x (w2::ws) (by simp) (fun u hu=>hws u (by simp [hu]))
  have q4z:=z009 hAO (w::w2::ws) (by simp) hws
  obtain ⟨extra,qc6⟩:=z011 n gs (w2::ws)
  simp only [z008] at q4z ⊢
  set gs':=(z008 n gs (w2::ws)).1
  set w':=(z008 n gs (w2::ws)).2
  have qju:gs.length≤ gs'.length:=by rw [qc6,Z17];omega
  have qjv:w < n+gs.length:=hws w (by simp)
  have q4a:gateAt ⟨gs'++[⟨GateOp.or,[w,w']⟩],0⟩ gs'.length=⟨GateOp.or,[w,w']⟩:=by
   rw [z068 (by simp)];simp
  have qd4:opnd ⟨gs'++[⟨GateOp.or,[w,w']⟩],0⟩ gs'.length 0=w:=by
   unfold opnd;rw [q4a];rfl
  have qd5:opnd ⟨gs'++[⟨GateOp.or,[w,w']⟩],0⟩ gs'.length 1=w':=by
   unfold opnd;rw [q4a];rfl
  have qd6:gs'.length < (gs'++[({op:=GateOp.or,inputs:=[w,w']}:Gate)]).length:=by simp
  rw [z142 q4z.1 x qd6 (by rw [q4a]),qd4,qd5]
  rw [z139 gs' [({op:=GateOp.or,inputs:=[w,w']}:Gate)] 0 0 x (by omega),
   z139 gs' [({op:=GateOp.or,inputs:=[w,w']}:Gate)] 0 0 x qd3.2]
  have hvw:wval ⟨gs',0⟩ x w=wval ⟨gs,0⟩ x w:=by
   rw [qc6];exact z139 gs extra 0 0 x qjv
  rw [hvw,ih]
  apply Bool.eq_iff_iff.mpr
  simp only [Z13,Z1,Z10,exists_eq_or_imp]
lemma z007 {n:ℕ} {gs:List Gate} (hAO:IsAO2 n ⟨gs,0⟩)
  {op:GateOp} (hop:op=GateOp.and∨ op=GateOp.or)
  {w0 w1:ℕ} (h0:w0 < n+gs.length) (h1:w1 < n+gs.length):
  IsAO2 n ⟨gs++[⟨op,[w0,w1]⟩],0⟩:=by
 refine ⟨?_,?_,?_⟩
 ·intro g hg
  simp only [List.mem_append,List.mem_singleton] at hg
  rcases hg with hg | rfl
  ·exact hAO.1 g hg
  ·exact hop
 ·intro j hj u hu
  simp only [Z17,List.length_singleton] at hj
  by_cases hlt:j < gs.length
  ·have q4a:gateAt ⟨gs++[⟨op,[w0,w1]⟩],0⟩ j=gateAt ⟨gs,0⟩ j:=by
    rw [z068 (by simp;omega),z068 hlt];simp [List.getElem_append_left hlt]
   rw [q4a] at hu
   exact hAO.2.1 j hlt u hu
  ·have qjw:j=gs.length:=by omega
   subst qjw
   have q4a:gateAt ⟨gs++[⟨op,[w0,w1]⟩],0⟩ gs.length=⟨op,[w0,w1]⟩:=by
    rw [z068 (by simp)];simp
   rw [q4a] at hu
   simp only [Z10,Z11,or_false] at hu
   rcases hu with rfl | rfl <;> assumption
 ·intro g hg
  simp only [List.mem_append,List.mem_singleton] at hg
  rcases hg with hg | rfl
  ·exact hAO.2.2 g hg
  ·rfl
def z016 (n:ℕ) (C:Circuit) (lamList:List ℕ):ℕ→ ℕ
 | w=>
  if hw:w < n then w
  else
   let k:=w - n
   if hk:k < C.gates.length then
    if k∈ lamList then n+lamList.idxOf k
    else if (orIn n C (opnd C k 0)).Nonempty then
     if hlt:opnd C k 0 < w then z016 n C lamList (opnd C k 0) else 0
    else
     if hlt:opnd C k 1 < w then z016 n C lamList (opnd C k 1) else 0
   else 0
termination_by w=>w
def z082 (n:ℕ) (C:Circuit) (lamList:List ℕ):List Gate:=
 lamList.map fun k=>⟨GateOp.or,[z016 n C lamList (opnd C k 0),z016 n C lamList (opnd C k 1)]⟩
lemma z017 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (lamList:List ℕ)
  (q1m:lamList.Pairwise (· < ·)):
  ∀ w < n+C.gates.length,z016 n C lamList w < n∨
   (n≤ w∧ ∃ k∈ lamList,k≤ w - n∧ z016 n C lamList w=n+lamList.idxOf k):=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih=>
  intro qnx
  unfold z016
  dsimp only
  split_ifs with hw hk q23 h0 q80 h1
  ·exact Or.inl hw
  ·exact Or.inr ⟨by omega,w - n,q23,le_refl _,rfl⟩
  ·rcases ih (opnd C (w - n) 0) q80 (by omega) with hlt | ⟨qmg,k,qd7,qny,heq⟩
   ·exact Or.inl hlt
   ·exact Or.inr ⟨by omega,k,qd7,by omega,heq⟩
  ·exfalso;have:=z104 hAO hk 0;omega
  ·rcases ih (opnd C (w - n) 1) h1 (by omega) with hlt | ⟨qmg,k,qd7,qny,heq⟩
   ·exact Or.inl hlt
   ·exact Or.inr ⟨by omega,k,qd7,by omega,heq⟩
  ·exfalso;have:=z104 hAO hk 1;omega
  ·exfalso;omega
lemma z077 {l:List ℕ} (q1m:l.Pairwise (· < ·))
  {a b:ℕ} (ha:a∈ l) (hb:b∈ l) (hab:a < b):l.idxOf a < l.idxOf b:=by
 induction l with
 | nil=>cases ha
 | cons x xs ih=>
  rw [List.pairwise_cons] at q1m
  simp only [Z10] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  ·omega
  ·rw [List.idxOf_cons_self]
   have hne:a≠ b:=Nat.ne_of_lt hab
   rw [List.idxOf_cons_ne _ (by simp [hne])]
   exact Nat.succ_pos _
  ·have:=q1m.1 a ha;omega
  ·have qnz:x≠ a:=by have:=q1m.1 a ha;omega
   have qax:x≠ b:=by have:=q1m.1 b hb;omega
   rw [List.idxOf_cons_ne _ (by simp [qnz]),List.idxOf_cons_ne _ (by simp [qax])]
   exact Nat.succ_lt_succ (ih q1m.2 ha hb)
lemma z076 {l:List ℕ} (q61:l.Nodup) (j:ℕ) (hj:j < l.length):
  l.idxOf l[j]=j:=by
 induction l generalizing j with
 | nil=>cases hj
 | cons x xs ih=>
  rw [List.nodup_cons] at q61
  cases j with
  | zero=>simp
  | succ j'=>
   simp only [List.getElem_cons_succ]
   have hj':j' < xs.length:=by simp only [List.length_cons] at hj;omega
   have hne:x≠ xs[j']:=fun h=>q61.1 (h ▸ List.getElem_mem hj')
   rw [List.idxOf_cons_ne _ (by simp [hne]),ih q61.2 j' hj']
lemma z083 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C)
  (lamList:List ℕ) (q1m:lamList.Pairwise (· < ·))
  (q4b:∀ k∈ lamList,k < C.gates.length):
  IsAO2 n ⟨z082 n C lamList,0⟩:=by
 refine ⟨?_,?_,?_⟩
 ·intro g hg
  simp only [z082,List.mem_map] at hg
  rcases hg with ⟨k,_,rfl⟩
  exact Or.inr rfl
 ·intro j hj u hu
  simp only [z082,List.length_map] at hj
  rw [z068 (by simp [z082,hj])] at hu
  simp only [z082,List.getElem_map,Z10,Z11,or_false] at hu
  set k:=lamList[j]
  have q3w:k∈ lamList:=List.getElem_mem hj
  have q0d:k < C.gates.length:=q4b k q3w
  have q92:lamList.idxOf k=j:=by
   have q61:lamList.Nodup:=q1m.imp (fun {a b} h=>Nat.ne_of_lt h)
   exact z076 q61 j hj
  have check_b:∀ b:Fin 2,z016 n C lamList (opnd C k b) < n+j:=by
   intro b
   have qph:opnd C k b < n+k:=z104 hAO q0d b
   rcases z017 hAO lamList q1m (opnd C k b) (by omega) with hlt | ⟨qmg,k',qo0,qo1,heq⟩
   ·omega
   ·rw [heq]
    have qjx:k' < k:=by omega
    have qd8:=z077 q1m qo0 q3w qjx
    rw [q92] at qd8
    omega
  rcases hu with rfl | rfl
  ·exact check_b 0
  ·exact check_b 1
 ·intro g hg
  simp only [z082,List.mem_map] at hg
  rcases hg with ⟨k,_,rfl⟩
  rfl
def z001 {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (w:ℕ):Prop:=
 w < n+C.gates.length∧ (orIn n C w).Nonempty∧
  (∀ k,w=n+k→ ¬ BelowF G C k)∧
  (∀ k,OrReaches n C w k→ k∈ orN G C→
   (orIn n C (opnd C k 0)).Nonempty→ (orIn n C (opnd C k 1)).Nonempty→ k∈ lam G C)
lemma z087 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (hne:∃ u v:Fin n,G.Adj u v)
  {k:ℕ} (hk:k∈ orN G C) (hlw:z001 G C (n+k))
  (b:Fin 2) (qax:(orIn n C (opnd C k b)).Nonempty):
  z001 G C (opnd C k b):=by
 have hk':=z096.mp hk
 have hlt:opnd C k b < n+k:=z104 hL.1 hk'.1 b
 refine ⟨by omega,qax,?_,?_⟩
 ·intro m hm hbm
  exact z091 hL q01 hne hk'.1 hk'.2.1 hk'.2.2 b (by rw [hm];exact hbm)
 ·intro m hrm q9d h0 h1
  apply hlw.2.2.2 m _ q9d h0 h1
  exact (z111 hk'.1).mpr
   (Or.inr ⟨hk'.2.1,opnd C k b,z105 hL.1 hk'.1 b,hrm.1,hlt,hrm⟩)
lemma z086 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (hne:∃ u v:Fin n,G.Adj u v)
  {a:ℕ} (ha:a∈ tops G C) (b:Fin 2)
  (qax:(side (n:=n) C a b).Nonempty) (q18:(side (n:=n) C a (1 - b)).card=1):
  z001 G C (opnd C a b):=by
 have ha':=z098.mp ha
 have hlt:opnd C a b < n+a:=z104 hL.1 ha'.1 b
 refine ⟨by omega,qax,?_,?_⟩
 ·intro m hm hbm
  exact z089 hL hne ha'.1 ha'.2.1 b (by rw [hm];exact hbm)
 ·intro m hrm q9d h0 h1
  unfold lam
  exact Z0.mpr ⟨q9d,h0,h1,a,ha,b,q18,hrm⟩
lemma z018 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (hne:∃ u v:Fin n,G.Adj u v)
  (lamList:List ℕ) (q1m:lamList.Pairwise (· < ·))
  (q0s:∀ k,k∈ lamList↔ k∈ lam G C)
  (x:Fin n→ Bool):
  ∀ w,z001 G C w→
   z016 n C lamList w < n+lamList.length∧
   wval ⟨z082 n C lamList,0⟩ x (z016 n C lamList w)=
    decide (∃ u∈ orIn n C w,x u=true):=by
 have q4b:∀ k∈ lamList,k < C.gates.length:=fun k hk=>by
  have:=(q0s k).mp hk;exact (z096.mp (Z0.mp this).1).1
 have qd9:=z083 hL.1 lamList q1m q4b
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih=>
  intro hlw
  by_cases hwn:w < n
  ·have hbp:z016 n C lamList w=w:=by unfold z016;rw [dif_pos hwn]
   rw [hbp]
   refine ⟨by omega,?_⟩
   rw [z144 _ x w hwn]
   apply Bool.eq_iff_iff.mpr
   simp only [Z1]
   constructor
   ·intro h;exact ⟨⟨w,hwn⟩,(z095 C _ _).mpr rfl,h⟩
   ·rintro ⟨u,hu,hxu⟩
    have heq:=(z095 C u ⟨w,hwn⟩).mp hu
    subst heq;exact hxu
  ·have q0d:w - n < C.gates.length:=by have:=hlw.1;omega
   have q0f:w=n+(w - n):=by omega
   set k:=w - n
   have q5w:¬ BelowF G C k:=hlw.2.2.1 k q0f
   have q3d:(gateAt C k).op=GateOp.or:=by
    rcases hL.1.1 _ (z069 q0d) with q17 | hor
    ·exfalso
     have q0g:=z107 (n:=n) q0d q17
     rw [← q0f] at q0g
     exact hlw.2.1.ne_empty q0g
    ·exact hor
   have q04:k∈ orN G C:=z096.mpr ⟨q0d,q3d,q5w⟩
   have q9e:z001 G C (n+k):=by rwa [← q0f]
   have q0o:orIn n C w=orIn n C (opnd C k 0) ∪ orIn n C (opnd C k 1):=by
    rw [q0f];exact z108 hL.1 q0d q3d
   have q80:opnd C k 0 < w:=by have:=z104 hL.1 q0d 0;omega
   have q58:opnd C k 1 < w:=by have:=z104 hL.1 q0d 1;omega
   by_cases q23:k∈ lamList
   ·have hbp:z016 n C lamList w=n+lamList.idxOf k:=by
     unfold z016;rw [dif_neg hwn,dif_pos q0d,if_pos q23]
    have q9f:lamList.idxOf k < lamList.length:=List.idxOf_lt_length_iff.mpr q23
    have hkl:k∈ lam G C:=(q0s k).mp q23
    have q6w:(orIn n C (opnd C k 0)).Nonempty:=(Z0.mp hkl).2.1
    have q62:(orIn n C (opnd C k 1)).Nonempty:=(Z0.mp hkl).2.2.1
    have ih0:=ih (opnd C k 0) q80 (z087 hL q01 hne q04 q9e 0 q6w)
    have ih1:=ih (opnd C k 1) q58 (z087 hL q01 hne q04 q9e 1 q62)
    rw [hbp]
    refine ⟨by omega,?_⟩
    have hj':lamList.idxOf k < (z082 n C lamList).length:=by simp [z082,q9f]
    have qo2:lamList[lamList.idxOf k]=k:=List.getElem_idxOf q9f
    have q4a:gateAt ⟨z082 n C lamList,0⟩ (lamList.idxOf k)=
      ⟨GateOp.or,[z016 n C lamList (opnd C k 0),z016 n C lamList (opnd C k 1)]⟩:=by
     rw [z068 hj'];simp [z082,qo2]
    rw [z142 qd9 x hj' (by rw [q4a])]
    have qd4:opnd ⟨z082 n C lamList,0⟩ (lamList.idxOf k) 0=
      z016 n C lamList (opnd C k 0):=by unfold opnd;rw [q4a];rfl
    have qd5:opnd ⟨z082 n C lamList,0⟩ (lamList.idxOf k) 1=
      z016 n C lamList (opnd C k 1):=by unfold opnd;rw [q4a];rfl
    rw [qd4,qd5,ih0.2,ih1.2,q0o]
    apply Bool.eq_iff_iff.mpr
    simp only [Z13,Z1,Z4]
    constructor
    ·rintro (⟨u,hu,hxu⟩ | ⟨u,hu,hxu⟩)
     ·exact ⟨u,Or.inl hu,hxu⟩
     ·exact ⟨u,Or.inr hu,hxu⟩
    ·rintro ⟨u,hu | hu,hxu⟩
     ·exact Or.inl ⟨u,hu,hxu⟩
     ·exact Or.inr ⟨u,hu,hxu⟩
   ·have q5b:¬ ((orIn n C (opnd C k 0)).Nonempty∧ (orIn n C (opnd C k 1)).Nonempty):=by
     rintro ⟨h0,h1⟩
     apply q23
     rw [q0s]
     exact q9e.2.2.2 k (z115 q0d) q04 h0 h1
    by_cases q6w:(orIn n C (opnd C k 0)).Nonempty
    ·have q5c:orIn n C (opnd C k 1)=∅:=by
      by_contra qgb;exact q5b ⟨q6w,Finset.nonempty_iff_ne_empty.mpr qgb⟩
     have hbp:z016 n C lamList w=z016 n C lamList (opnd C k 0):=by
      conv_lhs=>unfold z016
      dsimp only
      rw [dif_neg hwn,dif_pos q0d,if_neg q23,if_pos q6w,dif_pos q80]
     rw [hbp,q0o,q5c,Finset.union_empty]
     exact ih (opnd C k 0) q80 (z087 hL q01 hne q04 q9e 0 q6w)
    ·have q50:orIn n C (opnd C k 0)=∅:=Z25.mp q6w
     have q62:(orIn n C (opnd C k 1)).Nonempty:=by
      have qay:=hlw.2.1
      rw [q0o,q50,Finset.empty_union] at qay
      exact qay
     have hbp:z016 n C lamList w=z016 n C lamList (opnd C k 1):=by
      conv_lhs=>unfold z016
      dsimp only
      rw [dif_neg hwn,dif_pos q0d,if_neg q23,if_neg q6w,dif_pos q58]
     rw [hbp,q0o,q50,Finset.empty_union]
     exact ih (opnd C k 1) q58 (z087 hL q01 hne q04 q9e 1 q62)
def z003 (n:ℕ) (gs:List Gate) (v:Fin n) (base:Option ℕ) (extra:List (Fin n)):
  List Gate × ℕ:=
 match base,extra with
 | some bw,[]=>
  (gs++[⟨GateOp.and,[v.val,bw]⟩],n+gs.length)
 | some bw,e::es=>
  let r1:=z008 n gs ((e::es).map Fin.val)
  let gs2:=r1.1++[⟨GateOp.or,[bw,r1.2]⟩]
  (gs2++[⟨GateOp.and,[v.val,n+r1.1.length]⟩],n+gs2.length)
 | none,e::es=>
  let r1:=z008 n gs ((e::es).map Fin.val)
  (r1.1++[⟨GateOp.and,[v.val,r1.2]⟩],n+r1.1.length)
 | none,[]=>(gs,0)
def z005 (n:ℕ) (gs:List Gate):
  List (Fin n × Option ℕ × List (Fin n))→ List Gate × List ℕ
 | []=>(gs,[])
 | (v,base,extra)::rest=>
  let r:=z003 n gs v base extra
  let r2:=z005 n r.1 rest
  (r2.1,r.2::r2.2)
lemma z004 {n:ℕ} {gs:List Gate} (hAO:IsAO2 n ⟨gs,0⟩)
  (v:Fin n) (base:Option ℕ) (extra:List (Fin n))
  (qgc:∀ bw,base=some bw→ bw < n+gs.length)
  (hne:base.isSome∨ extra≠ []):
  (∃ ex:List Gate,(z003 n gs v base extra).1=gs++ex)∧
  (z003 n gs v base extra).1.length=
   gs.length+extra.length+(if base.isSome then 1 else 0)∧
  IsAO2 n ⟨(z003 n gs v base extra).1,0⟩∧
  (z003 n gs v base extra).2 < n+(z003 n gs v base extra).1.length∧
  ∀ x:Fin n→ Bool,
   wval ⟨(z003 n gs v base extra).1,0⟩ x (z003 n gs v base extra).2=
    (x v && (decide (∃ bw,base=some bw∧ wval ⟨gs,0⟩ x bw=true) ||
     decide (∃ u∈ extra,x u=true))):=by
 cases base with
 | none=>
  cases extra with
  | nil=>simp at hne
  | cons e es=>
   have hws:∀ w∈ (e::es).map Fin.val,w < n+gs.length:=by
    intro w hw;simp only [List.mem_map] at hw;rcases hw with ⟨u,_,rfl⟩;omega
   obtain ⟨ex1,q94⟩:=z011 n gs ((e::es).map Fin.val)
   have q9g:=z010 n gs ((e::es).map Fin.val) (by simp)
   have ⟨qda,q58⟩:=z009 hAO ((e::es).map Fin.val) (by simp) hws
   dsimp only [z003]
   set gs1:=(z008 n gs ((e::es).map Fin.val)).1
   set w1:=(z008 n gs ((e::es).map Fin.val)).2
   have q8p:=z007 qda (Or.inl rfl) (by omega:v.val < n+gs1.length) q58
   refine ⟨⟨ex1++[⟨GateOp.and,[v.val,w1]⟩],by rw [q94,List.append_assoc]⟩,
    ?_,q8p,by simp,?_⟩
   ·simp only [Z17,List.length_cons,List.length_nil,q9g,List.length_map,
     Option.isSome_none,Bool.false_eq_true,↓reduceIte]
    omega
   ·intro x
    have q4a:gateAt ⟨gs1++[⟨GateOp.and,[v.val,w1]⟩],0⟩ gs1.length=
      ⟨GateOp.and,[v.val,w1]⟩:=by rw [z068 (by simp)];simp
    rw [z140 q8p x (by simp) (by rw [q4a])]
    have qd4:opnd ⟨gs1++[⟨GateOp.and,[v.val,w1]⟩],0⟩ gs1.length 0=v.val:=by
     unfold opnd;rw [q4a];rfl
    have qd5:opnd ⟨gs1++[⟨GateOp.and,[v.val,w1]⟩],0⟩ gs1.length 1=w1:=by
     unfold opnd;rw [q4a];rfl
    rw [qd4,qd5,z144 _ x v.val v.isLt,
     z139 gs1 [⟨GateOp.and,[v.val,w1]⟩] 0 0 x q58,
     z012 hAO x ((e::es).map Fin.val) (by simp) hws]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [Z13,Z1,List.mem_map,false_or,reduceCtorEq,false_and,exists_false]
    constructor
    ·rintro ⟨_,⟨u,hu,rfl⟩,hxu⟩
     rw [z144 _ x u.val u.isLt] at hxu;exact ⟨u,hu,hxu⟩
    ·rintro ⟨u,hu,hxu⟩
     exact ⟨u.val,⟨u,hu,rfl⟩,by rw [z144 _ x u.val u.isLt];exact hxu⟩
 | some bw=>
  have hbw:bw < n+gs.length:=qgc bw rfl
  cases extra with
  | nil=>
   have q8p:=z007 hAO (Or.inl rfl) (by omega:v.val < n+gs.length) hbw
   refine ⟨⟨[⟨GateOp.and,[v.val,bw]⟩],rfl⟩,?_,q8p,by simp [z003],?_⟩
   ·simp [z003]
   ·intro x
    simp only [z003]
    have q4a:gateAt ⟨gs++[⟨GateOp.and,[v.val,bw]⟩],0⟩ gs.length=
      ⟨GateOp.and,[v.val,bw]⟩:=by rw [z068 (by simp)];simp
    rw [z140 q8p x (by simp) (by rw [q4a])]
    have qd4:opnd ⟨gs++[⟨GateOp.and,[v.val,bw]⟩],0⟩ gs.length 0=v.val:=by
     unfold opnd;rw [q4a];rfl
    have qd5:opnd ⟨gs++[⟨GateOp.and,[v.val,bw]⟩],0⟩ gs.length 1=bw:=by
     unfold opnd;rw [q4a];rfl
    rw [qd4,qd5,z144 _ x v.val v.isLt,
     z139 gs [⟨GateOp.and,[v.val,bw]⟩] 0 0 x hbw]
    congr 1
    cases h:wval ⟨gs,0⟩ x bw <;> simp [h]
  | cons e es=>
   have hws:∀ w∈ (e::es).map Fin.val,w < n+gs.length:=by
    intro w hw;simp only [List.mem_map] at hw;rcases hw with ⟨u,_,rfl⟩;omega
   obtain ⟨ex1,q94⟩:=z011 n gs ((e::es).map Fin.val)
   have q9g:=z010 n gs ((e::es).map Fin.val) (by simp)
   have ⟨qda,q58⟩:=z009 hAO ((e::es).map Fin.val) (by simp) hws
   dsimp only [z003]
   set gs1:=(z008 n gs ((e::es).map Fin.val)).1
   set w1:=(z008 n gs ((e::es).map Fin.val)).2
   have qmh:bw < n+gs1.length:=by rw [q94,Z17];omega
   have q8p:=z007 qda (Or.inr rfl) qmh q58
   set gs2:=gs1++[⟨GateOp.or,[bw,w1]⟩]
   have qj2:=z007 q8p (Or.inl rfl)
    (by simp [gs2];omega:v.val < n+gs2.length) (by simp [gs2]:n+gs1.length < n+gs2.length)
   refine ⟨⟨ex1++[⟨GateOp.or,[bw,w1]⟩,⟨GateOp.and,[v.val,n+gs1.length]⟩],
     by simp only [gs2,q94,List.append_assoc];rfl⟩,
    ?_,qj2,by simp [gs2],?_⟩
   ·simp only [gs2,Z17,List.length_cons,List.length_nil,q9g,
     List.length_map,Option.isSome_some,↓reduceIte]
    omega
   ·intro x
    have qdb:gateAt ⟨gs2++[⟨GateOp.and,[v.val,n+gs1.length]⟩],0⟩ gs2.length=
      ⟨GateOp.and,[v.val,n+gs1.length]⟩:=by rw [z068 (by simp)];simp
    rw [z140 qj2 x (by simp) (by rw [qdb])]
    have qjy:opnd ⟨gs2++[⟨GateOp.and,[v.val,n+gs1.length]⟩],0⟩ gs2.length 0=v.val:=by
     unfold opnd;rw [qdb];rfl
    have qjz:opnd ⟨gs2++[⟨GateOp.and,[v.val,n+gs1.length]⟩],0⟩ gs2.length 1=
      n+gs1.length:=by unfold opnd;rw [qdb];rfl
    rw [qjy,qjz,z144 _ x v.val v.isLt,
     z139 gs2 [⟨GateOp.and,[v.val,n+gs1.length]⟩] 0 0 x (by simp [gs2])]
    have qdc:gateAt ⟨gs2,0⟩ gs1.length=⟨GateOp.or,[bw,w1]⟩:=by
     rw [z068 (by simp [gs2])];simp [gs2]
    rw [z142 q8p x (by simp [gs2]) (by rw [qdc])]
    have qk0:opnd ⟨gs2,0⟩ gs1.length 0=bw:=by unfold opnd;rw [qdc];rfl
    have qk1:opnd ⟨gs2,0⟩ gs1.length 1=w1:=by unfold opnd;rw [qdc];rfl
    rw [qk0,qk1,z139 gs1 [⟨GateOp.or,[bw,w1]⟩] 0 0 x qmh,
     z139 gs1 [⟨GateOp.or,[bw,w1]⟩] 0 0 x q58]
    have qo3:wval ⟨gs1,0⟩ x bw=wval ⟨gs,0⟩ x bw:=by
     rw [q94];exact z139 gs ex1 0 0 x hbw
    rw [qo3,z012 hAO x ((e::es).map Fin.val) (by simp) hws]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [Z13,Z1,List.mem_map,Option.some.injEq,exists_eq_left']
    constructor
    ·rintro (h | ⟨_,⟨u,hu,rfl⟩,hxu⟩)
     ·exact Or.inl h
     ·rw [z144 _ x u.val u.isLt] at hxu;exact Or.inr ⟨u,hu,hxu⟩
    ·rintro (h | ⟨u,hu,hxu⟩)
     ·exact Or.inl h
     ·exact Or.inr ⟨u.val,⟨u,hu,rfl⟩,by rw [z144 _ x u.val u.isLt];exact hxu⟩
lemma z006 {n:ℕ} {gs:List Gate} (hAO:IsAO2 n ⟨gs,0⟩)
  (items:List (Fin n × Option ℕ × List (Fin n)))
  (q9h:∀ it∈ items,(∀ bw,it.2.1=some bw→ bw < n+gs.length)∧
   (it.2.1.isSome∨ it.2.2≠ [])):
  (∃ ex:List Gate,(z005 n gs items).1=gs++ex)∧
  (z005 n gs items).1.length=
   gs.length+(items.map fun it=>it.2.2.length+(if it.2.1.isSome then 1 else 0)).sum∧
  (z005 n gs items).2.length=items.length∧
  IsAO2 n ⟨(z005 n gs items).1,0⟩∧
  (∀ w∈ (z005 n gs items).2,w < n+(z005 n gs items).1.length)∧
  ∀ x:Fin n→ Bool,
   (∃ w∈ (z005 n gs items).2,wval ⟨(z005 n gs items).1,0⟩ x w=true)↔
    ∃ it∈ items,x it.1=true∧
     ((∃ bw,it.2.1=some bw∧ wval ⟨gs,0⟩ x bw=true)∨
      ∃ u∈ it.2.2,x u=true):=by
 induction items generalizing gs with
 | nil=>
  refine ⟨⟨[],by simp [z005]⟩,by simp [z005],rfl,hAO,by simp [z005],?_⟩
  intro x;simp [z005]
 | cons it rest ih=>
  rcases it with ⟨v,base,extra⟩
  have hit:=q9h (v,base,extra) (by simp)
  obtain ⟨⟨ex1,q94⟩,q9g,qda,q58,qk2⟩:=z004 hAO v base extra hit.1 hit.2
  dsimp only [z005]
  set r:=z003 n gs v base extra
  have qd3:∀ it'∈ rest,(∀ bw,it'.2.1=some bw→ bw < n+r.1.length)∧
    (it'.2.1.isSome∨ it'.2.2≠ []):=by
   intro it' qk3
   have h0:=q9h it' (by simp [qk3])
   exact ⟨fun bw hbw=>by have:=h0.1 bw hbw;rw [q94,Z17];omega,h0.2⟩
  obtain ⟨⟨ex2,qb2⟩,qdd,q63,q8p,qj3,qde⟩:=ih qda qd3
  refine ⟨⟨ex1++ex2,by rw [qb2,q94,List.append_assoc]⟩,?_,?_,q8p,?_,?_⟩
  ·simp only [qdd,q9g,Z15,List.sum_cons];omega
  ·simp only [List.length_cons,q63]
  ·intro w hw
   simp only [Z10] at hw
   rcases hw with rfl | hw
   ·rw [qb2,Z17];omega
   ·exact qj3 w hw
  ·intro x
   simp only [Z10,exists_eq_or_imp]
   have hvw:wval ⟨(z005 n r.1 rest).1,0⟩ x r.2=
     (x v && (decide (∃ bw,base=some bw∧ wval ⟨gs,0⟩ x bw=true) ||
      decide (∃ u∈ extra,x u=true))):=by
    rw [qb2,z139 r.1 ex2 0 0 x q58,qk2 x]
   have q9i:(∃ w∈ (z005 n r.1 rest).2,wval ⟨(z005 n r.1 rest).1,0⟩ x w=true)↔
     ∃ it'∈ rest,x it'.1=true∧
      ((∃ bw,it'.2.1=some bw∧ wval ⟨gs,0⟩ x bw=true)∨
       ∃ u∈ it'.2.2,x u=true):=by
    rw [qde x]
    apply exists_congr;intro it'
    apply and_congr_right;intro qk3
    apply and_congr_right;intro _
    apply or_congr_left
    apply exists_congr;intro bw
    apply and_congr_right;intro hbw
    have qgd:=(q9h it' (by simp [qk3])).1 bw hbw
    rw [q94,z139 gs ex1 0 0 x qgd]
   rw [hvw,q9i]
   simp only [Z12,Z13,Z1]
lemma z093 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (h4:NoFourCycle G)
  {g1 g2:ℕ} (qdf:g1≠ g2) (q00:∀ k,k∈ junk G C↔ k=g1∨ k=g2)
  (hne:∃ u v:Fin n,G.Adj u v)
  (Zact Zhas:Finset (Fin n)) (L:Fin n→ Finset (Fin n)) (topOf:Fin n→ ℕ)
  (q5d:Zhas⊆ Zact)
  (q8q:∀ v∈ Zact,(L v).Nonempty)
  (qge:∀ v∈ Zact,∀ u∈ L v,G.Adj v u)
  (qgf:∀ e∈ Ustar G C,∃ v∈ Zact,∃ u∈ L v,e=s(v,u))
  (q41:∀ v∈ Zhas,topOf v∈ tops G C \ centreless G C)
  (q64:∀ v∈ Zhas,side (n:=n) C (topOf v) 0={v}∨ side (n:=n) C (topOf v) 1={v})
  (q5e:∀ v1∈ Zhas,∀ v2∈ Zhas,topOf v1=topOf v2→ v1=v2):
  2 * (centreless G C).card+(orN G C \ lam G C).card+2≤
   (∑ v∈ Zact,(L v).card)+(Zact \ Zhas).card:=by
 classical
 set S_tops:=tops G C \ centreless G C
 set lamList:=(lam G C).sort (·≤ ·)
 have q1m:lamList.Pairwise (· < ·):=
  ((Finset.pairwise_sort (lam G C) (·≤ ·)).and (Finset.sort_nodup (lam G C) (·≤ ·))).imp
   (fun ⟨h1,h2⟩=>Nat.lt_of_le_of_ne h1 h2)
 have q0s:∀ k,k∈ lamList↔ k∈ lam G C:=fun k=>Finset.mem_sort (·≤ ·)
 have q42:lamList.length=(lam G C).card:=Finset.length_sort (·≤ ·)
 have q4b:∀ k∈ lamList,k < C.gates.length:=fun k hk=>
  (z096.mp (Z0.mp ((q0s k).mp hk)).1).1
 set gs1:=z082 n C lamList
 have qda:IsAO2 n ⟨gs1,0⟩:=z083 hL.1 lamList q1m q4b
 have q43:gs1.length=(lam G C).card:=by simp [gs1,z082,q42]
 let mkTopItem:ℕ→ Fin n × Option ℕ × List (Fin n):=fun a=>
  if h:∃ v∈ Zhas,topOf v=a then
   let v:=Classical.choose h
   have hv:=Classical.choose_spec h
   have hs:side (n:=n) C a 0={v}∨ side (n:=n) C a 1={v}:=by
    rw [← hv.2];exact q64 v hv.1
   let b:Fin 2:=if side (n:=n) C a 0={v} then 1 else 0
   (v,some (z016 n C lamList (opnd C a b)),(L v).toList)
  else
   if ha:a∈ S_tops then
    have hst:=z129 hL.1 h4 ha
    if h0:(side (n:=n) C a 0).card=1 then
     let v:=Classical.choose (Finset.card_eq_one.mp h0)
     (v,some (z016 n C lamList (opnd C a 1)),[])
    else
     have h1:(side (n:=n) C a 1).card=1:=hst.2.2.resolve_left h0
     let v:=Classical.choose (Finset.card_eq_one.mp h1)
     (v,some (z016 n C lamList (opnd C a 0)),[])
   else
    (Classical.choose hne,none,[])
 let topItems:=S_tops.toList.map mkTopItem
 let newItems:=(Zact \ Zhas).toList.map fun v=>(v,(none:Option ℕ),(L v).toList)
 let allItems:=topItems++newItems
 have q19:∀ a∈ S_tops,
   let it:=mkTopItem a
   (∀ bw,it.2.1=some bw→ bw < n+gs1.length)∧
   it.2.1.isSome∧
   (∀ x:Fin n→ Bool,
    (x it.1=true∧ ((∃ bw,it.2.1=some bw∧ wval ⟨gs1,0⟩ x bw=true)∨
     ∃ u∈ it.2.2,x u=true))↔
    ((∃ u∈ side (n:=n) C a 0,x u=true)∧ (∃ v∈ side (n:=n) C a 1,x v=true))∨
     ∃ v∈ Zhas,topOf v=a∧ x v=true∧ ∃ u∈ L v,x u=true):=by
  intro a ha
  have q25:a∈ tops G C:=(Z2.mp ha).1
  have hst:=z129 hL.1 h4 ha
  by_cases h:∃ v∈ Zhas,topOf v=a
  ·simp only [mkTopItem,dif_pos h]
   set v:=Classical.choose h
   have hv:=Classical.choose_spec h
   have hs:side (n:=n) C a 0={v}∨ side (n:=n) C a 1={v}:=by
    rw [← hv.2];exact q64 v hv.1
   set b:Fin 2:=if side (n:=n) C a 0={v} then 1 else 0
   have q51:side (n:=n) C a (1 - b)={v}:=by
    by_cases h0:side (n:=n) C a 0={v}
    ·simp [b,h0]
    ·simp [b,h0];exact hs.resolve_left h0
   have q18:(side (n:=n) C a (1 - b)).card=1:=by rw [q51];simp
   have qax:(side (n:=n) C a b).Nonempty:=by
    by_cases h0:side (n:=n) C a 0={v}
    ·simp [b,h0];exact hst.2.1
    ·simp [b,h0];exact hst.1
   have hlw:=z086 hL hne q25 b qax q18
   refine ⟨?_,rfl,?_⟩
   ·intro bw hbw
    injection hbw with hbw;subst hbw
    have:=(z018 hL q01 hne lamList q1m q0s (fun _=>false) _ hlw).1
    rw [q43,← q42];exact this
   ·intro x
    have hbp:wval ⟨gs1,0⟩ x (z016 n C lamList (opnd C a b))=
      decide (∃ u∈ orIn n C (opnd C a b),x u=true):=
     (z018 hL q01 hne lamList q1m q0s x _ hlw).2
    simp only [Option.some.injEq,exists_eq_left',hbp,Z1,Finset.mem_toList]
    have qk4:∀ v'∈ Zhas,topOf v'=a→ v'=v:=fun v' hv' heq=>
     q5e v' hv' v hv.1 (heq.trans hv.2.symm)
    constructor
    ·rintro ⟨hxv,qb3 | ⟨u,hu,hxu⟩⟩
     ·left
      by_cases h0:side (n:=n) C a 0={v}
      ·simp only [b,if_pos h0] at qb3
       exact ⟨⟨v,by rw [h0];simp,hxv⟩,qb3⟩
      ·simp only [b,if_neg h0] at qb3
       have h1:side (n:=n) C a 1={v}:=hs.resolve_left h0
       exact ⟨qb3,⟨v,by rw [h1];simp,hxv⟩⟩
     ·right;exact ⟨v,hv.1,hv.2,hxv,u,hu,hxu⟩
    ·rintro (⟨h0,h1⟩ | ⟨v',hv',heq,qk5,u,hu,hxu⟩)
     ·by_cases hs0:side (n:=n) C a 0={v}
      ·simp only [b,if_pos hs0]
       rcases h0 with ⟨u0,hu0,qk6⟩
       rw [hs0,Z3] at hu0;subst hu0
       exact ⟨qk6,Or.inl h1⟩
      ·simp only [b,if_neg hs0]
       have hs1:side (n:=n) C a 1={v}:=hs.resolve_left hs0
       rcases h1 with ⟨u1,hu1,qk7⟩
       rw [hs1,Z3] at hu1;subst hu1
       exact ⟨qk7,Or.inl h0⟩
     ·have qk8:=qk4 v' hv' heq;subst qk8
      exact ⟨qk5,Or.inr ⟨u,hu,hxu⟩⟩
  ·simp only [mkTopItem,dif_neg h,dif_pos ha]
   by_cases h0:(side (n:=n) C a 0).card=1
   ·simp only [dif_pos h0]
    set v:=Classical.choose (Finset.card_eq_one.mp h0)
    have hv:side (n:=n) C a 0={v}:=Classical.choose_spec (Finset.card_eq_one.mp h0)
    have hlw:=z086 hL hne q25 1 hst.2.1 (by simpa using h0)
    refine ⟨?_,rfl,?_⟩
    ·intro bw hbw
     injection hbw with hbw;subst hbw
     have:=(z018 hL q01 hne lamList q1m q0s (fun _=>false) _ hlw).1
     rw [q43,← q42];exact this
    ·intro x
     have hbp:wval ⟨gs1,0⟩ x (z016 n C lamList (opnd C a 1))=
       decide (∃ u∈ orIn n C (opnd C a 1),x u=true):=
      (z018 hL q01 hne lamList q1m q0s x _ hlw).2
     simp only [Option.some.injEq,exists_eq_left',hbp,Z1,
      Z11,false_and,exists_false,or_false]
     have hno:¬ ∃ v'∈ Zhas,topOf v'=a∧ x v'=true∧ ∃ u∈ L v',x u=true:=by
      rintro ⟨v',hv',heq,_⟩;exact h ⟨v',hv',heq⟩
     rw [or_iff_left hno,hv]
     simp only [Z3,exists_eq_left]
     rfl
   ·simp only [dif_neg h0]
    have h1:(side (n:=n) C a 1).card=1:=hst.2.2.resolve_left h0
    set v:=Classical.choose (Finset.card_eq_one.mp h1)
    have hv:side (n:=n) C a 1={v}:=Classical.choose_spec (Finset.card_eq_one.mp h1)
    have hlw:=z086 hL hne q25 0 hst.1 (by simpa using h1)
    refine ⟨?_,rfl,?_⟩
    ·intro bw hbw
     injection hbw with hbw;subst hbw
     have:=(z018 hL q01 hne lamList q1m q0s (fun _=>false) _ hlw).1
     rw [q43,← q42];exact this
    ·intro x
     have hbp:wval ⟨gs1,0⟩ x (z016 n C lamList (opnd C a 0))=
       decide (∃ u∈ orIn n C (opnd C a 0),x u=true):=
      (z018 hL q01 hne lamList q1m q0s x _ hlw).2
     simp only [Option.some.injEq,exists_eq_left',hbp,Z1,
      Z11,false_and,exists_false,or_false]
     have hno:¬ ∃ v'∈ Zhas,topOf v'=a∧ x v'=true∧ ∃ u∈ L v',x u=true:=by
      rintro ⟨v',hv',heq,_⟩;exact h ⟨v',hv',heq⟩
     rw [or_iff_left hno,hv]
     simp only [Z3,exists_eq_left]
     exact and_comm
 have qdg:∀ it∈ allItems,
   (∀ bw,it.2.1=some bw→ bw < n+gs1.length)∧ (it.2.1.isSome∨ it.2.2≠ []):=by
  intro it hit
  simp only [allItems,topItems,newItems,List.mem_append,List.mem_map,Finset.mem_toList] at hit
  rcases hit with ⟨a,ha,rfl⟩ | ⟨v,hv,rfl⟩
  ·have h:=q19 a ha
   exact ⟨h.1,Or.inl h.2.1⟩
  ·refine ⟨fun bw hbw=>(by cases hbw),Or.inr ?_⟩
   intro q0g
   simp only [List.map_eq_nil_iff] at q0g
   obtain ⟨u,hu⟩:=q8q v (Z2.mp hv).1
   have:u∈ (L v).toList:=Finset.mem_toList.mpr hu
   rw [q0g] at this;cases this
 obtain ⟨⟨ex2,qb2⟩,qdd,q63,q8p,qj3,qde⟩:=z006 qda allItems qdg
 set gs2:=(z005 n gs1 allItems).1
 set topWires:=(z005 n gs1 allItems).2
 have q9j:allItems≠ []:=by
  intro q0g
  have qgg:S_tops=∅:=by
   have h1:topItems=[]:=(List.append_eq_nil_iff.mp q0g).1
   simp only [topItems,List.map_eq_nil_iff] at h1
   ext a;simp only [Finset.notMem_empty,iff_false]
   intro ha;have:=Finset.mem_toList.mpr ha;rw [h1] at this;cases this
  have qgh:Zact \ Zhas=∅:=by
   have h2:newItems=[]:=(List.append_eq_nil_iff.mp q0g).2
   simp only [newItems,List.map_eq_nil_iff] at h2
   ext v;simp only [Finset.notMem_empty,iff_false]
   intro hv;have:=Finset.mem_toList.mpr hv;rw [h2] at this;cases this
  have q9k:Zhas=∅:=by
   ext v;simp only [Finset.notMem_empty,iff_false]
   intro hv;have:=q41 v hv;rw [qgg] at this;exact Finset.notMem_empty _ this
  have q9l:Zact=∅:=by
   rw [q9k,Finset.sdiff_empty] at qgh;exact qgh
  obtain ⟨u,v,huv⟩:=hne
  have qgi:s(u,v)∈ G.edgeFinset:=SimpleGraph.mem_edgeFinset.mpr huv
  have qdh:starEdges G C=∅:=by
   ext e;simp only [Finset.notMem_empty,iff_false,starEdges,Finset.mem_biUnion,
    Z19,Z18]
   rintro ⟨a,ha,⟨p,⟨hp0,hp1⟩,_⟩⟩
   have haS:a∈ S_tops:=by
    rw [Z2];refine ⟨ha,fun hc=>?_⟩
    rw [centreless,Z0] at hc
    rcases hc.2 with h0 | h1
    ·rw [h0] at hp0;exact Finset.notMem_empty _ hp0
    ·rw [h1] at hp1;exact Finset.notMem_empty _ hp1
   rw [qgg] at haS;exact Finset.notMem_empty _ haS
  have q26:s(u,v)∈ Ustar G C:=by unfold Ustar;rw [qdh,Finset.sdiff_empty];exact qgi
  obtain ⟨w,hw,_⟩:=qgf _ q26
  rw [q9l] at hw;exact Finset.notMem_empty _ hw
 have q9m:topWires≠ []:=by
  intro h;rw [h] at q63;exact q9j (List.eq_nil_of_length_eq_zero q63.symm)
 obtain ⟨qj2,qpi⟩:=z009 q8p topWires q9m qj3
 let C':Circuit:=⟨(z008 n gs2 topWires).1,(z008 n gs2 topWires).2⟩
 have q4x:IsAO2 n C':=qj2
 have q6z:circuitFun n C'=graphFun G ∅:=by
  funext x
  change wval ⟨(z008 n gs2 topWires).1,0⟩ x (z008 n gs2 topWires).2=graphFun G ∅ x
  rw [z012 q8p x topWires q9m qj3]
  apply Bool.eq_iff_iff.mpr
  rw [Z1,qde x,z073]
  constructor
  ·rintro ⟨it,hit,hxv,qgj⟩
   simp only [allItems,topItems,newItems,List.mem_append,List.mem_map,Finset.mem_toList] at hit
   rcases hit with ⟨a,ha,rfl⟩ | ⟨v,hv,rfl⟩
   ·have qdi:=(q19 a ha).2.2 x
    rcases qdi.mp ⟨hxv,qgj⟩ with ⟨⟨u0,hu0,qk6⟩,⟨u1,hu1,qk7⟩⟩ | ⟨v,hv,_,qk5,u,hu,hxu⟩
    ·exact ⟨u0,u1,z132 hL.1 (Z2.mp ha).1 hu0 hu1,qk6,qk7⟩
    ·exact ⟨v,u,qge v (q5d hv) u hu,qk5,hxu⟩
   ·rcases qgj with ⟨bw,hbw,_⟩ | ⟨u,hu,hxu⟩
    ·cases hbw
    ·rw [Finset.mem_toList] at hu
     exact ⟨v,u,qge v (Z2.mp hv).1 u hu,hxv,hxu⟩
  ·rintro ⟨u,v,huv,hxu,hxv⟩
   have he:s(u,v)∈ G.edgeFinset:=SimpleGraph.mem_edgeFinset.mpr huv
   by_cases hst:s(u,v)∈ starEdges G C
   ·simp only [starEdges,Finset.mem_biUnion,Z19,Z18] at hst
    rcases hst with ⟨a,ha,⟨p0,p1⟩,⟨hp0,hp1⟩,qg0⟩
    have haS:a∈ S_tops:=by
     rw [Z2];refine ⟨ha,fun hc=>?_⟩
     rw [centreless,Z0] at hc
     rcases hc.2 with h0 | h1
     ·rw [h0] at hp0;exact Finset.notMem_empty _ hp0
     ·rw [h1] at hp1;exact Finset.notMem_empty _ hp1
    refine ⟨mkTopItem a,?_,?_⟩
    ·simp only [allItems,topItems,List.mem_append,List.mem_map,Finset.mem_toList]
     exact Or.inl ⟨a,haS,rfl⟩
    ·apply ((q19 a haS).2.2 x).mpr
     left
     rw [Sym2.eq_iff] at qg0
     rcases qg0 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
     ·exact ⟨⟨p0,hp0,hxu⟩,⟨p1,hp1,hxv⟩⟩
     ·exact ⟨⟨p0,hp0,hxv⟩,⟨p1,hp1,hxu⟩⟩
   ·have q26:s(u,v)∈ Ustar G C:=Z2.mpr ⟨he,hst⟩
    obtain ⟨w,hw,z,hz,heq⟩:=qgf _ q26
    rw [Sym2.eq_iff] at heq
    have hxw:x w=true:=by rcases heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> assumption
    have hxz:x z=true:=by rcases heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> assumption
    by_cases hwh:w∈ Zhas
    ·refine ⟨mkTopItem (topOf w),?_,?_⟩
     ·simp only [allItems,topItems,List.mem_append,List.mem_map,Finset.mem_toList]
      exact Or.inl ⟨topOf w,q41 w hwh,rfl⟩
     ·apply ((q19 (topOf w) (q41 w hwh)).2.2 x).mpr
      right
      exact ⟨w,hwh,rfl,hxw,z,hz,hxz⟩
    ·refine ⟨(w,none,(L w).toList),?_,hxw,Or.inr ⟨z,Finset.mem_toList.mpr hz,hxz⟩⟩
     simp only [allItems,newItems,List.mem_append,List.mem_map,Finset.mem_toList]
     exact Or.inr ⟨w,Z2.mpr ⟨hw,hwh⟩,rfl⟩
 have qb4:(topItems.map fun it=>it.2.2.length+(if it.2.1.isSome then 1 else 0)).sum=
   (∑ v∈ Zhas,(L v).card)+S_tops.card:=by
  have qo4:(topItems.map fun it=>it.2.2.length+(if it.2.1.isSome then 1 else 0)).sum=
    ∑ a∈ S_tops,((mkTopItem a).2.2.length+1):=by
   simp only [topItems,List.map_map]
   rw [← Finset.sum_map_toList]
   congr 1
   apply List.map_congr_left
   intro a ha
   rw [Finset.mem_toList] at ha
   simp only [Function.comp_apply,(q19 a ha).2.1,↓reduceIte]
  rw [qo4,Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,mul_one]
  congr 1
  have qc7:∑ a∈ S_tops,(mkTopItem a).2.2.length=
    ∑ a∈ S_tops,if h:∃ v∈ Zhas,topOf v=a then (L (Classical.choose h)).card else 0:=by
   apply Finset.sum_congr rfl
   intro a ha
   by_cases h:∃ v∈ Zhas,topOf v=a
   ·simp only [mkTopItem,dif_pos h,Finset.length_toList]
   ·simp only [mkTopItem,dif_neg h,dif_pos ha]
    split_ifs <;> rfl
  rw [qc7]
  have qb5:Zhas.image topOf⊆ S_tops:=by
   intro a ha;simp only [Z19] at ha;rcases ha with ⟨v,hv,rfl⟩;exact q41 v hv
  rw [← Finset.sum_subset qb5]
  ·rw [Finset.sum_image (fun v1 hv1 v2 hv2 heq=>q5e v1 hv1 v2 hv2 heq)]
   apply Finset.sum_congr rfl
   intro v hv
   have hex:∃ v'∈ Zhas,topOf v'=topOf v:=⟨v,hv,rfl⟩
   rw [dif_pos hex]
   have hch:=Classical.choose_spec hex
   rw [q5e _ hch.1 v hv hch.2]
  ·intro a _ q8o
   rw [dif_neg]
   rintro ⟨v,hv,rfl⟩
   exact q8o (Finset.mem_image_of_mem topOf hv)
 have qb6:(newItems.map fun it=>it.2.2.length+(if it.2.1.isSome then 1 else 0)).sum=
   ∑ v∈ Zact \ Zhas,(L v).card:=by
  simp only [newItems,List.map_map]
  rw [← Finset.sum_map_toList]
  congr 1
  apply List.map_congr_left
  intro v _
  simp [Finset.length_toList]
 have qb7:(allItems.map fun it=>it.2.2.length+(if it.2.1.isSome then 1 else 0)).sum=
   (∑ v∈ Zact,(L v).card)+S_tops.card:=by
  simp only [allItems,List.map_append,List.sum_append,qb4,qb6]
  have qmi:∑ v∈ Zact,(L v).card=(∑ v∈ Zhas,(L v).card)+(∑ v∈ Zact \ Zhas,(L v).card):=by
   rw [← Finset.sum_union Finset.disjoint_sdiff,Finset.union_sdiff_of_subset q5d]
  omega
 have q81:allItems.length=S_tops.card+(Zact \ Zhas).card:=by
  simp [allItems,topItems,newItems]
 have qj4:C'.size=
   (lam G C).card+(∑ v∈ Zact,(L v).card)+2 * S_tops.card+(Zact \ Zhas).card - 1:=by
  change (z008 n gs2 topWires).1.length=_
  rw [z010 n gs2 topWires q9m,q63,q81,qdd,q43,qb7]
  have qj5:0 < S_tops.card+(Zact \ Zhas).card:=by
   rw [← q81];exact List.length_pos_of_ne_nil q9j
  omega
 have qmj:C.size≤ C'.size:=hL.2.2 C' q4x q6z
 have qo5:=z024 hL
 have q93:=z133 hL q01 hne
 have qg1:(junk G C).card=2:=by
  have:junk G C={g1,g2}:=by ext k;simp [q00]
  rw [this,Finset.card_pair qdf]
 have q65:centreless G C⊆ tops G C:=Finset.filter_subset _ _
 have qdj:(tops G C).card=S_tops.card+(centreless G C).card:=by
  rw [z019 q65];have:=Finset.card_le_card q65;omega
 have q82:lam G C⊆ orN G C:=Finset.filter_subset _ _
 have q8r:(orN G C).card=(lam G C).card+(orN G C \ lam G C).card:=by
  rw [z019 q82];have:=Finset.card_le_card q82;omega
 omega
lemma z106 {α:Type} [DecidableEq α] {n:ℕ} {C:Circuit} (hAO:IsAO2 n C)
  (Items:Finset α) (H:Finset ℕ) (hH:∀ k∈ H,k < C.gates.length)
  (R:ℕ→ Finset α)
  (q83:∀ w < n+C.gates.length,(∀ k∈ H,w≠ n+k)→ (R w).card≤ 1)
  (qdk:∀ k∈ H,R (n+k)⊆ R (opnd C k 0) ∪ R (opnd C k 1)):
  ∃ comp:α→ ℕ,
   Items.card≤ (Items.image comp).card+H.card∧
   ∀ w < n+C.gates.length,∃ c:ℕ,∀ a∈ R w,comp a=c:=by
 have qo6:∀ m≤ C.gates.length,
   ∃ comp:α→ ℕ,
    Items.card≤ (Items.image comp).card+(H.filter (· < m)).card∧
    ∀ w < n+m,∃ c:ℕ,∀ a∈ R w,comp a=c:=by
  intro m
  induction m with
  | zero=>
   intro _
   refine ⟨fun a=>Items.toList.idxOf a,?_,?_⟩
   ·have qo7:Set.InjOn (fun a=>Items.toList.idxOf a) (Items:Set α):=by
     intro a ha b hb heq
     have ha':a∈ Items.toList:=Finset.mem_toList.mpr ha
     have hb':b∈ Items.toList:=Finset.mem_toList.mpr hb
     have hla:Items.toList.idxOf a < Items.toList.length:=List.idxOf_lt_length_iff.mpr ha'
     have hlb:Items.toList.idxOf b < Items.toList.length:=List.idxOf_lt_length_iff.mpr hb'
     have h1:=List.getElem_idxOf hla
     have h2:=List.getElem_idxOf hlb
     rw [← h1,← h2]
     simp [heq]
    rw [Finset.card_image_of_injOn qo7]
    simp
   ·intro w hw
    have hsm:(R w).card≤ 1:=q83 w (by omega) (fun k _=>by omega)
    by_cases hne:(R w).Nonempty
    ·obtain ⟨a,ha⟩:=hne
     refine ⟨Items.toList.idxOf a,fun b hb=>?_⟩
     have hba:b=a:=by
      by_contra qay
      have hle:=Finset.card_le_card (show ({b,a}:Finset α)⊆ R w by
       intro x hx;simp only [Z6,Z3] at hx
       rcases hx with rfl | rfl <;> assumption)
      rw [Finset.card_pair qay] at hle;omega
     subst hba;rfl
    ·refine ⟨0,fun b hb=>absurd ⟨b,hb⟩ hne⟩
  | succ m ih=>
   intro hm
   obtain ⟨comp,q18,q2w⟩:=ih (by omega)
   by_cases hmH:m∈ H
   ·have q9n:H.filter (· < m+1)=insert m (H.filter (· < m)):=by
     ext k;simp only [Z0,Z6]
     constructor
     ·rintro ⟨hk,hlt⟩
      by_cases hkm:k=m
      ·exact Or.inl hkm
      ·exact Or.inr ⟨hk,by omega⟩
     ·rintro (rfl | ⟨hk,hlt⟩)
      ·exact ⟨hmH,by omega⟩
      ·exact ⟨hk,by omega⟩
    have qdl:m∉ H.filter (· < m):=by simp
    obtain ⟨c0,hc0⟩:=q2w (opnd C m 0) (z104 hAO (by omega) 0)
    obtain ⟨c1,hc1⟩:=q2w (opnd C m 1) (z104 hAO (by omega) 1)
    let comp':α→ ℕ:=fun a=>if comp a=c1 then c0 else comp a
    refine ⟨comp',?_,?_⟩
    ·have qgk:Items.image comp⊆ insert c1 (Items.image comp'):=by
      intro c hc
      simp only [Z19] at hc
      rcases hc with ⟨a,ha,rfl⟩
      simp only [Z6,Z19]
      by_cases h:comp a=c1
      ·exact Or.inl h
      ·exact Or.inr ⟨a,ha,by simp [comp',h]⟩
     have hle:=Finset.card_le_card qgk
     have qo8:=Finset.card_insert_le c1 (Items.image comp')
     rw [q9n,Z24 qdl]
     omega
    ·intro w hw
     by_cases hlt:w < n+m
     ·obtain ⟨c,hc⟩:=q2w w hlt
      refine ⟨if c=c1 then c0 else c,fun a ha=>?_⟩
      simp only [comp',hc a ha]
     ·have q8s:w=n+m:=by omega
      subst q8s
      refine ⟨c0,fun a ha=>?_⟩
      have q23:=qdk m hmH ha
      rw [Z4] at q23
      rcases q23 with h0 | h1
      ·by_cases h:c0=c1 <;> simp [comp',hc0 a h0,h]
      ·simp only [comp',hc1 a h1,↓reduceIte]
   ·have q9n:H.filter (· < m+1)=H.filter (· < m):=by
     ext k;simp only [Z0]
     constructor
     ·rintro ⟨hk,hlt⟩;exact ⟨hk,by have:k≠ m:=fun h=>hmH (h ▸ hk);omega⟩
     ·rintro ⟨hk,hlt⟩;exact ⟨hk,by omega⟩
    refine ⟨comp,by rw [q9n];exact q18,?_⟩
    intro w hw
    by_cases hlt:w < n+m
    ·exact q2w w hlt
    ·have q8s:w=n+m:=by omega
     subst q8s
     have hsm:(R (n+m)).card≤ 1:=q83 (n+m) (by omega)
      (fun k hk heq=>hmH ((show m=k by omega) ▸ hk))
     by_cases hne:(R (n+m)).Nonempty
     ·obtain ⟨a,ha⟩:=hne
      refine ⟨comp a,fun b hb=>?_⟩
      have hba:b=a:=by
       by_contra qay
       have hle:=Finset.card_le_card (show ({b,a}:Finset α)⊆ R (n+m) by
        intro x hx;simp only [Z6,Z3] at hx
        rcases hx with rfl | rfl <;> assumption)
       rw [Finset.card_pair qay] at hle;omega
      subst hba;rfl
     ·refine ⟨0,fun b hb=>absurd ⟨b,hb⟩ hne⟩
 obtain ⟨comp,q18,q2w⟩:=qo6 C.gates.length (le_refl _)
 have q9n:H.filter (· < C.gates.length)=H:=
  Finset.filter_true_of_mem (fun k hk=>hH k hk)
 rw [q9n] at q18
 exact ⟨comp,q18,q2w⟩
lemma z101 {α:Type} [DecidableEq α] {Items S:Finset α} {comp:α→ ℕ} {Hcard:ℕ}
  (q18:Items.card≤ (Items.image comp).card+Hcard)
  (q9o:S⊆ Items) (qpj:S.Nonempty) (q2w:∃ c,∀ a∈ S,comp a=c):
  S.card≤ Hcard+1:=by
 obtain ⟨c,hc⟩:=q2w
 have qgk:Items.image comp⊆ insert c ((Items \ S).image comp):=by
  intro y hy
  simp only [Z19] at hy
  rcases hy with ⟨a,ha,rfl⟩
  simp only [Z6,Z19,Z2]
  by_cases haS:a∈ S
  ·exact Or.inl (hc a haS)
  ·exact Or.inr ⟨a,⟨ha,haS⟩,rfl⟩
 have h1:=Finset.card_le_card qgk
 have h2:=Finset.card_insert_le c ((Items \ S).image comp)
 have h3:((Items \ S).image comp).card≤ (Items \ S).card:=Finset.card_image_le
 have h4:=z019 q9o
 have h5:=Finset.card_le_card q9o
 omega
lemma z134 {α:Type} [DecidableEq α] {Items S1 S2:Finset α} {comp:α→ ℕ}
  {Hcard:ℕ} (q18:Items.card≤ (Items.image comp).card+Hcard)
  (q9o:S1 ∪ S2⊆ Items)
  (hm1:∃ c1,∀ a∈ S1,comp a=c1) (hm2:∃ c2,∀ a∈ S2,comp a=c2):
  (S1 ∪ S2).card≤ Hcard+2:=by
 obtain ⟨c1,hc1⟩:=hm1
 obtain ⟨c2,hc2⟩:=hm2
 have qgk:Items.image comp⊆ insert c1 (insert c2 ((Items \ (S1 ∪ S2)).image comp)):=by
  intro y hy
  simp only [Z19] at hy
  rcases hy with ⟨a,ha,rfl⟩
  simp only [Z6,Z19,Z2,Z4]
  by_cases ha1:a∈ S1
  ·exact Or.inl (hc1 a ha1)
  ·by_cases ha2:a∈ S2
   ·exact Or.inr (Or.inl (hc2 a ha2))
   ·exact Or.inr (Or.inr ⟨a,⟨ha,fun h=>h.elim ha1 ha2⟩,rfl⟩)
 have h1:=Finset.card_le_card qgk
 have h2:=Finset.card_insert_le c1 (insert c2 ((Items \ (S1 ∪ S2)).image comp))
 have h3:=Finset.card_insert_le c2 ((Items \ (S1 ∪ S2)).image comp)
 have h4:((Items \ (S1 ∪ S2)).image comp).card≤ (Items \ (S1 ∪ S2)).card:=Finset.card_image_le
 have h5:=z019 q9o
 have h6:=Finset.card_le_card q9o
 omega
def z000 {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit)
  (g:ℕ) (Ci Di:Finset (Fin n)) (z zp:Fin n):Prop:=
 G.Adj z zp∧ z∈ Ci∧ zp∈ Di∧ (∀ c∈ Ci,G.Adj c zp)∧ (∀ d∈ Di,G.Adj d z)∧
  2≤ Ci.card∧ 2≤ Di.card∧
  ∀ x:Fin n→ Bool,gateVal n C g x=(decide (∃ c∈ Ci,x c=true) && decide (∃ d∈ Di,x d=true))
def z045 {n:ℕ} (Ci Di:Finset (Fin n)) (z zp:Fin n):Finset (Sym2 (Fin n)):=
 (Di.image fun d=>s(z,d)) ∪ (Ci.image fun c=>s(c,zp))
lemma z043 (b:Fin 2):b=0∨ b=1:=by
 fin_cases b <;> simp
lemma z044 {a b:Fin 2} (h:a≠ b):1 - a=b:=by
 fin_cases a <;> fin_cases b <;> simp_all
lemma z015 {a b c:Bool} (h1:a≠ c) (h2:b≠ c):a=b:=by
 cases a <;> cases b <;> cases c <;> simp_all
lemma z046 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u≠ s v)
  {g:ℕ} {Ci Di:Finset (Fin n)} {z zp:Fin n} (hf:z000 G C g Ci Di z zp)
  {c:Fin n} (hc:c∈ Ci):s c=s z:=by
 have h1:=q03 z zp hf.1
 have h2:=q03 c zp (hf.2.2.2.1 c hc)
 cases hz:s z <;> cases hzp:s zp <;> cases hsc:s c <;> simp_all
lemma z047 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u≠ s v)
  {g:ℕ} {Ci Di:Finset (Fin n)} {z zp:Fin n} (hf:z000 G C g Ci Di z zp)
  {d:Fin n} (hd:d∈ Di):s d=s zp:=by
 have h1:=q03 z zp hf.1
 have h2:=q03 d z (hf.2.2.2.2.1 d hd)
 cases hz:s z <;> cases hzp:s zp <;> cases hsd:s d <;> simp_all
lemma z048 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u≠ s v)
  {g:ℕ} {Ci Di:Finset (Fin n)} {z zp:Fin n} (hf:z000 G C g Ci Di z zp):
  Disjoint Ci Di:=by
 rw [Finset.disjoint_left]
 intro u huC huD
 have h1:=z046 q03 hf huC
 have h2:=z047 q03 hf huD
 exact q03 z zp hf.1 (h1.symm.trans h2)
lemma z051 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (h4:NoFourCycle G)
  {g:ℕ} {Ci Di:Finset (Fin n)} {z zp:Fin n} (hf:z000 G C g Ci Di z zp)
  {c d:Fin n} (hc:c∈ Ci) (hcz:c≠ z) (hd:d∈ Di) (q1e:d≠ zp):
  ¬ G.Adj c d:=by
 intro qk9
 exact q1e (z102 h4 hcz qk9 (hf.2.2.2.2.1 d hd).symm
  (hf.2.2.2.1 c hc) hf.1)
lemma z049 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {g:ℕ} {Ci Di:Finset (Fin n)} {z zp:Fin n} (hf:z000 G C g Ci Di z zp):
  ∃ c∈ Ci,c≠ z:=by
 have hlt:1 < Ci.card:=by have:=hf.2.2.2.2.2.1;omega
 obtain ⟨a,ha,b,hb,hab⟩:=Finset.one_lt_card.mp hlt
 by_cases haz:a=z
 ·exact ⟨b,hb,fun hbz=>hab (haz.trans hbz.symm)⟩
 ·exact ⟨a,ha,haz⟩
lemma z050 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {g:ℕ} {Ci Di:Finset (Fin n)} {z zp:Fin n} (hf:z000 G C g Ci Di z zp):
  ∃ d∈ Di,d≠ zp:=by
 have hlt:1 < Di.card:=by have:=hf.2.2.2.2.2.2.1;omega
 obtain ⟨a,ha,b,hb,hab⟩:=Finset.one_lt_card.mp hlt
 by_cases haz:a=zp
 ·exact ⟨b,hb,fun hbz=>hab (haz.trans hbz.symm)⟩
 ·exact ⟨a,ha,haz⟩
lemma z052 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u≠ s v) (h4:NoFourCycle G)
  {g:ℕ} {Ci Di:Finset (Fin n)} {z zp:Fin n} (hf:z000 G C g Ci Di z zp)
  {u v:Fin n} (huv:G.Adj u v):
  gateVal n C g (pairInput u v)=true↔ s(u,v)∈ z045 Ci Di z zp:=by
 have q4y:=z048 q03 hf
 rw [hf.2.2.2.2.2.2.2 (pairInput u v),Z12,Z1,Z1]
 simp only [pairInput,Z1,z045,Z4,Z19,Sym2.eq_iff]
 constructor
 ·rintro ⟨⟨c,hc,rfl | rfl⟩,⟨d,hd,hdu | hdv⟩⟩
  ·subst hdu;exact absurd hc (Finset.disjoint_right.mp q4y hd)
  ·subst hdv
   by_cases hcz:c=z
   ·subst hcz;exact Or.inl ⟨d,hd,Or.inl ⟨rfl,rfl⟩⟩
   ·by_cases q1e:d=zp
    ·subst q1e;exact Or.inr ⟨c,hc,Or.inl ⟨rfl,rfl⟩⟩
    ·exact absurd huv (z051 h4 hf hc hcz hd q1e)
  ·subst hdu
   by_cases hcz:c=z
   ·subst hcz;exact Or.inl ⟨d,hd,Or.inr ⟨rfl,rfl⟩⟩
   ·by_cases q1e:d=zp
    ·subst q1e;exact Or.inr ⟨c,hc,Or.inr ⟨rfl,rfl⟩⟩
    ·exact absurd huv.symm (z051 h4 hf hc hcz hd q1e)
  ·subst hdv;exact absurd hc (Finset.disjoint_right.mp q4y hd)
 ·rintro (⟨d,hd,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ | ⟨c,hc,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩)
  ·exact ⟨⟨z,hf.2.1,Or.inl rfl⟩,⟨d,hd,Or.inr rfl⟩⟩
  ·exact ⟨⟨z,hf.2.1,Or.inr rfl⟩,⟨d,hd,Or.inl rfl⟩⟩
  ·exact ⟨⟨c,hc,Or.inl rfl⟩,⟨zp,hf.2.2.1,Or.inr rfl⟩⟩
  ·exact ⟨⟨c,hc,Or.inr rfl⟩,⟨zp,hf.2.2.1,Or.inl rfl⟩⟩
lemma z055 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (h4:NoFourCycle G)
  {g:ℕ} {Ci Di:Finset (Fin n)} {z zp:Fin n} (hf:z000 G C g Ci Di z zp)
  {c:Fin n} (hc:c∈ Ci) (hcz:c≠ z):
  ¬ (∀ x:Fin n→ Bool,gateVal n C g x=true→ x c=true→ graphFun G ∅ x=true):=by
 intro hw
 obtain ⟨d,hd,q1e⟩:=z050 hf
 have q10:gateVal n C g (pairInput c d)=true:=by
  rw [hf.2.2.2.2.2.2.2,Z12,Z1,Z1]
  exact ⟨⟨c,hc,by simp [pairInput]⟩,⟨d,hd,by simp [pairInput]⟩⟩
 have hF:=hw (pairInput c d) q10 (by simp [pairInput])
 exact z051 h4 hf hc hcz hd q1e ((z074 c d).mp hF)
lemma z056 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (h4:NoFourCycle G)
  {g:ℕ} {Ci Di:Finset (Fin n)} {z zp:Fin n} (hf:z000 G C g Ci Di z zp)
  {d:Fin n} (hd:d∈ Di) (q1e:d≠ zp):
  ¬ (∀ x:Fin n→ Bool,gateVal n C g x=true→ x d=true→ graphFun G ∅ x=true):=by
 intro hw
 obtain ⟨c,hc,hcz⟩:=z049 hf
 have q10:gateVal n C g (pairInput c d)=true:=by
  rw [hf.2.2.2.2.2.2.2,Z12,Z1,Z1]
  exact ⟨⟨c,hc,by simp [pairInput]⟩,⟨d,hd,by simp [pairInput]⟩⟩
 have hF:=hw (pairInput c d) q10 (by simp [pairInput])
 exact z051 h4 hf hc hcz hd q1e ((z074 c d).mp hF)
lemma z054 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u≠ s v) (h4:NoFourCycle G)
  {g:ℕ} {Ci Di:Finset (Fin n)} {z zp:Fin n} (hf:z000 G C g Ci Di z zp)
  {w:Fin n} (hw:∀ x:Fin n→ Bool,gateVal n C g x=true→ x w=true→ graphFun G ∅ x=true)
  (hsw:s w=s z) {d:Fin n} (hd:d∈ Di) (q1e:d≠ zp):G.Adj w d:=by
 obtain ⟨c,hc,hcz⟩:=z049 hf
 let x:Fin n→ Bool:=fun v=>decide (v=c∨ v=d∨ v=w)
 have hg:gateVal n C g x=true:=by
  rw [hf.2.2.2.2.2.2.2,Z12,Z1,Z1]
  exact ⟨⟨c,hc,by simp [x]⟩,⟨d,hd,by simp [x]⟩⟩
 have hF:=(z073 x).mp (hw x hg (by simp [x]))
 rcases hF with ⟨a,b,hab,ha,hb⟩
 simp only [x,Z1] at ha hb
 have hsc:s c=s z:=z046 q03 hf hc
 have hsd:s d=s zp:=z047 q03 hf hd
 have qgl:¬ G.Adj c d:=z051 h4 hf hc hcz hd q1e
 rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
 ·exact absurd hab (G.loopless.irrefl _)
 ·exact absurd hab qgl
 ·exact absurd (hsc.trans hsw.symm) (q03 _ _ hab)
 ·exact absurd hab.symm qgl
 ·exact absurd hab (G.loopless.irrefl _)
 ·exact hab.symm
 ·exact absurd (hsw.trans hsc.symm) (q03 _ _ hab)
 ·exact hab
 ·exact absurd hab (G.loopless.irrefl _)
lemma z053 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u≠ s v) (h4:NoFourCycle G)
  {g:ℕ} {Ci Di:Finset (Fin n)} {z zp:Fin n} (hf:z000 G C g Ci Di z zp)
  {w:Fin n} (hw:∀ x:Fin n→ Bool,gateVal n C g x=true→ x w=true→ graphFun G ∅ x=true)
  (hsw:s w=s zp) {c:Fin n} (hc:c∈ Ci) (hcz:c≠ z):G.Adj w c:=by
 obtain ⟨d,hd,q1e⟩:=z050 hf
 let x:Fin n→ Bool:=fun v=>decide (v=c∨ v=d∨ v=w)
 have hg:gateVal n C g x=true:=by
  rw [hf.2.2.2.2.2.2.2,Z12,Z1,Z1]
  exact ⟨⟨c,hc,by simp [x]⟩,⟨d,hd,by simp [x]⟩⟩
 have hF:=(z073 x).mp (hw x hg (by simp [x]))
 rcases hF with ⟨a,b,hab,ha,hb⟩
 simp only [x,Z1] at ha hb
 have hsc:s c=s z:=z046 q03 hf hc
 have hsd:s d=s zp:=z047 q03 hf hd
 have qgl:¬ G.Adj c d:=z051 h4 hf hc hcz hd q1e
 rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
 ·exact absurd hab (G.loopless.irrefl _)
 ·exact absurd hab qgl
 ·exact hab.symm
 ·exact absurd hab.symm qgl
 ·exact absurd hab (G.loopless.irrefl _)
 ·exact absurd (hsd.trans hsw.symm) (q03 _ _ hab)
 ·exact hab
 ·exact absurd (hsw.trans hsd.symm) (q03 _ _ hab)
 ·exact absurd hab (G.loopless.irrefl _)
lemma z130 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (hne:∃ u v:Fin n,G.Adj u v)
  {a:ℕ} (ha:a∈ tops G C) (b:Fin 2):
  ∀ k,opnd C a b=n+k→ ¬ BelowF G C k:=by
 have ha':=z098.mp ha
 intro k hk hbk
 exact z089 hL hne ha'.1 ha'.2.1 b (by rw [hk];exact hbk)
lemma z135 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u≠ s v)
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (h4:NoFourCycle G)
  {g1 g2:ℕ} (q00:∀ k,k∈ junk G C↔ k=g1∨ k=g2)
  {C1 D1 C2 D2:Finset (Fin n)} {z1 zp1 z2 zp2:Fin n}
  (hf1:z000 G C g1 C1 D1 z1 zp1) (hf2:z000 G C g2 C2 D2 z2 zp2):
  Ustar G C⊆ z045 C1 D1 z1 zp1 ∪ z045 C2 D2 z2 zp2:=by
 have hne:∃ u v:Fin n,G.Adj u v:=⟨z1,zp1,hf1.1⟩
 intro e he
 rw [Ustar,Z2] at he
 rcases he with ⟨heG,q9p⟩
 induction e using Sym2.ind with
 | _ u v=>
  have huv:G.Adj u v:=SimpleGraph.mem_edgeFinset.mp heG
  have hcx:circuitFun n C (pairInput u v)=true:=by
   rw [congrFun hL.2.1 (pairInput u v)];exact (z074 u v).mpr huv
  obtain ⟨a,ha,hva⟩:=(z023 hL hne _).mp hcx
  have ha':=z098.mp ha
  rw [z070,z140 hL.1 _ ha'.1 ha'.2.1,Z12] at hva
  have hw0:=(z103 hL q01 hne q00 (opnd C a 0)
   (by have:=z104 hL.1 ha'.1 0;omega) (z130 hL hne ha 0) (pairInput u v)).mp hva.1
  have hw1:=(z103 hL q01 hne q00 (opnd C a 1)
   (by have:=z104 hL.1 ha'.1 1;omega) (z130 hL hne ha 1) (pairInput u v)).mp hva.2
  have q5b:¬ ((∃ w∈ side (n:=n) C a 0,pairInput u v w=true)∧
    (∃ w∈ side (n:=n) C a 1,pairInput u v w=true)):=by
   rintro ⟨⟨w0,q95,qgm⟩,⟨w1,qgn,qgo⟩⟩
   apply q9p
   simp only [starEdges,Finset.mem_biUnion,Z19,Z18]
   simp only [pairInput,Z1] at qgm qgo
   have q52:w0≠ w1:=fun h=>by subst h;exact G.loopless.irrefl w0 (z132 hL.1 ha q95 qgn)
   refine ⟨a,ha,(w0,w1),⟨q95,qgn⟩,?_⟩
   rw [Sym2.eq_iff]
   rcases qgm with rfl | rfl <;> rcases qgo with rfl | rfl
   ·exact absurd rfl q52
   ·exact Or.inl ⟨rfl,rfl⟩
   ·exact Or.inr ⟨rfl,rfl⟩
   ·exact absurd rfl q52
  rw [Z4,← z052 q03 h4 hf1 huv,← z052 q03 h4 hf2 huv]
  rcases hw0 with h0 | ⟨_,hg1⟩ | ⟨_,hg2⟩
  ·rcases hw1 with h1 | ⟨_,hg1⟩ | ⟨_,hg2⟩
   ·exact absurd ⟨h0,h1⟩ q5b
   ·exact Or.inl hg1
   ·exact Or.inr hg2
  ·exact Or.inl hg1
  ·exact Or.inr hg2
lemma z123 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (hne:∃ u v:Fin n,G.Adj u v)
  {g1 g2:ℕ} (q00:∀ k,k∈ junk G C↔ k=g1∨ k=g2)
  {k:ℕ} (hk:k∈ orN G C)
  (hn1:¬ OrReaches n C (n+k) g1) (hn2:¬ OrReaches n C (n+k) g2):
  2≤ (orIn n C (n+k)).card:=by
 have hk':=z096.mp hk
 have q10:∀ x,wval C x (n+k)=true↔ ∃ u∈ orIn n C (n+k),x u=true:=by
  intro x
  have h:=z103 hL q01 hne q00 (n+k) (by omega)
   (fun m hm=>by have:m=k:=(by omega);subst this;exact hk'.2.2) x
  simpa [hn1,hn2] using h
 have qb8:(orIn n C (n+k)).Nonempty:=by
  have qaz:=(q10 (fun _=>true)).mp (z138 hL.1 (n+k) (by omega))
  rcases qaz with ⟨u,hu,_⟩;exact ⟨u,hu⟩
 by_contra hlt
 push Not at hlt
 have q0t:(orIn n C (n+k)).card=1:=by
  have:=Finset.Nonempty.card_pos qb8;omega
 obtain ⟨u,hu⟩:=Finset.card_eq_one.mp q0t
 apply z090 hL hne hk'.1 (by omega:u.val < n+k)
 intro x
 apply Bool.eq_iff_iff.mpr
 rw [z144 C x u.val u.isLt,q10 x,hu]
 simp
lemma z084 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (hne:∃ u v:Fin n,G.Adj u v)
  {g1 g2:ℕ} (q00:∀ k,k∈ junk G C↔ k=g1∨ k=g2)
  {k:ℕ} (hk:k∈ lam G C) (qo9:k < g2):
  2≤ (orIn n C (n+k)).card:=by
 have q4c:=Z0.mp hk
 have q04:=z096.mp q4c.1
 have q6w:(orIn n C (opnd C k 0)).Nonempty:=q4c.2.1
 have q62:(orIn n C (opnd C k 1)).Nonempty:=q4c.2.2.1
 have q0o:=z108 hL.1 q04.1 q04.2.1
 have qka:(orIn n C (n+k)).Nonempty:=by
  rw [q0o];exact q6w.mono Finset.subset_union_left
 by_contra hlt
 push Not at hlt
 have q0t:(orIn n C (n+k)).card=1:=by
  have:=Finset.Nonempty.card_pos qka;omega
 obtain ⟨u,hu⟩:=Finset.card_eq_one.mp q0t
 have qgp:orIn n C (opnd C k 0)⊆ {u}:=by rw [← hu,q0o];exact Finset.subset_union_left
 have q3e:orIn n C (opnd C k 1)⊆ {u}:=by rw [← hu,q0o];exact Finset.subset_union_right
 have qoa:orIn n C (opnd C k 0)={u}:=by
  ext v;constructor
  ·exact fun h=>qgp h
  ·intro hv;rw [Z3] at hv;subst hv
   obtain ⟨w,hw⟩:=q6w
   have:=Z3.mp (qgp hw);subst this;exact hw
 have qob:orIn n C (opnd C k 1)={u}:=by
  ext v;constructor
  ·exact fun h=>q3e h
  ·intro hv;rw [Z3] at hv;subst hv
   obtain ⟨w,hw⟩:=q62
   have:=Z3.mp (q3e hw);subst this;exact hw
 have qkb:¬ OrReaches n C (opnd C k 0) g2:=fun h=>by
  have h1:=z113 h;have h2:=z104 hL.1 q04.1 0;omega
 have qkc:¬ OrReaches n C (opnd C k 1) g2:=fun h=>by
  have h1:=z113 h;have h2:=z104 hL.1 q04.1 1;omega
 have hnb:∀ b:Fin 2,∀ m,opnd C k b=n+m→ ¬ BelowF G C m:=fun b m hm hbm=>
  z091 hL q01 hne q04.1 q04.2.1 q04.2.2 b (by rw [hm];exact hbm)
 have hv0:∀ x,wval C x (opnd C k 0)=true↔
   x u=true∨ (OrReaches n C (opnd C k 0) g1∧ gateVal n C g1 x=true):=by
  intro x
  have h:=z103 hL q01 hne q00 (opnd C k 0)
   (by have:=z104 hL.1 q04.1 0;omega) (hnb 0) x
  simpa [qoa,qkb] using h
 have hv1:∀ x,wval C x (opnd C k 1)=true↔
   x u=true∨ (OrReaches n C (opnd C k 1) g1∧ gateVal n C g1 x=true):=by
  intro x
  have h:=z103 hL q01 hne q00 (opnd C k 1)
   (by have:=z104 hL.1 q04.1 1;omega) (hnb 1) x
  simpa [qob,qkc] using h
 by_cases hr0:OrReaches n C (opnd C k 0) g1
 ·apply z090 hL hne q04.1 (z104 hL.1 q04.1 0)
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [z142 hL.1 x q04.1 q04.2.1,Z13,hv0 x,hv1 x]
  simp [hr0]
  tauto
 ·apply z090 hL hne q04.1 (z104 hL.1 q04.1 1)
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [z142 hL.1 x q04.1 q04.2.1,Z13,hv0 x,hv1 x]
  simp [hr0]
lemma z085 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hAO:IsAO2 n C) (h4:NoFourCycle G)
  {v:Fin n} {k:ℕ} (hk:k∈ lam G C)
  (q0c:∀ u∈ orIn n C (n+k),G.Adj v u)
  (q18:2≤ (orIn n C (n+k)).card):
  ∀ u∈ orIn n C (n+k),s(v,u)∈ starEdges G C:=by
 have q4c:=Z0.mp hk
 rcases q4c.2.2.2 with ⟨a,ha,b,q0t,q0q⟩
 obtain ⟨v',hv'⟩:=Finset.card_eq_one.mp q0t
 have q66:orIn n C (n+k)⊆ side (n:=n) C a b:=z109 q0q
 obtain ⟨u1,hu1,u2,hu2,qd2⟩:=Finset.one_lt_card.mp (by omega:1 < (orIn n C (n+k)).card)
 have q9q:∀ u∈ orIn n C (n+k),G.Adj v' u:=by
  intro u hu
  have qgq:v'∈ side (n:=n) C a (1 - b):=by rw [hv'];simp
  have hum:u∈ side (n:=n) C a b:=q66 hu
  fin_cases b
  ·exact (z132 hAO ha hum qgq).symm
  ·exact z132 hAO ha qgq hum
 have qoc:v=v':=z102 h4 qd2
  (q0c u1 hu1).symm (q0c u2 hu2).symm (q9q u1 hu1).symm (q9q u2 hu2).symm
 subst qoc
 intro u hu
 simp only [starEdges,Finset.mem_biUnion,Z19,Z18]
 have qgq:v∈ side (n:=n) C a (1 - b):=by rw [hv'];simp
 have hum:u∈ side (n:=n) C a b:=q66 hu
 fin_cases b
 ·exact ⟨a,ha,(u,v),⟨hum,qgq⟩,Sym2.eq_swap⟩
 ·exact ⟨a,ha,(v,u),⟨qgq,hum⟩,rfl⟩
lemma z066 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u≠ s v)
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C)
  {g1 g2:ℕ} (q0y:g1 < g2) (q00:∀ k,k∈ junk G C↔ k=g1∨ k=g2)
  {C1 D1:Finset (Fin n)} {z1 zp1:Fin n} (hf1:z000 G C g1 C1 D1 z1 zp1):
  (¬ OrReaches n C (opnd C g1 0) g1∧ ¬ OrReaches n C (opnd C g1 0) g2∧
  ¬ OrReaches n C (opnd C g1 1) g1∧ ¬ OrReaches n C (opnd C g1 1) g2)∧
  ∃ b1:Fin 2,side (n:=n) C g1 b1=C1∧ side (n:=n) C g1 (1 - b1)=D1:=by
 have hne:∃ u v:Fin n,G.Adj u v:=⟨z1,zp1,hf1.1⟩
 have q8t:=z094.mp ((q00 g1).mpr (Or.inl rfl))
 have q80:=z104 hL.1 q8t.1 0
 have q58:=z104 hL.1 q8t.1 1
 have qmk:¬ OrReaches n C (opnd C g1 0) g1:=fun h=>by have:=h.1;have:=z113 h;omega
 have qgr:¬ OrReaches n C (opnd C g1 0) g2:=fun h=>by have:=h.1;have:=z113 h;omega
 have qml:¬ OrReaches n C (opnd C g1 1) g1:=fun h=>by have:=h.1;have:=z113 h;omega
 have qgs:¬ OrReaches n C (opnd C g1 1) g2:=fun h=>by have:=h.1;have:=z113 h;omega
 refine ⟨⟨qmk,qgr,qml,qgs⟩,?_⟩
 have hnb:∀ b:Fin 2,∀ m,opnd C g1 b=n+m→ ¬ BelowF G C m:=fun b m hm hbm=>
  z089 hL hne q8t.1 q8t.2.1 b (by rw [hm];exact hbm)
 have q10:∀ x:Fin n→ Bool,
   ((∃ u∈ side (n:=n) C g1 0,x u=true)∧ (∃ v∈ side (n:=n) C g1 1,x v=true))↔
   ((∃ c∈ C1,x c=true)∧ (∃ d∈ D1,x d=true)):=by
  intro x
  have h0:=z103 hL q01 hne q00 (opnd C g1 0) (by omega) (hnb 0) x
  have h1:=z103 hL q01 hne q00 (opnd C g1 1) (by omega) (hnb 1) x
  have hg:=hf1.2.2.2.2.2.2.2 x
  rw [z070,z140 hL.1 x q8t.1 q8t.2.1] at hg
  have qdi:=congrArg (·=true) hg
  simp only [Z12,Z1] at qdi
  rw [← qdi,h0,h1]
  simp [qmk,qgr,qml,qgs,side]
 have q1a:=z048 q03 hf1
 have q27:Disjoint (side (n:=n) C g1 0) (side (n:=n) C g1 1):=by
  rw [Finset.disjoint_left];intro v hv0 hv1
  have h:=(q10 (fun w=>decide (w=v))).mp ⟨⟨v,hv0,by simp⟩,⟨v,hv1,by simp⟩⟩
  rcases h with ⟨⟨c,hc,hvc⟩,⟨d,hd,hvd⟩⟩
  simp only [Z1] at hvc hvd
  subst hvc;subst hvd
  exact Finset.disjoint_left.mp q1a hc hd
 have q0u:∀ u v:Fin n,u≠ v→
   (((u∈ side (n:=n) C g1 0∧ v∈ side (n:=n) C g1 1)∨
   (v∈ side (n:=n) C g1 0∧ u∈ side (n:=n) C g1 1))↔
   ((u∈ C1∧ v∈ D1)∨ (v∈ C1∧ u∈ D1))):=by
  intro u v huv
  have h:=q10 (pairInput u v)
  simp only [pairInput,Z1] at h
  constructor
  ·intro hs
   have hcd:(∃ c∈ C1,c=u∨ c=v)∧ (∃ d∈ D1,d=u∨ d=v):=by
    apply h.mp
    rcases hs with ⟨hu,hv⟩ | ⟨hv,hu⟩
    ·exact ⟨⟨u,hu,Or.inl rfl⟩,⟨v,hv,Or.inr rfl⟩⟩
    ·exact ⟨⟨v,hv,Or.inr rfl⟩,⟨u,hu,Or.inl rfl⟩⟩
   rcases hcd with ⟨⟨c,hc,rfl | rfl⟩,⟨d,hd,hdu | hdv⟩⟩
   ·subst hdu;exact absurd hc (Finset.disjoint_right.mp q1a hd)
   ·subst hdv;exact Or.inl ⟨hc,hd⟩
   ·subst hdu;exact Or.inr ⟨hc,hd⟩
   ·subst hdv;exact absurd hc (Finset.disjoint_right.mp q1a hd)
  ·intro hcd
   have hs:(∃ a∈ side (n:=n) C g1 0,a=u∨ a=v)∧
     (∃ b∈ side (n:=n) C g1 1,b=u∨ b=v):=by
    apply h.mpr
    rcases hcd with ⟨hu,hv⟩ | ⟨hv,hu⟩
    ·exact ⟨⟨u,hu,Or.inl rfl⟩,⟨v,hv,Or.inr rfl⟩⟩
    ·exact ⟨⟨v,hv,Or.inr rfl⟩,⟨u,hu,Or.inl rfl⟩⟩
   rcases hs with ⟨⟨a,ha,rfl | rfl⟩,⟨b,hb,hbu | hbv⟩⟩
   ·subst hbu;exact absurd ha (Finset.disjoint_right.mp q27 hb)
   ·subst hbv;exact Or.inl ⟨ha,hb⟩
   ·subst hbu;exact Or.inr ⟨ha,hb⟩
   ·subst hbv;exact absurd ha (Finset.disjoint_right.mp q27 hb)
 have qkd:z1≠ zp1:=G.ne_of_adj hf1.1
 have hzz:=(q0u z1 zp1 qkd).mpr (Or.inl ⟨hf1.2.1,hf1.2.2.1⟩)
 rcases hzz with ⟨hz0,qgt⟩ | ⟨qgu,hz1⟩
 ·refine ⟨0,?_,?_⟩
  ·ext u
   constructor
   ·intro hu
    have q70:u≠ zp1:=fun h=>by subst h;exact Finset.disjoint_left.mp q27 hu qgt
    rcases (q0u u zp1 q70).mp (Or.inl ⟨hu,qgt⟩) with ⟨huC,_⟩ | ⟨qke,_⟩
    ·exact huC
    ·exact absurd qke (Finset.disjoint_right.mp q1a hf1.2.2.1)
   ·intro hu
    have q70:u≠ zp1:=fun h=>by subst h;exact Finset.disjoint_left.mp q1a hu hf1.2.2.1
    rcases (q0u u zp1 q70).mpr (Or.inl ⟨hu,hf1.2.2.1⟩) with ⟨hu0,_⟩ | ⟨qgu,_⟩
    ·exact hu0
    ·exact absurd qgu (Finset.disjoint_right.mp q27 qgt)
  ·ext v
   simp only [sub_zero]
   constructor
   ·intro hv
    have q71:z1≠ v:=fun h=>by subst h;exact Finset.disjoint_left.mp q27 hz0 hv
    rcases (q0u z1 v q71).mp (Or.inl ⟨hz0,hv⟩) with ⟨_,hvD⟩ | ⟨_,hzD⟩
    ·exact hvD
    ·exact absurd hzD (Finset.disjoint_left.mp q1a hf1.2.1)
   ·intro hv
    have q71:z1≠ v:=fun h=>by subst h;exact Finset.disjoint_left.mp q1a hf1.2.1 hv
    rcases (q0u z1 v q71).mpr (Or.inl ⟨hf1.2.1,hv⟩) with ⟨_,hv1⟩ | ⟨_,hz1⟩
    ·exact hv1
    ·exact absurd hz1 (Finset.disjoint_left.mp q27 hz0)
 ·refine ⟨1,?_,?_⟩
  ·ext u
   constructor
   ·intro hu
    have q70:u≠ zp1:=fun h=>by subst h;exact Finset.disjoint_left.mp q27 qgu hu
    rcases (q0u u zp1 q70).mp (Or.inr ⟨qgu,hu⟩) with ⟨huC,_⟩ | ⟨qke,_⟩
    ·exact huC
    ·exact absurd qke (Finset.disjoint_right.mp q1a hf1.2.2.1)
   ·intro hu
    have q70:u≠ zp1:=fun h=>by subst h;exact Finset.disjoint_left.mp q1a hu hf1.2.2.1
    rcases (q0u u zp1 q70).mpr (Or.inl ⟨hu,hf1.2.2.1⟩) with ⟨_,qgt⟩ | ⟨_,hu1⟩
    ·exact absurd qgt (Finset.disjoint_left.mp q27 qgu)
    ·exact hu1
  ·ext v
   have h11:(1:Fin 2) - 1=0:=rfl
   rw [h11]
   constructor
   ·intro hv
    have q71:z1≠ v:=fun h=>by subst h;exact Finset.disjoint_left.mp q27 hv hz1
    rcases (q0u z1 v q71).mp (Or.inr ⟨hv,hz1⟩) with ⟨_,hvD⟩ | ⟨_,hzD⟩
    ·exact hvD
    ·exact absurd hzD (Finset.disjoint_left.mp q1a hf1.2.1)
   ·intro hv
    have q71:z1≠ v:=fun h=>by subst h;exact Finset.disjoint_left.mp q1a hf1.2.1 hv
    rcases (q0u z1 v q71).mpr (Or.inl ⟨hf1.2.1,hv⟩) with ⟨hz0,_⟩ | ⟨hv0,_⟩
    ·exact absurd hz0 (Finset.disjoint_right.mp q27 hz1)
    ·exact hv0
lemma z067 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u≠ s v) (h4:NoFourCycle G)
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C)
  {g1 g2:ℕ} (q0y:g1 < g2) (q00:∀ k,k∈ junk G C↔ k=g1∨ k=g2)
  {C1 D1 C2 D2:Finset (Fin n)} {z1 zp1 z2 zp2:Fin n}
  (hf1:z000 G C g1 C1 D1 z1 zp1) (hf2:z000 G C g2 C2 D2 z2 zp2)
  (hsz:s z1=s z2) (q1l:s zp1=s zp2):
  ¬ OrReaches n C (opnd C g2 0) g2∧ ¬ OrReaches n C (opnd C g2 1) g2∧
  ∃ b2:Fin 2,
   side (n:=n) C g2 b2⊆ C2∧ side (n:=n) C g2 (1 - b2)⊆ D2∧
   (OrReaches n C (opnd C g2 b2) g1→ C1⊆ C2∧ zp1=zp2∧ C2=C1 ∪ side (n:=n) C g2 b2)∧
   (¬ OrReaches n C (opnd C g2 b2) g1→ side (n:=n) C g2 b2=C2)∧
   (OrReaches n C (opnd C g2 (1 - b2)) g1→ D1⊆ D2∧ z1=z2∧ D2=D1 ∪ side (n:=n) C g2 (1 - b2))∧
   (¬ OrReaches n C (opnd C g2 (1 - b2)) g1→ side (n:=n) C g2 (1 - b2)=D2):=by
 have hne:∃ u v:Fin n,G.Adj u v:=⟨z1,zp1,hf1.1⟩
 have q72:=z094.mp ((q00 g2).mpr (Or.inr rfl))
 have q80:=z104 hL.1 q72.1 0
 have q58:=z104 hL.1 q72.1 1
 have qgr:¬ OrReaches n C (opnd C g2 0) g2:=fun h=>by have:=z113 h;omega
 have qgs:¬ OrReaches n C (opnd C g2 1) g2:=fun h=>by have:=z113 h;omega
 refine ⟨qgr,qgs,?_⟩
 have hnb:∀ b:Fin 2,∀ m,opnd C g2 b=n+m→ ¬ BelowF G C m:=fun b m hm hbm=>
  z089 hL hne q72.1 q72.2.1 b (by rw [hm];exact hbm)
 have q10:∀ x,
   (((∃ u∈ side (n:=n) C g2 0,x u=true)∨ (OrReaches n C (opnd C g2 0) g1∧ gateVal n C g1 x=true))∧
   ((∃ v∈ side (n:=n) C g2 1,x v=true)∨ (OrReaches n C (opnd C g2 1) g1∧ gateVal n C g1 x=true)))↔
   ((∃ c∈ C2,x c=true)∧ (∃ d∈ D2,x d=true)):=by
  intro x
  have h0:=z103 hL q01 hne q00 (opnd C g2 0) (by omega) (hnb 0) x
  have h1:=z103 hL q01 hne q00 (opnd C g2 1) (by omega) (hnb 1) x
  have hg:=hf2.2.2.2.2.2.2.2 x
  rw [z070,z140 hL.1 x q72.1 q72.2.1] at hg
  have qdi:=congrArg (·=true) hg
  simp only [Z12,Z1] at qdi
  rw [← qdi,h0,h1]
  simp [qgr,qgs,side]
 have q1n:=z048 q03 hf2
 have qc8:=z048 q03 hf1
 have q02:s z2≠ s zp2:=q03 z2 zp2 hf2.1
 have qgv:∀ b:Fin 2,OrReaches n C (opnd C g2 b) g1→
   (∃ d∈ D2,d∈ side (n:=n) C g2 (1 - b))→ C1⊆ C2:=by
  intro b hrb ⟨d2,hd2,qod⟩ c1 hc1
  let x:Fin n→ Bool:=fun v=>decide (v=c1∨ v=zp1∨ v=d2)
  have q1o:gateVal n C g1 x=true:=by
   rw [hf1.2.2.2.2.2.2.2,Z12,Z1,Z1]
   exact ⟨⟨c1,hc1,by simp [x]⟩,⟨zp1,hf1.2.2.1,by simp [x]⟩⟩
  have q1b:∃ v∈ side (n:=n) C g2 (1 - b),x v=true:=⟨d2,qod,by simp [x]⟩
  have h2:(∃ c∈ C2,x c=true)∧ (∃ d∈ D2,x d=true):=by
   apply (q10 x).mp
   fin_cases b
   ·exact ⟨Or.inr ⟨hrb,q1o⟩,Or.inl q1b⟩
   ·exact ⟨Or.inl q1b,Or.inr ⟨hrb,q1o⟩⟩
  rcases h2.1 with ⟨c,q4d,hxc⟩
  simp only [x,Z1] at hxc
  have hsc:s c=s z2:=z046 q03 hf2 q4d
  rcases hxc with rfl | rfl | rfl
  ·exact q4d
  ·exact absurd (hsc.symm.trans q1l) q02
  ·exact absurd (hsc.symm.trans (z047 q03 hf2 hd2)) q02
 have qgw:∀ b:Fin 2,OrReaches n C (opnd C g2 b) g1→
   (∃ c∈ C2,c∈ side (n:=n) C g2 (1 - b))→ D1⊆ D2:=by
  intro b hrb ⟨c2,hc2,qoe⟩ d1 hd1
  let x:Fin n→ Bool:=fun v=>decide (v=z1∨ v=d1∨ v=c2)
  have q1o:gateVal n C g1 x=true:=by
   rw [hf1.2.2.2.2.2.2.2,Z12,Z1,Z1]
   exact ⟨⟨z1,hf1.2.1,by simp [x]⟩,⟨d1,hd1,by simp [x]⟩⟩
  have q1b:∃ v∈ side (n:=n) C g2 (1 - b),x v=true:=⟨c2,qoe,by simp [x]⟩
  have h2:(∃ c∈ C2,x c=true)∧ (∃ d∈ D2,x d=true):=by
   apply (q10 x).mp
   fin_cases b
   ·exact ⟨Or.inr ⟨hrb,q1o⟩,Or.inl q1b⟩
   ·exact ⟨Or.inl q1b,Or.inr ⟨hrb,q1o⟩⟩
  rcases h2.2 with ⟨d,q4e,hxd⟩
  simp only [x,Z1] at hxd
  have hsd:s d=s zp2:=z047 q03 hf2 q4e
  rcases hxd with rfl | rfl | rfl
  ·exact absurd (hsz.symm.trans hsd) q02
  ·exact q4e
  ·exact absurd ((z046 q03 hf2 hc2).symm.trans hsd) q02
 have qb9:C1⊆ C2→ zp1=zp2:=by
  intro q0c
  obtain ⟨c,hc,hcz⟩:=z049 hf1
  exact z102 h4 hcz (hf1.2.2.2.1 c hc) hf1.1
   (hf2.2.2.2.1 c (q0c hc)) (hf2.2.2.2.1 z1 (q0c hf1.2.1))
 have qdm:D1⊆ D2→ z1=z2:=by
  intro q0c
  obtain ⟨d,hd,q1e⟩:=z050 hf1
  exact z102 h4 q1e (hf1.2.2.2.2.1 d hd) hf1.1.symm
   (hf2.2.2.2.2.1 d (q0c hd)) (hf2.2.2.2.2.1 zp1 (q0c hf1.2.2.1))
 have q33:∀ b:Fin 2,side (n:=n) C g2 b=∅→ OrReaches n C (opnd C g2 b) g1:=by
  intro b q0g
  by_contra hnr
  have h:=(q10 (fun _=>true)).mpr ⟨⟨z2,hf2.2.1,rfl⟩,⟨zp2,hf2.2.2.1,rfl⟩⟩
  fin_cases b
  ·dsimp at q0g hnr
   rcases h.1 with ⟨u,hu,_⟩ | ⟨hr,_⟩
   ·rw [q0g] at hu;exact Finset.notMem_empty _ hu
   ·exact hnr hr
  ·dsimp at q0g hnr
   rcases h.2 with ⟨u,hu,_⟩ | ⟨hr,_⟩
   ·rw [q0g] at hu;exact Finset.notMem_empty _ hu
   ·exact hnr hr
 have q27:Disjoint (side (n:=n) C g2 0) (side (n:=n) C g2 1):=by
  rw [Finset.disjoint_left];intro v hv0 hv1
  have h:=(q10 (fun w=>decide (w=v))).mp ⟨Or.inl ⟨v,hv0,by simp⟩,Or.inl ⟨v,hv1,by simp⟩⟩
  rcases h with ⟨⟨c,hc,hvc⟩,⟨d,hd,hvd⟩⟩
  simp only [Z1] at hvc hvd;subst hvc;subst hvd
  exact Finset.disjoint_left.mp q1n hc hd
 have q67:∀ u∈ side (n:=n) C g2 0,∀ v∈ side (n:=n) C g2 1,
   (u∈ C2∧ v∈ D2)∨ (u∈ D2∧ v∈ C2):=by
  intro u hu v hv
  have h:=(q10 (pairInput u v)).mp
   ⟨Or.inl ⟨u,hu,by simp [pairInput]⟩,Or.inl ⟨v,hv,by simp [pairInput]⟩⟩
  simp only [pairInput,Z1] at h
  rcases h with ⟨⟨c,hc,rfl | rfl⟩,⟨d,hd,hdu | hdv⟩⟩
  ·subst hdu;exact absurd hc (Finset.disjoint_right.mp q1n hd)
  ·subst hdv;exact Or.inl ⟨hc,hd⟩
  ·subst hdu;exact Or.inr ⟨hd,hc⟩
  ·subst hdv;exact absurd hc (Finset.disjoint_right.mp q1n hd)
 have q0i:∃ x,gateVal n C g1 x≠ gateVal n C g2 x:=by
  by_contra qaz;push Not at qaz
  exact z090 hL hne q72.1 (by omega:n+g1 < n+g2) qaz
 have q8u:∃ b2:Fin 2,side (n:=n) C g2 b2⊆ C2∧ side (n:=n) C g2 (1 - b2)⊆ D2:=by
  by_cases q6w:(side (n:=n) C g2 0).Nonempty
  ·by_cases q62:(side (n:=n) C g2 1).Nonempty
   ·obtain ⟨u0,hu0⟩:=q6w
    obtain ⟨v0,hv0⟩:=q62
    rcases q67 u0 hu0 v0 hv0 with ⟨qgx,qkf⟩ | ⟨qgy,qkg⟩
    ·refine ⟨0,?_,?_⟩
     ·intro u hu
      rcases q67 u hu v0 hv0 with ⟨huC,_⟩ | ⟨_,qkg⟩
      ·exact huC
      ·exact absurd qkg (Finset.disjoint_right.mp q1n qkf)
     ·intro v hv
      simp only [sub_zero] at hv
      rcases q67 u0 hu0 v hv with ⟨_,hvD⟩ | ⟨qgy,_⟩
      ·exact hvD
      ·exact absurd qgy (Finset.disjoint_left.mp q1n qgx)
    ·refine ⟨1,?_,?_⟩
     ·intro v hv
      rcases q67 u0 hu0 v hv with ⟨qgx,_⟩ | ⟨_,hvC⟩
      ·exact absurd qgx (Finset.disjoint_right.mp q1n qgy)
      ·exact hvC
     ·intro u hu
      have h11:(1:Fin 2) - 1=0:=rfl;rw [h11] at hu
      rcases q67 u hu v0 hv0 with ⟨_,qkf⟩ | ⟨huD,_⟩
      ·exact absurd qkf (Finset.disjoint_left.mp q1n qkg)
      ·exact huD
   ·have q5c:side (n:=n) C g2 1=∅:=Z25.mp q62
    have hr1:OrReaches n C (opnd C g2 1) g1:=q33 1 q5c
    have qdn:∀ x,gateVal n C g2 x=true→ gateVal n C g1 x=true:=by
     intro x hx
     have h:=(q10 x).mpr (by
      rw [hf2.2.2.2.2.2.2.2] at hx;simpa [Z12,Z1] using hx)
     rcases h.2 with ⟨v,hv,_⟩ | ⟨_,hg1⟩
     ·rw [q5c] at hv;exact absurd hv (Finset.notMem_empty _)
     ·exact hg1
    have q1t:C2⊆ C1:=by
     intro c hc
     have h1:=qdn (pairInput c zp2) (by
      rw [hf2.2.2.2.2.2.2.2,Z12,Z1,Z1]
      exact ⟨⟨c,hc,by simp [pairInput]⟩,⟨zp2,hf2.2.2.1,by simp [pairInput]⟩⟩)
     rw [hf1.2.2.2.2.2.2.2,Z12,Z1,Z1] at h1
     rcases h1.1 with ⟨c',hc',qc9⟩
     simp only [pairInput,Z1] at qc9
     rcases qc9 with rfl | rfl
     ·exact hc'
     ·exact absurd ((z046 q03 hf1 hc').trans hsz).symm q02
    have q1u:D2⊆ D1:=by
     intro d hd
     have h1:=qdn (pairInput z2 d) (by
      rw [hf2.2.2.2.2.2.2.2,Z12,Z1,Z1]
      exact ⟨⟨z2,hf2.2.1,by simp [pairInput]⟩,⟨d,hd,by simp [pairInput]⟩⟩)
     rw [hf1.2.2.2.2.2.2.2,Z12,Z1,Z1] at h1
     rcases h1.2 with ⟨d',hd',q3x⟩
     simp only [pairInput,Z1] at q3x
     rcases q3x with rfl | rfl
     ·exact absurd ((z047 q03 hf1 hd').trans q1l) (hsz.symm ▸ q02)
     ·exact hd'
    have q26:∀ u∈ side (n:=n) C g2 0,(u∈ C2∧ D1⊆ D2)∨ (u∈ D2∧ C1⊆ C2):=by
     intro u hu
     by_cases hsu:s u=s z2
     ·left
      have hD:D1⊆ D2:=by
       intro d1 hd1
       let x:Fin n→ Bool:=fun w=>decide (w=u∨ w=z1∨ w=d1)
       have q1o:gateVal n C g1 x=true:=by
        rw [hf1.2.2.2.2.2.2.2,Z12,Z1,Z1]
        exact ⟨⟨z1,hf1.2.1,by simp [x]⟩,⟨d1,hd1,by simp [x]⟩⟩
       have h2:=(q10 x).mp ⟨Or.inl ⟨u,hu,by simp [x]⟩,Or.inr ⟨hr1,q1o⟩⟩
       rcases h2.2 with ⟨d,q4e,hxd⟩
       simp only [x,Z1] at hxd
       have hsd:=z047 q03 hf2 q4e
       rcases hxd with rfl | rfl | rfl
       ·exact absurd (hsu.symm.trans hsd) q02
       ·exact absurd (hsz.symm.trans hsd) q02
       ·exact q4e
      have qkh:u∈ C2:=by
       have qdo:D1=D2:=Finset.Subset.antisymm hD q1u
       have qdp:C1≠ C2:=by
        intro heq
        rcases q0i with ⟨x,hx⟩
        apply hx
        rw [hf1.2.2.2.2.2.2.2,hf2.2.2.2.2.2.2.2,heq,qdo]
       have qdq:∃ c1∈ C1,c1∉ C2:=by
        by_contra hno;push Not at hno
        exact qdp (Finset.Subset.antisymm hno q1t)
       obtain ⟨c1,hc1,qki⟩:=qdq
       let x:Fin n→ Bool:=fun w=>decide (w=u∨ w=c1∨ w=zp1)
       have q1o:gateVal n C g1 x=true:=by
        rw [hf1.2.2.2.2.2.2.2,Z12,Z1,Z1]
        exact ⟨⟨c1,hc1,by simp [x]⟩,⟨zp1,hf1.2.2.1,by simp [x]⟩⟩
       have h2:=(q10 x).mp ⟨Or.inl ⟨u,hu,by simp [x]⟩,Or.inr ⟨hr1,q1o⟩⟩
       rcases h2.1 with ⟨c,q4d,hxc⟩
       simp only [x,Z1] at hxc
       rcases hxc with rfl | rfl | rfl
       ·exact q4d
       ·exact absurd q4d qki
       ·exact absurd ((z046 q03 hf2 q4d).symm.trans q1l) q02
      exact ⟨qkh,hD⟩
     ·right
      have q24:s u=s zp2:=by cases hu':s u <;> cases hz':s z2 <;> cases qof:s zp2 <;> simp_all
      have hC:C1⊆ C2:=by
       intro c1 hc1
       let x:Fin n→ Bool:=fun w=>decide (w=u∨ w=c1∨ w=zp1)
       have q1o:gateVal n C g1 x=true:=by
        rw [hf1.2.2.2.2.2.2.2,Z12,Z1,Z1]
        exact ⟨⟨c1,hc1,by simp [x]⟩,⟨zp1,hf1.2.2.1,by simp [x]⟩⟩
       have h2:=(q10 x).mp ⟨Or.inl ⟨u,hu,by simp [x]⟩,Or.inr ⟨hr1,q1o⟩⟩
       rcases h2.1 with ⟨c,q4d,hxc⟩
       simp only [x,Z1] at hxc
       have hsc:=z046 q03 hf2 q4d
       rcases hxc with rfl | rfl | rfl
       ·exact absurd (q24.symm.trans hsc).symm q02
       ·exact q4d
       ·exact absurd (q1l.symm.trans hsc).symm q02
      have qkj:u∈ D2:=by
       have qdr:C1=C2:=Finset.Subset.antisymm hC q1t
       have qds:D1≠ D2:=by
        intro heq
        rcases q0i with ⟨x,hx⟩
        apply hx
        rw [hf1.2.2.2.2.2.2.2,hf2.2.2.2.2.2.2.2,qdr,heq]
       have qdt:∃ d1∈ D1,d1∉ D2:=by
        by_contra hno;push Not at hno
        exact qds (Finset.Subset.antisymm hno q1u)
       obtain ⟨d1,hd1,qkk⟩:=qdt
       let x:Fin n→ Bool:=fun w=>decide (w=u∨ w=z1∨ w=d1)
       have q1o:gateVal n C g1 x=true:=by
        rw [hf1.2.2.2.2.2.2.2,Z12,Z1,Z1]
        exact ⟨⟨z1,hf1.2.1,by simp [x]⟩,⟨d1,hd1,by simp [x]⟩⟩
       have h2:=(q10 x).mp ⟨Or.inl ⟨u,hu,by simp [x]⟩,Or.inr ⟨hr1,q1o⟩⟩
       rcases h2.2 with ⟨d,q4e,hxd⟩
       simp only [x,Z1] at hxd
       rcases hxd with rfl | rfl | rfl
       ·exact q4e
       ·exact absurd (hsz.symm.trans (z047 q03 hf2 q4e)) q02
       ·exact absurd q4e qkk
      exact ⟨qkj,hC⟩
    obtain ⟨u0,hu0⟩:=q6w
    rcases q26 u0 hu0 with ⟨qgx,q73⟩ | ⟨qgy,q74⟩
    ·refine ⟨0,?_,by simp [q5c]⟩
     intro u hu
     rcases q26 u hu with ⟨huC,_⟩ | ⟨_,q74⟩
     ·exact huC
     ·exfalso
      have q75:C1=C2:=Finset.Subset.antisymm q74 q1t
      have qba:D1=D2:=Finset.Subset.antisymm q73 q1u
      rcases q0i with ⟨x,hx⟩
      exact hx (by rw [hf1.2.2.2.2.2.2.2,hf2.2.2.2.2.2.2.2,q75,qba])
    ·refine ⟨1,by simp [q5c],?_⟩
     have h11:(1:Fin 2) - 1=0:=rfl;rw [h11]
     intro u hu
     rcases q26 u hu with ⟨_,q73⟩ | ⟨huD,_⟩
     ·exfalso
      have q75:C1=C2:=Finset.Subset.antisymm q74 q1t
      have qba:D1=D2:=Finset.Subset.antisymm q73 q1u
      rcases q0i with ⟨x,hx⟩
      exact hx (by rw [hf1.2.2.2.2.2.2.2,hf2.2.2.2.2.2.2.2,q75,qba])
     ·exact huD
  ·have q50:side (n:=n) C g2 0=∅:=Z25.mp q6w
   have hr0:OrReaches n C (opnd C g2 0) g1:=q33 0 q50
   by_cases q62:(side (n:=n) C g2 1).Nonempty
   ·
    have qdn:∀ x,gateVal n C g2 x=true→ gateVal n C g1 x=true:=by
     intro x hx
     have h:=(q10 x).mpr (by
      rw [hf2.2.2.2.2.2.2.2] at hx;simpa [Z12,Z1] using hx)
     rcases h.1 with ⟨v,hv,_⟩ | ⟨_,hg1⟩
     ·rw [q50] at hv;exact absurd hv (Finset.notMem_empty _)
     ·exact hg1
    have q1t:C2⊆ C1:=by
     intro c hc
     have h1:=qdn (pairInput c zp2) (by
      rw [hf2.2.2.2.2.2.2.2,Z12,Z1,Z1]
      exact ⟨⟨c,hc,by simp [pairInput]⟩,⟨zp2,hf2.2.2.1,by simp [pairInput]⟩⟩)
     rw [hf1.2.2.2.2.2.2.2,Z12,Z1,Z1] at h1
     rcases h1.1 with ⟨c',hc',qc9⟩
     simp only [pairInput,Z1] at qc9
     rcases qc9 with rfl | rfl
     ·exact hc'
     ·exact absurd ((z046 q03 hf1 hc').trans hsz).symm q02
    have q1u:D2⊆ D1:=by
     intro d hd
     have h1:=qdn (pairInput z2 d) (by
      rw [hf2.2.2.2.2.2.2.2,Z12,Z1,Z1]
      exact ⟨⟨z2,hf2.2.1,by simp [pairInput]⟩,⟨d,hd,by simp [pairInput]⟩⟩)
     rw [hf1.2.2.2.2.2.2.2,Z12,Z1,Z1] at h1
     rcases h1.2 with ⟨d',hd',q3x⟩
     simp only [pairInput,Z1] at q3x
     rcases q3x with rfl | rfl
     ·exact absurd ((z047 q03 hf1 hd').trans q1l) (hsz.symm ▸ q02)
     ·exact hd'
    have q26:∀ u∈ side (n:=n) C g2 1,(u∈ C2∧ D1⊆ D2)∨ (u∈ D2∧ C1⊆ C2):=by
     intro u hu
     by_cases hsu:s u=s z2
     ·left
      have hD:D1⊆ D2:=by
       intro d1 hd1
       let x:Fin n→ Bool:=fun w=>decide (w=u∨ w=z1∨ w=d1)
       have q1o:gateVal n C g1 x=true:=by
        rw [hf1.2.2.2.2.2.2.2,Z12,Z1,Z1]
        exact ⟨⟨z1,hf1.2.1,by simp [x]⟩,⟨d1,hd1,by simp [x]⟩⟩
       have h2:=(q10 x).mp ⟨Or.inr ⟨hr0,q1o⟩,Or.inl ⟨u,hu,by simp [x]⟩⟩
       rcases h2.2 with ⟨d,q4e,hxd⟩
       simp only [x,Z1] at hxd
       have hsd:=z047 q03 hf2 q4e
       rcases hxd with rfl | rfl | rfl
       ·exact absurd (hsu.symm.trans hsd) q02
       ·exact absurd (hsz.symm.trans hsd) q02
       ·exact q4e
      have qkh:u∈ C2:=by
       have qdo:D1=D2:=Finset.Subset.antisymm hD q1u
       have qdp:C1≠ C2:=by
        intro heq;rcases q0i with ⟨x,hx⟩
        exact hx (by rw [hf1.2.2.2.2.2.2.2,hf2.2.2.2.2.2.2.2,heq,qdo])
       have qdq:∃ c1∈ C1,c1∉ C2:=by
        by_contra hno;push Not at hno;exact qdp (Finset.Subset.antisymm hno q1t)
       obtain ⟨c1,hc1,qki⟩:=qdq
       let x:Fin n→ Bool:=fun w=>decide (w=u∨ w=c1∨ w=zp1)
       have q1o:gateVal n C g1 x=true:=by
        rw [hf1.2.2.2.2.2.2.2,Z12,Z1,Z1]
        exact ⟨⟨c1,hc1,by simp [x]⟩,⟨zp1,hf1.2.2.1,by simp [x]⟩⟩
       have h2:=(q10 x).mp ⟨Or.inr ⟨hr0,q1o⟩,Or.inl ⟨u,hu,by simp [x]⟩⟩
       rcases h2.1 with ⟨c,q4d,hxc⟩
       simp only [x,Z1] at hxc
       rcases hxc with rfl | rfl | rfl
       ·exact q4d
       ·exact absurd q4d qki
       ·exact absurd ((z046 q03 hf2 q4d).symm.trans q1l) q02
      exact ⟨qkh,hD⟩
     ·right
      have q24:s u=s zp2:=by cases hu':s u <;> cases hz':s z2 <;> cases qof:s zp2 <;> simp_all
      have hC:C1⊆ C2:=by
       intro c1 hc1
       let x:Fin n→ Bool:=fun w=>decide (w=u∨ w=c1∨ w=zp1)
       have q1o:gateVal n C g1 x=true:=by
        rw [hf1.2.2.2.2.2.2.2,Z12,Z1,Z1]
        exact ⟨⟨c1,hc1,by simp [x]⟩,⟨zp1,hf1.2.2.1,by simp [x]⟩⟩
       have h2:=(q10 x).mp ⟨Or.inr ⟨hr0,q1o⟩,Or.inl ⟨u,hu,by simp [x]⟩⟩
       rcases h2.1 with ⟨c,q4d,hxc⟩
       simp only [x,Z1] at hxc
       have hsc:=z046 q03 hf2 q4d
       rcases hxc with rfl | rfl | rfl
       ·exact absurd (q24.symm.trans hsc).symm q02
       ·exact q4d
       ·exact absurd (q1l.symm.trans hsc).symm q02
      have qkj:u∈ D2:=by
       have qdr:C1=C2:=Finset.Subset.antisymm hC q1t
       have qds:D1≠ D2:=by
        intro heq;rcases q0i with ⟨x,hx⟩
        exact hx (by rw [hf1.2.2.2.2.2.2.2,hf2.2.2.2.2.2.2.2,qdr,heq])
       have qdt:∃ d1∈ D1,d1∉ D2:=by
        by_contra hno;push Not at hno;exact qds (Finset.Subset.antisymm hno q1u)
       obtain ⟨d1,hd1,qkk⟩:=qdt
       let x:Fin n→ Bool:=fun w=>decide (w=u∨ w=z1∨ w=d1)
       have q1o:gateVal n C g1 x=true:=by
        rw [hf1.2.2.2.2.2.2.2,Z12,Z1,Z1]
        exact ⟨⟨z1,hf1.2.1,by simp [x]⟩,⟨d1,hd1,by simp [x]⟩⟩
       have h2:=(q10 x).mp ⟨Or.inr ⟨hr0,q1o⟩,Or.inl ⟨u,hu,by simp [x]⟩⟩
       rcases h2.2 with ⟨d,q4e,hxd⟩
       simp only [x,Z1] at hxd
       rcases hxd with rfl | rfl | rfl
       ·exact q4e
       ·exact absurd (hsz.symm.trans (z047 q03 hf2 q4e)) q02
       ·exact absurd q4e qkk
      exact ⟨qkj,hC⟩
    obtain ⟨u0,hu0⟩:=q62
    rcases q26 u0 hu0 with ⟨qgx,q73⟩ | ⟨qgy,q74⟩
    ·refine ⟨1,?_,by simp [q50]⟩
     intro u hu
     rcases q26 u hu with ⟨huC,_⟩ | ⟨_,q74⟩
     ·exact huC
     ·exfalso
      have q75:C1=C2:=Finset.Subset.antisymm q74 q1t
      have qba:D1=D2:=Finset.Subset.antisymm q73 q1u
      rcases q0i with ⟨x,hx⟩
      exact hx (by rw [hf1.2.2.2.2.2.2.2,hf2.2.2.2.2.2.2.2,q75,qba])
    ·refine ⟨0,by simp [q50],?_⟩
     simp only [sub_zero]
     intro u hu
     rcases q26 u hu with ⟨_,q73⟩ | ⟨huD,_⟩
     ·exfalso
      have q75:C1=C2:=Finset.Subset.antisymm q74 q1t
      have qba:D1=D2:=Finset.Subset.antisymm q73 q1u
      rcases q0i with ⟨x,hx⟩
      exact hx (by rw [hf1.2.2.2.2.2.2.2,hf2.2.2.2.2.2.2.2,q75,qba])
     ·exact huD
   ·
    exfalso
    have q5c:side (n:=n) C g2 1=∅:=Z25.mp q62
    have hr1:OrReaches n C (opnd C g2 1) g1:=q33 1 q5c
    rcases q0i with ⟨x,hx⟩
    apply hx
    apply Bool.eq_iff_iff.mpr
    rw [hf2.2.2.2.2.2.2.2,Z12,Z1,Z1,← q10 x]
    simp [q50,q5c,hr0,hr1]
 obtain ⟨b2,q68,q69⟩:=q8u
 refine ⟨b2,q68,q69,?_,?_,?_,?_⟩
 ·intro hrb
  have qkl:C1⊆ C2:=by
   by_cases qmm:(side (n:=n) C g2 (1 - b2)).Nonempty
   ·obtain ⟨d,hd⟩:=qmm
    exact qgv b2 hrb ⟨d,q69 hd,hd⟩
   ·have qkm:side (n:=n) C g2 (1 - b2)=∅:=Z25.mp qmm
    have qg2:=q33 (1 - b2) qkm
    intro c1 hc1
    have h2:=(q10 (pairInput c1 zp1)).mp (by
     have q1o:gateVal n C g1 (pairInput c1 zp1)=true:=by
      rw [hf1.2.2.2.2.2.2.2,Z12,Z1,Z1]
      exact ⟨⟨c1,hc1,by simp [pairInput]⟩,⟨zp1,hf1.2.2.1,by simp [pairInput]⟩⟩
     fin_cases b2
     ·exact ⟨Or.inr ⟨hrb,q1o⟩,Or.inr ⟨qg2,q1o⟩⟩
     ·exact ⟨Or.inr ⟨qg2,q1o⟩,Or.inr ⟨hrb,q1o⟩⟩)
    rcases h2.1 with ⟨c,q4d,hxc⟩
    simp only [pairInput,Z1] at hxc
    rcases hxc with rfl | rfl
    ·exact q4d
    ·exact absurd ((z046 q03 hf2 q4d).symm.trans q1l) q02
  refine ⟨qkl,qb9 qkl,?_⟩
  apply Finset.Subset.antisymm
  ·intro c hc
   rw [Z4]
   by_cases hcS:c∈ side (n:=n) C g2 b2
   ·exact Or.inr hcS
   ·left
    have h:=(q10 (pairInput c zp2)).mpr
     ⟨⟨c,hc,by simp [pairInput]⟩,⟨zp2,hf2.2.2.1,by simp [pairInput]⟩⟩
    have q3f:(∃ u∈ side (n:=n) C g2 b2,pairInput c zp2 u=true)∨
      (OrReaches n C (opnd C g2 b2) g1∧ gateVal n C g1 (pairInput c zp2)=true):=by
     fin_cases b2
     ·exact h.1
     ·exact h.2
    rcases q3f with ⟨u,hu,hxu⟩ | ⟨_,q1o⟩
    ·simp only [pairInput,Z1] at hxu
     rcases hxu with rfl | rfl
     ·exact absurd hu hcS
     ·exact absurd (q68 hu) (Finset.disjoint_right.mp q1n hf2.2.2.1)
    ·rw [hf1.2.2.2.2.2.2.2,Z12,Z1,Z1] at q1o
     rcases q1o.1 with ⟨c',hc',qc9⟩
     simp only [pairInput,Z1] at qc9
     rcases qc9 with rfl | rfl
     ·exact hc'
     ·exact absurd ((z046 q03 hf1 hc').trans hsz).symm q02
  ·exact Finset.union_subset qkl q68
 ·intro qog
  apply Finset.Subset.antisymm q68
  intro c hc
  have h:=(q10 (pairInput c zp2)).mpr
   ⟨⟨c,hc,by simp [pairInput]⟩,⟨zp2,hf2.2.2.1,by simp [pairInput]⟩⟩
  have q3f:(∃ u∈ side (n:=n) C g2 b2,pairInput c zp2 u=true)∨
    (OrReaches n C (opnd C g2 b2) g1∧ gateVal n C g1 (pairInput c zp2)=true):=by
   fin_cases b2
   ·exact h.1
   ·exact h.2
  rcases q3f with ⟨u,hu,hxu⟩ | ⟨hr,_⟩
  ·simp only [pairInput,Z1] at hxu
   rcases hxu with rfl | rfl
   ·exact hu
   ·exact absurd (q68 hu) (Finset.disjoint_right.mp q1n hf2.2.2.1)
  ·exact absurd hr qog
 ·intro qg2
  have qkn:D1⊆ D2:=by
   by_cases qmn:(side (n:=n) C g2 b2).Nonempty
   ·obtain ⟨c,hc⟩:=qmn
    have q51:1 - (1 - b2)=b2:=by fin_cases b2 <;> rfl
    exact qgw (1 - b2) qg2 ⟨c,q68 hc,by rw [q51];exact hc⟩
   ·have qko:side (n:=n) C g2 b2=∅:=Z25.mp qmn
    have hrb:=q33 b2 qko
    intro d1 hd1
    have h2:=(q10 (pairInput z1 d1)).mp (by
     have q1o:gateVal n C g1 (pairInput z1 d1)=true:=by
      rw [hf1.2.2.2.2.2.2.2,Z12,Z1,Z1]
      exact ⟨⟨z1,hf1.2.1,by simp [pairInput]⟩,⟨d1,hd1,by simp [pairInput]⟩⟩
     fin_cases b2
     ·exact ⟨Or.inr ⟨hrb,q1o⟩,Or.inr ⟨qg2,q1o⟩⟩
     ·exact ⟨Or.inr ⟨qg2,q1o⟩,Or.inr ⟨hrb,q1o⟩⟩)
    rcases h2.2 with ⟨d,q4e,hxd⟩
    simp only [pairInput,Z1] at hxd
    rcases hxd with rfl | rfl
    ·exact absurd (hsz.symm.trans (z047 q03 hf2 q4e)) q02
    ·exact q4e
  refine ⟨qkn,qdm qkn,?_⟩
  apply Finset.Subset.antisymm
  ·intro d hd
   rw [Z4]
   by_cases hdS:d∈ side (n:=n) C g2 (1 - b2)
   ·exact Or.inr hdS
   ·left
    have h:=(q10 (pairInput z2 d)).mpr
     ⟨⟨z2,hf2.2.1,by simp [pairInput]⟩,⟨d,hd,by simp [pairInput]⟩⟩
    have q3f:(∃ u∈ side (n:=n) C g2 (1 - b2),pairInput z2 d u=true)∨
      (OrReaches n C (opnd C g2 (1 - b2)) g1∧ gateVal n C g1 (pairInput z2 d)=true):=by
     fin_cases b2
     ·exact h.2
     ·exact h.1
    rcases q3f with ⟨u,hu,hxu⟩ | ⟨_,q1o⟩
    ·simp only [pairInput,Z1] at hxu
     rcases hxu with rfl | rfl
     ·exact absurd (q69 hu) (Finset.disjoint_left.mp q1n hf2.2.1)
     ·exact absurd hu hdS
    ·rw [hf1.2.2.2.2.2.2.2,Z12,Z1,Z1] at q1o
     rcases q1o.2 with ⟨d',hd',q3x⟩
     simp only [pairInput,Z1] at q3x
     rcases q3x with rfl | rfl
     ·exact absurd ((z047 q03 hf1 hd').trans q1l) (hsz.symm ▸ q02)
     ·exact hd'
  ·exact Finset.union_subset qkn q69
 ·intro qkp
  apply Finset.Subset.antisymm q69
  intro d hd
  have h:=(q10 (pairInput z2 d)).mpr
   ⟨⟨z2,hf2.2.1,by simp [pairInput]⟩,⟨d,hd,by simp [pairInput]⟩⟩
  have q3f:(∃ u∈ side (n:=n) C g2 (1 - b2),pairInput z2 d u=true)∨
    (OrReaches n C (opnd C g2 (1 - b2)) g1∧ gateVal n C g1 (pairInput z2 d)=true):=by
   fin_cases b2
   ·exact h.2
   ·exact h.1
  rcases q3f with ⟨u,hu,hxu⟩ | ⟨hr,_⟩
  ·simp only [pairInput,Z1] at hxu
   rcases hxu with rfl | rfl
   ·exact absurd (q69 hu) (Finset.disjoint_left.mp q1n hf2.2.1)
   ·exact hu
  ·exact absurd hr qkp
def z039 {n:ℕ} (C:Circuit) (H lamSet:Finset ℕ) (g1:ℕ)
  (zItem:Option (Fin n)) (M S:Finset (Fin n)):ℕ→ Finset (Option (Fin n))
 | w=>
  if hw:w < n then
   let u:Fin n:=⟨w,hw⟩
   if u∈ M then {some u} else if u∈ S then {none} else ∅
  else
   let k:=w - n
   if hk:k < C.gates.length then
    if k=g1 then {zItem}
    else if k∈ lamSet then {none}
    else if k∈ H then
     if h0:opnd C k 0 < w then
      if h1:opnd C k 1 < w then
       z039 C H lamSet g1 zItem M S (opnd C k 0) ∪ z039 C H lamSet g1 zItem M S (opnd C k 1)
      else ∅
     else ∅
    else ∅
   else ∅
termination_by w=>w
lemma z041 {n:ℕ} {C:Circuit} (H lamSet:Finset ℕ) (g1:ℕ)
  (zItem:Option (Fin n)) (M S:Finset (Fin n))
  {w:ℕ} (q8o:∀ k∈ H,w≠ n+k):
  (z039 C H lamSet g1 zItem M S w).card≤ 1:=by
 by_cases hw:w < n
 ·unfold z039;simp only [dif_pos hw];split_ifs <;> simp
 ·by_cases hkH:w - n∈ H
  ·exact absurd (by omega:w=n+(w - n)) (q8o (w - n) hkH)
  ·unfold z039;simp only [dif_neg hw,hkH,↓reduceIte];split_ifs <;> simp
lemma z042 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (H lamSet:Finset ℕ) (g1:ℕ)
  (zItem:Option (Fin n)) (M S:Finset (Fin n))
  (q3g:∀ k∈ H,k < C.gates.length)
  (q34:g1∉ H) (q1v:Disjoint H lamSet)
  {k:ℕ} (hk:k∈ H):
  z039 C H lamSet g1 zItem M S (n+k)⊆
   z039 C H lamSet g1 zItem M S (opnd C k 0) ∪ z039 C H lamSet g1 zItem M S (opnd C k 1):=by
 have q0d:=q3g k hk
 have q80:=z104 hAO q0d 0
 have q58:=z104 hAO q0d 1
 have qoh:k≠ g1:=fun h=>q34 (h ▸ hk)
 have qkq:k∉ lamSet:=Finset.disjoint_left.mp q1v hk
 conv_lhs=>unfold z039
 rw [dif_neg (by omega),Nat.add_sub_cancel_left,dif_pos q0d,if_neg qoh,if_neg qkq,
  if_pos hk,dif_pos q80,dif_pos q58]
lemma z040 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (h4:NoFourCycle G)
  (hne:∃ u v:Fin n,G.Adj u v)
  {g1 g2:ℕ} (q00:∀ k,k∈ junk G C↔ k=g1∨ k=g2)
  (H:Finset ℕ) (v:Fin n) (zItem:Option (Fin n)) (M S:Finset (Fin n))
  (q8v:∀ u∈ S,G.Adj v u)
  (qg3:∀ u∈ M,s(v,u)∈ Ustar G C)
  (q3g:∀ k∈ H,k < C.gates.length)
  (q34:g1∉ H) (q1v:Disjoint H (lam G C)):
  ∀ w < n+g2,
   (∀ k,OrReaches n C w k→ k < C.gates.length∧ k∈ orN G C ∪ {g1})→
   (∀ k,OrReaches n C w k→ k∈ orN G C \ lam G C→ k∈ H)→
   orIn n C w⊆ S→
   (∀ u∈ orIn n C w,u∈ M→ some u∈ z039 C H (lam G C) g1 zItem M S w)∧
   (∀ u∈ orIn n C w,u∉ M→ none∈ z039 C H (lam G C) g1 zItem M S w)∧
   (OrReaches n C w g1→ zItem∈ z039 C H (lam G C) g1 zItem M S w∨
    none∈ z039 C H (lam G C) g1 zItem M S w):=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih=>
  intro q53 q28 q5f q35
  by_cases hwn:w < n
  ·refine ⟨?_,?_,fun hr=>absurd hr (z112 hwn)⟩
   ·intro u hu huM
    have heq:=(z095 C u ⟨w,hwn⟩).mp hu
    subst heq;unfold z039;rw [dif_pos hwn,if_pos huM];simp
   ·intro u hu huM
    have heq:=(z095 C u ⟨w,hwn⟩).mp hu
    have huS:=q35 hu
    subst heq;unfold z039;rw [dif_pos hwn,if_neg huM,if_pos huS];simp
  ·have q0d:w - n < C.gates.length:=by
    have q2p:=z094.mp ((q00 g2).mpr (Or.inr rfl));omega
   have q0f:w=n+(w - n):=by omega
   set k:=w - n
   have qgz:OrReaches n C w k:=by rw [q0f];exact z115 q0d
   have q3w:=(q28 k qgz).2
   rw [Z4,Z3] at q3w
   rcases q3w with q04 | rfl
   ·have qkr:k≠ g1:=by
     intro h;subst h
     have h1:=(z096.mp q04).2.1
     have h2:=(z094.mp ((q00 k).mpr (Or.inl rfl))).2.1
     rw [h1] at h2;cases h2
    by_cases q6a:k∈ lam G C
    ·have qh0:2≤ (orIn n C (n+k)).card:=
      z084 hL q01 hne q00 q6a (by omega)
     have q5g:=z085 hL.1 h4 q6a
      (fun u hu=>q8v u (q35 (by rwa [q0f]))) qh0
     have q4f:z039 C H (lam G C) g1 zItem M S w={none}:=by
      unfold z039;rw [dif_neg hwn,dif_pos q0d,if_neg qkr,if_pos q6a]
     rw [q4f]
     refine ⟨?_,fun _ _ _=>Finset.mem_singleton_self none,fun _=>Or.inr (Finset.mem_singleton_self none)⟩
     intro u hu huM
     exfalso
     have h1:=q5g u (by rwa [← q0f])
     have h2:=(Z2.mp (qg3 u huM)).2
     exact h2 h1
    ·have qoi:k∈ H:=q5f k qgz (Z2.mpr ⟨q04,q6a⟩)
     have hk':=z096.mp q04
     have q80:opnd C k 0 < w:=by have:=z104 hL.1 hk'.1 0;omega
     have q58:opnd C k 1 < w:=by have:=z104 hL.1 hk'.1 1;omega
     have q4f:z039 C H (lam G C) g1 zItem M S w=
       z039 C H (lam G C) g1 zItem M S (opnd C k 0) ∪
       z039 C H (lam G C) g1 zItem M S (opnd C k 1):=by
      conv_lhs=>unfold z039
      rw [dif_neg hwn,dif_pos q0d,if_neg qkr,if_neg q6a,if_pos qoi,
       dif_pos q80,dif_pos q58]
     have q2m:∀ b:Fin 2,∀ m,OrReaches n C (opnd C k b) m→ OrReaches n C w m:=by
      intro b m hrm
      rw [q0f,z111 hk'.1]
      exact Or.inr ⟨hk'.2.1,opnd C k b,z105 hL.1 hk'.1 b,hrm.1,z104 hL.1 hk'.1 b,hrm⟩
     have q0o:orIn n C w=orIn n C (opnd C k 0) ∪ orIn n C (opnd C k 1):=by
      rw [q0f];exact z108 hL.1 hk'.1 hk'.2.1
     have ih0:=ih (opnd C k 0) q80 (by omega)
      (fun m hm=>q28 m (q2m 0 m hm))
      (fun m hm=>q5f m (q2m 0 m hm))
      (fun u hu=>q35 (by rw [q0o];exact Finset.mem_union_left _ hu))
     have ih1:=ih (opnd C k 1) q58 (by omega)
      (fun m hm=>q28 m (q2m 1 m hm))
      (fun m hm=>q5f m (q2m 1 m hm))
      (fun u hu=>q35 (by rw [q0o];exact Finset.mem_union_right _ hu))
     rw [q4f]
     refine ⟨?_,?_,?_⟩
     ·intro u hu huM
      rw [q0o,Z4] at hu
      rcases hu with h0 | h1
      ·exact Finset.mem_union_left _ (ih0.1 u h0 huM)
      ·exact Finset.mem_union_right _ (ih1.1 u h1 huM)
     ·intro u hu huM
      rw [q0o,Z4] at hu
      rcases hu with h0 | h1
      ·exact Finset.mem_union_left _ (ih0.2.1 u h0 huM)
      ·exact Finset.mem_union_right _ (ih1.2.1 u h1 huM)
     ·intro hr
      rw [q0f,z111 hk'.1] at hr
      rcases hr with heq | ⟨_,u,hu,_,_,qmo⟩
      ·exact absurd heq.symm qkr
      ·rw [z071 hL.1 hk'.1] at hu
       simp only [Z10,Z11,or_false] at hu
       rcases hu with rfl | rfl
       ·exact (ih0.2.2 qmo).imp (Finset.mem_union_left _) (Finset.mem_union_left _)
       ·exact (ih1.2.2 qmo).imp (Finset.mem_union_right _) (Finset.mem_union_right _)
   ·have q4f:z039 C H (lam G C) k zItem M S w={zItem}:=by
     unfold z039;rw [dif_neg hwn,dif_pos q0d,if_pos rfl]
    have q5x:=z094.mp ((q00 k).mpr (Or.inl rfl))
    have q0g:orIn n C w=∅:=by rw [q0f];exact z107 (n:=n) q0d q5x.2.1
    rw [q4f,q0g]
    exact ⟨by simp,by simp,fun _=>Or.inl (Finset.mem_singleton_self zItem)⟩
lemma z125 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (h4:NoFourCycle G)
  (hne:∃ u v:Fin n,G.Adj u v)
  {g1 g2:ℕ} (q00:∀ k,k∈ junk G C↔ k=g1∨ k=g2)
  {w:ℕ} (q53:w < n+g2)
  (q76:∀ k,w=n+k→ ¬ BelowF G C k)
  (hn1:¬ OrReaches n C w g1)
  {v:Fin n} {S:Finset (Fin n)} (hS:orIn n C w=S) (q8v:∀ u∈ S,G.Adj v u):
  let M:=S.filter (fun u=>s(v,u)∈ Ustar G C)
  let H:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w k)
  (M.Nonempty→ M.card≤ H.card+1)∧
  ((∃ r∈ S,r∉ M)→ M.card≤ H.card):=by
 intro M H
 have q3g:∀ k∈ H,k < C.gates.length:=fun k hk=>
  (z096.mp (Z2.mp (Z0.mp hk).1).1).1
 have q34:g1∉ H:=fun hg=>by
  have h1:=(z096.mp (Z2.mp (Z0.mp hg).1).1).2.1
  have h2:=(z094.mp ((q00 g1).mpr (Or.inl rfl))).2.1
  rw [h1] at h2;cases h2
 have q1v:Disjoint H (lam G C):=by
  rw [Finset.disjoint_left];intro k hk hkl
  exact (Z2.mp (Z0.mp hk).1).2 hkl
 have q28:∀ k,OrReaches n C w k→ k < C.gates.length∧ k∈ orN G C ∪ {g1}:=by
  intro k hk
  have qks:k≤ w - n:=z113 hk
  have q0d:k < C.gates.length:=by
   have q2p:=z094.mp ((q00 g2).mpr (Or.inr rfl));omega
  refine ⟨q0d,?_⟩
  have q5w:¬ BelowF G C k:=by
   intro hbk
   by_cases hwn:w < n
   ·exact z112 hwn hk
   ·have q0f:w=n+(w - n):=by omega
    have q10:=z117 hL.1
    have q9r:∀ u < n+C.gates.length,(∀ m,u=n+m→ ¬ BelowF G C m)→
      OrReaches n C u k→ False:=by
     intro u
     induction u using Nat.strong_induction_on with
     | ind u ihu=>
      intro qkt q77 qdu
      by_cases hun:u < n
      ·exact z112 hun qdu
      ·have q36:u - n < C.gates.length:=by omega
       have q1d:u=n+(u - n):=by omega
       rw [q1d,z111 q36] at qdu
       rcases qdu with rfl | ⟨qaw,x,hx,hnx,qoj,qku⟩
       ·exact q77 (u - n) q1d hbk
       ·rw [z071 hL.1 q36] at hx
        simp only [Z10,Z11,or_false] at hx
        have qkv:∀ m,x=n+m→ ¬ BelowF G C m:=by
         intro m hm hbm
         rcases hx with rfl | rfl
         ·exact z091 hL q01 hne q36 qaw (q77 _ q1d) 0 (by rw [hm];exact hbm)
         ·exact z091 hL q01 hne q36 qaw (q77 _ q1d) 1 (by rw [hm];exact hbm)
        exact ihu x (by omega) (by omega) qkv qku
    have q2p:=z094.mp ((q00 g2).mpr (Or.inr rfl))
    exact q9r w (by omega) q76 hk
  rcases hL.1.1 _ (z069 q0d) with q17 | hor
  ·have hkj:k∈ junk G C:=z094.mpr ⟨q0d,q17,q5w⟩
   rw [q00] at hkj
   rcases hkj with rfl | rfl
   ·exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
   ·have:=hk.1;omega
  ·exact Finset.mem_union_left _ (z096.mpr ⟨q0d,hor,q5w⟩)
 have qg3:∀ u∈ M,s(v,u)∈ Ustar G C:=fun u hu=>(Z0.mp hu).2
 have qca:=z040 hL q01 h4 hne q00 H v none M S q8v qg3 q3g q34 q1v
  w q53 q28 (fun k hk hkd=>Z0.mpr ⟨hkd,hk⟩) (by rw [hS])
 let Items:Finset (Option (Fin n)):=insert none (M.image some)
 obtain ⟨comp,q18,q2w⟩:=z106 hL.1 Items H q3g
  (z039 C H (lam G C) g1 none M S)
  (fun u _ q8o=>z041 H (lam G C) g1 none M S q8o)
  (fun k hk=>z042 hL.1 H (lam G C) g1 none M S q3g q34 q1v hk)
 have q2p:=z094.mp ((q00 g2).mpr (Or.inr rfl))
 obtain ⟨c,hc⟩:=q2w w (by omega)
 have q84:M.image some⊆ z039 C H (lam G C) g1 none M S w:=by
  intro y hy;simp only [Z19] at hy;rcases hy with ⟨u,hu,rfl⟩
  exact qca.1 u (by rw [hS];exact (Z0.mp hu).1) hu
 have q78:(M.image some).card=M.card:=Finset.card_image_of_injective M (Option.some_injective (Fin n))
 constructor
 ·intro qkw
  have hle:=z101 q18 (Finset.subset_insert none (M.image some))
   (qkw.image some) ⟨c,fun a ha=>hc a (q84 ha)⟩
  omega
 ·rintro ⟨r,hrS,qj6⟩
  have qdv:none∈ z039 C H (lam G C) g1 none M S w:=qca.2.1 r (by rw [hS];exact hrS) qj6
  have q1p:Items⊆ z039 C H (lam G C) g1 none M S w:=by
   intro a ha;simp only [Items,Z6] at ha
   rcases ha with rfl | ha
   ·exact qdv
   ·exact q84 ha
  have hle:=z101 q18 (Finset.Subset.refl Items) ⟨none,Finset.mem_insert_self _ _⟩
   ⟨c,fun a ha=>hc a (q1p ha)⟩
  have q3h:none∉ M.image some:=by simp
  have q79:Items.card=M.card+1:=by
   simp only [Items,Z24 q3h,q78]
  omega
lemma z099 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (h4:NoFourCycle G)
  (hne:∃ u v:Fin n,G.Adj u v)
  {g1 g2:ℕ} (q00:∀ k,k∈ junk G C↔ k=g1∨ k=g2)
  {w1 w2:ℕ} (qcb:w1 < n+g2) (qcc:w2 < n+g2)
  (qh1:∀ k,w1=n+k→ ¬ BelowF G C k) (qh2:∀ k,w2=n+k→ ¬ BelowF G C k)
  {v:Fin n} {S1 S2:Finset (Fin n)}
  (hS1:orIn n C w1=S1) (qdw:orIn n C w2⊆ S2)
  (qcd:S1 ∪ S2=S1 ∪ orIn n C w2)
  (q8v:∀ u∈ S1 ∪ S2,G.Adj v u)
  {z0:Fin n} (qh3:z0∈ S1)
  (qh4:z0∈ orIn n C w2∨ OrReaches n C w2 g1):
  let S:=S1 ∪ S2
  let M:=S.filter (fun u=>s(v,u)∈ Ustar G C)
  let H:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w1 k∨ OrReaches n C w2 k)
  (M.Nonempty→ M.card≤ H.card+1)∧
  (z0∉ M→ M.card≤ H.card)∧
  (¬ OrReaches n C w2 g1→ (∃ r∈ S,r∉ M)→ M.card≤ H.card):=by
 intro S M H
 have q3g:∀ k∈ H,k < C.gates.length:=fun k hk=>
  (z096.mp (Z2.mp (Z0.mp hk).1).1).1
 have q34:g1∉ H:=fun hg=>by
  have h1:=(z096.mp (Z2.mp (Z0.mp hg).1).1).2.1
  have h2:=(z094.mp ((q00 g1).mpr (Or.inl rfl))).2.1
  rw [h1] at h2;cases h2
 have q1v:Disjoint H (lam G C):=by
  rw [Finset.disjoint_left];intro k hk hkl
  exact (Z2.mp (Z0.mp hk).1).2 hkl
 have q37:∀ w < n+g2,(∀ k,w=n+k→ ¬ BelowF G C k)→
   ∀ k,OrReaches n C w k→ k < C.gates.length∧ k∈ orN G C ∪ {g1}:=by
  intro w q53 q76 k hk
  have qks:k≤ w - n:=z113 hk
  have q2p:=z094.mp ((q00 g2).mpr (Or.inr rfl))
  have q0d:k < C.gates.length:=by omega
  refine ⟨q0d,?_⟩
  have q5w:¬ BelowF G C k:=by
   intro hbk
   have q9r:∀ u < n+C.gates.length,(∀ m,u=n+m→ ¬ BelowF G C m)→
     OrReaches n C u k→ False:=by
    intro u
    induction u using Nat.strong_induction_on with
    | ind u ihu=>
     intro qkt q77 qdu
     by_cases hun:u < n
     ·exact z112 hun qdu
     ·have q36:u - n < C.gates.length:=by omega
      have q1d:u=n+(u - n):=by omega
      rw [q1d,z111 q36] at qdu
      rcases qdu with rfl | ⟨qaw,x,hx,hnx,qoj,qku⟩
      ·exact q77 (u - n) q1d hbk
      ·rw [z071 hL.1 q36] at hx
       simp only [Z10,Z11,or_false] at hx
       have qkv:∀ m,x=n+m→ ¬ BelowF G C m:=by
        intro m hm hbm
        rcases hx with rfl | rfl
        ·exact z091 hL q01 hne q36 qaw (q77 _ q1d) 0 (by rw [hm];exact hbm)
        ·exact z091 hL q01 hne q36 qaw (q77 _ q1d) 1 (by rw [hm];exact hbm)
       exact ihu x (by omega) (by omega) qkv qku
   exact q9r w (by omega) q76 hk
  rcases hL.1.1 _ (z069 q0d) with q17 | hor
  ·have hkj:k∈ junk G C:=z094.mpr ⟨q0d,q17,q5w⟩
   rw [q00] at hkj
   rcases hkj with rfl | rfl
   ·exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
   ·have:=hk.1;omega
  ·exact Finset.mem_union_left _ (z096.mpr ⟨q0d,hor,q5w⟩)
 let zItem:Option (Fin n):=if z0∈ M then some z0 else none
 have qg3:∀ u∈ M,s(v,u)∈ Ustar G C:=fun u hu=>(Z0.mp hu).2
 have hp1:=z040 hL q01 h4 hne q00 H v zItem M S q8v qg3 q3g q34 q1v
  w1 qcb (q37 w1 qcb qh1) (fun k hk hkd=>Z0.mpr ⟨hkd,Or.inl hk⟩)
  (by rw [hS1];exact Finset.subset_union_left)
 have hp2:=z040 hL q01 h4 hne q00 H v zItem M S q8v qg3 q3g q34 q1v
  w2 qcc (q37 w2 qcc qh2) (fun k hk hkd=>Z0.mpr ⟨hkd,Or.inr hk⟩)
  (Finset.Subset.trans qdw Finset.subset_union_right)
 let Items:Finset (Option (Fin n)):=insert none (M.image some)
 obtain ⟨comp,q18,q2w⟩:=z106 hL.1 Items H q3g
  (z039 C H (lam G C) g1 zItem M S)
  (fun u _ q8o=>z041 H (lam G C) g1 zItem M S q8o)
  (fun k hk=>z042 hL.1 H (lam G C) g1 zItem M S q3g q34 q1v hk)
 have q2p:=z094.mp ((q00 g2).mpr (Or.inr rfl))
 obtain ⟨c1,hc1⟩:=q2w w1 (by omega)
 obtain ⟨c2,hc2⟩:=q2w w2 (by omega)
 set R1:=z039 C H (lam G C) g1 zItem M S w1
 set R2:=z039 C H (lam G C) g1 zItem M S w2
 have q85:M.image some⊆ R1 ∪ R2:=by
  intro y hy;simp only [Z19] at hy;rcases hy with ⟨u,hu,rfl⟩
  have huS:u∈ S1 ∪ orIn n C w2:=by rw [← qcd];exact (Z0.mp hu).1
  rw [Z4] at huS
  rcases huS with h1 | h2
  ·exact Finset.mem_union_left _ (hp1.1 u (by rw [hS1];exact h1) hu)
  ·exact Finset.mem_union_right _ (hp2.1 u h2 hu)
 have q6b:zItem∈ R1:=by
  by_cases hzM:z0∈ M
  ·simp only [zItem,if_pos hzM];exact hp1.1 z0 (by rw [hS1];exact qh3) hzM
  ·simp only [zItem,if_neg hzM];exact hp1.2.1 z0 (by rw [hS1];exact qh3) hzM
 have q1q:zItem∈ R2∨ none∈ R2:=by
  rcases qh4 with hz2 | hr2
  ·left
   by_cases hzM:z0∈ M
   ·simp only [zItem,if_pos hzM];exact hp2.1 z0 hz2 hzM
   ·simp only [zItem,if_neg hzM];exact hp2.2.1 z0 hz2 hzM
  ·exact hp2.2.2 hr2
 have q78:(M.image some).card=M.card:=Finset.card_image_of_injective M (Option.some_injective (Fin n))
 have q3h:none∉ M.image some:=by simp
 have q79:Items.card=M.card+1:=by
  simp only [Items,Z24 q3h,q78]
 refine ⟨?_,?_,?_⟩
 ·intro qkw
  rcases q1q with qkx | qdx
  ·have qh5:c1=c2:=(hc1 zItem q6b).symm.trans (hc2 zItem qkx)
   have hle:=z101 q18 (Finset.subset_insert none (M.image some))
    (qkw.image some) ⟨c1,fun a ha=>by
     rcases Z4.mp (q85 ha) with h1 | h2
     ·exact hc1 a h1
     ·rw [qh5];exact hc2 a h2⟩
   omega
  ·have q8w:Items⊆ (R1 ∩ Items) ∪ (R2 ∩ Items):=by
    intro a ha
    simp only [Z4,Z5]
    by_cases q9s:a=none
    ·subst q9s;exact Or.inr ⟨qdx,ha⟩
    ·have haM:a∈ M.image some:=by
      simp only [Items,Z6] at ha;exact ha.resolve_left q9s
     rcases Z4.mp (q85 haM) with h1 | h2
     ·exact Or.inl ⟨h1,ha⟩
     ·exact Or.inr ⟨h2,ha⟩
   have hle:=z134 q18
    (Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right)
    ⟨c1,fun a ha=>hc1 a (Z5.mp ha).1⟩
    ⟨c2,fun a ha=>hc2 a (Z5.mp ha).1⟩
   have qok:=Finset.card_le_card q8w
   omega
 ·intro qh6
  have q6c:zItem=none:=by simp [zItem,qh6]
  have q86:none∈ R1:=by rwa [← q6c]
  have qbb:none∈ R2:=by
   rcases q1q with h | h
   ·rwa [q6c] at h
   ·exact h
  have qh5:c1=c2:=(hc1 none q86).symm.trans (hc2 none qbb)
  have q1p:Items⊆ R1 ∪ R2:=by
   intro a ha;simp only [Items,Z6] at ha
   rcases ha with rfl | ha
   ·exact Finset.mem_union_left _ q86
   ·exact q85 ha
  have hle:=z101 q18 (Finset.Subset.refl Items) ⟨none,Finset.mem_insert_self _ _⟩
   ⟨c1,fun a ha=>by
    rcases Z4.mp (q1p ha) with h1 | h2
    ·exact hc1 a h1
    ·rw [qh5];exact hc2 a h2⟩
  omega
 ·intro qol ⟨r,hrS,qj6⟩
  have hz2:z0∈ orIn n C w2:=qh4.resolve_right qol
  have qkx:zItem∈ R2:=by
   by_cases hzM:z0∈ M
   ·simp only [zItem,if_pos hzM];exact hp2.1 z0 hz2 hzM
   ·simp only [zItem,if_neg hzM];exact hp2.2.1 z0 hz2 hzM
  have qh5:c1=c2:=(hc1 zItem q6b).symm.trans (hc2 zItem qkx)
  have qdy:none∈ R1 ∪ R2:=by
   have hr':r∈ S1 ∪ orIn n C w2:=by rwa [← qcd]
   rcases Z4.mp hr' with h1 | h2
   ·exact Finset.mem_union_left _ (hp1.2.1 r (by rw [hS1];exact h1) qj6)
   ·exact Finset.mem_union_right _ (hp2.2.1 r h2 qj6)
  have q1p:Items⊆ R1 ∪ R2:=by
   intro a ha;simp only [Items,Z6] at ha
   rcases ha with rfl | ha
   ·exact qdy
   ·exact q85 ha
  have hle:=z101 q18 (Finset.Subset.refl Items) ⟨none,Finset.mem_insert_self _ _⟩
   ⟨c1,fun a ha=>by
    rcases Z4.mp (q1p ha) with h1 | h2
    ·exact hc1 a h1
    ·rw [qh5];exact hc2 a h2⟩
  omega
def z124 (n:ℕ) (C:Circuit) (g1 g2 w:ℕ):Prop:=
 OrReaches n C w g1∨ OrReaches n C w g2
noncomputable def z126 {n:ℕ} (C:Circuit) (s:Fin n→ Bool) (z1:Fin n) (g1 g2 a:ℕ):Fin n:=
 letI:=Classical.dec
 if h0:(side (n:=n) C a 0).card=1 then
  let u:=Classical.choose (Finset.card_eq_one.mp h0)
  if h1:(side (n:=n) C a 1).card=1 then
   let v:=Classical.choose (Finset.card_eq_one.mp h1)
   if z124 n C g1 g2 (opnd C a 0)∧ ¬ z124 n C g1 g2 (opnd C a 1) then v
   else if z124 n C g1 g2 (opnd C a 1)∧ ¬ z124 n C g1 g2 (opnd C a 0) then u
   else if s u=s z1 then u else v
  else u
 else if h1:(side (n:=n) C a 1).card=1 then
  Classical.choose (Finset.card_eq_one.mp h1)
 else z1
lemma z128 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hAO:IsAO2 n C) (h4:NoFourCycle G) (s:Fin n→ Bool) (z1:Fin n) (g1 g2:ℕ)
  {a:ℕ} (ha:a∈ tops G C \ centreless G C):
  side (n:=n) C a 0={z126 C s z1 g1 g2 a}∨
   side (n:=n) C a 1={z126 C s z1 g1 g2 a}:=by
 have hst:=z129 hAO h4 ha
 unfold z126
 by_cases h0:(side (n:=n) C a 0).card=1
 ·simp only [dif_pos h0]
  have hu:=Classical.choose_spec (Finset.card_eq_one.mp h0)
  by_cases h1:(side (n:=n) C a 1).card=1
  ·simp only [dif_pos h1]
   have hv:=Classical.choose_spec (Finset.card_eq_one.mp h1)
   split_ifs
   ·exact Or.inr hv
   ·exact Or.inl hu
   ·exact Or.inl hu
   ·exact Or.inr hv
  ·simp only [dif_neg h1];exact Or.inl hu
 ·have h1:(side (n:=n) C a 1).card=1:=hst.2.2.resolve_left h0
  simp only [dif_neg h0,dif_pos h1]
  exact Or.inr (Classical.choose_spec (Finset.card_eq_one.mp h1))
lemma z127 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hAO:IsAO2 n C) (h4:NoFourCycle G) (s:Fin n→ Bool) (z1:Fin n) (g1 g2:ℕ)
  {u v:Fin n} (he:s(u,v)∈ starEdges G C):
  ∃ a∈ tops G C \ centreless G C,z126 C s z1 g1 g2 a=u∨ z126 C s z1 g1 g2 a=v:=by
 simp only [starEdges,Finset.mem_biUnion,Z19,Z18] at he
 rcases he with ⟨a,ha,⟨p0,p1⟩,⟨hp0,hp1⟩,qg0⟩
 have haS:a∈ tops G C \ centreless G C:=by
  rw [Z2];refine ⟨ha,fun hc=>?_⟩
  rw [centreless,Z0] at hc
  rcases hc.2 with h0 | h1
  ·rw [h0] at hp0;exact Finset.notMem_empty _ hp0
  ·rw [h1] at hp1;exact Finset.notMem_empty _ hp1
 refine ⟨a,haS,?_⟩
 rw [Sym2.eq_iff] at qg0
 rcases z128 hAO h4 s z1 g1 g2 haS with h0 | h1
 ·rw [h0,Z3] at hp0
  rcases qg0 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  ·exact Or.inl hp0.symm
  ·exact Or.inr hp0.symm
 ·rw [h1,Z3] at hp1
  rcases qg0 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  ·exact Or.inr hp1.symm
  ·exact Or.inl hp1.symm
lemma z100 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
  {C:Circuit} (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C)
  (hne:∃ u v:Fin n,G.Adj u v)
  {g1 g2:ℕ} (q00:∀ k,k∈ junk G C↔ k=g1∨ k=g2)
  {g:ℕ} (hg:g=g1∨ g=g2):
  ∀ w < n+C.gates.length,(∀ k,w=n+k→ ¬ BelowF G C k)→
   (orIn n C w).Nonempty→ OrReaches n C w g→
   ∃ m∈ orN G C \ lam G C,
    OrReaches n C w m∧ OrReaches n C (n+m) g∧
    (orIn n C (n+m)).Nonempty∧ orIn n C (n+m)⊆ orIn n C w∧
    (orIn n C (opnd C m 0)=∅∨ orIn n C (opnd C m 1)=∅):=by
 have hgj:=z094.mp ((q00 g).mpr hg)
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih=>
  intro q53 hnb q52 hrg
  by_cases hwn:w < n
  ·exact absurd hrg (z112 hwn)
  ·have q0d:w - n < C.gates.length:=by omega
   have q0f:w=n+(w - n):=by omega
   set k:=w - n
   have q5w:¬ BelowF G C k:=hnb k q0f
   have q3d:(gateAt C k).op=GateOp.or:=by
    rcases hL.1.1 _ (z069 q0d) with q17 | hor
    ·exfalso;have q0g:=z107 (n:=n) q0d q17
     rw [← q0f] at q0g;exact q52.ne_empty q0g
    ·exact hor
   have q04:k∈ orN G C:=z096.mpr ⟨q0d,q3d,q5w⟩
   by_cases q0g:orIn n C (opnd C k 0)=∅∨ orIn n C (opnd C k 1)=∅
   ·refine ⟨k,Z2.mpr ⟨q04,fun hkl=>?_⟩,
     by rw [q0f];exact z115 q0d,by rwa [← q0f],
     by rwa [← q0f],by rw [← q0f],q0g⟩
    have hf:=Z0.mp hkl
    rcases q0g with h0 | h1
    ·exact hf.2.1.ne_empty h0
    ·exact hf.2.2.1.ne_empty h1
   ·push Not at q0g
    have q6w:(orIn n C (opnd C k 0)).Nonempty:=q0g.1
    have q62:(orIn n C (opnd C k 1)).Nonempty:=q0g.2
    rw [q0f,z111 q0d] at hrg
    have qom:k≠ g:=fun h=>by rw [h,hgj.2.1] at q3d;cases q3d
    rcases hrg with rfl | ⟨_,u,hu,hnu,qjq,qmp⟩
    ·exact absurd rfl qom
    ·rw [z071 hL.1 q0d] at hu
     simp only [Z10,Z11,or_false] at hu
     have qmq:∀ b:Fin 2,∀ m,opnd C k b=n+m→ ¬ BelowF G C m:=fun b m hm hbm=>
      z091 hL q01 hne q0d q3d q5w b (by rw [hm];exact hbm)
     have q6d:∀ b:Fin 2,orIn n C (opnd C k b)⊆ orIn n C w:=by
      intro b;rw [q0f,z108 hL.1 q0d q3d]
      fin_cases b
      ·exact Finset.subset_union_left
      ·exact Finset.subset_union_right
     rcases hu with rfl | rfl
     ·obtain ⟨m,hm,hwm,hmg,qky,qdz,hme⟩:=
       ih (opnd C k 0) (by omega) (by omega) (qmq 0) q6w qmp
      refine ⟨m,hm,?_,hmg,qky,Finset.Subset.trans qdz (q6d 0),hme⟩
      rw [q0f,z111 q0d]
      exact Or.inr ⟨q3d,opnd C k 0,z105 hL.1 q0d 0,hwm.1,z104 hL.1 q0d 0,hwm⟩
     ·obtain ⟨m,hm,hwm,hmg,qky,qdz,hme⟩:=
       ih (opnd C k 1) (by omega) (by omega) (qmq 1) q62 qmp
      refine ⟨m,hm,?_,hmg,qky,Finset.Subset.trans qdz (q6d 1),hme⟩
      rw [q0f,z111 q0d]
      exact Or.inr ⟨q3d,opnd C k 1,z105 hL.1 q0d 1,hwm.1,z104 hL.1 q0d 1,hwm⟩
lemma z122 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
  {C:Circuit} (hL:IsLeastAO G C)
  {g1 g2:ℕ} (q0y:g1 < g2) (q00:∀ k,k∈ junk G C↔ k=g1∨ k=g2)
  {w:ℕ} (q53:w < n+C.gates.length) (hnb:∀ k,w=n+k→ ¬ BelowF G C k)
  (q0g:orIn n C w=∅) (hr1:OrReaches n C w g1) (hr2:OrReaches n C w g2):
  ∃ m∈ orN G C \ lam G C,g2 < m∧ orIn n C (n+m)=∅:=by
 have hnw:n≤ w:=hr1.1
 have q0d:w - n < C.gates.length:=by omega
 have q0f:w=n+(w - n):=by omega
 set k:=w - n
 have q5w:¬ BelowF G C k:=hnb k q0f
 have qo8:g2≤ k:=by have:=z113 hr2;omega
 have qpk:k≠ g2:=by
  intro h;subst h
  have q2p:=z094.mp ((q00 k).mpr (Or.inr rfl))
  rw [q0f,z111 q0d] at hr1
  rcases hr1 with h1 | ⟨hor,_⟩
  ·omega
  ·rw [q2p.2.1] at hor;cases hor
 have q3d:(gateAt C k).op=GateOp.or:=by
  rcases hL.1.1 _ (z069 q0d) with q17 | hor
  ·exfalso
   have hkj:=(q00 k).mp (z094.mpr ⟨q0d,q17,q5w⟩)
   rcases hkj with rfl | rfl <;> omega
  ·exact hor
 have q04:k∈ orN G C:=z096.mpr ⟨q0d,q3d,q5w⟩
 have q50:orIn n C (opnd C k 0)=∅:=by
  have hu:=z108 hL.1 q0d q3d
  rw [← q0f,q0g] at hu
  exact (Finset.union_eq_empty.mp hu.symm).1
 refine ⟨k,Z2.mpr ⟨q04,fun hkl=>(Z0.mp hkl).2.1.ne_empty q50⟩,
  by omega,by rwa [← q0f]⟩
lemma z131 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hAO:IsAO2 n C) {a:ℕ} (ha:a∈ tops G C) (b:Fin 2)
  {g:ℕ} (hr:OrReaches n C (opnd C a b) g)
  {w:Fin n} (hw:w∈ side (n:=n) C a (1 - b)):
  ∀ x:Fin n→ Bool,gateVal n C g x=true→ x w=true→ graphFun G ∅ x=true:=by
 have ha':=z098.mp ha
 intro x hgx hxw
 apply ha'.2.2 x
 rw [z070,z140 hAO x ha'.1 ha'.2.1,Z12]
 have hv1:=z117 hAO x hr hgx
 have hv2:=z110 hAO x hw hxw
 fin_cases b
 ·exact ⟨hv1,hv2⟩
 ·exact ⟨hv2,hv1⟩
lemma z072 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u≠ s v) (h4:NoFourCycle G)
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C)
  {g1 g2:ℕ} (q00:∀ k,k∈ junk G C↔ k=g1∨ k=g2)
  {C1 D1 C2 D2:Finset (Fin n)} {z1 zp1 z2 zp2:Fin n}
  (hf1:z000 G C g1 C1 D1 z1 zp1) (hf2:z000 G C g2 C2 D2 z2 zp2)
  (hsz:s z1=s z2) (q1l:s zp1=s zp2)
  {v u:Fin n} (qh7:s(v,u)∈ Ustar G C)
  (q1f:
   (gateVal n C g1 (pairInput v u)=true→
    (¬ ∀ x,gateVal n C g1 x=true→ x u=true→ graphFun G ∅ x=true)∧
    (∀ w:Fin n,s w=s v→ (∀ x,gateVal n C g1 x=true→ x w=true→ graphFun G ∅ x=true)→ G.Adj w u))∧
   (gateVal n C g2 (pairInput v u)=true→
    (¬ ∀ x,gateVal n C g2 x=true→ x u=true→ graphFun G ∅ x=true)∧
    (∀ w:Fin n,s w=s v→ (∀ x,gateVal n C g2 x=true→ x w=true→ graphFun G ∅ x=true)→ G.Adj w u)))
  (q4g:¬ (gateVal n C g1 (pairInput v u)=true∧ gateVal n C g2 (pairInput v u)=true∧
   ∀ x,gateVal n C g1 x=true→ gateVal n C g2 x=true→ graphFun G ∅ x=true)):
  (∃ a∈ tops G C \ centreless G C,z126 C s z1 g1 g2 a=v)∨
  (∃ a∈ centreless G C,∃ b:Fin 2,∃ g:ℕ,(g=g1∨ g=g2)∧
   gateVal n C g (pairInput v u)=true∧
   side (n:=n) C a b=∅∧ OrReaches n C (opnd C a b) g∧ v∈ side (n:=n) C a (1 - b))∨
  (s v=s zp1∧ ∃ a∈ tops G C \ centreless G C,∃ b:Fin 2,∃ g:ℕ,(g=g1∨ g=g2)∧
   gateVal n C g (pairInput v u)=true∧
   side (n:=n) C a (1 - b)={v}∧ OrReaches n C (opnd C a b) g∧
   ∃ g':ℕ,(g'=g1∨ g'=g2)∧ g'≠ g∧ OrReaches n C (opnd C a (1 - b)) g'∧
   ∃ mv∈ orN G C \ lam G C,OrReaches n C (n+mv) g'∧ orIn n C (n+mv)={v}∧
   ∃ u':Fin n,side (n:=n) C a b={u'}∧ s u'=s z1∧
   ∃ mu∈ orN G C \ lam G C,OrReaches n C (n+mu) g∧ orIn n C (n+mu)={u'}):=by
 have hne:∃ a b:Fin n,G.Adj a b:=⟨z1,zp1,hf1.1⟩
 have qh8:G.Adj v u:=SimpleGraph.mem_edgeFinset.mp (Z2.mp qh7).1
 have q6e:s(v,u)∉ starEdges G C:=(Z2.mp qh7).2
 have hcx:circuitFun n C (pairInput v u)=true:=by
  rw [congrFun hL.2.1 (pairInput v u)];exact (z074 v u).mpr qh8
 obtain ⟨a,ha,hva⟩:=(z023 hL hne _).mp hcx
 have ha':=z098.mp ha
 rw [z070,z140 hL.1 _ ha'.1 ha'.2.1,Z12] at hva
 have hw0:=(z103 hL q01 hne q00 (opnd C a 0)
  (by have:=z104 hL.1 ha'.1 0;omega) (z130 hL hne ha 0) (pairInput v u)).mp hva.1
 have hw1:=(z103 hL q01 hne q00 (opnd C a 1)
  (by have:=z104 hL.1 ha'.1 1;omega) (z130 hL hne ha 1) (pairInput v u)).mp hva.2
 have q54:¬ ((∃ w∈ side (n:=n) C a 0,pairInput v u w=true)∧
   (∃ w∈ side (n:=n) C a 1,pairInput v u w=true)):=by
  rintro ⟨⟨w0,q95,qgm⟩,⟨w1,qgn,qgo⟩⟩
  apply q6e
  simp only [starEdges,Finset.mem_biUnion,Z19,Z18]
  simp only [pairInput,Z1] at qgm qgo
  have q52:w0≠ w1:=fun h=>by subst h;exact G.loopless.irrefl w0 (z132 hL.1 ha q95 qgn)
  refine ⟨a,ha,(w0,w1),⟨q95,qgn⟩,?_⟩
  rw [Sym2.eq_iff]
  rcases qgm with rfl | rfl <;> rcases qgo with rfl | rfl
  ·exact absurd rfl q52
  ·exact Or.inl ⟨rfl,rfl⟩
  ·exact Or.inr ⟨rfl,rfl⟩
  ·exact absurd rfl q52
 have q1k:∀ g,(g=g1∨ g=g2)→
   ¬ (OrReaches n C (opnd C a 0) g∧ OrReaches n C (opnd C a 1) g):=by
  rintro g hg ⟨h0,h1⟩
  have hgj:=z094.mp ((q00 g).mpr hg)
  apply hgj.2.2
  intro x hgx
  apply ha'.2.2 x
  rw [z070,z140 hL.1 x ha'.1 ha'.2.1,Z12]
  exact ⟨z117 hL.1 x h0 hgx,z117 hL.1 x h1 hgx⟩
 have q2r:∀ g g',(g=g1∧ g'=g2∨ g=g2∧ g'=g1)→
   gateVal n C g (pairInput v u)=true→ gateVal n C g' (pairInput v u)=true→
   ¬ (OrReaches n C (opnd C a 0) g∧ OrReaches n C (opnd C a 1) g'):=by
  rintro g g' qon hgv qmr ⟨h0,h1⟩
  apply q4g
  rcases qon with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  ·refine ⟨hgv,qmr,fun x hx1 hx2=>ha'.2.2 x ?_⟩
   rw [z070,z140 hL.1 x ha'.1 ha'.2.1,Z12]
   exact ⟨z117 hL.1 x h0 hx1,z117 hL.1 x h1 hx2⟩
  ·refine ⟨qmr,hgv,fun x hx1 hx2=>ha'.2.2 x ?_⟩
   rw [z070,z140 hL.1 x ha'.1 ha'.2.1,Z12]
   exact ⟨z117 hL.1 x h0 hx2,z117 hL.1 x h1 hx1⟩
 have q0v:∀ b:Fin 2,∀ g,(g=g1∨ g=g2)→
   OrReaches n C (opnd C a b) g→ gateVal n C g (pairInput v u)=true→
   (∃ w∈ side (n:=n) C a (1 - b),pairInput v u w=true)→
   v∈ side (n:=n) C a (1 - b):=by
  intro b g hg hrb hgv ⟨w,hwm,hxw⟩
  simp only [pairInput,Z1] at hxw
  rcases hxw with rfl | rfl
  ·exact hwm
  ·exfalso
   have q3i:=z131 hL.1 ha b hrb hwm
   rcases hg with rfl | rfl
   ·exact (q1f.1 hgv).1 q3i
   ·exact (q1f.2 hgv).1 q3i
 have qh9:∃ b:Fin 2,∃ g:ℕ,(g=g1∨ g=g2)∧
   OrReaches n C (opnd C a b) g∧ gateVal n C g (pairInput v u)=true∧
   v∈ side (n:=n) C a (1 - b):=by
  rcases hw0 with h0 | ⟨hr0,hg1⟩ | ⟨hr0,hg2⟩
  ·rcases hw1 with h1 | ⟨hr1,hg1⟩ | ⟨hr1,hg2⟩
   ·exact absurd ⟨h0,h1⟩ q54
   ·exact ⟨1,g1,Or.inl rfl,hr1,hg1,q0v 1 g1 (Or.inl rfl) hr1 hg1 (by simpa [side] using h0)⟩
   ·exact ⟨1,g2,Or.inr rfl,hr1,hg2,q0v 1 g2 (Or.inr rfl) hr1 hg2 (by simpa [side] using h0)⟩
  ·rcases hw1 with h1 | ⟨hr1,_⟩ | ⟨hr1,hg2⟩
   ·exact ⟨0,g1,Or.inl rfl,hr0,hg1,q0v 0 g1 (Or.inl rfl) hr0 hg1 (by simpa [side] using h1)⟩
   ·exact absurd ⟨hr0,hr1⟩ (q1k g1 (Or.inl rfl))
   ·exact absurd ⟨hr0,hr1⟩ (q2r g1 g2 (Or.inl ⟨rfl,rfl⟩) hg1 hg2)
  ·rcases hw1 with h1 | ⟨hr1,hg1⟩ | ⟨hr1,_⟩
   ·exact ⟨0,g2,Or.inr rfl,hr0,hg2,q0v 0 g2 (Or.inr rfl) hr0 hg2 (by simpa [side] using h1)⟩
   ·exact absurd ⟨hr0,hr1⟩ (q2r g2 g1 (Or.inr ⟨rfl,rfl⟩) hg2 hg1)
   ·exact absurd ⟨hr0,hr1⟩ (q1k g2 (Or.inr rfl))
 obtain ⟨b,g,hg,hrb,hgv,q0p⟩:=qh9
 by_cases q0g:side (n:=n) C a b=∅
 ·right;left
  have haC:a∈ centreless G C:=by
   unfold centreless;rw [Z0]
   refine ⟨ha,?_⟩
   fin_cases b
   ·exact Or.inl q0g
   ·exact Or.inr q0g
  exact ⟨a,haC,b,g,hg,hgv,q0g,hrb,q0p⟩
 ·have qax:(side (n:=n) C a b).Nonempty:=Finset.nonempty_iff_ne_empty.mpr q0g
  have haS:a∈ tops G C \ centreless G C:=by
   rw [Z2];refine ⟨ha,fun hc=>?_⟩
   unfold centreless at hc;rw [Z0] at hc
   rcases z043 b with rfl | rfl
   ·rcases hc.2 with h0 | h1
    ·exact q0g h0
    ·simp only [sub_zero] at q0p;rw [h1] at q0p;exact Finset.notMem_empty _ q0p
   ·rcases hc.2 with h0 | h1
    ·have h11:(1:Fin 2) - 1=0:=rfl;rw [h11,h0] at q0p;exact Finset.notMem_empty _ q0p
    ·exact q0g h1
  have q09:side (n:=n) C a (1 - b)={v}:=by
   ext w
   simp only [Z3]
   constructor
   ·intro hw
    by_contra q52
    have q4h:1 < (side (n:=n) C a (1 - b)).card:=
     Finset.one_lt_card.mpr ⟨w,hw,v,q0p,q52⟩
    have hst:=z129 hL.1 h4 haS
    have q1c:(side (n:=n) C a b).card=1:=by
     rcases z043 b with rfl | rfl
     ·simp only [sub_zero] at q4h;exact hst.2.2.resolve_right (by omega)
     ·have h11:(1:Fin 2) - 1=0:=rfl;rw [h11] at q4h
      exact hst.2.2.resolve_left (by omega)
    obtain ⟨w0,hw0⟩:=Finset.card_eq_one.mp q1c
    have q95:w0∈ side (n:=n) C a b:=by rw [hw0];simp
    have q6f:G.Adj v w0:=by
     rcases z043 b with rfl | rfl
     ·exact (z132 hL.1 ha q95 q0p).symm
     ·exact z132 hL.1 ha q0p q95
    have q6g:G.Adj w w0:=by
     rcases z043 b with rfl | rfl
     ·exact (z132 hL.1 ha q95 hw).symm
     ·exact z132 hL.1 ha hw q95
    have qms:s w=s v:=z015 (q03 w w0 q6g) (q03 v w0 q6f)
    have q3i:=z131 hL.1 ha b hrb hw
    have qe0:G.Adj w u:=by
     rcases hg with rfl | rfl
     ·exact (q1f.1 hgv).2 w qms q3i
     ·exact (q1f.2 hgv).2 w qms q3i
    have qbc:w0=u:=z102 h4 q52 q6g q6f qe0 qh8
    subst qbc
    apply q6e
    simp only [starEdges,Finset.mem_biUnion,Z19,Z18]
    rcases z043 b with rfl | rfl
    ·exact ⟨a,ha,(w0,v),⟨q95,q0p⟩,Sym2.eq_swap⟩
    ·exact ⟨a,ha,(v,w0),⟨q0p,q95⟩,rfl⟩
   ·rintro rfl;exact q0p
  by_cases qj7:z126 C s z1 g1 g2 a=v
  ·exact Or.inl ⟨a,haS,qj7⟩
  ·right;right
   have q0a:(side (n:=n) C a (1 - b)).card=1:=by rw [q09];simp
   have q1c:(side (n:=n) C a b).card=1:=by
    by_contra qmt
    apply qj7
    unfold z126
    rcases z043 b with rfl | rfl
    ·simp only [sub_zero] at q0a q09
     rw [dif_neg qmt,dif_pos q0a]
     have hch:=Classical.choose_spec (Finset.card_eq_one.mp q0a)
     exact Finset.singleton_injective (hch.symm.trans q09)
    ·have h11:(1:Fin 2) - 1=0:=rfl
     rw [h11] at q0a q09
     rw [dif_pos q0a,dif_neg qmt]
     have hch:=Classical.choose_spec (Finset.card_eq_one.mp q0a)
     exact Finset.singleton_injective (hch.symm.trans q09)
   obtain ⟨u',hu'⟩:=Finset.card_eq_one.mp q1c
   have qbd:z124 n C g1 g2 (opnd C a b):=by
    rcases hg with rfl | rfl
    ·exact Or.inl hrb
    ·exact Or.inr hrb
   have q4i:z124 n C g1 g2 (opnd C a (1 - b)):=by
    by_contra qha
    apply qj7
    unfold z126
    rcases z043 b with rfl | rfl
    ·simp only [sub_zero] at q0a q09 qha
     rw [dif_pos q1c,dif_pos q0a,if_pos ⟨qbd,qha⟩]
     have hch:=Classical.choose_spec (Finset.card_eq_one.mp q0a)
     exact Finset.singleton_injective (hch.symm.trans q09)
    ·have h11:(1:Fin 2) - 1=0:=rfl
     rw [h11] at q0a q09 qha
     rw [dif_pos q0a,dif_pos q1c,if_neg (fun h=>qha h.1),if_pos ⟨qbd,qha⟩]
     have hch:=Classical.choose_spec (Finset.card_eq_one.mp q0a)
     exact Finset.singleton_injective (hch.symm.trans q09)
   have q9t:s u'=s z1:=by
    have q5h:G.Adj u' v:=by
     have qhb:u'∈ side (n:=n) C a b:=by rw [hu'];simp
     rcases z043 b with rfl | rfl
     ·exact z132 hL.1 ha qhb q0p
     ·exact (z132 hL.1 ha q0p qhb).symm
    have qbe:s u'≠ s v:=q03 u' v q5h
    by_contra qhc
    have qhd:s v=s z1:=z015 qbe.symm (Ne.symm qhc)
    apply qj7
    unfold z126
    rcases z043 b with rfl | rfl
    ·simp only [sub_zero] at q0a q09 q4i
     have qkz:=Classical.choose_spec (Finset.card_eq_one.mp q1c)
     have ql0:=Classical.choose_spec (Finset.card_eq_one.mp q0a)
     have qhe:Classical.choose (Finset.card_eq_one.mp q1c)=u':=
      Finset.singleton_injective (qkz.symm.trans hu')
     have qj8:Classical.choose (Finset.card_eq_one.mp q0a)=v:=
      Finset.singleton_injective (ql0.symm.trans q09)
     rw [dif_pos q1c,dif_pos q0a,if_neg (fun h=>h.2 q4i),
      if_neg (fun h=>h.2 qbd),qhe,if_neg qhc,qj8]
    ·have h11:(1:Fin 2) - 1=0:=rfl
     rw [h11] at q0a q09 q4i
     have qkz:=Classical.choose_spec (Finset.card_eq_one.mp q0a)
     have ql0:=Classical.choose_spec (Finset.card_eq_one.mp q1c)
     have qhe:Classical.choose (Finset.card_eq_one.mp q0a)=v:=
      Finset.singleton_injective (qkz.symm.trans q09)
     have qj8:Classical.choose (Finset.card_eq_one.mp q1c)=u':=
      Finset.singleton_injective (ql0.symm.trans hu')
     rw [dif_pos q0a,dif_pos q1c,if_neg (fun h=>h.2 qbd),
      if_neg (fun h=>h.2 q4i),qhe,if_pos qhd]
   have qe1:s v=s zp1:=by
    have q5h:G.Adj u' v:=by
     have qhb:u'∈ side (n:=n) C a b:=by rw [hu'];simp
     rcases z043 b with rfl | rfl
     ·exact z132 hL.1 ha qhb q0p
     ·exact (z132 hL.1 ha q0p qhb).symm
    exact z015 (q03 u' v q5h).symm (by rw [q9t];exact (q03 z1 zp1 hf1.1).symm)
   obtain ⟨g',hg',qj9⟩:∃ g',(g'=g1∨ g'=g2)∧ OrReaches n C (opnd C a (1 - b)) g':=by
    rcases q4i with h1 | h2
    ·exact ⟨g1,Or.inl rfl,h1⟩
    ·exact ⟨g2,Or.inr rfl,h2⟩
   have q7a:g'≠ g:=by
    intro heq;subst heq
    apply q1k g' hg'
    fin_cases b
    ·exact ⟨hrb,by simpa using qj9⟩
    ·exact ⟨by simpa using qj9,hrb⟩
   obtain ⟨mv,qe2,_,q38,qhf,q7b,_⟩:=
    z100 hL q01 hne q00 hg'
     (opnd C a (1 - b)) (by have:=z104 hL.1 ha'.1 (1 - b);omega)
     (z130 hL hne ha (1 - b)) (by rw [side] at q09;rw [q09];simp) qj9
   have q05:orIn n C (n+mv)={v}:=by
    rw [side] at q09;rw [q09] at q7b
    ext w;constructor
    ·exact fun hw=>q7b hw
    ·intro hw;rw [Z3] at hw;subst hw
     obtain ⟨y,hy⟩:=qhf
     have:=Z3.mp (q7b hy);subst this;exact hy
   obtain ⟨mu,qe3,_,q3j,qhg,q7c,_⟩:=
    z100 hL q01 hne q00 hg
     (opnd C a b) (by have:=z104 hL.1 ha'.1 b;omega)
     (z130 hL hne ha b) (by rw [side] at hu';rw [hu'];simp) hrb
   have q06:orIn n C (n+mu)={u'}:=by
    rw [side] at hu';rw [hu'] at q7c
    ext w;constructor
    ·exact fun hw=>q7c hw
    ·intro hw;rw [Z3] at hw;subst hw
     obtain ⟨y,hy⟩:=qhg
     have:=Z3.mp (q7c hy);subst this;exact hy
   exact ⟨qe1,a,haS,b,g,hg,hgv,q09,hrb,g',hg',q7a,qj9,
    mv,qe2,q38,q05,u',hu',q9t,mu,qe3,q3j,q06⟩
lemma z136 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (hne:∃ u v:Fin n,G.Adj u v)
  {g1 g2:ℕ} (q00:∀ k,k∈ junk G C↔ k=g1∨ k=g2)
  {w:ℕ} (q53:w < n+C.gates.length) (q76:∀ k,w=n+k→ ¬ BelowF G C k)
  (A:Finset (Fin n)) (ql1:A.Nonempty) (qhh:A⊆ orIn n C w)
  (FacAll:Finset ℕ)
  (q2n:∀ k,OrReaches n C w k→ k∈ lam G C ∪ FacAll→ (orIn n C (n+k) ∩ A).card≤ 1):
  let H:=(orN G C \ lam G C).filter (fun k=>
   OrReaches n C w k∧ k∉ FacAll∧ 2≤ (orIn n C (n+k) ∩ A).card)
  A.card≤ H.card+1:=by
 intro H
 let R:ℕ→ Finset (Fin n):=fun u=>
  if hu:u < n then
   if ⟨u,hu⟩∈ A then {⟨u,hu⟩} else ∅
  else if OrReaches n C w (u - n) then orIn n C u ∩ A else ∅
 have q3g:∀ k∈ H,k < C.gates.length:=fun k hk=>
  (z096.mp (Z2.mp (Z0.mp hk).1).1).1
 have q83:∀ u < n+C.gates.length,(∀ k∈ H,u≠ n+k)→ (R u).card≤ 1:=by
  intro u hu q8o
  dsimp only [R]
  split_ifs with hun q23 q0q
  ·simp
  ·simp
  ·have q0d:u - n < C.gates.length:=by omega
   have q1d:u=n+(u - n):=by omega
   set k:=u - n
   have q5w:¬ BelowF G C k:=by
    intro hbk
    have q9r:∀ x < n+C.gates.length,(∀ m,x=n+m→ ¬ BelowF G C m)→
      OrReaches n C x k→ False:=by
     intro x
     induction x using Nat.strong_induction_on with
     | ind x ihx=>
      intro qoo qe4 ql2
      by_cases hxn:x < n
      ·exact z112 hxn ql2
      ·have q36:x - n < C.gates.length:=by omega
       have qbf:x=n+(x - n):=by omega
       rw [qbf,z111 q36] at ql2
       rcases ql2 with heq | ⟨qaw,y,hy,hny,qpl,qop⟩
       ·exact qe4 (x - n) qbf (heq ▸ hbk)
       ·rw [z071 hL.1 q36] at hy
        simp only [Z10,Z11,or_false] at hy
        have qoq:∀ m,y=n+m→ ¬ BelowF G C m:=by
         intro m hm hbm
         rcases hy with rfl | rfl
         ·exact z091 hL q01 hne q36 qaw (qe4 _ qbf) 0 (by rw [hm];exact hbm)
         ·exact z091 hL q01 hne q36 qaw (qe4 _ qbf) 1 (by rw [hm];exact hbm)
        exact ihx y (by omega) (by omega) qoq qop
    exact q9r w q53 q76 q0q
   rcases hL.1.1 _ (z069 q0d) with q17 | hor
   ·rw [q1d,z107 (n:=n) q0d q17];simp
   ·have q04:k∈ orN G C:=z096.mpr ⟨q0d,hor,q5w⟩
    by_cases hkl:k∈ lam G C
    ·rw [q1d];exact q2n k q0q (Finset.mem_union_left _ hkl)
    ·by_cases hkf:k∈ FacAll
     ·rw [q1d];exact q2n k q0q (Finset.mem_union_right _ hkf)
     ·by_contra hgt
      push Not at hgt
      have hkH:k∈ H:=Z0.mpr
       ⟨Z2.mpr ⟨q04,hkl⟩,q0q,hkf,by rw [← q1d];omega⟩
      exact q8o k hkH q1d
  ·simp
 have qdk:∀ k∈ H,R (n+k)⊆ R (opnd C k 0) ∪ R (opnd C k 1):=by
  intro k hk
  have hkf:=Z0.mp hk
  have q04:=z096.mp (Z2.mp hkf.1).1
  have q0q:OrReaches n C w k:=hkf.2.1
  intro a ha
  dsimp only [R] at ha
  rw [dif_neg (by omega),Nat.add_sub_cancel_left,if_pos q0q,Z5,
   z108 hL.1 q04.1 q04.2.1,Z4] at ha
  rw [Z4]
  rcases ha.1 with h0 | h1
  ·left
   dsimp only [R]
   by_cases h0n:opnd C k 0 < n
   ·rw [dif_pos h0n]
    have q3z:a=⟨opnd C k 0,h0n⟩:=(z095 C a ⟨opnd C k 0,h0n⟩).mp h0
    subst q3z;rw [if_pos ha.2];exact Finset.mem_singleton_self _
   ·rw [dif_neg h0n]
    have hr0:OrReaches n C w (opnd C k 0 - n):=by
     apply z116 q0q
     rw [z111 q04.1]
     refine Or.inr ⟨q04.2.1,opnd C k 0,z105 hL.1 q04.1 0,by omega,
      z104 hL.1 q04.1 0,?_⟩
     have qhe:opnd C k 0=n+(opnd C k 0 - n):=by omega
     have hrs:OrReaches n C (n+(opnd C k 0 - n)) (opnd C k 0 - n):=
      z115 (by have:=z104 hL.1 q04.1 0;have:=q04.1;omega)
     rwa [← qhe] at hrs
    rw [if_pos hr0,Z5];exact ⟨h0,ha.2⟩
  ·right
   dsimp only [R]
   by_cases h1n:opnd C k 1 < n
   ·rw [dif_pos h1n]
    have q3z:a=⟨opnd C k 1,h1n⟩:=(z095 C a ⟨opnd C k 1,h1n⟩).mp h1
    subst q3z;rw [if_pos ha.2];exact Finset.mem_singleton_self _
   ·rw [dif_neg h1n]
    have hr1:OrReaches n C w (opnd C k 1 - n):=by
     apply z116 q0q
     rw [z111 q04.1]
     refine Or.inr ⟨q04.2.1,opnd C k 1,z105 hL.1 q04.1 1,by omega,
      z104 hL.1 q04.1 1,?_⟩
     have qj8:opnd C k 1=n+(opnd C k 1 - n):=by omega
     have hrs:OrReaches n C (n+(opnd C k 1 - n)) (opnd C k 1 - n):=
      z115 (by have:=z104 hL.1 q04.1 1;have:=q04.1;omega)
     rwa [← qj8] at hrs
    rw [if_pos hr1,Z5];exact ⟨h1,ha.2⟩
 obtain ⟨comp,q18,q2w⟩:=z106 hL.1 A H q3g R q83 qdk
 obtain ⟨c,hc⟩:=q2w w q53
 have q9u:A⊆ R w:=by
  intro a ha
  dsimp only [R]
  by_cases hwn:w < n
  ·rw [dif_pos hwn]
   have q3z:a=⟨w,hwn⟩:=(z095 C a ⟨w,hwn⟩).mp (qhh ha)
   subst q3z;rw [if_pos ha];exact Finset.mem_singleton_self _
  ·rw [dif_neg hwn]
   have hrw:OrReaches n C w (w - n):=by
    have q8s:w=n+(w - n):=by omega
    have hrs:OrReaches n C (n+(w - n)) (w - n):=z115 (by omega)
    rwa [← q8s] at hrs
   rw [if_pos hrw,Z5];exact ⟨qhh ha,ha⟩
 exact z101 q18 (Finset.Subset.refl A) ql1 ⟨c,fun a ha=>hc a (q9u ha)⟩
lemma z037 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (hne:∃ u v:Fin n,G.Adj u v)
  {g1 g2:ℕ} (q0y:g1 < g2) (q00:∀ k,k∈ junk G C↔ k=g1∨ k=g2)
  (q29:centreless G C=∅):
  ∃ m∈ orN G C \ lam G C,g2 < m:=by
 have q2p:=z094.mp ((q00 g2).mpr (Or.inr rfl))
 have q9b:=z120 hL hne
 have q32:=z121 hL hne
 have q9v:BelowF G C (C.output - n):=by
  rcases Z4.mp q32 with h | h
  ·exact (z098.mp h).2.2
  ·exact (z097.mp h).2.2
 have q4j:∀ k < C.gates.length,¬ BelowF G C k→ InCone n C g2 k→
   OrReaches n C (n+k) g2:=by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih=>
   intro hk hnb hin
   have hgt:g2 < k:=z079 hin
   have q3d:(gateAt C k).op=GateOp.or:=by
    rcases hL.1.1 _ (z069 hk) with q17 | hor
    ·exfalso
     have hkj:=(q00 k).mp (z094.mpr ⟨hk,q17,hnb⟩)
     rcases hkj with rfl | rfl <;> omega
    ·exact hor
   rw [z078 hk] at hin
   rcases hin with ⟨w,hw,hnw,qmu,heq | q0c⟩
   ·rw [z111 hk]
    refine Or.inr ⟨q3d,w,hw,hnw,qmu,?_⟩
    rw [show w=n+g2 by omega];exact z115 q2p.1
   ·have qhi:¬ BelowF G C (w - n):=by
     intro hbw
     rw [z071 hL.1 hk] at hw
     simp only [Z10,Z11,or_false] at hw
     rcases hw with rfl | rfl
     ·exact z091 hL q01 hne hk q3d hnb 0
       (by rw [show opnd C k 0=n+(opnd C k 0 - n) by omega];exact hbw)
     ·exact z091 hL q01 hne hk q3d hnb 1
       (by rw [show opnd C k 1=n+(opnd C k 1 - n) by omega];exact hbw)
    have qe5:=ih (w - n) (by omega) (by omega) qhi q0c
    rw [z111 hk]
    exact Or.inr ⟨q3d,w,hw,hnw,qmu,by rwa [show n+(w - n)=w by omega] at qe5⟩
 have qe6:∀ j < C.gates.length,BelowF G C j→ InCone n C g2 j→
   ∃ a∈ tops G C,∃ b:Fin 2,OrReaches n C (opnd C a b) g2:=by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih=>
   intro hj hbf hin
   rcases hL.1.1 _ (z069 hj) with q17 | hor
   ·have q8x:j∈ tops G C:=z098.mpr ⟨hj,q17,hbf⟩
    rw [z078 hj] at hin
    rcases hin with ⟨w,hw,hnw,qfz,heq | q0c⟩
    ·rw [z071 hL.1 hj] at hw
     simp only [Z10,Z11,or_false] at hw
     have hrg:OrReaches n C w g2:=by rw [show w=n+g2 by omega];exact z115 q2p.1
     rcases hw with rfl | rfl
     ·exact ⟨j,q8x,0,hrg⟩
     ·exact ⟨j,q8x,1,hrg⟩
    ·rw [z071 hL.1 hj] at hw
     simp only [Z10,Z11,or_false] at hw
     rcases hw with rfl | rfl
     ·have qhi:=z130 hL hne q8x 0 (opnd C j 0 - n) (by omega)
      have hr:=q4j (opnd C j 0 - n) (by omega) qhi q0c
      exact ⟨j,q8x,0,by rwa [show n+(opnd C j 0 - n)=opnd C j 0 by omega] at hr⟩
     ·have qhi:=z130 hL hne q8x 1 (opnd C j 1 - n) (by omega)
      have hr:=q4j (opnd C j 1 - n) (by omega) qhi q0c
      exact ⟨j,q8x,1,by rwa [show n+(opnd C j 1 - n)=opnd C j 1 by omega] at hr⟩
   ·rw [z078 hj] at hin
    rcases hin with ⟨w,hw,hnw,qfz,heq | q0c⟩
    ·exfalso
     rw [z071 hL.1 hj] at hw
     simp only [Z10,Z11,or_false] at hw
     have qor:BelowF G C g2:=by
      rcases hw with rfl | rfl
      ·have h0:=(z119 hL hj hor hbf 0).2.2;rwa [← heq] at h0
      ·have h1:=(z119 hL hj hor hbf 1).2.2;rwa [← heq] at h1
     exact q2p.2.2 qor
    ·rw [z071 hL.1 hj] at hw
     simp only [Z10,Z11,or_false] at hw
     rcases hw with rfl | rfl
     ·have h0:=z119 hL hj hor hbf 0
      exact ih (opnd C j 0 - n) (by omega) h0.2.1 h0.2.2 q0c
     ·have h1:=z119 hL hj hor hbf 1
      exact ih (opnd C j 1 - n) (by omega) h1.2.1 h1.2.2 q0c
 have qbg:InCone n C g2 (C.output - n):=by
  have hc:=(z088 hL hne g2 q2p.1).2
  rcases hc with heq | ⟨_,hin⟩
  ·exfalso;apply q2p.2.2;rw [show g2=C.output - n by omega];exact q9v
  ·exact hin
 obtain ⟨a,ha,b,hrb⟩:=qe6 (C.output - n) (by omega) q9v qbg
 have ha':=z098.mp ha
 have qax:(side (n:=n) C a b).Nonempty:=by
  rw [Finset.nonempty_iff_ne_empty]
  intro q0g
  have hac:a∈ centreless G C:=by
   unfold centreless;rw [Z0]
   refine ⟨ha,?_⟩;fin_cases b
   ·exact Or.inl q0g
   ·exact Or.inr q0g
  rw [q29] at hac;exact Finset.notMem_empty _ hac
 obtain ⟨m,hm,_,qg4,_,_,_⟩:=z100 hL q01 hne q00 (Or.inr rfl)
  (opnd C a b) (by have:=z104 hL.1 ha'.1 b;omega) (z130 hL hne ha b) qax hrb
 have hle:g2≤ m:=by have:=z113 qg4;omega
 have qmv:m≠ g2:=by
  intro h;subst h
  have h1:=(z096.mp (Z2.mp hm).1).2.1
  rw [h1] at q2p;cases q2p.2.1
 exact ⟨m,hm,by omega⟩
lemma z022 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u≠ s v) (h4:NoFourCycle G)
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C)
  {g1 g2:ℕ} (q0y:g1 < g2) (q00:∀ k,k∈ junk G C↔ k=g1∨ k=g2)
  {C1 D1 C2 D2:Finset (Fin n)} {z zp:Fin n}
  (hf1:z000 G C g1 C1 D1 z zp) (hf2:z000 G C g2 C2 D2 z zp):False:=by
 classical
 have hne:∃ u v:Fin n,G.Adj u v:=⟨z,zp,hf1.1⟩
 have qdf:g1≠ g2:=Nat.ne_of_lt q0y
 have q5x:=z094.mp ((q00 g1).mpr (Or.inl rfl))
 have q2p:=z094.mp ((q00 g2).mpr (Or.inr rfl))
 have q39:z≠ zp:=G.ne_of_adj hf1.1
 obtain ⟨⟨qce,qcf,qcg,qch⟩,b1,qci,qb0⟩:=
  z066 q03 hL q01 q0y q00 hf1
 obtain ⟨qcj,qck,b2,q44,q2o,q6h,q3k,q5a,q2a⟩:=
  z067 q03 h4 hL q01 q0y q00 hf1 hf2 rfl rfl
 set w1C:=opnd C g1 b1
 set w1D:=opnd C g1 (1 - b1)
 set w2C:=opnd C g2 b2
 set w2D:=opnd C g2 (1 - b2)
 set Cs:=C1 ∪ C2
 set Ds:=D1 ∪ D2
 set MC:=Cs.filter (fun c=>s(c,zp)∈ Ustar G C)
 set MD:=Ds.filter (fun d=>s(z,d)∈ Ustar G C)
 set FacC:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w1C k∨ OrReaches n C w2C k)
 set FacD:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w1D k∨ OrReaches n C w2D k)
 have q5i:∀ k∈ FacC,k < g2:=by
  intro k hk
  have hr:=(Z0.mp hk).2
  rcases hr with h1 | h2
  ·have:=z113 h1;have:=z104 hL.1 q5x.1 b1;omega
  ·have:=z113 h2;have:=z104 hL.1 q2p.1 b2;omega
 have q1g:∀ k∈ FacD,k < g2:=by
  intro k hk
  have hr:=(Z0.mp hk).2
  rcases hr with h1 | h2
  ·have:=z113 h1;have:=z104 hL.1 q5x.1 (1 - b1);omega
  ·have:=z113 h2;have:=z104 hL.1 q2p.1 (1 - b2);omega
 have q7d:Disjoint Cs Ds:=by
  rw [Finset.disjoint_left];intro u huC huD
  have hsc:s u=s z:=by
   rcases Z4.mp huC with h | h
   ·exact z046 q03 hf1 h
   ·exact z046 q03 hf2 h
  have hsd:s u=s zp:=by
   rcases Z4.mp huD with h | h
   ·exact z047 q03 hf1 h
   ·exact z047 q03 hf2 h
  exact q03 z zp hf1.1 (hsc.symm.trans hsd)
 have q5j:Disjoint FacC FacD:=by
  rw [Finset.disjoint_left];intro k hkC hkD
  have q04:=z096.mp (Z2.mp (Z0.mp hkC).1).1
  have q68:orIn n C (n+k)⊆ Cs:=by
   rcases (Z0.mp hkC).2 with h1 | h2
   ·exact Finset.Subset.trans (z109 h1) (by rw [show orIn n C w1C=C1 from qci];exact Finset.subset_union_left)
   ·exact Finset.Subset.trans (z109 h2) (Finset.Subset.trans q44 Finset.subset_union_right)
  have q69:orIn n C (n+k)⊆ Ds:=by
   rcases (Z0.mp hkD).2 with h1 | h2
   ·exact Finset.Subset.trans (z109 h1) (by rw [show orIn n C w1D=D1 from qb0];exact Finset.subset_union_left)
   ·exact Finset.Subset.trans (z109 h2) (Finset.Subset.trans q2o Finset.subset_union_right)
  have q0g:orIn n C (n+k)=∅:=by
   ext u;simp only [Finset.notMem_empty,iff_false]
   intro hu;exact Finset.disjoint_left.mp q7d (q68 hu) (q69 hu)
  have qo9:k < g2:=q5i k hkC
  have hn2:¬ OrReaches n C (n+k) g2:=fun h=>by have:=z113 h;omega
  have q10:∀ x,wval C x (n+k)=true↔ OrReaches n C (n+k) g1∧ gateVal n C g1 x=true:=by
   intro x
   have h:=z103 hL q01 hne q00 (n+k) (by omega)
    (fun m hm=>by have:m=k:=(by omega);subst this;exact q04.2.2) x
   simpa [q0g,hn2] using h
  have hr1:OrReaches n C (n+k) g1:=((q10 (fun _=>true)).mp (z138 hL.1 (n+k) (by omega))).1
  have qdn:g1≤ k:=by have:=z113 hr1;omega
  have qgb:k≠ g1:=fun h=>by rw [h,q5x.2.1] at q04;cases q04.2.1
  apply z090 hL hne q04.1 (by omega:n+g1 < n+k)
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [q10 x];simp [hr1,z070]
 have q2q:∀ a,a∈ junk G C→ ∀ b:Fin 2,∀ m,opnd C a b=n+m→ ¬ BelowF G C m:=by
  intro a ha b m hm hbm
  have ha':=z094.mp ha
  exact z089 hL hne ha'.1 ha'.2.1 b (by rw [hm];exact hbm)
 have qbh:C1 ∪ C2=C1 ∪ orIn n C w2C:=by
  by_cases hr:OrReaches n C w2C g1
  ·have h:=q6h hr
   rw [Finset.union_eq_right.mpr h.1,h.2.2];rfl
  ·rw [show orIn n C w2C=C2 from q3k hr]
 have q5k:D1 ∪ D2=D1 ∪ orIn n C w2D:=by
  by_cases hr:OrReaches n C w2D g1
  ·have h:=q5a hr
   rw [Finset.union_eq_right.mpr h.1,h.2.2];rfl
  ·rw [show orIn n C w2D=D2 from q2a hr]
 have qhj:z∈ orIn n C w2C∨ OrReaches n C w2C g1:=by
  by_cases hr:OrReaches n C w2C g1
  ·exact Or.inr hr
  ·left;rw [show orIn n C w2C=C2 from q3k hr];exact hf2.2.1
 have qe7:zp∈ orIn n C w2D∨ OrReaches n C w2D g1:=by
  by_cases hr:OrReaches n C w2D g1
  ·exact Or.inr hr
  ·left;rw [show orIn n C w2D=D2 from q2a hr];exact hf2.2.2.1
 have q5l:=z099 hL q01 h4 hne q00
  (by have:=z104 hL.1 q5x.1 b1;omega:w1C < n+g2)
  (z104 hL.1 q2p.1 b2)
  (q2q g1 ((q00 g1).mpr (Or.inl rfl)) b1)
  (q2q g2 ((q00 g2).mpr (Or.inr rfl)) b2)
  (show orIn n C w1C=C1 from qci) q44 qbh
  (fun u hu=>by rcases Z4.mp hu with h | h;exact (hf1.2.2.2.1 u h).symm;exact (hf2.2.2.2.1 u h).symm)
  hf1.2.1 qhj
 have q7e:=z099 hL q01 h4 hne q00
  (by have:=z104 hL.1 q5x.1 (1 - b1);omega:w1D < n+g2)
  (z104 hL.1 q2p.1 (1 - b2))
  (q2q g1 ((q00 g1).mpr (Or.inl rfl)) (1 - b1))
  (q2q g2 ((q00 g2).mpr (Or.inr rfl)) (1 - b2))
  (show orIn n C w1D=D1 from qb0) q2o q5k
  (fun u hu=>by rcases Z4.mp hu with h | h;exact (hf1.2.2.2.2.1 u h).symm;exact (hf2.2.2.2.2.1 u h).symm)
  hf1.2.2.1 qe7
 have qhk:Cs.filter (fun u=>s(zp,u)∈ Ustar G C)=MC:=by
  ext u;simp [MC,Sym2.eq_swap]
 dsimp only at q5l q7e
 rw [qhk] at q5l
 have q5m:FacC ∪ FacD⊆ orN G C \ lam G C:=
  Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
 have q5n:=z135 q03 hL q01 h4 q00 hf1 hf2
 have run_surgery:∀ L:Fin n→ Finset (Fin n),
   (∀ u∈ L z,G.Adj z u)→ (∀ u∈ L zp,G.Adj zp u)→
   (∀ e∈ Ustar G C,(∃ u∈ L z,e=s(z,u))∨ (∃ u∈ L zp,e=s(zp,u)))→
   let Zact:=({z,zp}:Finset (Fin n)).filter (fun v=>(L v).Nonempty)
   let Zhas:=Zact.filter (fun v=>∃ a∈ tops G C \ centreless G C,z126 C s z g1 g2 a=v)
   2 * (centreless G C).card+(orN G C \ lam G C).card+2≤
    (L z).card+(L zp).card+(Zact \ Zhas).card:=by
  intro L hLz q5y q8w Zact Zhas
  let topOf:Fin n→ ℕ:=fun v=>
   if h:∃ a∈ tops G C \ centreless G C,z126 C s z g1 g2 a=v then Classical.choose h else 0
  have qhl:=z093 hL q01 h4 qdf q00 hne Zact Zhas L topOf
   (Finset.filter_subset _ _)
   (fun v hv=>(Z0.mp hv).2)
   (fun v hv u hu=>by
    have hv':=(Z0.mp hv).1
    simp only [Z6,Z3] at hv'
    rcases hv' with rfl | rfl
    ·exact hLz u hu
    ·exact q5y u hu)
   (fun e he=>by
    rcases q8w e he with ⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩
    ·exact ⟨z,Z0.mpr ⟨by simp,⟨u,hu⟩⟩,u,hu,rfl⟩
    ·exact ⟨zp,Z0.mpr ⟨by simp,⟨u,hu⟩⟩,u,hu,rfl⟩)
   (fun v hv=>by
    have h:=(Z0.mp hv).2
    simp only [topOf,dif_pos h];exact (Classical.choose_spec h).1)
   (fun v hv=>by
    have h:=(Z0.mp hv).2
    simp only [topOf,dif_pos h]
    have hsp:=Classical.choose_spec h
    have q3f:=z128 hL.1 h4 s z g1 g2 hsp.1
    rwa [hsp.2] at q3f)
   (fun v1 hv1 v2 hv2 heq=>by
    have h1:=(Z0.mp hv1).2
    have h2:=(Z0.mp hv2).2
    simp only [topOf,dif_pos h1,dif_pos h2] at heq
    have qhm:=Classical.choose_spec h1
    have qhn:=Classical.choose_spec h2
    rw [← qhm.2,heq,qhn.2])
  have qe8:∑ v∈ Zact,(L v).card≤ (L z).card+(L zp).card:=by
   calc ∑ v∈ Zact,(L v).card≤ ∑ v∈ ({z,zp}:Finset (Fin n)),(L v).card:=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _=(L z).card+(L zp).card:=Finset.sum_pair q39
  omega
 by_cases he0:s(z,zp)∈ Ustar G C
 ·
  have qja:z∈ MC:=Z0.mpr ⟨Finset.mem_union_left _ hf1.2.1,he0⟩
  have q9w:zp∈ MD:=Z0.mpr ⟨Finset.mem_union_left _ hf1.2.2.1,he0⟩
  have qho:MC.card≤ FacC.card+1:=q5l.1 ⟨z,qja⟩
  have qcl:MD.card≤ FacD.card+1:=q7e.1 ⟨zp,q9w⟩
  have q7f:FacC.card+FacD.card≤ (orN G C \ lam G C).card:=by
   rw [← Finset.card_union_of_disjoint q5j];exact Finset.card_le_card q5m
  by_cases qmw:(MD.erase zp).Nonempty
  ·
   let L:Fin n→ Finset (Fin n):=fun v=>if v=z then MD else if v=zp then MC.erase z else ∅
   have hLz:L z=MD:=by simp [L]
   have q5y:L zp=MC.erase z:=by simp [L,q39.symm]
   have q8w:∀ e∈ Ustar G C,(∃ u∈ L z,e=s(z,u))∨ (∃ u∈ L zp,e=s(zp,u)):=by
    intro e he
    have heF:=q5n he
    simp only [Z4,z045,Z19] at heF
    rcases heF with (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩) | (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩)
    ·left;exact ⟨d,by rw [hLz];exact Z0.mpr ⟨Finset.mem_union_left _ hd,he⟩,rfl⟩
    ·by_cases hcz:c=z
     ·subst hcz;left;exact ⟨zp,by rw [hLz];exact q9w,rfl⟩
     ·right;exact ⟨c,by rw [q5y];exact Finset.mem_erase.mpr ⟨hcz,Z0.mpr ⟨Finset.mem_union_left _ hc,he⟩⟩,Sym2.eq_swap⟩
    ·left;exact ⟨d,by rw [hLz];exact Z0.mpr ⟨Finset.mem_union_right _ hd,he⟩,rfl⟩
    ·by_cases hcz:c=z
     ·subst hcz;left;exact ⟨zp,by rw [hLz];exact q9w,rfl⟩
     ·right;exact ⟨c,by rw [q5y];exact Finset.mem_erase.mpr ⟨hcz,Z0.mpr ⟨Finset.mem_union_right _ hc,he⟩⟩,Sym2.eq_swap⟩
   have q55:=run_surgery L
    (fun u hu=>by rw [hLz] at hu;rcases Z4.mp (Z0.mp hu).1 with h | h;exact (hf1.2.2.2.2.1 u h).symm;exact (hf2.2.2.2.2.1 u h).symm)
    (fun u hu=>by rw [q5y] at hu;rcases Z4.mp (Z0.mp (Finset.mem_of_mem_erase hu)).1 with h | h;exact (hf1.2.2.2.1 u h).symm;exact (hf2.2.2.2.1 u h).symm)
    q8w
   dsimp only at q55
   set Zact:=({z,zp}:Finset (Fin n)).filter (fun v=>(L v).Nonempty)
   set Zhas:=Zact.filter (fun v=>∃ a∈ tops G C \ centreless G C,z126 C s z g1 g2 a=v)
   have qhp:(Zact \ Zhas).card≤ 2:=by
    calc (Zact \ Zhas).card≤ Zact.card:=Finset.card_le_card Finset.sdiff_subset
     _≤ ({z,zp}:Finset (Fin n)).card:=Finset.card_le_card (Finset.filter_subset _ _)
     _=2:=Finset.card_pair q39
   have qbi:(MC.erase z).card=MC.card - 1:=Finset.card_erase_of_mem qja
   rw [hLz,q5y,qbi] at q55
   by_cases q0m:centreless G C=∅
   ·obtain ⟨m,q9x,qg4⟩:=z037 hL q01 hne q0y q00 q0m
    have q7g:m∉ FacC ∪ FacD:=by
     intro hmF;rcases Z4.mp hmF with h | h
     ·have:=q5i m h;omega
     ·have:=q1g m h;omega
    have q7h:FacC.card+FacD.card+1≤ (orN G C \ lam G C).card:=by
     have qe9:insert m (FacC ∪ FacD)⊆ orN G C \ lam G C:=Finset.insert_subset q9x q5m
     have qhq:=Finset.card_le_card qe9
     rw [Z24 q7g,Finset.card_union_of_disjoint q5j] at qhq
     exact qhq
    have qhr:z∈ Zhas:=by
     have qhs:z∈ Zact:=Z0.mpr ⟨by simp,by rw [hLz];exact ⟨zp,q9w⟩⟩
     rw [Z0];refine ⟨qhs,?_⟩
     obtain ⟨d,hd⟩:=qmw
     have q1e:d≠ zp:=(Finset.mem_erase.mp hd).1
     have qea:=Z0.mp (Finset.mem_of_mem_erase hd)
     have qbj:s(z,d)∈ Ustar G C:=qea.2
     have qos:G.Adj z d:=SimpleGraph.mem_edgeFinset.mp (Z2.mp qbj).1
     have q4k:¬ (gateVal n C g1 (pairInput z d)=true∧ gateVal n C g2 (pairInput z d)=true∧
       ∀ x,gateVal n C g1 x=true→ gateVal n C g2 x=true→ graphFun G ∅ x=true):=by
      rintro ⟨_,_,qaz⟩
      obtain ⟨c1,hc1,q87⟩:=z049 hf1
      obtain ⟨d1,hd1,q6i⟩:=z050 hf1
      obtain ⟨c2,hc2,q6x⟩:=z049 hf2
      obtain ⟨d2,hd2,q8y⟩:=z050 hf2
      let x:Fin n→ Bool:=fun w=>decide (w=c1∨ w=d1∨ w=c2∨ w=d2)
      have q1o:gateVal n C g1 x=true:=by
       rw [hf1.2.2.2.2.2.2.2,Z12,Z1,Z1]
       exact ⟨⟨c1,hc1,by simp [x]⟩,⟨d1,hd1,by simp [x]⟩⟩
      have ql3:gateVal n C g2 x=true:=by
       rw [hf2.2.2.2.2.2.2.2,Z12,Z1,Z1]
       exact ⟨⟨c2,hc2,by simp [x]⟩,⟨d2,hd2,by simp [x]⟩⟩
      have hFx:=(z073 x).mp (qaz x q1o ql3)
      rcases hFx with ⟨a,b,hab,ha,hb⟩
      simp only [x,Z1] at ha hb
      have q9y:s c1=s z:=z046 q03 hf1 hc1
      have q9z:s c2=s z:=z046 q03 hf2 hc2
      have qa0:s d1=s zp:=z047 q03 hf1 hd1
      have qa1:s d2=s zp:=z047 q03 hf2 hd2
      have q3y:∀ c d',(c=c1∨ c=c2)→ (d'=d1∨ d'=d2)→ ¬ G.Adj c d':=by
       intro c d' hc hd' qk9
       have qot:c≠ z:=hc.elim (fun h=>h ▸ q87) (fun h=>h ▸ q6x)
       have ql4:d'≠ zp:=hd'.elim (fun h=>h ▸ q6i) (fun h=>h ▸ q8y)
       have qbk:G.Adj c zp:=hc.elim (fun h=>h ▸ hf1.2.2.2.1 c1 hc1) (fun h=>h ▸ hf2.2.2.2.1 c2 hc2)
       have hdz:G.Adj d' z:=hd'.elim (fun h=>h ▸ hf1.2.2.2.2.1 d1 hd1) (fun h=>h ▸ hf2.2.2.2.2.1 d2 hd2)
       exact ql4 (z102 h4 qot qk9 hdz.symm qbk hf1.1)
      rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
      ·exact G.loopless.irrefl _ hab
      ·exact q3y _ _ (Or.inl rfl) (Or.inl rfl) hab
      ·exact q03 _ _ hab (q9y.trans q9z.symm)
      ·exact q3y _ _ (Or.inl rfl) (Or.inr rfl) hab
      ·exact q3y _ _ (Or.inl rfl) (Or.inl rfl) hab.symm
      ·exact G.loopless.irrefl _ hab
      ·exact q3y _ _ (Or.inr rfl) (Or.inl rfl) hab.symm
      ·exact q03 _ _ hab (qa0.trans qa1.symm)
      ·exact q03 _ _ hab (q9z.trans q9y.symm)
      ·exact q3y _ _ (Or.inr rfl) (Or.inl rfl) hab
      ·exact G.loopless.irrefl _ hab
      ·exact q3y _ _ (Or.inr rfl) (Or.inr rfl) hab
      ·exact q3y _ _ (Or.inl rfl) (Or.inr rfl) hab.symm
      ·exact q03 _ _ hab (qa1.trans qa0.symm)
      ·exact q3y _ _ (Or.inr rfl) (Or.inr rfl) hab.symm
      ·exact G.loopless.irrefl _ hab
     have hnw:
       (gateVal n C g1 (pairInput z d)=true→
        (¬ ∀ x,gateVal n C g1 x=true→ x d=true→ graphFun G ∅ x=true)∧
        (∀ w:Fin n,s w=s z→ (∀ x,gateVal n C g1 x=true→ x w=true→ graphFun G ∅ x=true)→ G.Adj w d))∧
       (gateVal n C g2 (pairInput z d)=true→
        (¬ ∀ x,gateVal n C g2 x=true→ x d=true→ graphFun G ∅ x=true)∧
        (∀ w:Fin n,s w=s z→ (∀ x,gateVal n C g2 x=true→ x w=true→ graphFun G ∅ x=true)→ G.Adj w d)):=by
      constructor
      ·intro h1
       have hd1:d∈ D1:=by
        rw [hf1.2.2.2.2.2.2.2,Z12,Z1,Z1] at h1
        rcases h1.2 with ⟨d',hd',q3x⟩
        simp only [pairInput,Z1] at q3x
        rcases q3x with rfl | rfl
        ·exact absurd (z047 q03 hf1 hd') (q03 _ zp hf1.1)
        ·exact hd'
       exact ⟨z056 h4 hf1 hd1 q1e,
        fun w hsw hw=>z054 q03 h4 hf1 hw hsw hd1 q1e⟩
      ·intro h2
       have hd2:d∈ D2:=by
        rw [hf2.2.2.2.2.2.2.2,Z12,Z1,Z1] at h2
        rcases h2.2 with ⟨d',hd',q3x⟩
        simp only [pairInput,Z1] at q3x
        rcases q3x with rfl | rfl
        ·exact absurd (z047 q03 hf2 hd') (q03 _ zp hf2.1)
        ·exact hd'
       exact ⟨z056 h4 hf2 hd2 q1e,
        fun w hsw hw=>z054 q03 h4 hf2 hw hsw hd2 q1e⟩
     rcases z072 q03 h4 hL q01 q00 hf1 hf2 rfl rfl qbj hnw q4k with
      hA | ⟨a,haC,_⟩ | ⟨qa2,_⟩
     ·exact hA
     ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
     ·exact absurd qa2 (q03 z zp hf1.1)
    have q6j:(Zact \ Zhas).card≤ 1:=by
     have q3e:Zact \ Zhas⊆ {zp}:=by
      intro v hv
      have hv1:=(Z0.mp (Z2.mp hv).1).1
      have hv2:=(Z2.mp hv).2
      simp only [Z6,Z3] at hv1 ⊢
      exact hv1.resolve_left (fun h=>hv2 (h ▸ qhr))
     exact (Finset.card_le_card q3e).trans (by simp)
    omega
   ·have qa3:1≤ (centreless G C).card:=
     Finset.Nonempty.card_pos (Finset.nonempty_iff_ne_empty.mpr q0m)
    omega
  ·
   have q88:MD={zp}:=by
    ext d;simp only [Z3]
    constructor
    ·intro hd;by_contra qay
     exact qmw ⟨d,Finset.mem_erase.mpr ⟨qay,hd⟩⟩
    ·rintro rfl;exact q9w
   let L:Fin n→ Finset (Fin n):=fun v=>if v=zp then MC else ∅
   have hLz:L z=∅:=by simp [L,q39]
   have q5y:L zp=MC:=by simp [L]
   have q8w:∀ e∈ Ustar G C,(∃ u∈ L z,e=s(z,u))∨ (∃ u∈ L zp,e=s(zp,u)):=by
    intro e he
    have heF:=q5n he
    simp only [Z4,z045,Z19] at heF
    rcases heF with (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩) | (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩)
    ·have qbl:d∈ MD:=Z0.mpr ⟨Finset.mem_union_left _ hd,he⟩
     rw [q88,Z3] at qbl;subst qbl
     right;exact ⟨z,by rw [q5y];exact qja,Sym2.eq_swap⟩
    ·right;exact ⟨c,by rw [q5y];exact Z0.mpr ⟨Finset.mem_union_left _ hc,he⟩,Sym2.eq_swap⟩
    ·have qbl:d∈ MD:=Z0.mpr ⟨Finset.mem_union_right _ hd,he⟩
     rw [q88,Z3] at qbl;subst qbl
     right;exact ⟨z,by rw [q5y];exact qja,Sym2.eq_swap⟩
    ·right;exact ⟨c,by rw [q5y];exact Z0.mpr ⟨Finset.mem_union_right _ hc,he⟩,Sym2.eq_swap⟩
   have q55:=run_surgery L
    (fun u hu=>by rw [hLz] at hu;exact absurd hu (Finset.notMem_empty _))
    (fun u hu=>by rw [q5y] at hu;rcases Z4.mp (Z0.mp hu).1 with h | h;exact (hf1.2.2.2.1 u h).symm;exact (hf2.2.2.2.1 u h).symm)
    q8w
   dsimp only at q55
   set Zact:=({z,zp}:Finset (Fin n)).filter (fun v=>(L v).Nonempty)
   set Zhas:=Zact.filter (fun v=>∃ a∈ tops G C \ centreless G C,z126 C s z g1 g2 a=v)
   have q6j:(Zact \ Zhas).card≤ 1:=by
    have q3e:Zact \ Zhas⊆ {zp}:=by
     intro v hv
     have hv1:=Z0.mp (Z2.mp hv).1
     simp only [Z6,Z3] at hv1 ⊢
     rcases hv1.1 with rfl | rfl
     ·rw [hLz] at hv1;exact absurd hv1.2 (by simp)
     ·rfl
    exact (Finset.card_le_card q3e).trans (by simp)
   rw [hLz,q5y,Z20,zero_add] at q55
   have qjb:FacC.card≤ (orN G C \ lam G C).card:=
    Finset.card_le_card (Finset.filter_subset _ _)
   by_cases q0m:centreless G C=∅
   ·obtain ⟨m,q9x,qg4⟩:=z037 hL q01 hne q0y q00 q0m
    have q7g:m∉ FacC:=fun h=>by have:=q5i m h;omega
    have q7h:FacC.card+1≤ (orN G C \ lam G C).card:=by
     have qe9:=Finset.insert_subset q9x (Finset.filter_subset _ _:FacC⊆ orN G C \ lam G C)
     have qhq:=Finset.card_le_card qe9
     rw [Z24 q7g] at qhq;exact qhq
    omega
   ·have qa3:1≤ (centreless G C).card:=
     Finset.Nonempty.card_pos (Finset.nonempty_iff_ne_empty.mpr q0m)
    omega
 ·
  have qht:z∉ MC:=fun h=>he0 (Z0.mp h).2
  have qeb:zp∉ MD:=fun h=>he0 (Z0.mp h).2
  have qho:MC.card≤ FacC.card:=q5l.2.1 qht
  have qcl:MD.card≤ FacD.card:=q7e.2.1 qeb
  have q7f:FacC.card+FacD.card≤ (orN G C \ lam G C).card:=by
   rw [← Finset.card_union_of_disjoint q5j];exact Finset.card_le_card q5m
  have qbm:s(z,zp)∈ starEdges G C:=by
   by_contra hns
   exact he0 (Z2.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hf1.1,hns⟩)
  obtain ⟨a0,qmx,qhu⟩:=z127 hL.1 h4 s z g1 g2 qbm
  let L:Fin n→ Finset (Fin n):=fun v=>if v=z then MD else if v=zp then MC else ∅
  have hLz:L z=MD:=by simp [L]
  have q5y:L zp=MC:=by simp [L,q39.symm]
  have q8w:∀ e∈ Ustar G C,(∃ u∈ L z,e=s(z,u))∨ (∃ u∈ L zp,e=s(zp,u)):=by
   intro e he
   have heF:=q5n he
   simp only [Z4,z045,Z19] at heF
   rcases heF with (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩) | (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩)
   ·left;exact ⟨d,by rw [hLz];exact Z0.mpr ⟨Finset.mem_union_left _ hd,he⟩,rfl⟩
   ·right;exact ⟨c,by rw [q5y];exact Z0.mpr ⟨Finset.mem_union_left _ hc,he⟩,Sym2.eq_swap⟩
   ·left;exact ⟨d,by rw [hLz];exact Z0.mpr ⟨Finset.mem_union_right _ hd,he⟩,rfl⟩
   ·right;exact ⟨c,by rw [q5y];exact Z0.mpr ⟨Finset.mem_union_right _ hc,he⟩,Sym2.eq_swap⟩
  have q55:=run_surgery L
   (fun u hu=>by rw [hLz] at hu;rcases Z4.mp (Z0.mp hu).1 with h | h;exact (hf1.2.2.2.2.1 u h).symm;exact (hf2.2.2.2.2.1 u h).symm)
   (fun u hu=>by rw [q5y] at hu;rcases Z4.mp (Z0.mp hu).1 with h | h;exact (hf1.2.2.2.1 u h).symm;exact (hf2.2.2.2.1 u h).symm)
   q8w
  dsimp only at q55
  set Zact:=({z,zp}:Finset (Fin n)).filter (fun v=>(L v).Nonempty)
  set Zhas:=Zact.filter (fun v=>∃ a∈ tops G C \ centreless G C,z126 C s z g1 g2 a=v)
  have q6j:(Zact \ Zhas).card≤ 1:=by
   rcases qhu with qhv | qec
   ·have q3e:Zact \ Zhas⊆ {zp}:=by
     intro v hv
     have hv1:=(Z0.mp (Z2.mp hv).1).1
     have hv2:=(Z2.mp hv).2
     simp only [Z6,Z3] at hv1 ⊢
     rcases hv1 with rfl | rfl
     ·exact absurd (Z0.mpr ⟨(Z2.mp hv).1,a0,qmx,qhv⟩) hv2
     ·rfl
    exact (Finset.card_le_card q3e).trans (by simp)
   ·have q3e:Zact \ Zhas⊆ {z}:=by
     intro v hv
     have hv1:=(Z0.mp (Z2.mp hv).1).1
     have hv2:=(Z2.mp hv).2
     simp only [Z6,Z3] at hv1 ⊢
     rcases hv1 with rfl | rfl
     ·rfl
     ·exact absurd (Z0.mpr ⟨(Z2.mp hv).1,a0,qmx,qec⟩) hv2
    exact (Finset.card_le_card q3e).trans (by simp)
  rw [hLz,q5y] at q55
  omega
lemma z014 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u≠ s v)
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (hne:∃ u v:Fin n,G.Adj u v)
  {g1 g2:ℕ} (q00:∀ k,k∈ junk G C↔ k=g1∨ k=g2)
  {w:ℕ} (q53:w < n+C.gates.length) (q76:∀ k,w=n+k→ ¬ BelowF G C k)
  {u v:Fin n} (hu:u∈ orIn n C w) (hv:v∈ orIn n C w) (qa2:s u≠ s v)
  (FacAll:Finset ℕ) (qa4:∀ k∈ FacAll,∀ x y,x∈ orIn n C (n+k)→ y∈ orIn n C (n+k)→ s x=s y):
  ∃ m∈ orN G C \ lam G C,m∉ FacAll∧ 2≤ (orIn n C (n+m)).card:=by
 have huv:u≠ v:=fun h=>qa2 (h ▸ rfl)
 let A:Finset (Fin n):={u,v}
 have q2n:∀ k,OrReaches n C w k→ k∈ lam G C ∪ FacAll→ (orIn n C (n+k) ∩ A).card≤ 1:=by
  intro k _ hk
  by_contra hgt;push Not at hgt
  obtain ⟨x,hx,y,hy,hxy⟩:=Finset.one_lt_card.mp hgt
  have hx':=Z5.mp hx
  have hy':=Z5.mp hy
  have qou:s x≠ s y:=by
   simp only [A,Z6,Z3] at hx' hy'
   rcases hx'.2 with rfl | rfl <;> rcases hy'.2 with rfl | rfl
   ·exact absurd rfl hxy
   ·exact qa2
   ·exact qa2.symm
   ·exact absurd rfl hxy
  rcases Z4.mp hk with qa5 | q6y
  ·rcases (Z0.mp qa5).2.2.2 with ⟨a,ha,b,q0t,hr⟩
   obtain ⟨c,hc⟩:=Finset.card_eq_one.mp q0t
   have q0c:=z109 hr
   have hcm:c∈ side (n:=n) C a (1 - b):=by rw [hc];simp
   have hax:G.Adj c x:=by
    fin_cases b
    ·exact (z132 hL.1 ha (q0c hx'.1) hcm).symm
    ·exact z132 hL.1 ha hcm (q0c hx'.1)
   have hay:G.Adj c y:=by
    fin_cases b
    ·exact (z132 hL.1 ha (q0c hy'.1) hcm).symm
    ·exact z132 hL.1 ha hcm (q0c hy'.1)
   have h1:=q03 c x hax
   have h2:=q03 c y hay
   cases sc:s c <;> cases sx:s x <;> cases sy:s y <;> simp_all
  ·exact qou (qa4 k q6y x y hx'.1 hy'.1)
 have hwb:=z136 hL q01 hne q00 q53 q76 A ⟨u,by simp [A]⟩
  (fun x hx=>by simp only [A,Z6,Z3] at hx;rcases hx with rfl | rfl <;> assumption)
  FacAll q2n
 rw [Finset.card_pair huv] at hwb
 have qov:((orN G C \ lam G C).filter (fun k=>
   OrReaches n C w k∧ k∉ FacAll∧ 2≤ (orIn n C (n+k) ∩ A).card)).Nonempty:=
  Finset.card_pos.mp (by omega)
 obtain ⟨m,hm⟩:=qov
 have hmf:=Z0.mp hm
 exact ⟨m,hmf.1,hmf.2.2.1,le_trans hmf.2.2.2 (Finset.card_le_card Finset.inter_subset_left)⟩
lemma z021 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u≠ s v) (h4:NoFourCycle G)
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C)
  {g1 g2:ℕ} (q0y:g1 < g2) (q00:∀ k,k∈ junk G C↔ k=g1∨ k=g2)
  {C1 D1 C2 D2:Finset (Fin n)} {z zp1 zp2:Fin n} (q0h:zp1≠ zp2)
  (hf1:z000 G C g1 C1 D1 z zp1) (hf2:z000 G C g2 C2 D2 z zp2):False:=by
 classical
 have hne:∃ u v:Fin n,G.Adj u v:=⟨z,zp1,hf1.1⟩
 have qdf:g1≠ g2:=Nat.ne_of_lt q0y
 have q5x:=z094.mp ((q00 g1).mpr (Or.inl rfl))
 have q2p:=z094.mp ((q00 g2).mpr (Or.inr rfl))
 have q1l:s zp1=s zp2:=by
  have h1:=q03 z zp1 hf1.1
  have h2:=q03 z zp2 hf2.1
  cases sz:s z <;> cases s1:s zp1 <;> cases s2:s zp2 <;> simp_all
 have q2s:z≠ zp1:=G.ne_of_adj hf1.1
 have q2t:z≠ zp2:=G.ne_of_adj hf2.1
 obtain ⟨⟨qce,qcf,qcg,qch⟩,b1,qci,qb0⟩:=
  z066 q03 hL q01 q0y q00 hf1
 obtain ⟨qcj,qck,b2,q44,q2o,q6h,q3k,q5a,q2a⟩:=
  z067 q03 h4 hL q01 q0y q00 hf1 hf2 rfl q1l
 set w1C:=opnd C g1 b1
 set w1D:=opnd C g1 (1 - b1)
 set w2C:=opnd C g2 b2
 set w2D:=opnd C g2 (1 - b2)
 have q4l:¬ OrReaches n C w1C g1:=by fin_cases b1 <;> assumption
 have q7i:¬ OrReaches n C w1C g2:=by fin_cases b1 <;> assumption
 have q4m:¬ OrReaches n C w1D g1:=by fin_cases b1 <;> assumption
 have q7j:¬ OrReaches n C w1D g2:=by fin_cases b1 <;> assumption
 have q2x:¬ OrReaches n C w2C g1:=fun h=>q0h (q6h h).2.1
 have q7k:¬ OrReaches n C w2C g2:=by fin_cases b2 <;> assumption
 have q7l:¬ OrReaches n C w2D g2:=by fin_cases b2 <;> assumption
 have q4n:orIn n C w2C=C2:=q3k q2x
 set MC1:=C1.filter (fun c=>s(c,zp1)∈ Ustar G C)
 set MC2:=C2.filter (fun c=>s(c,zp2)∈ Ustar G C)
 set MD1:=D1.filter (fun d=>s(z,d)∈ Ustar G C)
 set MD2:=D2.filter (fun d=>s(z,d)∈ Ustar G C)
 set MD:=MD1 ∪ MD2
 set FacC1:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w1C k)
 set FacC2:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w2C k)
 set FacD:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w1D k∨ OrReaches n C w2D k)
 have q2q:∀ a,a∈ junk G C→ ∀ b:Fin 2,∀ m,opnd C a b=n+m→ ¬ BelowF G C m:=by
  intro a ha b m hm hbm
  have ha':=z094.mp ha
  exact z089 hL hne ha'.1 ha'.2.1 b (by rw [hm];exact hbm)
 have q1w:=z125 hL q01 h4 hne q00
  (by have:=z104 hL.1 q5x.1 b1;omega:w1C < n+g2)
  (q2q g1 ((q00 g1).mpr (Or.inl rfl)) b1) q4l
  (show orIn n C w1C=C1 from qci) (fun u hu=>(hf1.2.2.2.1 u hu).symm)
 have q1h:=z125 hL q01 h4 hne q00
  (z104 hL.1 q2p.1 b2)
  (q2q g2 ((q00 g2).mpr (Or.inr rfl)) b2) q2x
  q4n (fun u hu=>(hf2.2.2.2.1 u hu).symm)
 have qa6:C1.filter (fun u=>s(zp1,u)∈ Ustar G C)=MC1:=by ext u;simp [MC1,Sym2.eq_swap]
 have qa7:C2.filter (fun u=>s(zp2,u)∈ Ustar G C)=MC2:=by ext u;simp [MC2,Sym2.eq_swap]
 dsimp only at q1w q1h
 rw [qa6] at q1w
 rw [qa7] at q1h
 have ql5:(MC1.erase z).card≤ FacC1.card:=by
  by_cases hzM:z∈ MC1
  ·rw [Finset.card_erase_of_mem hzM];have h1:MC1.card≤ FacC1.card+1:=q1w.1 ⟨z,hzM⟩;omega
  ·rw [Finset.erase_eq_of_notMem hzM];exact q1w.2 ⟨z,hf1.2.1,hzM⟩
 have ql6:(MC2.erase z).card≤ FacC2.card:=by
  by_cases hzM:z∈ MC2
  ·rw [Finset.card_erase_of_mem hzM];have h2:MC2.card≤ FacC2.card+1:=q1h.1 ⟨z,hzM⟩;omega
  ·rw [Finset.erase_eq_of_notMem hzM];exact q1h.2 ⟨z,hf2.2.1,hzM⟩
 have q0j:∀ k∈ FacC1,k < g2∧ ¬ OrReaches n C (n+k) g1∧ ¬ OrReaches n C (n+k) g2∧
   orIn n C (n+k)⊆ C1∧ 2≤ (orIn n C (n+k)).card:=by
  intro k hk
  have hkf:=Z0.mp hk
  have hle:=z113 hkf.2
  have hlt:=z104 hL.1 q5x.1 b1
  have hn1:¬ OrReaches n C (n+k) g1:=fun h=>q4l (z116 hkf.2 h)
  have hn2:¬ OrReaches n C (n+k) g2:=fun h=>q7i (z116 hkf.2 h)
  have q0c:orIn n C (n+k)⊆ C1:=by
   have:=z109 hkf.2;rwa [show orIn n C w1C=C1 from qci] at this
  exact ⟨by omega,hn1,hn2,q0c,
   z123 hL q01 hne q00 (Z2.mp hkf.1).1 hn1 hn2⟩
 have q0k:∀ k∈ FacC2,k < g2∧ ¬ OrReaches n C (n+k) g1∧ ¬ OrReaches n C (n+k) g2∧
   orIn n C (n+k)⊆ C2∧ 2≤ (orIn n C (n+k)).card:=by
  intro k hk
  have hkf:=Z0.mp hk
  have hle:=z113 hkf.2
  have hlt:=z104 hL.1 q2p.1 b2
  have hn1:¬ OrReaches n C (n+k) g1:=fun h=>q2x (z116 hkf.2 h)
  have hn2:¬ OrReaches n C (n+k) g2:=fun h=>q7k (z116 hkf.2 h)
  have q0c:orIn n C (n+k)⊆ C2:=by
   have:=z109 hkf.2;rwa [q4n] at this
  exact ⟨by omega,hn1,hn2,q0c,
   z123 hL q01 hne q00 (Z2.mp hkf.1).1 hn1 hn2⟩
 have q1g:∀ k∈ FacD,k < g2∧ orIn n C (n+k)⊆ D1 ∪ D2:=by
  intro k hk
  rcases (Z0.mp hk).2 with h1 | h2
  ·have:=z113 h1;have:=z104 hL.1 q5x.1 (1 - b1)
   have q0c:=z109 h1
   rw [show orIn n C w1D=D1 from qb0] at q0c
   exact ⟨by omega,Finset.Subset.trans q0c Finset.subset_union_left⟩
  ·have:=z113 h2;have:=z104 hL.1 q2p.1 (1 - b2)
   exact ⟨by omega,Finset.Subset.trans (z109 h2) (Finset.Subset.trans q2o Finset.subset_union_right)⟩
 have qa8:Disjoint FacC1 FacC2:=by
  rw [Finset.disjoint_left];intro k hk1 hk2
  have h1:=q0j k hk1
  have h2:=q0k k hk2
  obtain ⟨u1,hu1,u2,hu2,qd2⟩:=Finset.one_lt_card.mp (by omega:1 < (orIn n C (n+k)).card)
  exact q0h (z102 h4 qd2
   (hf1.2.2.2.1 u1 (h1.2.2.2.1 hu1)) (hf1.2.2.2.1 u2 (h1.2.2.2.1 hu2))
   (hf2.2.2.2.1 u1 (h2.2.2.2.1 hu1)) (hf2.2.2.2.1 u2 (h2.2.2.2.1 hu2)))
 have qbn:Disjoint FacC1 FacD:=by
  rw [Finset.disjoint_left];intro k hk1 hkD
  have h1:=q0j k hk1
  have hD:=q1g k hkD
  obtain ⟨u,hu⟩:=Finset.card_pos.mp (by omega:0 < (orIn n C (n+k)).card)
  have hsc:=z046 q03 hf1 (h1.2.2.2.1 hu)
  have hsd:s u=s zp1:=by
   rcases Z4.mp (hD.2 hu) with h | h
   ·exact z047 q03 hf1 h
   ·exact (z047 q03 hf2 h).trans q1l.symm
  exact q03 z zp1 hf1.1 (hsc.symm.trans hsd)
 have qbo:Disjoint FacC2 FacD:=by
  rw [Finset.disjoint_left];intro k hk2 hkD
  have h2:=q0k k hk2
  have hD:=q1g k hkD
  obtain ⟨u,hu⟩:=Finset.card_pos.mp (by omega:0 < (orIn n C (n+k)).card)
  have hsc:=z046 q03 hf2 (h2.2.2.2.1 hu)
  have hsd:s u=s zp1:=by
   rcases Z4.mp (hD.2 hu) with h | h
   ·exact z047 q03 hf1 h
   ·exact (z047 q03 hf2 h).trans q1l.symm
  exact q03 z zp1 hf1.1 (hsc.symm.trans hsd)
 set FacAll:=FacC1 ∪ FacC2 ∪ FacD
 have q07:FacAll⊆ orN G C \ lam G C:=
  Finset.union_subset (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
   (Finset.filter_subset _ _)
 have q13:FacAll.card=FacC1.card+FacC2.card+FacD.card:=by
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨qbn,qbo⟩),
   Finset.card_union_of_disjoint qa8]
 have q0b:∀ k∈ FacAll,k < g2:=by
  intro k hk;simp only [FacAll,Z4] at hk
  rcases hk with (h | h) | h
  ·exact (q0j k h).1
  ·exact (q0k k h).1
  ·exact (q1g k h).1
 have q2b:∀ k∈ FacAll,∀ x y,x∈ orIn n C (n+k)→ y∈ orIn n C (n+k)→ s x=s y:=by
  intro k hk x y hx hy;simp only [FacAll,Z4] at hk
  rcases hk with (h | h) | h
  ·exact (z046 q03 hf1 ((q0j k h).2.2.2.1 hx)).trans
    (z046 q03 hf1 ((q0j k h).2.2.2.1 hy)).symm
  ·exact (z046 q03 hf2 ((q0k k h).2.2.2.1 hx)).trans
    (z046 q03 hf2 ((q0k k h).2.2.2.1 hy)).symm
  ·have hsD:∀ u∈ D1 ∪ D2,s u=s zp1:=fun u hu=>by
    rcases Z4.mp hu with h1 | h2
    ·exact z047 q03 hf1 h1
    ·exact (z047 q03 hf2 h2).trans q1l.symm
   exact (hsD x ((q1g k h).2 hx)).trans (hsD y ((q1g k h).2 hy)).symm
 have q5n:=z135 q03 hL q01 h4 q00 hf1 hf2
 have run_surgery3:∀ L:Fin n→ Finset (Fin n),
   (∀ u∈ L z,G.Adj z u)→ (∀ u∈ L zp1,G.Adj zp1 u)→ (∀ u∈ L zp2,G.Adj zp2 u)→
   (∀ e∈ Ustar G C,(∃ u∈ L z,e=s(z,u))∨ (∃ u∈ L zp1,e=s(zp1,u))∨ (∃ u∈ L zp2,e=s(zp2,u)))→
   let Zact:=({z,zp1,zp2}:Finset (Fin n)).filter (fun v=>(L v).Nonempty)
   let Zhas:=Zact.filter (fun v=>∃ a∈ tops G C \ centreless G C,z126 C s z g1 g2 a=v)
   2 * (centreless G C).card+(orN G C \ lam G C).card+2≤
    (L z).card+(L zp1).card+(L zp2).card+(Zact \ Zhas).card:=by
  intro L hLz hL1 hL2 q8w Zact Zhas
  let topOf:Fin n→ ℕ:=fun v=>
   if h:∃ a∈ tops G C \ centreless G C,z126 C s z g1 g2 a=v then Classical.choose h else 0
  have qhl:=z093 hL q01 h4 qdf q00 hne Zact Zhas L topOf
   (Finset.filter_subset _ _)
   (fun v hv=>(Z0.mp hv).2)
   (fun v hv u hu=>by
    have hv':=(Z0.mp hv).1
    simp only [Z6,Z3] at hv'
    rcases hv' with rfl | rfl | rfl
    ·exact hLz u hu
    ·exact hL1 u hu
    ·exact hL2 u hu)
   (fun e he=>by
    rcases q8w e he with ⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩
    ·exact ⟨z,Z0.mpr ⟨by simp,⟨u,hu⟩⟩,u,hu,rfl⟩
    ·exact ⟨zp1,Z0.mpr ⟨by simp,⟨u,hu⟩⟩,u,hu,rfl⟩
    ·exact ⟨zp2,Z0.mpr ⟨by simp,⟨u,hu⟩⟩,u,hu,rfl⟩)
   (fun v hv=>by
    have h:=(Z0.mp hv).2
    simp only [topOf,dif_pos h];exact (Classical.choose_spec h).1)
   (fun v hv=>by
    have h:=(Z0.mp hv).2
    simp only [topOf,dif_pos h]
    have hsp:=Classical.choose_spec h
    have q3f:=z128 hL.1 h4 s z g1 g2 hsp.1
    rwa [hsp.2] at q3f)
   (fun v1 hv1 v2 hv2 heq=>by
    have h1:=(Z0.mp hv1).2
    have h2:=(Z0.mp hv2).2
    simp only [topOf,dif_pos h1,dif_pos h2] at heq
    have qhm:=Classical.choose_spec h1
    have qhn:=Classical.choose_spec h2
    rw [← qhm.2,heq,qhn.2])
  have qe8:∑ v∈ Zact,(L v).card≤ (L z).card+(L zp1).card+(L zp2).card:=by
   calc ∑ v∈ Zact,(L v).card≤ ∑ v∈ ({z,zp1,zp2}:Finset (Fin n)),(L v).card:=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _=(L z).card+(L zp1).card+(L zp2).card:=by
      rw [Finset.sum_insert (by simp [q2s,q2t]),Finset.sum_pair q0h];omega
  omega
 have q0l:∀ c1∈ MC1.erase z,
   (∃ a∈ tops G C \ centreless G C,z126 C s z g1 g2 a=zp1)∨
   (∃ a∈ centreless G C,∃ b:Fin 2,side (n:=n) C a b=∅∧ OrReaches n C (opnd C a b) g1∧ zp1∈ side (n:=n) C a (1 - b))∨
   (∃ mv∈ orN G C \ lam G C,g2 < mv∧ orIn n C (n+mv)={zp1}∧
    ∃ u':Fin n,s u'=s z∧ ∃ mu∈ orN G C \ lam G C,OrReaches n C (n+mu) g1∧ orIn n C (n+mu)={u'}):=by
  intro c1 hc1
  have q87:c1≠ z:=(Finset.mem_erase.mp hc1).1
  have q45:=Z0.mp (Finset.mem_of_mem_erase hc1)
  have hU:s(zp1,c1)∈ Ustar G C:=by rw [Sym2.eq_swap];exact q45.2
  have hG:G.Adj zp1 c1:=(hf1.2.2.2.1 c1 q45.1).symm
  have q3a:gateVal n C g2 (pairInput zp1 c1)=false:=by
   rw [Z14,ne_eq,z052 q03 h4 hf2 hG]
   simp only [z045,Z4,Z19,Sym2.eq_iff]
   rintro (⟨d,_,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ | ⟨c,hc,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩)
   ·exact q2s rfl
   ·exact q87 rfl
   ·exact absurd (z046 q03 hf2 hc).symm (q03 z _ hf1.1)
   ·exact q0h rfl
  have hnw:
    (gateVal n C g1 (pairInput zp1 c1)=true→
     (¬ ∀ x,gateVal n C g1 x=true→ x c1=true→ graphFun G ∅ x=true)∧
     (∀ w:Fin n,s w=s zp1→ (∀ x,gateVal n C g1 x=true→ x w=true→ graphFun G ∅ x=true)→ G.Adj w c1))∧
    (gateVal n C g2 (pairInput zp1 c1)=true→
     (¬ ∀ x,gateVal n C g2 x=true→ x c1=true→ graphFun G ∅ x=true)∧
     (∀ w:Fin n,s w=s zp1→ (∀ x,gateVal n C g2 x=true→ x w=true→ graphFun G ∅ x=true)→ G.Adj w c1)):=
   ⟨fun _=>⟨z055 h4 hf1 q45.1 q87,
    fun w hsw hw=>z053 q03 h4 hf1 hw hsw q45.1 q87⟩,
   fun h2=>by rw [q3a] at h2;cases h2⟩
  rcases z072 q03 h4 hL q01 q00 hf1 hf2 rfl q1l hU hnw
    (fun h=>by rw [q3a] at h;cases h.2.1) with
   hA | ⟨a,haC,b,g,hg,hgv,q0g,hrb,ql7⟩ | ⟨_,a,haS,b,g,hg,hgv,_,_,g',hg',q7a,_,mv,hmv,q38,q05,u',_,q24,mu,hmu,q3j,q06⟩
  ·exact Or.inl hA
  ·have q56:g=g1:=hg.resolve_right (fun h=>by rw [h,q3a] at hgv;cases hgv)
   subst q56
   exact Or.inr (Or.inl ⟨a,haC,b,q0g,hrb,ql7⟩)
  ·have q56:g=g1:=hg.resolve_right (fun h=>by rw [h,q3a] at hgv;cases hgv)
   rw [q56] at q3j
   have qed:g'=g2:=hg'.resolve_left (by rw [q56] at q7a;exact q7a)
   rw [qed] at q38
   have q1r:g2 < mv:=by
    have hle:=z113 q38
    have qay:mv≠ g2:=fun h=>by
     have h1:=(z096.mp (Z2.mp hmv).1).2.1
     rw [h,q2p.2.1] at h1;cases h1
    omega
   exact Or.inr (Or.inr ⟨mv,hmv,q1r,q05,u',q24,mu,hmu,q3j,q06⟩)
 have q0n:∀ c2∈ MC2.erase z,
   (∃ a∈ tops G C \ centreless G C,z126 C s z g1 g2 a=zp2)∨
   (∃ a∈ centreless G C,∃ b:Fin 2,side (n:=n) C a b=∅∧ OrReaches n C (opnd C a b) g2∧ zp2∈ side (n:=n) C a (1 - b))∨
   (∃ mv∈ orN G C \ lam G C,OrReaches n C (n+mv) g1∧ orIn n C (n+mv)={zp2}∧
    ∃ u':Fin n,s u'=s z∧ ∃ mu∈ orN G C \ lam G C,g2 < mu∧ orIn n C (n+mu)={u'}):=by
  intro c2 hc2
  have q6x:c2≠ z:=(Finset.mem_erase.mp hc2).1
  have q46:=Z0.mp (Finset.mem_of_mem_erase hc2)
  have hU:s(zp2,c2)∈ Ustar G C:=by rw [Sym2.eq_swap];exact q46.2
  have hG:G.Adj zp2 c2:=(hf2.2.2.2.1 c2 q46.1).symm
  have q3b:gateVal n C g1 (pairInput zp2 c2)=false:=by
   rw [Z14,ne_eq,z052 q03 h4 hf1 hG]
   simp only [z045,Z4,Z19,Sym2.eq_iff]
   rintro (⟨d,_,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ | ⟨c,hc,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩)
   ·exact q2t rfl
   ·exact q6x rfl
   ·exact absurd ((z046 q03 hf1 hc).symm.trans q1l.symm) (q03 z zp1 hf1.1)
   ·exact q0h.symm rfl
  have hnw:
    (gateVal n C g1 (pairInput zp2 c2)=true→
     (¬ ∀ x,gateVal n C g1 x=true→ x c2=true→ graphFun G ∅ x=true)∧
     (∀ w:Fin n,s w=s zp2→ (∀ x,gateVal n C g1 x=true→ x w=true→ graphFun G ∅ x=true)→ G.Adj w c2))∧
    (gateVal n C g2 (pairInput zp2 c2)=true→
     (¬ ∀ x,gateVal n C g2 x=true→ x c2=true→ graphFun G ∅ x=true)∧
     (∀ w:Fin n,s w=s zp2→ (∀ x,gateVal n C g2 x=true→ x w=true→ graphFun G ∅ x=true)→ G.Adj w c2)):=
   ⟨fun h1=>(by rw [q3b] at h1;cases h1),
   fun _=>⟨z055 h4 hf2 q46.1 q6x,
    fun w hsw hw=>z053 q03 h4 hf2 hw hsw q46.1 q6x⟩⟩
  rcases z072 q03 h4 hL q01 q00 hf1 hf2 rfl q1l hU hnw
    (fun h=>by rw [q3b] at h;cases h.1) with
   hA | ⟨a,haC,b,g,hg,hgv,q0g,hrb,ql7⟩ | ⟨_,a,haS,b,g,hg,hgv,_,_,g',hg',q7a,_,mv,hmv,q38,q05,u',_,q24,mu,hmu,q3j,q06⟩
  ·exact Or.inl hA
  ·have q56:g=g2:=hg.resolve_left (fun h=>by rw [h,q3b] at hgv;cases hgv)
   subst q56
   exact Or.inr (Or.inl ⟨a,haC,b,q0g,hrb,ql7⟩)
  ·have q56:g=g2:=hg.resolve_left (fun h=>by rw [h,q3b] at hgv;cases hgv)
   rw [q56] at q3j
   have qed:g'=g1:=hg'.resolve_right (by rw [q56] at q7a;exact q7a)
   rw [qed] at q38
   have q2c:g2 < mu:=by
    have hle:=z113 q3j
    have qay:mu≠ g2:=fun h=>by
     have h1:=(z096.mp (Z2.mp hmu).1).2.1
     rw [h,q2p.2.1] at h1;cases h1
    omega
   exact Or.inr (Or.inr ⟨mv,hmv,q38,q05,u',q24,mu,hmu,q2c,q06⟩)
 have q2d:∀ d∈ MD,d≠ zp1→ d≠ zp2→
   (∃ a∈ tops G C \ centreless G C,z126 C s z g1 g2 a=z)∨
   (∃ a∈ centreless G C,∃ b:Fin 2,∃ g:ℕ,(g=g1∨ g=g2)∧
    gateVal n C g (pairInput z d)=true∧
    side (n:=n) C a b=∅∧ OrReaches n C (opnd C a b) g∧ z∈ side (n:=n) C a (1 - b)):=by
  intro d hd qee qef
  have qbj:s(z,d)∈ Ustar G C:=by
   rcases Z4.mp hd with h1 | h2
   ·exact (Z0.mp h1).2
   ·exact (Z0.mp h2).2
  have q4k:¬ (gateVal n C g1 (pairInput z d)=true∧ gateVal n C g2 (pairInput z d)=true∧
    ∀ x,gateVal n C g1 x=true→ gateVal n C g2 x=true→ graphFun G ∅ x=true):=by
   rintro ⟨qmy,qmz,qaz⟩
   have hd1:d∈ D1:=by
    rw [hf1.2.2.2.2.2.2.2,Z12,Z1,Z1] at qmy
    rcases qmy.2 with ⟨d',hd',q3x⟩
    simp only [pairInput,Z1] at q3x
    rcases q3x with rfl | rfl
    ·exact absurd (z047 q03 hf1 hd') (q03 _ zp1 hf1.1)
    ·exact hd'
   have hd2:d∈ D2:=by
    rw [hf2.2.2.2.2.2.2.2,Z12,Z1,Z1] at qmz
    rcases qmz.2 with ⟨d',hd',q3x⟩
    simp only [pairInput,Z1] at q3x
    rcases q3x with rfl | rfl
    ·exact absurd (z047 q03 hf2 hd') (q03 _ zp2 hf2.1)
    ·exact hd'
   obtain ⟨c1,hc1,q87⟩:=z049 hf1
   obtain ⟨c2,hc2,q6x⟩:=z049 hf2
   let x:Fin n→ Bool:=fun w=>decide (w=c1∨ w=c2∨ w=d)
   have q1o:gateVal n C g1 x=true:=by
    rw [hf1.2.2.2.2.2.2.2,Z12,Z1,Z1]
    exact ⟨⟨c1,hc1,by simp [x]⟩,⟨d,hd1,by simp [x]⟩⟩
   have ql3:gateVal n C g2 x=true:=by
    rw [hf2.2.2.2.2.2.2.2,Z12,Z1,Z1]
    exact ⟨⟨c2,hc2,by simp [x]⟩,⟨d,hd2,by simp [x]⟩⟩
   have hFx:=(z073 x).mp (qaz x q1o ql3)
   rcases hFx with ⟨a,b,hab,ha,hb⟩
   simp only [x,Z1] at ha hb
   have qn0:=z046 q03 hf1 hc1
   have qn1:=z046 q03 hf2 hc2
   have qhw:=z051 h4 hf1 hc1 q87 hd1 qee
   have qhx:=z051 h4 hf2 hc2 q6x hd2 qef
   rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
   ·exact G.loopless.irrefl _ hab
   ·exact q03 _ _ hab (qn0.trans qn1.symm)
   ·exact qhw hab
   ·exact q03 _ _ hab (qn1.trans qn0.symm)
   ·exact G.loopless.irrefl _ hab
   ·exact qhx hab
   ·exact qhw hab.symm
   ·exact qhx hab.symm
   ·exact G.loopless.irrefl _ hab
  have hnw:
    (gateVal n C g1 (pairInput z d)=true→
     (¬ ∀ x,gateVal n C g1 x=true→ x d=true→ graphFun G ∅ x=true)∧
     (∀ w:Fin n,s w=s z→ (∀ x,gateVal n C g1 x=true→ x w=true→ graphFun G ∅ x=true)→ G.Adj w d))∧
    (gateVal n C g2 (pairInput z d)=true→
     (¬ ∀ x,gateVal n C g2 x=true→ x d=true→ graphFun G ∅ x=true)∧
     (∀ w:Fin n,s w=s z→ (∀ x,gateVal n C g2 x=true→ x w=true→ graphFun G ∅ x=true)→ G.Adj w d)):=by
   constructor
   ·intro h1
    have hd1:d∈ D1:=by
     rw [hf1.2.2.2.2.2.2.2,Z12,Z1,Z1] at h1
     rcases h1.2 with ⟨d',hd',q3x⟩
     simp only [pairInput,Z1] at q3x
     rcases q3x with rfl | rfl
     ·exact absurd (z047 q03 hf1 hd') (q03 _ zp1 hf1.1)
     ·exact hd'
    exact ⟨z056 h4 hf1 hd1 qee,
     fun w hsw hw=>z054 q03 h4 hf1 hw hsw hd1 qee⟩
   ·intro h2
    have hd2:d∈ D2:=by
     rw [hf2.2.2.2.2.2.2.2,Z12,Z1,Z1] at h2
     rcases h2.2 with ⟨d',hd',q3x⟩
     simp only [pairInput,Z1] at q3x
     rcases q3x with rfl | rfl
     ·exact absurd (z047 q03 hf2 hd') (q03 _ zp2 hf2.1)
     ·exact hd'
    exact ⟨z056 h4 hf2 hd2 qef,
     fun w hsw hw=>z054 q03 h4 hf2 hw hsw hd2 qef⟩
  rcases z072 q03 h4 hL q01 q00 hf1 hf2 rfl q1l qbj hnw q4k with
   hA | hB | ⟨qa2,_⟩
  ·exact Or.inl hA
  ·exact Or.inr hB
  ·exact absurd qa2 (q03 z zp1 hf1.1)
 have close_slack1:MD.card+(MC1.erase z).card+(MC2.erase z).card≤ FacAll.card+1→ False:=by
  intro qjc
  let L1:Fin n→ Finset (Fin n):=fun v=>
   if v=z then MD else if v=zp1 then MC1.erase z else if v=zp2 then MC2.erase z else ∅
  have q8z:L1 z=MD:=by simp [L1]
  have q5o:L1 zp1=MC1.erase z:=by simp [L1,q2s.symm]
  have q5p:L1 zp2=MC2.erase z:=by simp [L1,q2t.symm,q0h.symm]
  have qeg:∀ e∈ Ustar G C,(∃ u∈ L1 z,e=s(z,u))∨ (∃ u∈ L1 zp1,e=s(zp1,u))∨ (∃ u∈ L1 zp2,e=s(zp2,u)):=by
   intro e he
   have heF:=q5n he
   simp only [Z4,z045,Z19] at heF
   rcases heF with (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩) | (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩)
   ·left;exact ⟨d,by rw [q8z];exact Finset.mem_union_left _ (Z0.mpr ⟨hd,he⟩),rfl⟩
   ·by_cases hcz:c=z
    ·subst hcz;left;exact ⟨zp1,by rw [q8z];exact Finset.mem_union_left _ (Z0.mpr ⟨hf1.2.2.1,he⟩),rfl⟩
    ·right;left;exact ⟨c,by rw [q5o];exact Finset.mem_erase.mpr ⟨hcz,Z0.mpr ⟨hc,he⟩⟩,Sym2.eq_swap⟩
   ·left;exact ⟨d,by rw [q8z];exact Finset.mem_union_right _ (Z0.mpr ⟨hd,he⟩),rfl⟩
   ·by_cases hcz:c=z
    ·subst hcz;left;exact ⟨zp2,by rw [q8z];exact Finset.mem_union_right _ (Z0.mpr ⟨hf2.2.2.1,he⟩),rfl⟩
    ·right;right;exact ⟨c,by rw [q5p];exact Finset.mem_erase.mpr ⟨hcz,Z0.mpr ⟨hc,he⟩⟩,Sym2.eq_swap⟩
  have q6k:=run_surgery3 L1
   (fun u hu=>by rw [q8z] at hu;rcases Z4.mp hu with h | h;exact (hf1.2.2.2.2.1 u (Z0.mp h).1).symm;exact (hf2.2.2.2.2.1 u (Z0.mp h).1).symm)
   (fun u hu=>by rw [q5o] at hu;exact (hf1.2.2.2.1 u (Z0.mp (Finset.mem_of_mem_erase hu)).1).symm)
   (fun u hu=>by rw [q5p] at hu;exact (hf2.2.2.2.1 u (Z0.mp (Finset.mem_of_mem_erase hu)).1).symm)
   qeg
  dsimp only at q6k
  set Zact:=({z,zp1,zp2}:Finset (Fin n)).filter (fun v=>(L1 v).Nonempty)
  set Zhas:=Zact.filter (fun v=>∃ a∈ tops G C \ centreless G C,z126 C s z g1 g2 a=v)
  rw [q8z,q5o,q5p] at q6k
  have q7f:FacAll.card≤ (orN G C \ lam G C).card:=Finset.card_le_card q07
  have qa9:(Zact \ Zhas).card≤ 3:=by
   calc (Zact \ Zhas).card≤ ({z,zp1,zp2}:Finset (Fin n)).card:=
      Finset.card_le_card (Finset.Subset.trans Finset.sdiff_subset (Finset.filter_subset _ _))
    _=3:=by rw [Z24 (by simp [q2s,q2t]),Finset.card_pair q0h]
  by_cases qaa:2≤ (centreless G C).card
  ·omega
  ·by_cases q6l:(centreless G C).card=1
   ·
    by_cases hZ3:(Zact \ Zhas).card≤ 2
    ·omega
    ·have q6m:Zact \ Zhas={z,zp1,zp2}:=by
      apply Finset.eq_of_subset_of_card_le
      ·exact Finset.Subset.trans Finset.sdiff_subset (Finset.filter_subset _ _)
      ·rw [Z24 (by simp [q2s,q2t]),Finset.card_pair q0h];omega
     have q08:zp1∈ Zact \ Zhas:=by rw [q6m];simp
     have q0e:zp2∈ Zact \ Zhas:=by rw [q6m];simp
     obtain ⟨c1,hc1⟩:(MC1.erase z).Nonempty:=by
      have:=(Z0.mp (Z2.mp q08).1).2;rwa [q5o] at this
     obtain ⟨c2,hc2⟩:(MC2.erase z).Nonempty:=by
      have:=(Z0.mp (Z2.mp q0e).1).2;rwa [q5p] at this
     have qhy:∃ m∈ orN G C \ lam G C,g2 < m:=by
      rcases q0l c1 hc1 with hA1 | ⟨a1,qeh,b1',qbp,qjd,q40⟩ | ⟨mv,hmv,q1r,_⟩
      ·exact absurd (Z0.mpr ⟨(Z2.mp q08).1,hA1⟩) (Z2.mp q08).2
      ·rcases q0n c2 hc2 with hA2 | ⟨a2,qhz,b2',qbq,qje,qbr⟩ | ⟨_,_,_,_,_,_,mu,hmu,q2c,_⟩
       ·exact absurd (Z0.mpr ⟨(Z2.mp q0e).1,hA2⟩) (Z2.mp q0e).2
       ·obtain ⟨a0,ha0⟩:=Finset.card_eq_one.mp q6l
        have qei:a1=a0:=Z3.mp (ha0 ▸ qeh)
        have qej:a2=a0:=Z3.mp (ha0 ▸ qhz)
        rw [qei] at qeh qbp qjd q40
        rw [qej] at qbq qje
        have ql8:b1'=b2':=by
         by_contra q2e
         have q51:1 - b1'=b2':=z044 q2e
         rw [q51,qbq] at q40;exact Finset.notMem_empty _ q40
        subst ql8
        have q1x:a0∈ tops G C:=(Z0.mp qeh).1
        have qek:=z098.mp q1x
        obtain ⟨m,hm,qg4,_⟩:=z122 hL q0y q00
         (by have:=z104 hL.1 qek.1 b1';omega) (z130 hL hne q1x b1')
         qbp qjd qje
        exact ⟨m,hm,qg4⟩
       ·exact ⟨mu,hmu,q2c⟩
      ·exact ⟨mv,hmv,q1r⟩
     obtain ⟨m,hm,qg4⟩:=qhy
     have qel:m∉ FacAll:=fun h=>by have:=q0b m h;omega
     have qcm:FacAll.card+1≤ (orN G C \ lam G C).card:=by
      have:=Finset.card_le_card (Finset.insert_subset hm q07)
      rwa [Z24 qel] at this
     omega
   ·
    have q0m:centreless G C=∅:=Finset.card_eq_zero.mp (by omega)
    obtain ⟨m0,hm0,qcn⟩:=z037 hL q01 hne q0y q00 q0m
    have qab:m0∉ FacAll:=fun h=>by have:=q0b m0 h;omega
    have q5q:FacAll.card+1≤ (orN G C \ lam G C).card:=by
     have:=Finset.card_le_card (Finset.insert_subset hm0 q07)
     rwa [Z24 qab] at this
    by_cases q2f:∃ d∈ MD,d≠ zp1∧ d≠ zp2
    ·obtain ⟨d,hd,hd1,hd2⟩:=q2f
     have qac:∃ a∈ tops G C \ centreless G C,z126 C s z g1 g2 a=z:=by
      rcases q2d d hd hd1 hd2 with hA | ⟨a,haC,_⟩
      ·exact hA
      ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
     have q7m:z∉ Zact \ Zhas:=fun h=>
      (Z2.mp h).2 (Z0.mpr ⟨(Z2.mp h).1,qac⟩)
     have q5d:Zact \ Zhas⊆ {zp1,zp2}:=by
      intro v hv
      have hv1:=(Z0.mp (Z2.mp hv).1).1
      simp only [Z6,Z3] at hv1 ⊢
      exact hv1.resolve_left (fun h=>q7m (h ▸ hv))
     have ql9:(Zact \ Zhas).card≤ 2:=(Finset.card_le_card q5d).trans (by rw [Finset.card_pair q0h])
     by_cases qla:(Zact \ Zhas).card≤ 1
     ·omega
     ·have qi0:Zact \ Zhas={zp1,zp2}:=
       Finset.eq_of_subset_of_card_le q5d (by rw [Finset.card_pair q0h];omega)
      have q08:zp1∈ Zact \ Zhas:=by rw [qi0];simp
      have q0e:zp2∈ Zact \ Zhas:=by rw [qi0];simp
      obtain ⟨c1,hc1⟩:(MC1.erase z).Nonempty:=by
       have:=(Z0.mp (Z2.mp q08).1).2;rwa [q5o] at this
      obtain ⟨c2,hc2⟩:(MC2.erase z).Nonempty:=by
       have:=(Z0.mp (Z2.mp q0e).1).2;rwa [q5p] at this
      obtain ⟨m1,hm1,qi1,q1i⟩:∃ m1∈ orN G C \ lam G C,g2 < m1∧ orIn n C (n+m1)={zp1}:=by
       rcases q0l c1 hc1 with hA | ⟨a,haC,_⟩ | ⟨mv,hmv,q1r,q05,_⟩
       ·exact absurd (Z0.mpr ⟨(Z2.mp q08).1,hA⟩) (Z2.mp q08).2
       ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
       ·exact ⟨mv,hmv,q1r,q05⟩
      obtain ⟨m2,hm2,qi2,u',q24,q16⟩:
        ∃ m2∈ orN G C \ lam G C,g2 < m2∧ ∃ u':Fin n,s u'=s z∧ orIn n C (n+m2)={u'}:=by
       rcases q0n c2 hc2 with hA | ⟨a,haC,_⟩ | ⟨_,_,_,_,u',q24,mu,hmu,q2c,q06⟩
       ·exact absurd (Z0.mpr ⟨(Z2.mp q0e).1,hA⟩) (Z2.mp q0e).2
       ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
       ·exact ⟨mu,hmu,q2c,u',q24,q06⟩
      have qem:m1≠ m2:=by
       intro heq;subst heq
       rw [q1i] at q16
       have q7n:zp1=u':=Finset.singleton_injective q16
       exact q03 z zp1 hf1.1 (q24.symm.trans (congrArg s q7n.symm))
      have q0z:Disjoint ({m1,m2}:Finset ℕ) FacAll:=by
       rw [Finset.disjoint_left];intro k hk hkf
       simp only [Z6,Z3] at hk
       have:=q0b k hkf
       rcases hk with rfl | rfl <;> omega
      have q57:{m1,m2} ∪ FacAll⊆ orN G C \ lam G C:=
       Finset.union_subset (Finset.insert_subset hm1 (Finset.singleton_subset_iff.mpr hm2)) q07
      have q2g:=Finset.card_le_card q57
      rw [Finset.card_union_of_disjoint q0z,Finset.card_pair qem] at q2g
      omega
    ·
     push Not at q2f
     let L2:Fin n→ Finset (Fin n):=fun v=>
      if v=zp1 then MC1 else if v=zp2 then MC2 else ∅
     have qlb:L2 z=∅:=by simp [L2,q2s,q2t]
     have q7o:L2 zp1=MC1:=by simp [L2]
     have q7p:L2 zp2=MC2:=by simp [L2,q0h.symm]
     have qlc:∀ e∈ Ustar G C,(∃ u∈ L2 z,e=s(z,u))∨ (∃ u∈ L2 zp1,e=s(zp1,u))∨ (∃ u∈ L2 zp2,e=s(zp2,u)):=by
      intro e he
      have heF:=q5n he
      simp only [Z4,z045,Z19] at heF
      rcases heF with (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩) | (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩)
      ·have qbl:d∈ MD:=Finset.mem_union_left _ (Z0.mpr ⟨hd,he⟩)
       by_cases hd1:d=zp1
       ·subst hd1;right;left;exact ⟨z,by rw [q7o];exact Z0.mpr ⟨hf1.2.1,he⟩,Sym2.eq_swap⟩
       ·have hd2:d=zp2:=q2f d qbl hd1
        subst hd2;right;right;exact ⟨z,by rw [q7p];exact Z0.mpr ⟨hf2.2.1,he⟩,Sym2.eq_swap⟩
      ·right;left;exact ⟨c,by rw [q7o];exact Z0.mpr ⟨hc,he⟩,Sym2.eq_swap⟩
      ·have qbl:d∈ MD:=Finset.mem_union_right _ (Z0.mpr ⟨hd,he⟩)
       by_cases hd1:d=zp1
       ·subst hd1;right;left;exact ⟨z,by rw [q7o];exact Z0.mpr ⟨hf1.2.1,he⟩,Sym2.eq_swap⟩
       ·have hd2:d=zp2:=q2f d qbl hd1
        subst hd2;right;right;exact ⟨z,by rw [q7p];exact Z0.mpr ⟨hf2.2.1,he⟩,Sym2.eq_swap⟩
      ·right;right;exact ⟨c,by rw [q7p];exact Z0.mpr ⟨hc,he⟩,Sym2.eq_swap⟩
     have qco:=run_surgery3 L2
      (fun u hu=>by rw [qlb] at hu;exact absurd hu (Finset.notMem_empty _))
      (fun u hu=>by rw [q7o] at hu;exact (hf1.2.2.2.1 u (Z0.mp hu).1).symm)
      (fun u hu=>by rw [q7p] at hu;exact (hf2.2.2.2.1 u (Z0.mp hu).1).symm)
      qlc
     dsimp only at qco
     set Zact2:=({z,zp1,zp2}:Finset (Fin n)).filter (fun v=>(L2 v).Nonempty)
     set Zhas2:=Zact2.filter (fun v=>∃ a∈ tops G C \ centreless G C,z126 C s z g1 g2 a=v)
     rw [qlb,q7o,q7p,Z20,zero_add] at qco
     have qcp:Zact2 \ Zhas2⊆ {zp1,zp2}:=by
      intro v hv
      have hv1:=Z0.mp (Z2.mp hv).1
      simp only [Z6,Z3] at hv1 ⊢
      rcases hv1.1 with rfl | rfl | rfl
      ·rw [qlb] at hv1;exact absurd hv1.2 (by simp)
      ·exact Or.inl rfl
      ·exact Or.inr rfl
     have qn2:(Zact2 \ Zhas2).card≤ 2:=(Finset.card_le_card qcp).trans (by rw [Finset.card_pair q0h])
     have q7q:MD.card=(if z∈ MC1 then 1 else 0)+(if z∈ MC2 then 1 else 0):=by
      have q88:MD=({zp1,zp2}:Finset (Fin n)).filter (fun d=>s(z,d)∈ Ustar G C):=by
       ext d;constructor
       ·intro hd
        have qn3:s(z,d)∈ Ustar G C:=by
         rcases Z4.mp hd with h | h <;> exact (Z0.mp h).2
        by_cases h1:d=zp1
        ·subst h1;exact Z0.mpr ⟨by simp,qn3⟩
        ·have h2:=q2f d hd h1;subst h2;exact Z0.mpr ⟨by simp,qn3⟩
       ·intro hd;have hdf:=Z0.mp hd
        simp only [Z6,Z3] at hdf
        rcases hdf.1 with rfl | rfl
        ·exact Finset.mem_union_left _ (Z0.mpr ⟨hf1.2.2.1,hdf.2⟩)
        ·exact Finset.mem_union_right _ (Z0.mpr ⟨hf2.2.2.1,hdf.2⟩)
      rw [q88]
      have qi3:z∈ MC1↔ s(z,zp1)∈ Ustar G C:=by
       simp [MC1,hf1.2.1]
      have qi4:z∈ MC2↔ s(z,zp2)∈ Ustar G C:=by
       simp [MC2,hf2.2.1]
      rw [Finset.filter_insert,Finset.filter_singleton]
      by_cases h1:s(z,zp1)∈ Ustar G C <;> by_cases h2:s(z,zp2)∈ Ustar G C <;>
       simp [h1,h2,qi3,qi4,q0h]
     have qld:MC1.card+MC2.card=MD.card+(MC1.erase z).card+(MC2.erase z).card:=by
      rw [q7q]
      by_cases h1:z∈ MC1 <;> by_cases h2:z∈ MC2
      ·rw [Finset.card_erase_of_mem h1,Finset.card_erase_of_mem h2];simp [h1,h2]
       have:=Finset.card_pos.mpr ⟨z,h1⟩;have:=Finset.card_pos.mpr ⟨z,h2⟩;omega
      ·rw [Finset.card_erase_of_mem h1,Finset.erase_eq_of_notMem h2];simp [h1,h2]
       have:=Finset.card_pos.mpr ⟨z,h1⟩;omega
      ·rw [Finset.erase_eq_of_notMem h1,Finset.card_erase_of_mem h2];simp [h1,h2]
       have:=Finset.card_pos.mpr ⟨z,h2⟩;omega
      ·rw [Finset.erase_eq_of_notMem h1,Finset.erase_eq_of_notMem h2];simp [h1,h2]
     by_cases qn4:(Zact2 \ Zhas2).card≤ 1
     ·omega
     ·have qcq:Zact2 \ Zhas2={zp1,zp2}:=
       Finset.eq_of_subset_of_card_le qcp (by rw [Finset.card_pair q0h];omega)
      have q08:zp1∈ Zact2 \ Zhas2:=by rw [qcq];simp
      have q0e:zp2∈ Zact2 \ Zhas2:=by rw [qcq];simp
      by_cases q62:(MC1.erase z).Nonempty
      ·by_cases qi5:(MC2.erase z).Nonempty
       ·obtain ⟨c1,hc1⟩:=q62
        obtain ⟨c2,hc2⟩:=qi5
        obtain ⟨m1,hm1,qi1,q1i⟩:∃ m1∈ orN G C \ lam G C,g2 < m1∧ orIn n C (n+m1)={zp1}:=by
         rcases q0l c1 hc1 with hA | ⟨a,haC,_⟩ | ⟨mv,hmv,q1r,q05,_⟩
         ·exact absurd (Z0.mpr ⟨(Z2.mp q08).1,hA⟩) (Z2.mp q08).2
         ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
         ·exact ⟨mv,hmv,q1r,q05⟩
        obtain ⟨m2,hm2,qi2,u',q24,q16⟩:
          ∃ m2∈ orN G C \ lam G C,g2 < m2∧ ∃ u':Fin n,s u'=s z∧ orIn n C (n+m2)={u'}:=by
         rcases q0n c2 hc2 with hA | ⟨a,haC,_⟩ | ⟨_,_,_,_,u',q24,mu,hmu,q2c,q06⟩
         ·exact absurd (Z0.mpr ⟨(Z2.mp q0e).1,hA⟩) (Z2.mp q0e).2
         ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
         ·exact ⟨mu,hmu,q2c,u',q24,q06⟩
        have qem:m1≠ m2:=by
         intro heq;subst heq
         rw [q1i] at q16
         have q7n:zp1=u':=Finset.singleton_injective q16
         exact q03 z zp1 hf1.1 (q24.symm.trans (congrArg s q7n.symm))
        have q0z:Disjoint ({m1,m2}:Finset ℕ) FacAll:=by
         rw [Finset.disjoint_left];intro k hk hkf
         simp only [Z6,Z3] at hk
         have:=q0b k hkf
         rcases hk with rfl | rfl <;> omega
        have q57:{m1,m2} ∪ FacAll⊆ orN G C \ lam G C:=
         Finset.union_subset (Finset.insert_subset hm1 (Finset.singleton_subset_iff.mpr hm2)) q07
        have q2g:=Finset.card_le_card q57
        rw [Finset.card_union_of_disjoint q0z,Finset.card_pair qem] at q2g
        omega
       ·
        have q3l:MC2.Nonempty:=by
         have:=(Z0.mp (Z2.mp q0e).1).2;rwa [q7p] at this
        obtain ⟨c2,hc2,q6x⟩:=z049 hf2
        have qad:c2∉ MC2:=fun h=>qi5 ⟨c2,Finset.mem_erase.mpr ⟨q6x,h⟩⟩
        have qae:MC2.card≤ FacC2.card:=q1h.2 ⟨c2,hc2,qad⟩
        have qen:MC1.card≤ FacC1.card+1:=q1w.1 (by
         have:=(Z0.mp (Z2.mp q08).1).2;rwa [q7o] at this)
        obtain ⟨c1,hc1⟩:=q62
        obtain ⟨mv,hmv,q1r,q05,u',q24,mu,hmu,qcr,q06⟩:
          ∃ mv∈ orN G C \ lam G C,g2 < mv∧ orIn n C (n+mv)={zp1}∧
           ∃ u':Fin n,s u'=s z∧ ∃ mu∈ orN G C \ lam G C,OrReaches n C (n+mu) g1∧ orIn n C (n+mu)={u'}:=by
         rcases q0l c1 hc1 with hA | ⟨a,haC,_⟩ | hC
         ·exact absurd (Z0.mpr ⟨(Z2.mp q08).1,hA⟩) (Z2.mp q08).2
         ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
         ·exact hC
        have qaf:mv≠ mu:=by
         intro heq;subst heq;rw [q05] at q06
         exact q03 z zp1 hf1.1 (q24.symm.trans (congrArg s (Finset.singleton_injective q06).symm))
        have qi6:mv∉ FacAll:=fun h=>by have:=q0b mv h;omega
        have q89:mu∉ FacAll:=by
         intro h;simp only [FacAll,Z4] at h
         rcases h with (h1 | h2) | hD
         ·exact (q0j mu h1).2.1 qcr
         ·exact (q0k mu h2).2.1 qcr
         ·have qle:u'∈ D1 ∪ D2:=(q1g mu hD).2 (by rw [q06];simp)
          rcases Z4.mp qle with h1 | h2
          ·exact q03 z zp1 hf1.1 (q24.symm.trans (z047 q03 hf1 h1))
          ·exact q03 z zp2 hf2.1 (q24.symm.trans (z047 q03 hf2 h2))
        have q0z:Disjoint ({mv,mu}:Finset ℕ) FacAll:=by
         rw [Finset.disjoint_left];intro k hk hkf
         simp only [Z6,Z3] at hk
         rcases hk with rfl | rfl
         ·exact qi6 hkf
         ·exact q89 hkf
        have q2g:FacAll.card+2≤ (orN G C \ lam G C).card:=by
         have q57:{mv,mu} ∪ FacAll⊆ orN G C \ lam G C:=
          Finset.union_subset (Finset.insert_subset hmv (Finset.singleton_subset_iff.mpr hmu)) q07
         have:=Finset.card_le_card q57
         rw [Finset.card_union_of_disjoint q0z,Finset.card_pair qaf] at this
         omega
        omega
      ·
       have qlf:MC1.Nonempty:=by
        have:=(Z0.mp (Z2.mp q08).1).2;rwa [q7o] at this
       obtain ⟨c1,hc1,q87⟩:=z049 hf1
       have qi7:c1∉ MC1:=fun h=>q62 ⟨c1,Finset.mem_erase.mpr ⟨q87,h⟩⟩
       have qen:MC1.card≤ FacC1.card:=q1w.2 ⟨c1,hc1,qi7⟩
       by_cases qi5:(MC2.erase z).Nonempty
       ·have qae:MC2.card≤ FacC2.card+1:=q1h.1 (by
         have:=(Z0.mp (Z2.mp q0e).1).2;rwa [q7p] at this)
        obtain ⟨c2,hc2⟩:=qi5
        obtain ⟨mv,hmv,qcs,q05,u',q24,mu,hmu,q2c,q06⟩:
          ∃ mv∈ orN G C \ lam G C,OrReaches n C (n+mv) g1∧ orIn n C (n+mv)={zp2}∧
           ∃ u':Fin n,s u'=s z∧ ∃ mu∈ orN G C \ lam G C,g2 < mu∧ orIn n C (n+mu)={u'}:=by
         rcases q0n c2 hc2 with hA | ⟨a,haC,_⟩ | hC
         ·exact absurd (Z0.mpr ⟨(Z2.mp q0e).1,hA⟩) (Z2.mp q0e).2
         ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
         ·exact hC
        have q89:mu∉ FacAll:=fun h=>by have:=q0b mu h;omega
        have qaf:mv≠ mu:=by
         intro heq;subst heq;rw [q05] at q06
         exact q03 z zp2 hf2.1 (q24.symm.trans (congrArg s (Finset.singleton_injective q06).symm))
        have qjf:FacC1.card+FacC2.card+2≤ (orN G C \ lam G C).card:=by
         by_cases qeo:mv∈ FacAll
         ·have qlg:mv∈ FacD:=by
           simp only [FacAll,Z4] at qeo
           rcases qeo with (h1 | h2) | hD
           ·exact absurd qcs (q0j mv h1).2.1
           ·exact absurd qcs (q0k mv h2).2.1
           ·exact hD
          have qow:1≤ FacD.card:=Finset.card_pos.mpr ⟨mv,qlg⟩
          have qcm:FacAll.card+1≤ (orN G C \ lam G C).card:=by
           have:=Finset.card_le_card (Finset.insert_subset hmu q07)
           rwa [Z24 q89] at this
          rw [q13] at qcm;omega
         ·have q0z:Disjoint ({mv,mu}:Finset ℕ) FacAll:=by
           rw [Finset.disjoint_left];intro k hk hkf
           simp only [Z6,Z3] at hk
           rcases hk with rfl | rfl
           ·exact qeo hkf
           ·exact q89 hkf
          have q57:{mv,mu} ∪ FacAll⊆ orN G C \ lam G C:=
           Finset.union_subset (Finset.insert_subset hmv (Finset.singleton_subset_iff.mpr hmu)) q07
          have:=Finset.card_le_card q57
          rw [Finset.card_union_of_disjoint q0z,Finset.card_pair qaf,q13] at this
          omega
        omega
       ·obtain ⟨c2,hc2,q6x⟩:=z049 hf2
        have qad:c2∉ MC2:=fun h=>qi5 ⟨c2,Finset.mem_erase.mpr ⟨q6x,h⟩⟩
        have qae:MC2.card≤ FacC2.card:=q1h.2 ⟨c2,hc2,qad⟩
        omega
 by_cases qag:(D1 ∩ D2).Nonempty
 ·obtain ⟨d0,hd0⟩:=qag
  have qlh:=(Z5.mp hd0).1
  have qli:=(Z5.mp hd0).2
  have q5k:D1 ∪ D2=D1 ∪ orIn n C w2D:=by
   by_cases hr:OrReaches n C w2D g1
   ·have h:=q5a hr;rw [Finset.union_eq_right.mpr h.1,h.2.2];rfl
   ·rw [show orIn n C w2D=D2 from q2a hr]
  have qep:d0∈ orIn n C w2D∨ OrReaches n C w2D g1:=by
   by_cases hr:OrReaches n C w2D g1
   ·exact Or.inr hr
   ·left;rw [show orIn n C w2D=D2 from q2a hr];exact qli
  have qeq:=z099 hL q01 h4 hne q00
   (by have:=z104 hL.1 q5x.1 (1 - b1);omega:w1D < n+g2)
   (z104 hL.1 q2p.1 (1 - b2))
   (q2q g1 ((q00 g1).mpr (Or.inl rfl)) (1 - b1))
   (q2q g2 ((q00 g2).mpr (Or.inr rfl)) (1 - b2))
   (show orIn n C w1D=D1 from qb0) q2o q5k
   (fun u hu=>by rcases Z4.mp hu with h | h;exact (hf1.2.2.2.2.1 u h).symm;exact (hf2.2.2.2.2.1 u h).symm)
   qlh qep
  have q7r:(D1 ∪ D2).filter (fun u=>s(z,u)∈ Ustar G C)=MD:=by
   ext u;simp [MD,MD1,MD2,Finset.filter_union]
  dsimp only at qeq
  rw [q7r] at qeq
  have qcl:MD.card≤ FacD.card+1:=by
   by_cases qct:MD.Nonempty
   ·exact qeq.1 qct
   ·rw [Z25.mp qct];simp
  exact close_slack1 (by rw [q13];omega)
 ·
  have q4o:Disjoint D1 D2:=Finset.disjoint_iff_inter_eq_empty.mpr (Z25.mp qag)
  have q2y:¬ OrReaches n C w2D g1:=fun hr=>
   Finset.disjoint_left.mp q4o hf1.2.2.1 ((q5a hr).1 hf1.2.2.1)
  have q4p:orIn n C w2D=D2:=q2a q2y
  set FacD1:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w1D k)
  set FacD2:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w2D k)
  have q8a:FacD=FacD1 ∪ FacD2:=by ext k;simp [FacD,FacD1,FacD2,and_or_left]
  have q1y:∀ k∈ FacD1,¬ OrReaches n C (n+k) g1∧ ¬ OrReaches n C (n+k) g2∧
    orIn n C (n+k)⊆ D1∧ 2≤ (orIn n C (n+k)).card:=by
   intro k hk
   have hkf:=Z0.mp hk
   have hn1:¬ OrReaches n C (n+k) g1:=fun h=>q4m (z116 hkf.2 h)
   have hn2:¬ OrReaches n C (n+k) g2:=fun h=>q7j (z116 hkf.2 h)
   have q0c:orIn n C (n+k)⊆ D1:=by
    have:=z109 hkf.2;rwa [show orIn n C w1D=D1 from qb0] at this
   exact ⟨hn1,hn2,q0c,z123 hL q01 hne q00 (Z2.mp hkf.1).1 hn1 hn2⟩
  have q2z:∀ k∈ FacD2,¬ OrReaches n C (n+k) g1∧ ¬ OrReaches n C (n+k) g2∧
    orIn n C (n+k)⊆ D2∧ 2≤ (orIn n C (n+k)).card:=by
   intro k hk
   have hkf:=Z0.mp hk
   have hn1:¬ OrReaches n C (n+k) g1:=fun h=>q2y (z116 hkf.2 h)
   have hn2:¬ OrReaches n C (n+k) g2:=fun h=>q7l (z116 hkf.2 h)
   have q0c:orIn n C (n+k)⊆ D2:=by
    have:=z109 hkf.2;rwa [q4p] at this
   exact ⟨hn1,hn2,q0c,z123 hL q01 hne q00 (Z2.mp hkf.1).1 hn1 hn2⟩
  have qah:Disjoint FacD1 FacD2:=by
   rw [Finset.disjoint_left];intro k hk1 hk2
   obtain ⟨u,hu⟩:=Finset.card_pos.mp (by have:=(q1y k hk1).2.2.2;omega:0 < (orIn n C (n+k)).card)
   exact Finset.disjoint_left.mp q4o ((q1y k hk1).2.2.1 hu) ((q2z k hk2).2.2.1 hu)
  have q90:FacD.card=FacD1.card+FacD2.card:=by
   rw [q8a,Finset.card_union_of_disjoint qah]
  have q14:∀ k∈ FacAll,¬ OrReaches n C (n+k) g1∧ ¬ OrReaches n C (n+k) g2:=by
   intro k hk;simp only [FacAll,q8a,Z4] at hk
   rcases hk with (h | h) | (h | h)
   ·exact ⟨(q0j k h).2.1,(q0j k h).2.2.1⟩
   ·exact ⟨(q0k k h).2.1,(q0k k h).2.2.1⟩
   ·exact ⟨(q1y k h).1,(q1y k h).2.1⟩
   ·exact ⟨(q2z k h).1,(q2z k h).2.1⟩
  have q47:=z125 hL q01 h4 hne q00
   (by have:=z104 hL.1 q5x.1 (1 - b1);omega:w1D < n+g2)
   (q2q g1 ((q00 g1).mpr (Or.inl rfl)) (1 - b1)) q4m
   (show orIn n C w1D=D1 from qb0) (fun u hu=>(hf1.2.2.2.2.1 u hu).symm)
  have q48:=z125 hL q01 h4 hne q00
   (z104 hL.1 q2p.1 (1 - b2))
   (q2q g2 ((q00 g2).mpr (Or.inr rfl)) (1 - b2)) q2y
   q4p (fun u hu=>(hf2.2.2.2.2.1 u hu).symm)
  have qbs:MD.card=MD1.card+MD2.card:=
   Finset.card_union_of_disjoint (Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) q4o)
  dsimp only at q47 q48
  by_cases qcu:MC1=C1∧ MC2=C2∧ MD1=D1∧ MD2=D2
  ·
   obtain ⟨q5r,qer,q3m,q3n⟩:=qcu
   have qes:MD1.card≤ FacD1.card+1:=q47.1 ⟨zp1,by change zp1∈ MD1;rw [q3m];exact hf1.2.2.1⟩
   have qet:MD2.card≤ FacD2.card+1:=q48.1 ⟨zp2,by change zp2∈ MD2;rw [q3n];exact hf2.2.2.1⟩
   let L1:Fin n→ Finset (Fin n):=fun v=>
    if v=z then MD else if v=zp1 then MC1.erase z else if v=zp2 then MC2.erase z else ∅
   have q8z:L1 z=MD:=by simp [L1]
   have q5o:L1 zp1=MC1.erase z:=by simp [L1,q2s.symm]
   have q5p:L1 zp2=MC2.erase z:=by simp [L1,q2t.symm,q0h.symm]
   have qeg:∀ e∈ Ustar G C,(∃ u∈ L1 z,e=s(z,u))∨ (∃ u∈ L1 zp1,e=s(zp1,u))∨ (∃ u∈ L1 zp2,e=s(zp2,u)):=by
    intro e he
    have heF:=q5n he
    simp only [Z4,z045,Z19] at heF
    rcases heF with (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩) | (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩)
    ·left;exact ⟨d,by rw [q8z];exact Finset.mem_union_left _ (Z0.mpr ⟨hd,he⟩),rfl⟩
    ·by_cases hcz:c=z
     ·subst hcz;left;exact ⟨zp1,by rw [q8z];exact Finset.mem_union_left _ (Z0.mpr ⟨hf1.2.2.1,he⟩),rfl⟩
     ·right;left;exact ⟨c,by rw [q5o];exact Finset.mem_erase.mpr ⟨hcz,Z0.mpr ⟨hc,he⟩⟩,Sym2.eq_swap⟩
    ·left;exact ⟨d,by rw [q8z];exact Finset.mem_union_right _ (Z0.mpr ⟨hd,he⟩),rfl⟩
    ·by_cases hcz:c=z
     ·subst hcz;left;exact ⟨zp2,by rw [q8z];exact Finset.mem_union_right _ (Z0.mpr ⟨hf2.2.2.1,he⟩),rfl⟩
     ·right;right;exact ⟨c,by rw [q5p];exact Finset.mem_erase.mpr ⟨hcz,Z0.mpr ⟨hc,he⟩⟩,Sym2.eq_swap⟩
   have q6k:=run_surgery3 L1
    (fun u hu=>by rw [q8z] at hu;rcases Z4.mp hu with h | h;exact (hf1.2.2.2.2.1 u (Z0.mp h).1).symm;exact (hf2.2.2.2.2.1 u (Z0.mp h).1).symm)
    (fun u hu=>by rw [q5o] at hu;exact (hf1.2.2.2.1 u (Z0.mp (Finset.mem_of_mem_erase hu)).1).symm)
    (fun u hu=>by rw [q5p] at hu;exact (hf2.2.2.2.1 u (Z0.mp (Finset.mem_of_mem_erase hu)).1).symm)
    qeg
   dsimp only at q6k
   set Zact:=({z,zp1,zp2}:Finset (Fin n)).filter (fun v=>(L1 v).Nonempty)
   set Zhas:=Zact.filter (fun v=>∃ a∈ tops G C \ centreless G C,z126 C s z g1 g2 a=v)
   rw [q8z,q5o,q5p] at q6k
   have qa9:(Zact \ Zhas).card≤ 3:=by
    calc (Zact \ Zhas).card≤ ({z,zp1,zp2}:Finset (Fin n)).card:=
       Finset.card_le_card (Finset.Subset.trans Finset.sdiff_subset (Finset.filter_subset _ _))
     _=3:=by rw [Z24 (by simp [q2s,q2t]),Finset.card_pair q0h]
   obtain ⟨c1,hc1,q87⟩:=z049 hf1
   obtain ⟨c2,hc2,q6x⟩:=z049 hf2
   obtain ⟨d1,hd1,q6i⟩:=z050 hf1
   obtain ⟨d2,hd2,q8y⟩:=z050 hf2
   have q6n:c1∈ MC1.erase z:=Finset.mem_erase.mpr ⟨q87,by rw [q5r];exact hc1⟩
   have q8b:c2∈ MC2.erase z:=Finset.mem_erase.mpr ⟨q6x,by rw [qer];exact hc2⟩
   have qai:d1∈ MD:=Finset.mem_union_left _ (by rw [q3m];exact hd1)
   have qi8:d2∈ MD:=Finset.mem_union_right _ (by rw [q3n];exact hd2)
   have q49:d1≠ zp2:=fun h=>Finset.disjoint_left.mp q4o hd1 (h ▸ hf2.2.2.1)
   have q8c:d2≠ zp1:=fun h=>Finset.disjoint_right.mp q4o hd2 (h ▸ hf1.2.2.1)
   have q11:∀ k,(OrReaches n C (n+k) g1∨ OrReaches n C (n+k) g2)→ k∉ FacAll:=by
    intro k hr hkf
    rcases hr with h1 | h2
    ·exact (q14 k hkf).1 h1
    ·exact (q14 k hkf).2 h2
   have q7f:FacAll.card≤ (orN G C \ lam G C).card:=Finset.card_le_card q07
   by_cases qaa:2≤ (centreless G C).card
   ·omega
   ·by_cases q6l:(centreless G C).card=1
    ·
     by_cases qla:(Zact \ Zhas).card≤ 1
     ·omega
     ·obtain ⟨a0,ha0⟩:=Finset.card_eq_one.mp q6l
      have qbt:a0∈ centreless G C:=by rw [ha0];simp
      have q1x:a0∈ tops G C:=(Z0.mp qbt).1
      have qek:=z098.mp q1x
      by_cases hZ3:(Zact \ Zhas).card=3
      ·
       have q6m:Zact \ Zhas={z,zp1,zp2}:=
        Finset.eq_of_subset_of_card_le
         (Finset.Subset.trans Finset.sdiff_subset (Finset.filter_subset _ _))
         (by rw [Z24 (by simp [q2s,q2t]),Finset.card_pair q0h];omega)
       have q8d:z∈ Zact \ Zhas:=by rw [q6m];simp
       have q08:zp1∈ Zact \ Zhas:=by rw [q6m];simp
       obtain ⟨b0,q6o,qi9,q96⟩:∃ b0:Fin 2,side (n:=n) C a0 b0=∅∧
         OrReaches n C (opnd C a0 b0) g1∧ z∈ side (n:=n) C a0 (1 - b0):=by
        rcases q2d d1 qai q6i q49 with hA | ⟨a,haC,b,g,hg,hgv,q0g,hrb,hzs⟩
        ·exact absurd (Z0.mpr ⟨(Z2.mp q8d).1,hA⟩) (Z2.mp q8d).2
        ·have q3z:a=a0:=Z3.mp (ha0 ▸ haC);subst q3z
         have qbu:gateVal n C g2 (pairInput z d1)=false:=by
          rw [Z14,ne_eq,z052 q03 h4 hf2 (hf1.2.2.2.2.1 d1 hd1).symm]
          simp only [z045,Z4,Z19,Sym2.eq_iff]
          rintro (⟨d,hd,⟨_,rfl⟩ | ⟨h1,_⟩⟩ | ⟨c,_,⟨_,rfl⟩ | ⟨_,h2⟩⟩)
          ·exact Finset.disjoint_left.mp q4o hd1 hd
          ·exact absurd (h1 ▸ z047 q03 hf1 hd1) (q03 z zp1 hf1.1)
          ·exact q49 rfl
          ·exact q2t.symm h2
         have q56:g=g1:=hg.resolve_right (fun h=>by rw [h,qbu] at hgv;cases hgv)
         subst q56;exact ⟨b,q0g,hrb,hzs⟩
       have qia:OrReaches n C (opnd C a0 b0) g2:=by
        rcases q2d d2 qi8 q8c q8y with hA | ⟨a,haC,b,g,hg,hgv,q0g,hrb,hzs⟩
        ·exact absurd (Z0.mpr ⟨(Z2.mp q8d).1,hA⟩) (Z2.mp q8d).2
        ·have q3z:a=a0:=Z3.mp (ha0 ▸ haC);subst q3z
         have qbv:gateVal n C g1 (pairInput z d2)=false:=by
          rw [Z14,ne_eq,z052 q03 h4 hf1 (hf2.2.2.2.2.1 d2 hd2).symm]
          simp only [z045,Z4,Z19,Sym2.eq_iff]
          rintro (⟨d,hd,⟨_,rfl⟩ | ⟨h1,_⟩⟩ | ⟨c,_,⟨_,rfl⟩ | ⟨_,h2⟩⟩)
          ·exact Finset.disjoint_left.mp q4o hd hd2
          ·exact absurd (h1 ▸ z047 q03 hf2 hd2) (q03 z zp2 hf2.1)
          ·exact q8c rfl
          ·exact q2s.symm h2
         have q56:g=g2:=hg.resolve_left (fun h=>by rw [h,qbv] at hgv;cases hgv)
         subst q56
         have hbe:b=b0:=by
          by_contra q2e
          have q51:1 - b0=b:=z044 (Ne.symm q2e)
          rw [q51,q0g] at q96;exact Finset.notMem_empty _ q96
         rwa [← hbe]
       obtain ⟨mp,hmp,qib,qeu⟩:=z122 hL q0y q00
        (by have:=z104 hL.1 qek.1 b0;omega) (z130 hL hne q1x b0)
        q6o qi9 qia
       obtain ⟨m2,hm2,q6p,qcv⟩:∃ m2∈ orN G C \ lam G C,m2∉ FacAll∧ (orIn n C (n+m2)).Nonempty:=by
        rcases q0l c1 q6n with hA | ⟨a,haC,b,q0g,_,q40⟩ | ⟨mv,hmv,q1r,q05,_⟩
        ·exact absurd (Z0.mpr ⟨(Z2.mp q08).1,hA⟩) (Z2.mp q08).2
        ·have q3z:a=a0:=Z3.mp (ha0 ▸ haC);subst q3z
         have hbe:b=b0:=by
          by_contra q2e
          have q51:1 - b0=b:=z044 (Ne.symm q2e)
          rw [q51,q0g] at q96;exact Finset.notMem_empty _ q96
         rw [hbe] at q40
         obtain ⟨mw,hmw,q6q,qox⟩:=z014 q03 hL q01 hne q00
          (by have:=z104 hL.1 qek.1 (1 - b0);omega)
          (z130 hL hne q1x (1 - b0)) q96 q40 (q03 z zp1 hf1.1)
          FacAll q2b
         exact ⟨mw,hmw,q6q,Finset.card_pos.mp (by omega)⟩
        ·exact ⟨mv,hmv,fun h=>by have:=q0b mv h;omega,by rw [q05];simp⟩
       have qic:mp∉ FacAll:=fun h=>by have:=q0b mp h;omega
       have qev:mp≠ m2:=fun h=>by rw [← h,qeu] at qcv;exact qcv.ne_empty rfl
       have q0z:Disjoint ({mp,m2}:Finset ℕ) FacAll:=by
        rw [Finset.disjoint_left];intro k hk hkf
        simp only [Z6,Z3] at hk
        rcases hk with rfl | rfl
        ·exact qic hkf
        ·exact q6p hkf
       have q2g:=Finset.card_le_card (Finset.union_subset
        (Finset.insert_subset hmp (Finset.singleton_subset_iff.mpr hm2)) q07)
       rw [Finset.card_union_of_disjoint q0z,Finset.card_pair qev] at q2g
       omega
      ·
       have qn5:(Zact \ Zhas).card=2:=by omega
       have qaj:∃ m∈ orN G C \ lam G C,m∉ FacAll:=by
        by_cases qew:z∈ Zact \ Zhas
        ·
         obtain ⟨b0,q6o,q96⟩:∃ b0:Fin 2,side (n:=n) C a0 b0=∅∧ z∈ side (n:=n) C a0 (1 - b0):=by
          rcases q2d d1 qai q6i q49 with hA | ⟨a,haC,b,_,_,_,q0g,_,hzs⟩
          ·exact absurd (Z0.mpr ⟨(Z2.mp qew).1,hA⟩) (Z2.mp qew).2
          ·have q3z:a=a0:=Z3.mp (ha0 ▸ haC);subst q3z
           exact ⟨b,q0g,hzs⟩
         have qid:zp1∈ Zact \ Zhas∨ zp2∈ Zact \ Zhas:=by
          by_contra hno;push Not at hno
          have q0c:Zact \ Zhas⊆ {z}:=by
           intro v hv
           have hv1:=(Z0.mp (Z2.mp hv).1).1
           simp only [Z6,Z3] at hv1 ⊢
           rcases hv1 with rfl | rfl | rfl
           ·rfl
           ·exact absurd hv hno.1
           ·exact absurd hv hno.2
          have:=(Finset.card_le_card q0c).trans (by simp:({z}:Finset (Fin n)).card≤ 1)
          omega
         rcases qid with q08 | q0e
         ·rcases q0l c1 q6n with hA | ⟨a,haC,b,q0g,_,q40⟩ | ⟨mv,hmv,q1r,_⟩
          ·exact absurd (Z0.mpr ⟨(Z2.mp q08).1,hA⟩) (Z2.mp q08).2
          ·have q3z:a=a0:=Z3.mp (ha0 ▸ haC);subst q3z
           have hbe:b=b0:=by
            by_contra q2e
            have q51:1 - b0=b:=z044 (Ne.symm q2e)
            rw [q51,q0g] at q96;exact Finset.notMem_empty _ q96
           rw [hbe] at q40
           obtain ⟨mw,hmw,q6q,_⟩:=z014 q03 hL q01 hne q00
            (by have:=z104 hL.1 qek.1 (1 - b0);omega)
            (z130 hL hne q1x (1 - b0)) q96 q40 (q03 z zp1 hf1.1)
            FacAll q2b
           exact ⟨mw,hmw,q6q⟩
          ·exact ⟨mv,hmv,fun h=>by have:=q0b mv h;omega⟩
         ·rcases q0n c2 q8b with hA | ⟨a,haC,b,q0g,_,qbr⟩ | ⟨_,_,_,_,_,_,mu,hmu,q2c,_⟩
          ·exact absurd (Z0.mpr ⟨(Z2.mp q0e).1,hA⟩) (Z2.mp q0e).2
          ·have q3z:a=a0:=Z3.mp (ha0 ▸ haC);subst q3z
           have hbe:b=b0:=by
            by_contra q2e
            have q51:1 - b0=b:=z044 (Ne.symm q2e)
            rw [q51,q0g] at q96;exact Finset.notMem_empty _ q96
           rw [hbe] at qbr
           obtain ⟨mw,hmw,q6q,_⟩:=z014 q03 hL q01 hne q00
            (by have:=z104 hL.1 qek.1 (1 - b0);omega)
            (z130 hL hne q1x (1 - b0)) q96 qbr (q03 z zp2 hf2.1)
            FacAll q2b
           exact ⟨mw,hmw,q6q⟩
          ·exact ⟨mu,hmu,fun h=>by have:=q0b mu h;omega⟩
        ·
         have q0c:Zact \ Zhas⊆ {zp1,zp2}:=by
          intro v hv
          have hv1:=(Z0.mp (Z2.mp hv).1).1
          simp only [Z6,Z3] at hv1 ⊢
          exact hv1.resolve_left (fun h=>qew (h ▸ hv))
         have qak:Zact \ Zhas={zp1,zp2}:=
          Finset.eq_of_subset_of_card_le q0c (by rw [Finset.card_pair q0h];omega)
         have q08:zp1∈ Zact \ Zhas:=by rw [qak];simp
         have q0e:zp2∈ Zact \ Zhas:=by rw [qak];simp
         rcases q0l c1 q6n with hA1 | ⟨a1,qeh,b1',qbp,qjd,q40⟩ | ⟨mv,hmv,q1r,_⟩
         ·exact absurd (Z0.mpr ⟨(Z2.mp q08).1,hA1⟩) (Z2.mp q08).2
         ·rcases q0n c2 q8b with hA2 | ⟨a2,qhz,b2',qbq,qje,qbr⟩ | ⟨_,_,_,_,_,_,mu,hmu,q2c,_⟩
          ·exact absurd (Z0.mpr ⟨(Z2.mp q0e).1,hA2⟩) (Z2.mp q0e).2
          ·have qei:a1=a0:=Z3.mp (ha0 ▸ qeh)
           have qej:a2=a0:=Z3.mp (ha0 ▸ qhz)
           subst qei;subst qej
           have ql8:b1'=b2':=by
            by_contra q2e
            have q51:1 - b1'=b2':=z044 q2e
            rw [q51,qbq] at q40;exact Finset.notMem_empty _ q40
           subst ql8
           obtain ⟨mp,hmp,qib,_⟩:=z122 hL q0y q00
            (by have:=z104 hL.1 qek.1 b1';omega) (z130 hL hne q1x b1')
            qbp qjd qje
           exact ⟨mp,hmp,fun h=>by have:=q0b mp h;omega⟩
          ·exact ⟨mu,hmu,fun h=>by have:=q0b mu h;omega⟩
         ·exact ⟨mv,hmv,fun h=>by have:=q0b mv h;omega⟩
       obtain ⟨m,hm,qel⟩:=qaj
       have q5q:=Finset.card_le_card (Finset.insert_subset hm q07)
       rw [Z24 qel] at q5q
       omega
    ·
     have q0m:centreless G C=∅:=Finset.card_eq_zero.mp (by omega)
     have qac:∃ a∈ tops G C \ centreless G C,z126 C s z g1 g2 a=z:=by
      rcases q2d d1 qai q6i q49 with hA | ⟨a,haC,_⟩
      ·exact hA
      ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
     have q7m:z∉ Zact \ Zhas:=fun h=>
      (Z2.mp h).2 (Z0.mpr ⟨(Z2.mp h).1,qac⟩)
     have q5d:Zact \ Zhas⊆ {zp1,zp2}:=by
      intro v hv
      have hv1:=(Z0.mp (Z2.mp hv).1).1
      simp only [Z6,Z3] at hv1 ⊢
      exact hv1.resolve_left (fun h=>q7m (h ▸ hv))
     have ql9:(Zact \ Zhas).card≤ 2:=(Finset.card_le_card q5d).trans (by rw [Finset.card_pair q0h])
     by_cases hZ0:(Zact \ Zhas).card=0
     ·obtain ⟨m0,hm0,qcn⟩:=z037 hL q01 hne q0y q00 q0m
      have qab:m0∉ FacAll:=fun h=>by have:=q0b m0 h;omega
      have q5q:=Finset.card_le_card (Finset.insert_subset hm0 q07)
      rw [Z24 qab] at q5q
      omega
     ·by_cases hZ1:(Zact \ Zhas).card=1
      ·
       have qb2:∃ m1 m2,m1≠ m2∧ m1∈ orN G C \ lam G C∧ m2∈ orN G C \ lam G C∧
         m1∉ FacAll∧ m2∉ FacAll:=by
        have qlj:(Zact \ Zhas).Nonempty:=Finset.card_pos.mp (by omega)
        obtain ⟨v,hv⟩:=qlj
        have hv':=q5d hv
        simp only [Z6,Z3] at hv'
        rcases hv' with q30 | q30
        ·rw [q30] at hv
         rcases q0l c1 q6n with hA | ⟨a,haC,_⟩ | ⟨mv,hmv,q1r,q05,u',q24,mu,hmu,q3j,q06⟩
         ·exact absurd (Z0.mpr ⟨(Z2.mp hv).1,hA⟩) (Z2.mp hv).2
         ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
         ·have qex:mv≠ mu:=fun h=>by
           rw [h,q06] at q05
           have:=Finset.singleton_injective q05
           exact q03 z zp1 hf1.1 (q24.symm.trans (congrArg s this))
          exact ⟨mv,mu,qex,hmv,hmu,fun h=>by have:=q0b mv h;omega,
           q11 mu (Or.inl q3j)⟩
        ·rw [q30] at hv
         rcases q0n c2 q8b with hA | ⟨a,haC,_⟩ | ⟨mv,hmv,qey,q05,u',q24,mu,hmu,q2c,q06⟩
         ·exact absurd (Z0.mpr ⟨(Z2.mp hv).1,hA⟩) (Z2.mp hv).2
         ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
         ·have qex:mv≠ mu:=fun h=>by
           rw [h,q06] at q05
           have:=Finset.singleton_injective q05
           exact q03 z zp2 hf2.1 (q24.symm.trans (congrArg s this))
          exact ⟨mv,mu,qex,hmv,hmu,q11 mv (Or.inl qey),
           fun h=>by have:=q0b mu h;omega⟩
       obtain ⟨m1,m2,qem,hm1,hm2,qal,q6p⟩:=qb2
       have q0z:Disjoint ({m1,m2}:Finset ℕ) FacAll:=by
        rw [Finset.disjoint_left];intro k hk hkf
        simp only [Z6,Z3] at hk
        rcases hk with rfl | rfl
        ·exact qal hkf
        ·exact q6p hkf
       have q2g:=Finset.card_le_card (Finset.union_subset
        (Finset.insert_subset hm1 (Finset.singleton_subset_iff.mpr hm2)) q07)
       rw [Finset.card_union_of_disjoint q0z,Finset.card_pair qem] at q2g
       omega
      ·
       have qak:Zact \ Zhas={zp1,zp2}:=
        Finset.eq_of_subset_of_card_le q5d (by rw [Finset.card_pair q0h];omega)
       have q08:zp1∈ Zact \ Zhas:=by rw [qak];simp
       have q0e:zp2∈ Zact \ Zhas:=by rw [qak];simp
       obtain ⟨m1,hm1,qal,q1i,u',q24,m3,hm3,qie,q8e⟩:
         ∃ m1∈ orN G C \ lam G C,m1∉ FacAll∧ orIn n C (n+m1)={zp1}∧
         ∃ u':Fin n,s u'=s z∧ ∃ m3∈ orN G C \ lam G C,m3∉ FacAll∧ orIn n C (n+m3)={u'}:=by
        rcases q0l c1 q6n with hA | ⟨a,haC,_⟩ | ⟨mv,hmv,q1r,q05,u',q24,mu,hmu,q3j,q06⟩
        ·exact absurd (Z0.mpr ⟨(Z2.mp q08).1,hA⟩) (Z2.mp q08).2
        ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
        ·exact ⟨mv,hmv,fun h=>by have:=q0b mv h;omega,q05,
          u',q24,mu,hmu,q11 mu (Or.inl q3j),q06⟩
       obtain ⟨m2,hm2,q6p,q16⟩:
         ∃ m2∈ orN G C \ lam G C,m2∉ FacAll∧ orIn n C (n+m2)={zp2}:=by
        rcases q0n c2 q8b with hA | ⟨a,haC,_⟩ | ⟨mv,hmv,qey,q05,_⟩
        ·exact absurd (Z0.mpr ⟨(Z2.mp q0e).1,hA⟩) (Z2.mp q0e).2
        ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
        ·exact ⟨mv,hmv,q11 mv (Or.inl qey),q05⟩
       have qem:m1≠ m2:=fun h=>by
        rw [h,q16] at q1i;exact q0h.symm (Finset.singleton_injective q1i)
       have qoy:m1≠ m3:=fun h=>by
        rw [h,q8e] at q1i
        have:=Finset.singleton_injective q1i
        exact q03 z zp1 hf1.1 (q24.symm.trans (congrArg s this))
       have qoz:m2≠ m3:=fun h=>by
        rw [h,q8e] at q16
        have:=Finset.singleton_injective q16
        exact q03 z zp2 hf2.1 (q24.symm.trans (congrArg s this))
       have q0z:Disjoint ({m1,m2,m3}:Finset ℕ) FacAll:=by
        rw [Finset.disjoint_left];intro k hk hkf
        simp only [Z6,Z3] at hk
        rcases hk with rfl | rfl | rfl
        ·exact qal hkf
        ·exact q6p hkf
        ·exact qie hkf
       have qez:=Finset.card_le_card (Finset.union_subset
        (Finset.insert_subset hm1 (Finset.insert_subset hm2 (Finset.singleton_subset_iff.mpr hm3))) q07)
       rw [Finset.card_union_of_disjoint q0z,
        Z24 (by simp [qem,qoy]),Finset.card_pair qoz] at qez
       omega
  ·
   have qes:MD1.card≤ FacD1.card+1:=by
    by_cases h:MD1.Nonempty
    ·exact q47.1 h
    ·rw [Z25.mp h];simp
   have qet:MD2.card≤ FacD2.card+1:=by
    by_cases h:MD2.Nonempty
    ·exact q48.1 h
    ·rw [Z25.mp h];simp
   apply close_slack1
   rw [q13,q90,qbs]
   by_cases q3m:MD1=D1
   ·by_cases q3n:MD2=D2
    ·
     have qif:z∈ MC1:=Z0.mpr ⟨hf1.2.1,(Z0.mp (by rw [q3m];exact hf1.2.2.1:zp1∈ MD1)).2⟩
     have qig:z∈ MC2:=Z0.mpr ⟨hf2.2.1,(Z0.mp (by rw [q3n];exact hf2.2.2.1:zp2∈ MD2)).2⟩
     by_cases q5r:MC1=C1
     ·have q3l:MC2≠ C2:=fun h=>qcu ⟨q5r,h,q3m,q3n⟩
      have hex:∃ r∈ C2,r∉ MC2:=by
       by_contra hno;push Not at hno
       exact q3l (Finset.Subset.antisymm (Finset.filter_subset _ _) hno)
      have hle:MC2.card≤ FacC2.card:=q1h.2 hex
      rw [Finset.card_erase_of_mem qig]
      have qj5:=Finset.card_pos.mpr ⟨z,qig⟩
      omega
     ·have hex:∃ r∈ C1,r∉ MC1:=by
       by_contra hno;push Not at hno
       exact q5r (Finset.Subset.antisymm (Finset.filter_subset _ _) hno)
      have hle:MC1.card≤ FacC1.card:=q1w.2 hex
      rw [Finset.card_erase_of_mem qif]
      have qj5:=Finset.card_pos.mpr ⟨z,qif⟩
      omega
    ·have hex:∃ r∈ D2,r∉ MD2:=by
      by_contra hno;push Not at hno
      exact q3n (Finset.Subset.antisymm (Finset.filter_subset _ _) hno)
     have hle:MD2.card≤ FacD2.card:=q48.2 hex
     omega
   ·have hex:∃ r∈ D1,r∉ MD1:=by
     by_contra hno;push Not at hno
     exact q3m (Finset.Subset.antisymm (Finset.filter_subset _ _) hno)
    have hle:MD1.card≤ FacD1.card:=q47.2 hex
    omega
lemma z020 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u≠ s v) (h4:NoFourCycle G)
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C)
  {g1 g2:ℕ} (q0y:g1 < g2) (q00:∀ k,k∈ junk G C↔ k=g1∨ k=g2)
  {C1 D1 C2 D2:Finset (Fin n)} {z1 zp1 z2 zp2:Fin n}
  (q5z:z1≠ z2) (q0h:zp1≠ zp2) (hsz:s z1=s z2) (q1l:s zp1=s zp2)
  (hf1:z000 G C g1 C1 D1 z1 zp1) (hf2:z000 G C g2 C2 D2 z2 zp2):False:=by
 classical
 have hne:∃ u v:Fin n,G.Adj u v:=⟨z1,zp1,hf1.1⟩
 have qdf:g1≠ g2:=Nat.ne_of_lt q0y
 have q5x:=z094.mp ((q00 g1).mpr (Or.inl rfl))
 have q2p:=z094.mp ((q00 g2).mpr (Or.inr rfl))
 have q02:s z1≠ s zp1:=q03 z1 zp1 hf1.1
 have q2h:z1≠ zp1:=fun h=>q02 (congrArg s h)
 have q1z:z1≠ zp2:=fun h=>q02 ((congrArg s h).trans q1l.symm)
 have q20:z2≠ zp1:=fun h=>q02 (hsz.trans (congrArg s h))
 have q2i:z2≠ zp2:=fun h=>q02 (hsz.trans ((congrArg s h).trans q1l.symm))
 obtain ⟨⟨qce,qcf,qcg,qch⟩,b1,qci,qb0⟩:=
  z066 q03 hL q01 q0y q00 hf1
 obtain ⟨qcj,qck,b2,q44,q2o,q6h,q3k,q5a,q2a⟩:=
  z067 q03 h4 hL q01 q0y q00 hf1 hf2 hsz q1l
 set w1C:=opnd C g1 b1
 set w1D:=opnd C g1 (1 - b1)
 set w2C:=opnd C g2 b2
 set w2D:=opnd C g2 (1 - b2)
 have q4l:¬ OrReaches n C w1C g1:=by fin_cases b1 <;> assumption
 have q7i:¬ OrReaches n C w1C g2:=by fin_cases b1 <;> assumption
 have q4m:¬ OrReaches n C w1D g1:=by fin_cases b1 <;> assumption
 have q7j:¬ OrReaches n C w1D g2:=by fin_cases b1 <;> assumption
 have q2x:¬ OrReaches n C w2C g1:=fun h=>q0h (q6h h).2.1
 have q7k:¬ OrReaches n C w2C g2:=by fin_cases b2 <;> assumption
 have q2y:¬ OrReaches n C w2D g1:=fun h=>q5z (q5a h).2.1
 have q7l:¬ OrReaches n C w2D g2:=by fin_cases b2 <;> assumption
 have q4n:orIn n C w2C=C2:=q3k q2x
 have q4p:orIn n C w2D=D2:=q2a q2y
 set FacC1:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w1C k)
 set FacD1:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w1D k)
 set FacC2:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w2C k)
 set FacD2:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w2D k)
 have q2q:∀ a,a∈ junk G C→ ∀ b:Fin 2,∀ m,opnd C a b=n+m→ ¬ BelowF G C m:=by
  intro a ha b m hm hbm
  have ha':=z094.mp ha
  exact z089 hL hne ha'.1 ha'.2.1 b (by rw [hm];exact hbm)
 have q1j:∀ k∈ FacC1,¬ OrReaches n C (n+k) g1∧ ¬ OrReaches n C (n+k) g2∧
   orIn n C (n+k)⊆ C1∧ 2≤ (orIn n C (n+k)).card:=by
  intro k hk;have hkf:=Z0.mp hk
  have hn1:¬ OrReaches n C (n+k) g1:=fun h=>q4l (z116 hkf.2 h)
  have hn2:¬ OrReaches n C (n+k) g2:=fun h=>q7i (z116 hkf.2 h)
  have q0c:=z109 hkf.2;rw [show orIn n C w1C=C1 from qci] at q0c
  exact ⟨hn1,hn2,q0c,z123 hL q01 hne q00 (Z2.mp hkf.1).1 hn1 hn2⟩
 have q1s:∀ k∈ FacD1,¬ OrReaches n C (n+k) g1∧ ¬ OrReaches n C (n+k) g2∧
   orIn n C (n+k)⊆ D1∧ 2≤ (orIn n C (n+k)).card:=by
  intro k hk;have hkf:=Z0.mp hk
  have hn1:¬ OrReaches n C (n+k) g1:=fun h=>q4m (z116 hkf.2 h)
  have hn2:¬ OrReaches n C (n+k) g2:=fun h=>q7j (z116 hkf.2 h)
  have q0c:=z109 hkf.2;rw [show orIn n C w1D=D1 from qb0] at q0c
  exact ⟨hn1,hn2,q0c,z123 hL q01 hne q00 (Z2.mp hkf.1).1 hn1 hn2⟩
 have q22:∀ k∈ FacC2,¬ OrReaches n C (n+k) g1∧ ¬ OrReaches n C (n+k) g2∧
   orIn n C (n+k)⊆ C2∧ 2≤ (orIn n C (n+k)).card:=by
  intro k hk;have hkf:=Z0.mp hk
  have hn1:¬ OrReaches n C (n+k) g1:=fun h=>q2x (z116 hkf.2 h)
  have hn2:¬ OrReaches n C (n+k) g2:=fun h=>q7k (z116 hkf.2 h)
  have q0c:=z109 hkf.2;rw [q4n] at q0c
  exact ⟨hn1,hn2,q0c,z123 hL q01 hne q00 (Z2.mp hkf.1).1 hn1 hn2⟩
 have q2j:∀ k∈ FacD2,¬ OrReaches n C (n+k) g1∧ ¬ OrReaches n C (n+k) g2∧
   orIn n C (n+k)⊆ D2∧ 2≤ (orIn n C (n+k)).card:=by
  intro k hk;have hkf:=Z0.mp hk
  have hn1:¬ OrReaches n C (n+k) g1:=fun h=>q2y (z116 hkf.2 h)
  have hn2:¬ OrReaches n C (n+k) g2:=fun h=>q7l (z116 hkf.2 h)
  have q0c:=z109 hkf.2;rw [q4p] at q0c
  exact ⟨hn1,hn2,q0c,z123 hL q01 hne q00 (Z2.mp hkf.1).1 hn1 hn2⟩
 have q0r:∀ {v1 v2:Fin n} {F1 F2:Finset ℕ},v1≠ v2→
   (∀ k∈ F1,(∀ u∈ orIn n C (n+k),G.Adj v1 u)∧ 2≤ (orIn n C (n+k)).card)→
   (∀ k∈ F2,∀ u∈ orIn n C (n+k),G.Adj v2 u)→ Disjoint F1 F2:=by
  intro v1 v2 F1 F2 qp0 h1 h2
  rw [Finset.disjoint_left];intro k hk1 hk2
  obtain ⟨u1,hu1,u2,hu2,qd2⟩:=Finset.one_lt_card.mp (by have:=(h1 k hk1).2;omega:1 < (orIn n C (n+k)).card)
  exact qp0 (z102 h4 qd2
   ((h1 k hk1).1 u1 hu1).symm ((h1 k hk1).1 u2 hu2).symm
   (h2 k hk2 u1 hu1).symm (h2 k hk2 u2 hu2).symm)
 have qf0:Disjoint FacC1 FacD1:=q0r q2h.symm
  (fun k hk=>⟨fun u hu=>(hf1.2.2.2.1 u ((q1j k hk).2.2.1 hu)).symm,(q1j k hk).2.2.2⟩)
  (fun k hk u hu=>(hf1.2.2.2.2.1 u ((q1s k hk).2.2.1 hu)).symm)
 have qf1:Disjoint FacC1 FacC2:=q0r q0h
  (fun k hk=>⟨fun u hu=>(hf1.2.2.2.1 u ((q1j k hk).2.2.1 hu)).symm,(q1j k hk).2.2.2⟩)
  (fun k hk u hu=>(hf2.2.2.2.1 u ((q22 k hk).2.2.1 hu)).symm)
 have qf2:Disjoint FacC1 FacD2:=q0r q20.symm
  (fun k hk=>⟨fun u hu=>(hf1.2.2.2.1 u ((q1j k hk).2.2.1 hu)).symm,(q1j k hk).2.2.2⟩)
  (fun k hk u hu=>(hf2.2.2.2.2.1 u ((q2j k hk).2.2.1 hu)).symm)
 have qf3:Disjoint FacD1 FacC2:=q0r q1z
  (fun k hk=>⟨fun u hu=>(hf1.2.2.2.2.1 u ((q1s k hk).2.2.1 hu)).symm,(q1s k hk).2.2.2⟩)
  (fun k hk u hu=>(hf2.2.2.2.1 u ((q22 k hk).2.2.1 hu)).symm)
 have qf4:Disjoint FacD1 FacD2:=q0r q5z
  (fun k hk=>⟨fun u hu=>(hf1.2.2.2.2.1 u ((q1s k hk).2.2.1 hu)).symm,(q1s k hk).2.2.2⟩)
  (fun k hk u hu=>(hf2.2.2.2.2.1 u ((q2j k hk).2.2.1 hu)).symm)
 have qf5:Disjoint FacC2 FacD2:=q0r q2i.symm
  (fun k hk=>⟨fun u hu=>(hf2.2.2.2.1 u ((q22 k hk).2.2.1 hu)).symm,(q22 k hk).2.2.2⟩)
  (fun k hk u hu=>(hf2.2.2.2.2.1 u ((q2j k hk).2.2.1 hu)).symm)
 set FacAll:=(FacC1 ∪ FacD1) ∪ (FacC2 ∪ FacD2)
 set Extra:=(orN G C \ lam G C) \ FacAll
 have q07:FacAll⊆ orN G C \ lam G C:=
  Finset.union_subset (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
   (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
 have q13:FacAll.card=FacC1.card+FacD1.card+FacC2.card+FacD2.card:=by
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
   ⟨Finset.disjoint_union_right.mpr ⟨qf1,qf2⟩,Finset.disjoint_union_right.mpr ⟨qf3,qf4⟩⟩),
   Finset.card_union_of_disjoint qf0,Finset.card_union_of_disjoint qf5]
  omega
 have q8r:(orN G C \ lam G C).card=FacAll.card+Extra.card:=by
  rw [z019 q07];have:=Finset.card_le_card q07;omega
 have q14:∀ k∈ FacAll,¬ OrReaches n C (n+k) g1∧ ¬ OrReaches n C (n+k) g2:=by
  intro k hk;simp only [FacAll,Z4] at hk
  rcases hk with (h | h) | (h | h)
  ·exact ⟨(q1j k h).1,(q1j k h).2.1⟩
  ·exact ⟨(q1s k h).1,(q1s k h).2.1⟩
  ·exact ⟨(q22 k h).1,(q22 k h).2.1⟩
  ·exact ⟨(q2j k h).1,(q2j k h).2.1⟩
 have q0w:∀ k∈ orN G C \ lam G C,(OrReaches n C (n+k) g1∨ OrReaches n C (n+k) g2)→ k∈ Extra:=by
  intro k hk hr
  exact Z2.mpr ⟨hk,fun hkf=>hr.elim (q14 k hkf).1 (q14 k hkf).2⟩
 set E1:=z045 C1 D1 z1 zp1
 set E2:=z045 C2 D2 z2 zp2
 set U1:=Ustar G C ∩ E1
 set U2:=Ustar G C ∩ E2
 set U12:=U1 ∩ U2
 have q5n:=z135 q03 hL q01 h4 q00 hf1 hf2
 have q4q:Ustar G C=U1 ∪ U2:=by
  ext e;simp only [U1,U2,Z4,Z5]
  constructor
  ·intro he;rcases Z4.mp (q5n he) with h1 | h2
   ·exact Or.inl ⟨he,h1⟩
   ·exact Or.inr ⟨he,h2⟩
  ·rintro (⟨he,_⟩ | ⟨he,_⟩) <;> exact he
 have q5s:∀ e∈ U12,e=s(z1,zp2)∨ e=s(z2,zp1):=by
  intro e he
  have he1:e∈ E1:=(Z5.mp (Z5.mp he).1).2
  have he2:e∈ E2:=(Z5.mp (Z5.mp he).2).2
  simp only [E1,E2,z045,Z4,Z19] at he1 he2
  rcases he1 with ⟨d1,hd1,rfl⟩ | ⟨c1,hc1,rfl⟩ <;>
  rcases he2 with ⟨d2,hd2,h2⟩ | ⟨c2,hc2,h2⟩ <;>
  rw [Sym2.eq_iff] at h2
  ·rcases h2 with ⟨h,_⟩ | ⟨h,_⟩
   ·exact absurd h.symm q5z
   ·exact absurd (hsz.trans (by rw [h];exact z047 q03 hf1 hd1)) q02
  ·rcases h2 with ⟨h,h'⟩ | ⟨_,h'⟩
   ·exact Or.inl (by rw [← h,← h'])
   ·exact absurd (q1l.trans (congrArg s h')).symm q02
  ·rcases h2 with ⟨h,h'⟩ | ⟨h,_⟩
   ·exact Or.inr (by rw [← h,← h'])
   ·exact absurd (hsz.trans (congrArg s h)) q02
  ·rcases h2 with ⟨_,h⟩ | ⟨h,_⟩
   ·exact absurd h.symm q0h
   ·exact absurd ((hsz.trans (z046 q03 hf2 hc2).symm).trans (congrArg s h)) q02
 have qjg:U12.card≤ 1:=by
  by_contra hgt;push Not at hgt
  obtain ⟨e1,he1,e2,he2,qn6⟩:=Finset.one_lt_card.mp hgt
  have hm1:=q5s e1 he1
  have hm2:=q5s e2 he2
  have qb1:s(z1,zp2)∈ U12∧ s(z2,zp1)∈ U12:=by
   rcases hm1 with rfl | rfl <;> rcases hm2 with rfl | rfl
   ·exact absurd rfl qn6
   ·exact ⟨he1,he2⟩
   ·exact ⟨he2,he1⟩
   ·exact absurd rfl qn6
  have qlk:G.Adj z1 zp2:=SimpleGraph.mem_edgeFinset.mp (Z2.mp (Z5.mp (Z5.mp qb1.1).1).1).1
  have qll:G.Adj z2 zp1:=SimpleGraph.mem_edgeFinset.mp (Z2.mp (Z5.mp (Z5.mp qb1.2).1).1).1
  exact q0h (z102 h4 q5z hf1.1 qll qlk hf2.1)
 have qih:(∀ e∈ U12,e=s(z1,zp2))∨ (∀ e∈ U12,e=s(z2,zp1)):=by
  by_cases q0g:U12=∅
  ·left;intro e he;rw [q0g] at he;exact absurd he (Finset.notMem_empty _)
  ·obtain ⟨e0,he0⟩:=Finset.nonempty_iff_ne_empty.mpr q0g
   have q0t:U12.card=1:=by have:=Finset.Nonempty.card_pos ⟨e0,he0⟩;omega
   obtain ⟨x,hx⟩:=Finset.card_eq_one.mp q0t
   have hx0:e0=x:=Z3.mp (hx ▸ he0)
   subst hx0
   rcases q5s e0 he0 with rfl | rfl
   ·left;intro e he;rw [hx,Z3] at he;exact he
   ·right;intro e he;rw [hx,Z3] at he;exact he
 set MC1:=C1.filter (fun c=>s(c,zp1)∈ Ustar G C)
 set MD1:=D1.filter (fun d=>s(z1,d)∈ Ustar G C)
 set MC2:=C2.filter (fun c=>s(c,zp2)∈ Ustar G C)
 set MD2:=D2.filter (fun d=>s(z2,d)∈ Ustar G C)
 have q6r:=z125 hL q01 h4 hne q00
  (by have:=z104 hL.1 q5x.1 b1;omega:w1C < n+g2)
  (q2q g1 ((q00 g1).mpr (Or.inl rfl)) b1) q4l
  (show orIn n C w1C=C1 from qci) (fun u hu=>(hf1.2.2.2.1 u hu).symm)
 have q8f:=z125 hL q01 h4 hne q00
  (by have:=z104 hL.1 q5x.1 (1 - b1);omega:w1D < n+g2)
  (q2q g1 ((q00 g1).mpr (Or.inl rfl)) (1 - b1)) q4m
  (show orIn n C w1D=D1 from qb0) (fun u hu=>(hf1.2.2.2.2.1 u hu).symm)
 have q6s:=z125 hL q01 h4 hne q00
  (z104 hL.1 q2p.1 b2)
  (q2q g2 ((q00 g2).mpr (Or.inr rfl)) b2) q2x
  q4n (fun u hu=>(hf2.2.2.2.1 u hu).symm)
 have q8g:=z125 hL q01 h4 hne q00
  (z104 hL.1 q2p.1 (1 - b2))
  (q2q g2 ((q00 g2).mpr (Or.inr rfl)) (1 - b2)) q2y
  q4p (fun u hu=>(hf2.2.2.2.2.1 u hu).symm)
 have qf6:C1.filter (fun u=>s(zp1,u)∈ Ustar G C)=MC1:=by ext u;simp [MC1,Sym2.eq_swap]
 have qf7:C2.filter (fun u=>s(zp2,u)∈ Ustar G C)=MC2:=by ext u;simp [MC2,Sym2.eq_swap]
 dsimp only at q6r q8f q6s q8g
 rw [qf6] at q6r;rw [qf7] at q6s
 have q8h:U1.card=MD1.card+(MC1.erase z1).card:=by
  have q4y:Disjoint (MD1.image fun d=>s(z1,d)) ((MC1.erase z1).image fun c=>s(c,zp1)):=by
   rw [Finset.disjoint_left];intro e h1 h2
   simp only [Z19,Finset.mem_erase] at h1 h2
   rcases h1 with ⟨d,hd,rfl⟩;rcases h2 with ⟨c,⟨hcz,hc⟩,heq⟩
   rw [Sym2.eq_iff] at heq
   rcases heq with ⟨rfl,rfl⟩ | ⟨_,h2'⟩
   ·exact hcz rfl
   ·exact q02 (congrArg s h2'.symm)
  have qii:U1=(MD1.image fun d=>s(z1,d)) ∪ ((MC1.erase z1).image fun c=>s(c,zp1)):=by
   ext e;simp only [U1,E1,z045,Z5,Z4,Z19,Finset.mem_erase,MD1,MC1,Z0]
   constructor
   ·rintro ⟨heU,⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩⟩
    ·exact Or.inl ⟨d,⟨hd,heU⟩,rfl⟩
    ·by_cases hcz:c=z1
     ·subst hcz;exact Or.inl ⟨zp1,⟨hf1.2.2.1,heU⟩,rfl⟩
     ·exact Or.inr ⟨c,⟨hcz,hc,heU⟩,rfl⟩
   ·rintro (⟨d,⟨hd,heU⟩,rfl⟩ | ⟨c,⟨_,hc,heU⟩,rfl⟩)
    ·exact ⟨heU,Or.inl ⟨d,hd,rfl⟩⟩
    ·exact ⟨heU,Or.inr ⟨c,hc,rfl⟩⟩
  rw [qii,Finset.card_union_of_disjoint q4y,
   Finset.card_image_of_injective _ (fun a b h=>by rw [Sym2.eq_iff] at h;rcases h with ⟨_,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl),
   Finset.card_image_of_injective _ (fun a b h=>by rw [Sym2.eq_iff] at h;rcases h with ⟨rfl,_⟩ | ⟨rfl,rfl⟩ <;> rfl)]
 have qbw:U2.card=MD2.card+(MC2.erase z2).card:=by
  have q4y:Disjoint (MD2.image fun d=>s(z2,d)) ((MC2.erase z2).image fun c=>s(c,zp2)):=by
   rw [Finset.disjoint_left];intro e h1 h2
   simp only [Z19,Finset.mem_erase] at h1 h2
   rcases h1 with ⟨d,hd,rfl⟩;rcases h2 with ⟨c,⟨hcz,hc⟩,heq⟩
   rw [Sym2.eq_iff] at heq
   rcases heq with ⟨rfl,rfl⟩ | ⟨_,h2'⟩
   ·exact hcz rfl
   ·exact q03 z2 zp2 hf2.1 (congrArg s h2'.symm)
  have qij:U2=(MD2.image fun d=>s(z2,d)) ∪ ((MC2.erase z2).image fun c=>s(c,zp2)):=by
   ext e;simp only [U2,E2,z045,Z5,Z4,Z19,Finset.mem_erase,MD2,MC2,Z0]
   constructor
   ·rintro ⟨heU,⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩⟩
    ·exact Or.inl ⟨d,⟨hd,heU⟩,rfl⟩
    ·by_cases hcz:c=z2
     ·subst hcz;exact Or.inl ⟨zp2,⟨hf2.2.2.1,heU⟩,rfl⟩
     ·exact Or.inr ⟨c,⟨hcz,hc,heU⟩,rfl⟩
   ·rintro (⟨d,⟨hd,heU⟩,rfl⟩ | ⟨c,⟨_,hc,heU⟩,rfl⟩)
    ·exact ⟨heU,Or.inl ⟨d,hd,rfl⟩⟩
    ·exact ⟨heU,Or.inr ⟨c,hc,rfl⟩⟩
  rw [qij,Finset.card_union_of_disjoint q4y,
   Finset.card_image_of_injective _ (fun a b h=>by rw [Sym2.eq_iff] at h;rcases h with ⟨_,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl),
   Finset.card_image_of_injective _ (fun a b h=>by rw [Sym2.eq_iff] at h;rcases h with ⟨rfl,_⟩ | ⟨rfl,rfl⟩ <;> rfl)]
 set loss1:ℕ:=if MC1=C1∧ MD1=D1 then 1 else 0
 set loss2:ℕ:=if MC2=C2∧ MD2=D2 then 1 else 0
 have qlm:U1.card≤ FacC1.card+FacD1.card+loss1:=by
  rw [q8h]
  by_cases hzM:z1∈ MC1
  ·rw [Finset.card_erase_of_mem hzM]
   have q97:zp1∈ MD1:=Z0.mpr ⟨hf1.2.2.1,(Z0.mp hzM).2⟩
   have qp1:MC1.card≤ FacC1.card+1:=q6r.1 ⟨z1,hzM⟩
   have qp2:MD1.card≤ FacD1.card+1:=q8f.1 ⟨zp1,q97⟩
   by_cases q4z:MC1=C1∧ MD1=D1
   ·simp only [loss1,if_pos q4z];omega
   ·simp only [loss1,if_neg q4z]
    by_cases q75:MC1=C1
    ·have qln:MD1≠ D1:=fun h=>q4z ⟨q75,h⟩
     have hex:∃ r∈ D1,r∉ MD1:=by by_contra h;push Not at h;exact qln (Finset.Subset.antisymm (Finset.filter_subset _ _) h)
     have qlo:MD1.card≤ FacD1.card:=q8f.2 hex;omega
    ·have hex:∃ r∈ C1,r∉ MC1:=by by_contra h;push Not at h;exact q75 (Finset.Subset.antisymm (Finset.filter_subset _ _) h)
     have qlp:MC1.card≤ FacC1.card:=q6r.2 hex;have qj5:=Finset.card_pos.mpr ⟨z1,hzM⟩;omega
  ·rw [Finset.erase_eq_of_notMem hzM]
   have q97:zp1∉ MD1:=fun h=>hzM (Z0.mpr ⟨hf1.2.1,(Z0.mp h).2⟩)
   have qlp:MC1.card≤ FacC1.card:=q6r.2 ⟨z1,hf1.2.1,hzM⟩
   have qlo:MD1.card≤ FacD1.card:=q8f.2 ⟨zp1,hf1.2.2.1,q97⟩
   omega
 have qlq:U2.card≤ FacC2.card+FacD2.card+loss2:=by
  rw [qbw]
  by_cases hzM:z2∈ MC2
  ·rw [Finset.card_erase_of_mem hzM]
   have q97:zp2∈ MD2:=Z0.mpr ⟨hf2.2.2.1,(Z0.mp hzM).2⟩
   have qp3:MC2.card≤ FacC2.card+1:=q6s.1 ⟨z2,hzM⟩
   have qp4:MD2.card≤ FacD2.card+1:=q8g.1 ⟨zp2,q97⟩
   by_cases q4z:MC2=C2∧ MD2=D2
   ·simp only [loss2,if_pos q4z];omega
   ·simp only [loss2,if_neg q4z]
    by_cases q75:MC2=C2
    ·have qln:MD2≠ D2:=fun h=>q4z ⟨q75,h⟩
     have hex:∃ r∈ D2,r∉ MD2:=by by_contra h;push Not at h;exact qln (Finset.Subset.antisymm (Finset.filter_subset _ _) h)
     have qlr:MD2.card≤ FacD2.card:=q8g.2 hex;omega
    ·have hex:∃ r∈ C2,r∉ MC2:=by by_contra h;push Not at h;exact q75 (Finset.Subset.antisymm (Finset.filter_subset _ _) h)
     have qls:MC2.card≤ FacC2.card:=q6s.2 hex;have qj5:=Finset.card_pos.mpr ⟨z2,hzM⟩;omega
  ·rw [Finset.erase_eq_of_notMem hzM]
   have q97:zp2∉ MD2:=fun h=>hzM (Z0.mpr ⟨hf2.2.1,(Z0.mp h).2⟩)
   have qls:MC2.card≤ FacC2.card:=q6s.2 ⟨z2,hf2.2.1,hzM⟩
   have qlr:MD2.card≤ FacD2.card:=q8g.2 ⟨zp2,hf2.2.2.1,q97⟩
   omega
 let isOwn:Fin n→ Prop:=fun v=>∃ a∈ tops G C \ centreless G C,z126 C s z1 g1 g2 a=v
 set MD1_ns:=MD1.erase zp1
 set MC1_ns:=MC1.erase z1
 set MD2_ns:=(D2.erase zp2).filter (fun d=>s(z2,d)∈ U2 \ U1)
 set MC2_ns:=(C2.erase z2).filter (fun c=>s(c,zp2)∈ U2 \ U1)
 let e1_to_z1:Prop:=MD1_ns.Nonempty∨ isOwn z1∨ ¬ MC1_ns.Nonempty
 let e2_to_z2:Prop:=MD2_ns.Nonempty∨ isOwn z2∨ ¬ MC2_ns.Nonempty
 let L:Fin n→ Finset (Fin n):=fun v=>
  if v=z1 then (if s(z1,zp1)∈ U1∧ e1_to_z1 then insert zp1 MD1_ns else MD1_ns)
  else if v=zp1 then (if s(z1,zp1)∈ U1∧ ¬ e1_to_z1 then insert z1 MC1_ns else MC1_ns)
  else if v=z2 then (if s(z2,zp2)∈ U2∧ e2_to_z2 then insert zp2 MD2_ns else MD2_ns)
  else if v=zp2 then (if s(z2,zp2)∈ U2∧ ¬ e2_to_z2 then insert z2 MC2_ns else MC2_ns)
  else ∅
 have qcw:L z1=if s(z1,zp1)∈ U1∧ e1_to_z1 then insert zp1 MD1_ns else MD1_ns:=by simp [L]
 have q6t:L zp1=if s(z1,zp1)∈ U1∧ ¬ e1_to_z1 then insert z1 MC1_ns else MC1_ns:=by simp [L,q2h.symm]
 have qcx:L z2=if s(z2,zp2)∈ U2∧ e2_to_z2 then insert zp2 MD2_ns else MD2_ns:=by simp [L,q5z.symm,q20]
 have q6u:L zp2=if s(z2,zp2)∈ U2∧ ¬ e2_to_z2 then insert z2 MC2_ns else MC2_ns:=by simp [L,q1z.symm,q0h.symm,q2i.symm]
 have qbx:({z1,zp1,z2,zp2}:Finset (Fin n)).card=4:=by
  rw [Z24 (by simp [q2h,q5z,q1z]),
   Z24 (by simp [q20.symm,q0h]),Finset.card_pair q2i]
 set Zact:=({z1,zp1,z2,zp2}:Finset (Fin n)).filter (fun v=>(L v).Nonempty)
 set Zhas:=Zact.filter isOwn
 set Znew:=Zact \ Zhas
 have qf8:s(z2,zp2)∉ U1:=by
  intro h
  have hE1:=(Z5.mp h).2
  simp only [E1,z045,Z4,Z19,Sym2.eq_iff] at hE1
  rcases hE1 with ⟨d,hd,⟨h1,_⟩ | ⟨h1,_⟩⟩ | ⟨c,hc,⟨_,h2⟩ | ⟨h1,_⟩⟩
  ·exact q5z h1
  ·exact q02 (by rw [h1,← q1l])
  ·exact q0h h2
  ·exact q02 ((z046 q03 hf1 hc).symm.trans (by rw [h1];exact q1l.symm))
 have q8w:∀ e∈ Ustar G C,∃ v∈ Zact,∃ u∈ L v,e=s(v,u):=by
  intro e he
  rw [q4q,Z4] at he
  by_cases he1:e∈ U1
  ·have hE1:=(Z5.mp he1).2
   have heU:=(Z5.mp he1).1
   simp only [E1,z045,Z4,Z19] at hE1
   rcases hE1 with ⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩
   ·by_cases q1e:d=zp1
    ·rw [q1e] at he1 ⊢
     by_cases q3o:e1_to_z1
     ·refine ⟨z1,Z0.mpr ⟨by simp,⟨zp1,by rw [qcw,if_pos ⟨he1,q3o⟩];simp⟩⟩,
       zp1,by rw [qcw,if_pos ⟨he1,q3o⟩];simp,rfl⟩
     ·refine ⟨zp1,Z0.mpr ⟨by simp,⟨z1,by rw [q6t,if_pos ⟨he1,q3o⟩];simp⟩⟩,
       z1,by rw [q6t,if_pos ⟨he1,q3o⟩];simp,Sym2.eq_swap⟩
    ·have q7s:d∈ MD1_ns:=Finset.mem_erase.mpr ⟨q1e,Z0.mpr ⟨hd,heU⟩⟩
     have hdL:d∈ L z1:=by rw [qcw];split_ifs;exact Finset.mem_insert_of_mem q7s;exact q7s
     exact ⟨z1,Z0.mpr ⟨by simp,⟨d,hdL⟩⟩,d,hdL,rfl⟩
   ·by_cases hcz:c=z1
    ·rw [hcz] at he1 ⊢
     by_cases q3o:e1_to_z1
     ·refine ⟨z1,Z0.mpr ⟨by simp,⟨zp1,by rw [qcw,if_pos ⟨he1,q3o⟩];simp⟩⟩,
       zp1,by rw [qcw,if_pos ⟨he1,q3o⟩];simp,rfl⟩
     ·refine ⟨zp1,Z0.mpr ⟨by simp,⟨z1,by rw [q6t,if_pos ⟨he1,q3o⟩];simp⟩⟩,
       z1,by rw [q6t,if_pos ⟨he1,q3o⟩];simp,Sym2.eq_swap⟩
    ·have q7t:c∈ MC1_ns:=Finset.mem_erase.mpr ⟨hcz,Z0.mpr ⟨hc,heU⟩⟩
     have hcL:c∈ L zp1:=by rw [q6t];split_ifs;exact Finset.mem_insert_of_mem q7t;exact q7t
     exact ⟨zp1,Z0.mpr ⟨by simp,⟨c,hcL⟩⟩,c,hcL,Sym2.eq_swap⟩
  ·have he2:e∈ U2:=he.resolve_left he1
   have qn7:e∈ U2 \ U1:=Z2.mpr ⟨he2,he1⟩
   have hE2:=(Z5.mp he2).2
   simp only [E2,z045,Z4,Z19] at hE2
   rcases hE2 with ⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩
   ·by_cases q1e:d=zp2
    ·rw [q1e] at he2 ⊢
     by_cases q3o:e2_to_z2
     ·refine ⟨z2,Z0.mpr ⟨by simp,⟨zp2,by rw [qcx,if_pos ⟨he2,q3o⟩];simp⟩⟩,
       zp2,by rw [qcx,if_pos ⟨he2,q3o⟩];simp,rfl⟩
     ·refine ⟨zp2,Z0.mpr ⟨by simp,⟨z2,by rw [q6u,if_pos ⟨he2,q3o⟩];simp⟩⟩,
       z2,by rw [q6u,if_pos ⟨he2,q3o⟩];simp,Sym2.eq_swap⟩
    ·have q7s:d∈ MD2_ns:=Z0.mpr ⟨Finset.mem_erase.mpr ⟨q1e,hd⟩,qn7⟩
     have hdL:d∈ L z2:=by rw [qcx];split_ifs;exact Finset.mem_insert_of_mem q7s;exact q7s
     exact ⟨z2,Z0.mpr ⟨by simp,⟨d,hdL⟩⟩,d,hdL,rfl⟩
   ·by_cases hcz:c=z2
    ·rw [hcz] at he2 ⊢
     by_cases q3o:e2_to_z2
     ·refine ⟨z2,Z0.mpr ⟨by simp,⟨zp2,by rw [qcx,if_pos ⟨he2,q3o⟩];simp⟩⟩,
       zp2,by rw [qcx,if_pos ⟨he2,q3o⟩];simp,rfl⟩
     ·refine ⟨zp2,Z0.mpr ⟨by simp,⟨z2,by rw [q6u,if_pos ⟨he2,q3o⟩];simp⟩⟩,
       z2,by rw [q6u,if_pos ⟨he2,q3o⟩];simp,Sym2.eq_swap⟩
    ·have q7t:c∈ MC2_ns:=Z0.mpr ⟨Finset.mem_erase.mpr ⟨hcz,hc⟩,qn7⟩
     have hcL:c∈ L zp2:=by rw [q6u];split_ifs;exact Finset.mem_insert_of_mem q7t;exact q7t
     exact ⟨zp2,Z0.mpr ⟨by simp,⟨c,hcL⟩⟩,c,hcL,Sym2.eq_swap⟩
 have qp5:(L z1).card+(L zp1).card=U1.card:=by
  rw [q8h,qcw,q6t]
  have qf9:zp1∉ MD1_ns:=Finset.notMem_erase _ _
  have qlt:z1∉ MC1_ns:=Finset.notMem_erase _ _
  by_cases he1:s(z1,zp1)∈ U1
  ·have q97:zp1∈ MD1:=Z0.mpr ⟨hf1.2.2.1,(Z5.mp he1).1⟩
   have qam:MD1_ns.card+1=MD1.card:=by
    rw [Finset.card_erase_of_mem q97];have:=Finset.card_pos.mpr ⟨zp1,q97⟩;omega
   by_cases q3o:e1_to_z1 <;> simp [he1,q3o,qf9,qlt] <;> omega
  ·have q97:zp1∉ MD1:=fun h=>he1 (Z5.mpr ⟨(Z0.mp h).2,
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ hf1.2.2.1)⟩)
   have qam:MD1_ns=MD1:=Finset.erase_eq_of_notMem q97
   simp [he1,qam]
 have qp6:(L z2).card+(L zp2).card=(U2 \ U1).card:=by
  have qfa:U2 \ U1=(MD2_ns.image fun d=>s(z2,d)) ∪ (MC2_ns.image fun c=>s(c,zp2)) ∪
    (if s(z2,zp2)∈ U2 then {s(z2,zp2)} else ∅):=by
   ext e;simp only [Z4,Z19,MD2_ns,MC2_ns,Z0,Finset.mem_erase]
   constructor
   ·intro he
    have he2:=(Z2.mp he).1
    have hE2:=(Z5.mp he2).2
    simp only [E2,z045,Z4,Z19] at hE2
    rcases hE2 with ⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩
    ·by_cases q1e:d=zp2
     ·subst q1e;right;rw [if_pos he2];exact Finset.mem_singleton_self _
     ·left;left;exact ⟨d,⟨⟨q1e,hd⟩,he⟩,rfl⟩
    ·by_cases hcz:c=z2
     ·subst hcz;right;rw [if_pos he2];exact Finset.mem_singleton_self _
     ·left;right;exact ⟨c,⟨⟨hcz,hc⟩,he⟩,rfl⟩
   ·rintro ((⟨d,⟨_,he⟩,rfl⟩ | ⟨c,⟨_,he⟩,rfl⟩) | hsp)
    ·exact he
    ·exact he
    ·split_ifs at hsp with he2
     ·rw [Z3] at hsp;subst hsp;exact Z2.mpr ⟨he2,qf8⟩
     ·exact absurd hsp (Finset.notMem_empty _)
  have qp7:Disjoint (MD2_ns.image fun d=>s(z2,d)) (MC2_ns.image fun c=>s(c,zp2)):=by
   rw [Finset.disjoint_left];intro e h1 h2
   simp only [Z19,MD2_ns,MC2_ns,Z0,Finset.mem_erase] at h1 h2
   rcases h1 with ⟨d,⟨⟨q1e,hd⟩,_⟩,rfl⟩;rcases h2 with ⟨c,⟨⟨hcz,hc⟩,_⟩,heq⟩
   rw [Sym2.eq_iff] at heq
   rcases heq with ⟨rfl,rfl⟩ | ⟨_,h2'⟩
   ·exact hcz rfl
   ·exact q03 z2 zp2 hf2.1 (congrArg s h2'.symm)
  have hd3:Disjoint ((MD2_ns.image fun d=>s(z2,d)) ∪ (MC2_ns.image fun c=>s(c,zp2)))
    (if s(z2,zp2)∈ U2 then {s(z2,zp2)} else ∅):=by
   rw [Finset.disjoint_right];intro e he hU
   split_ifs at he with he2
   ·rw [Z3] at he;subst he
    simp only [Z4,Z19,MD2_ns,MC2_ns,Z0,Finset.mem_erase,Sym2.eq_iff] at hU
    rcases hU with ⟨d,⟨⟨q1e,_⟩,_⟩,⟨_,h⟩ | ⟨h,_⟩⟩ | ⟨c,⟨⟨hcz,_⟩,_⟩,⟨h,_⟩ | ⟨_,h⟩⟩
    ·exact q1e h
    ·exact q2i h
    ·exact hcz h
    ·exact q2i h.symm
   ·exact absurd he (Finset.notMem_empty _)
  have qan:(U2 \ U1).card=MD2_ns.card+MC2_ns.card+(if s(z2,zp2)∈ U2 then 1 else 0):=by
   rw [qfa,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint qp7,
    Finset.card_image_of_injective _ (fun a b h=>by rw [Sym2.eq_iff] at h;rcases h with ⟨_,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl),
    Finset.card_image_of_injective _ (fun a b h=>by rw [Sym2.eq_iff] at h;rcases h with ⟨rfl,_⟩ | ⟨rfl,rfl⟩ <;> rfl)]
   split_ifs <;> simp
  rw [qan,qcx,q6u]
  have qf9:zp2∉ MD2_ns:=fun h=>(Finset.mem_erase.mp (Z0.mp h).1).1 rfl
  have qlt:z2∉ MC2_ns:=fun h=>(Finset.mem_erase.mp (Z0.mp h).1).1 rfl
  by_cases he2:s(z2,zp2)∈ U2 <;> by_cases q3o:e2_to_z2 <;>
   simp [he2,q3o,qf9,qlt] <;> omega
 have qc7:(∑ v∈ Zact,(L v).card)≤ (Ustar G C).card:=by
  have qdn:∑ v∈ Zact,(L v).card≤ ∑ v∈ ({z1,zp1,z2,zp2}:Finset (Fin n)),(L v).card:=
   Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have qp8:∑ v∈ ({z1,zp1,z2,zp2}:Finset (Fin n)),(L v).card=
    (L z1).card+(L zp1).card+(L z2).card+(L zp2).card:=by
   rw [Finset.sum_insert (by simp [q2h,q5z,q1z]),
    Finset.sum_insert (by simp [q20.symm,q0h]),Finset.sum_pair q2i];omega
  have qn8:(Ustar G C).card=U1.card+(U2 \ U1).card:=by
   have q4y:Disjoint U1 (U2 \ U1):=Finset.disjoint_sdiff
   rw [show Ustar G C=U1 ∪ (U2 \ U1) by rw [q4q,Finset.union_sdiff_self_eq_union],
    Finset.card_union_of_disjoint q4y]
  omega
 let topOf:Fin n→ ℕ:=fun v=>if h:isOwn v then Classical.choose h else 0
 have q55:=z093 hL q01 h4 qdf q00 hne Zact Zhas L topOf
  (Finset.filter_subset _ _)
  (fun v hv=>(Z0.mp hv).2)
  (fun v hv u hu=>by
   have hv':=(Z0.mp hv).1
   simp only [Z6,Z3] at hv'
   rcases hv' with rfl | rfl | rfl | rfl
   ·rw [qcw] at hu;split_ifs at hu
    ·rcases Z6.mp hu with rfl | hu
     ·exact hf1.1
     ·exact (hf1.2.2.2.2.1 u (Z0.mp (Finset.mem_of_mem_erase hu)).1).symm
    ·exact (hf1.2.2.2.2.1 u (Z0.mp (Finset.mem_of_mem_erase hu)).1).symm
   ·rw [q6t] at hu;split_ifs at hu
    ·rcases Z6.mp hu with rfl | hu
     ·exact hf1.1.symm
     ·exact (hf1.2.2.2.1 u (Z0.mp (Finset.mem_of_mem_erase hu)).1).symm
    ·exact (hf1.2.2.2.1 u (Z0.mp (Finset.mem_of_mem_erase hu)).1).symm
   ·rw [qcx] at hu;split_ifs at hu
    ·rcases Z6.mp hu with rfl | hu
     ·exact hf2.1
     ·exact (hf2.2.2.2.2.1 u (Finset.mem_of_mem_erase (Z0.mp hu).1)).symm
    ·exact (hf2.2.2.2.2.1 u (Finset.mem_of_mem_erase (Z0.mp hu).1)).symm
   ·rw [q6u] at hu;split_ifs at hu
    ·rcases Z6.mp hu with rfl | hu
     ·exact hf2.1.symm
     ·exact (hf2.2.2.2.1 u (Finset.mem_of_mem_erase (Z0.mp hu).1)).symm
    ·exact (hf2.2.2.2.1 u (Finset.mem_of_mem_erase (Z0.mp hu).1)).symm)
  q8w
  (fun v hv=>by have h:=(Z0.mp hv).2;simp only [topOf,dif_pos h];exact (Classical.choose_spec h).1)
  (fun v hv=>by
   have h:=(Z0.mp hv).2;simp only [topOf,dif_pos h]
   have hsp:=Classical.choose_spec h
   have q3f:=z128 hL.1 h4 s z1 g1 g2 hsp.1
   rwa [hsp.2] at q3f)
  (fun v1 hv1 v2 hv2 heq=>by
   have h1:=(Z0.mp hv1).2;have h2:=(Z0.mp hv2).2
   simp only [topOf,dif_pos h1,dif_pos h2] at heq
   have qhm:=Classical.choose_spec h1;have qhn:=Classical.choose_spec h2
   rw [← qhm.2,heq,qhn.2])
 have qg5:(Ustar G C).card+U12.card=U1.card+U2.card:=by
  rw [q4q];exact Finset.card_union_add_card_inter U1 U2
 have qgc:2 * (centreless G C).card+Extra.card+U12.card+2≤ Znew.card+loss1+loss2:=by
  have qn9:2 * (centreless G C).card+(orN G C \ lam G C).card+2≤
    (∑ v∈ Zact,(L v).card)+Znew.card:=q55
  omega
 let A1_edge:Fin n→ Prop:=fun v=>
  (v=z1∧ ∃ d∈ D1.erase zp1,s(z1,d)∈ U1 \ E2)∨
  (v=zp1∧ ∃ c∈ C1.erase z1,s(c,zp1)∈ U1 \ E2)
 let A2_edge:Fin n→ Prop:=fun v=>
  (v=z2∧ ∃ d∈ D2.erase zp2,s(z2,d)∈ U2 \ E1)∨
  (v=zp2∧ ∃ c∈ C2.erase z2,s(c,zp2)∈ U2 \ E1)
 set A1:=(Znew ∩ {z1,zp1}).filter (fun v=>
  A1_edge v∧ ∃ a∈ centreless G C,∃ b:Fin 2,side (n:=n) C a b=∅∧ OrReaches n C (opnd C a b) g1∧ v∈ side (n:=n) C a (1 - b))
 set A2:=(Znew ∩ {z2,zp2}).filter (fun v=>
  A2_edge v∧ ∃ a∈ centreless G C,∃ b:Fin 2,side (n:=n) C a b=∅∧ OrReaches n C (opnd C a b) g2∧ v∈ side (n:=n) C a (1 - b))
 set Zconf:=(Znew \ (A1 ∪ A2)).filter (fun v=>
  s v=s zp1∧ ∃ mv∈ Extra,orIn n C (n+mv)={v}∧
   ∃ u':Fin n,s u'=s z1∧ ∃ mu∈ Extra,orIn n C (n+mu)={u'})
 have qao:∀ v∈ Znew ∩ {z1,zp1},A1_edge v→ v∈ A1∨ v∈ Zconf:=by
  intro v hv qfb
  have q2k:v∈ Znew:=(Z5.mp hv).1
  have q21:¬ isOwn v:=fun ho=>(Z2.mp q2k).2 (Z0.mpr ⟨(Z2.mp q2k).1,ho⟩)
  rcases qfb with ⟨q30,d,hd,hzd⟩ | ⟨q30,c,hc,qbk⟩
  ·rw [q30] at hv q2k q21 ⊢
   have q1e:d≠ zp1:=(Finset.mem_erase.mp hd).1
   have qlu:d∈ D1:=Finset.mem_of_mem_erase hd
   have qlv:s(z1,d)∈ Ustar G C:=(Z5.mp (Z2.mp hzd).1).1
   have qfc:s(z1,d)∉ E2:=(Z2.mp hzd).2
   have qbu:gateVal n C g2 (pairInput z1 d)=false:=by
    rw [Z14,ne_eq,z052 q03 h4 hf2 (hf1.2.2.2.2.1 d qlu).symm];exact qfc
   have hnw:
     (gateVal n C g1 (pairInput z1 d)=true→
      (¬ ∀ x,gateVal n C g1 x=true→ x d=true→ graphFun G ∅ x=true)∧
      (∀ w:Fin n,s w=s z1→ (∀ x,gateVal n C g1 x=true→ x w=true→ graphFun G ∅ x=true)→ G.Adj w d))∧
     (gateVal n C g2 (pairInput z1 d)=true→
      (¬ ∀ x,gateVal n C g2 x=true→ x d=true→ graphFun G ∅ x=true)∧
      (∀ w:Fin n,s w=s z1→ (∀ x,gateVal n C g2 x=true→ x w=true→ graphFun G ∅ x=true)→ G.Adj w d)):=
    ⟨fun _=>⟨z056 h4 hf1 qlu q1e,fun w hsw hw=>z054 q03 h4 hf1 hw hsw qlu q1e⟩,
    fun h2=>(by rw [qbu] at h2;cases h2)⟩
   rcases z072 q03 h4 hL q01 q00 hf1 hf2 hsz q1l qlv hnw
     (fun h=>by rw [qbu] at h;cases h.2.1) with
    hA | ⟨a,haC,b,g,hg,hgv,q0g,hrb,hzs⟩ | ⟨qa2,_⟩
   ·exact absurd hA q21
   ·have q56:g=g1:=hg.resolve_right (fun h=>by rw [h,qbu] at hgv;cases hgv)
    rw [q56] at hrb
    exact Or.inl (Z0.mpr ⟨hv,Or.inl ⟨rfl,d,hd,hzd⟩,a,haC,b,q0g,hrb,hzs⟩)
   ·exact absurd qa2 q02
  ·rw [q30] at hv q2k q21 ⊢
   have qna:c≠ z1:=(Finset.mem_erase.mp hc).1
   have qlw:c∈ C1:=Finset.mem_of_mem_erase hc
   have qfd:s(zp1,c)∈ Ustar G C:=by rw [Sym2.eq_swap];exact (Z5.mp (Z2.mp qbk).1).1
   have qby:s(zp1,c)∉ E2:=by rw [Sym2.eq_swap];exact (Z2.mp qbk).2
   have qbu:gateVal n C g2 (pairInput zp1 c)=false:=by
    rw [Z14,ne_eq,z052 q03 h4 hf2 (hf1.2.2.2.1 c qlw).symm];exact qby
   have hnw:
     (gateVal n C g1 (pairInput zp1 c)=true→
      (¬ ∀ x,gateVal n C g1 x=true→ x c=true→ graphFun G ∅ x=true)∧
      (∀ w:Fin n,s w=s zp1→ (∀ x,gateVal n C g1 x=true→ x w=true→ graphFun G ∅ x=true)→ G.Adj w c))∧
     (gateVal n C g2 (pairInput zp1 c)=true→
      (¬ ∀ x,gateVal n C g2 x=true→ x c=true→ graphFun G ∅ x=true)∧
      (∀ w:Fin n,s w=s zp1→ (∀ x,gateVal n C g2 x=true→ x w=true→ graphFun G ∅ x=true)→ G.Adj w c)):=
    ⟨fun _=>⟨z055 h4 hf1 qlw qna,fun w hsw hw=>z053 q03 h4 hf1 hw hsw qlw qna⟩,
    fun h2=>(by rw [qbu] at h2;cases h2)⟩
   rcases z072 q03 h4 hL q01 q00 hf1 hf2 hsz q1l qfd hnw
     (fun h=>by rw [qbu] at h;cases h.2.1) with
    hA | ⟨a,haC,b,g,hg,hgv,q0g,hrb,hzs⟩ | ⟨hsv,_,_,_,g,hg,hgv,_,_,g',hg',_,_,mv,hmv,q38,q05,u',_,q24,mu,hmu,q3j,q06⟩
   ·exact absurd hA q21
   ·have q56:g=g1:=hg.resolve_right (fun h=>by rw [h,qbu] at hgv;cases hgv)
    rw [q56] at hrb
    exact Or.inl (Z0.mpr ⟨hv,Or.inr ⟨rfl,c,hc,qbk⟩,a,haC,b,q0g,hrb,hzs⟩)
   ·by_cases hA1:zp1∈ A1
    ·exact Or.inl hA1
    ·right
     have qp9:zp1∉ A2:=fun h=>by
      have:=(Z5.mp (Z0.mp h).1).2
      simp only [Z6,Z3] at this
      exact this.elim q20.symm q0h
     have qfe:mv∈ Extra:=q0w mv hmv (hg'.imp (fun h=>by rwa [← h]) (fun h=>by rwa [← h]))
     have qap:mu∈ Extra:=q0w mu hmu (hg.imp (fun h=>by rwa [← h]) (fun h=>by rwa [← h]))
     exact Z0.mpr ⟨Z2.mpr ⟨q2k,fun h=>(Z4.mp h).elim hA1 qp9⟩,
      hsv,mv,qfe,q05,u',q24,mu,qap,q06⟩
 have qaq:∀ v∈ Znew ∩ {z2,zp2},A2_edge v→ v∈ A2∨ v∈ Zconf:=by
  intro v hv qfb
  have q2k:v∈ Znew:=(Z5.mp hv).1
  have q21:¬ isOwn v:=fun ho=>(Z2.mp q2k).2 (Z0.mpr ⟨(Z2.mp q2k).1,ho⟩)
  rcases qfb with ⟨q30,d,hd,hzd⟩ | ⟨q30,c,hc,qbk⟩
  ·rw [q30] at hv q2k q21 ⊢
   have q1e:d≠ zp2:=(Finset.mem_erase.mp hd).1
   have q4e:d∈ D2:=Finset.mem_of_mem_erase hd
   have qlv:s(z2,d)∈ Ustar G C:=(Z5.mp (Z2.mp hzd).1).1
   have qff:s(z2,d)∉ E1:=(Z2.mp hzd).2
   have qbv:gateVal n C g1 (pairInput z2 d)=false:=by
    rw [Z14,ne_eq,z052 q03 h4 hf1 (hf2.2.2.2.2.1 d q4e).symm];exact qff
   have hnw:
     (gateVal n C g1 (pairInput z2 d)=true→
      (¬ ∀ x,gateVal n C g1 x=true→ x d=true→ graphFun G ∅ x=true)∧
      (∀ w:Fin n,s w=s z2→ (∀ x,gateVal n C g1 x=true→ x w=true→ graphFun G ∅ x=true)→ G.Adj w d))∧
     (gateVal n C g2 (pairInput z2 d)=true→
      (¬ ∀ x,gateVal n C g2 x=true→ x d=true→ graphFun G ∅ x=true)∧
      (∀ w:Fin n,s w=s z2→ (∀ x,gateVal n C g2 x=true→ x w=true→ graphFun G ∅ x=true)→ G.Adj w d)):=
    ⟨fun h1=>(by rw [qbv] at h1;cases h1),
    fun _=>⟨z056 h4 hf2 q4e q1e,fun w hsw hw=>z054 q03 h4 hf2 hw hsw q4e q1e⟩⟩
   rcases z072 q03 h4 hL q01 q00 hf1 hf2 hsz q1l qlv hnw
     (fun h=>by rw [qbv] at h;cases h.1) with
    hA | ⟨a,haC,b,g,hg,hgv,q0g,hrb,hzs⟩ | ⟨qa2,_⟩
   ·exact absurd hA q21
   ·have q56:g=g2:=hg.resolve_left (fun h=>by rw [h,qbv] at hgv;cases hgv)
    rw [q56] at hrb
    exact Or.inl (Z0.mpr ⟨hv,Or.inl ⟨rfl,d,hd,hzd⟩,a,haC,b,q0g,hrb,hzs⟩)
   ·exact absurd (hsz.trans qa2) q02
  ·rw [q30] at hv q2k q21 ⊢
   have qnb:c≠ z2:=(Finset.mem_erase.mp hc).1
   have q4d:c∈ C2:=Finset.mem_of_mem_erase hc
   have qfd:s(zp2,c)∈ Ustar G C:=by rw [Sym2.eq_swap];exact (Z5.mp (Z2.mp qbk).1).1
   have qbz:s(zp2,c)∉ E1:=by rw [Sym2.eq_swap];exact (Z2.mp qbk).2
   have qbv:gateVal n C g1 (pairInput zp2 c)=false:=by
    rw [Z14,ne_eq,z052 q03 h4 hf1 (hf2.2.2.2.1 c q4d).symm];exact qbz
   have hnw:
     (gateVal n C g1 (pairInput zp2 c)=true→
      (¬ ∀ x,gateVal n C g1 x=true→ x c=true→ graphFun G ∅ x=true)∧
      (∀ w:Fin n,s w=s zp2→ (∀ x,gateVal n C g1 x=true→ x w=true→ graphFun G ∅ x=true)→ G.Adj w c))∧
     (gateVal n C g2 (pairInput zp2 c)=true→
      (¬ ∀ x,gateVal n C g2 x=true→ x c=true→ graphFun G ∅ x=true)∧
      (∀ w:Fin n,s w=s zp2→ (∀ x,gateVal n C g2 x=true→ x w=true→ graphFun G ∅ x=true)→ G.Adj w c)):=
    ⟨fun h1=>(by rw [qbv] at h1;cases h1),
    fun _=>⟨z055 h4 hf2 q4d qnb,fun w hsw hw=>z053 q03 h4 hf2 hw hsw q4d qnb⟩⟩
   rcases z072 q03 h4 hL q01 q00 hf1 hf2 hsz q1l qfd hnw
     (fun h=>by rw [qbv] at h;cases h.1) with
    hA | ⟨a,haC,b,g,hg,hgv,q0g,hrb,hzs⟩ | ⟨hsv,_,_,_,g,hg,hgv,_,_,g',hg',_,_,mv,hmv,q38,q05,u',_,q24,mu,hmu,q3j,q06⟩
   ·exact absurd hA q21
   ·have q56:g=g2:=hg.resolve_left (fun h=>by rw [h,qbv] at hgv;cases hgv)
    rw [q56] at hrb
    exact Or.inl (Z0.mpr ⟨hv,Or.inr ⟨rfl,c,hc,qbk⟩,a,haC,b,q0g,hrb,hzs⟩)
   ·by_cases hA2:zp2∈ A2
    ·exact Or.inl hA2
    ·right
     have qpa:zp2∉ A1:=fun h=>by
      have:=(Z5.mp (Z0.mp h).1).2
      simp only [Z6,Z3] at this
      exact this.elim q1z.symm q0h.symm
     have qfe:mv∈ Extra:=q0w mv hmv (hg'.imp (fun h=>by rwa [← h]) (fun h=>by rwa [← h]))
     have qap:mu∈ Extra:=q0w mu hmu (hg.imp (fun h=>by rwa [← h]) (fun h=>by rwa [← h]))
     exact Z0.mpr ⟨Z2.mpr ⟨q2k,fun h=>(Z4.mp h).elim qpa hA2⟩,
      hsv,mv,qfe,q05,u',q24,mu,qap,q06⟩
 have qjh:(Znew ∩ {z1,zp1}).card+loss1≤ A1.card+(Zconf ∩ {zp1}).card+1+U12.card:=by
  have q3e:A1 ∪ (Zconf ∩ {zp1})⊆ Znew ∩ {z1,zp1}:=by
   refine Finset.union_subset (Finset.filter_subset _ _) ?_
   intro v hv;have h1:=(Z5.mp hv).1;have h2:=(Z5.mp hv).2
   rw [Z3] at h2;subst h2
   exact Z5.mpr ⟨(Z2.mp (Z0.mp h1).1).1,by simp⟩
  have qc8:Disjoint A1 (Zconf ∩ {zp1}):=by
   rw [Finset.disjoint_left];intro v hv1 hv2
   exact (Z2.mp (Z0.mp (Z5.mp hv2).1).1).2 (Finset.mem_union_left _ hv1)
  have qfg:(A1 ∪ (Zconf ∩ {zp1})).card=A1.card+(Zconf ∩ {zp1}).card:=
   Finset.card_union_of_disjoint qc8
  have qfh:z1∈ Znew→ (∃ d∈ MD1_ns,s(z1,d)∉ E2)→ z1∈ A1 ∪ (Zconf ∩ {zp1}):=by
   intro qik ⟨d,hd,qfi⟩
   have qil:=Finset.mem_erase.mp hd
   have q98:=Z0.mp qil.2
   have hU1:s(z1,d)∈ U1:=Z5.mpr ⟨q98.2,Finset.mem_union_left _ (Finset.mem_image_of_mem _ q98.1)⟩
   rcases qao z1 (Z5.mpr ⟨qik,by simp⟩)
     (Or.inl ⟨rfl,d,Finset.mem_erase.mpr ⟨qil.1,q98.1⟩,Z2.mpr ⟨hU1,qfi⟩⟩) with hA | hC
   ·exact Finset.mem_union_left _ hA
   ·exact absurd (Z0.mp hC).2.1 q02
  have qc0:zp1∈ Znew→ (∃ c∈ MC1_ns,s(c,zp1)∉ E2)→ zp1∈ A1 ∪ (Zconf ∩ {zp1}):=by
   intro qar ⟨c,hc,qfi⟩
   have qim:=Finset.mem_erase.mp hc
   have q99:=Z0.mp qim.2
   have hU1:s(c,zp1)∈ U1:=Z5.mpr ⟨q99.2,Finset.mem_union_right _ (Finset.mem_image_of_mem _ q99.1)⟩
   rcases qao zp1 (Z5.mpr ⟨qar,by simp⟩)
     (Or.inr ⟨rfl,c,Finset.mem_erase.mpr ⟨qim.1,q99.1⟩,Z2.mpr ⟨hU1,qfi⟩⟩) with hA | hC
   ·exact Finset.mem_union_left _ hA
   ·exact Finset.mem_union_right _ (Z5.mpr ⟨hC,by simp⟩)
  have qpm:((Znew ∩ {z1,zp1}) \ (A1 ∪ (Zconf ∩ {zp1}))).card+loss1≤ 1+U12.card:=by
   set R:=(Znew ∩ {z1,zp1}) \ (A1 ∪ (Zconf ∩ {zp1}))
   have qas:R⊆ {z1,zp1}:=Finset.Subset.trans Finset.sdiff_subset Finset.inter_subset_right
   have qpb:R.card≤ 2:=(Finset.card_le_card qas).trans (by rw [Finset.card_pair q2h])
   have q3c:z1∈ R→ ∀ d∈ MD1_ns,s(z1,d)∈ U12:=by
    intro hR d hd
    have q98:=Z0.mp (Finset.mem_of_mem_erase hd)
    have hU1:s(z1,d)∈ U1:=Z5.mpr ⟨q98.2,Finset.mem_union_left _ (Finset.mem_image_of_mem _ q98.1)⟩
    by_contra hnu
    have qfi:s(z1,d)∉ E2:=fun h=>hnu (Z5.mpr ⟨hU1,Z5.mpr ⟨q98.2,h⟩⟩)
    exact (Z2.mp hR).2 (qfh (Z5.mp (Z2.mp hR).1).1 ⟨d,hd,qfi⟩)
   have q2u:zp1∈ R→ ∀ c∈ MC1_ns,s(c,zp1)∈ U12:=by
    intro hR c hc
    have q99:=Z0.mp (Finset.mem_of_mem_erase hc)
    have hU1:s(c,zp1)∈ U1:=Z5.mpr ⟨q99.2,Finset.mem_union_right _ (Finset.mem_image_of_mem _ q99.1)⟩
    by_contra hnu
    have qfi:s(c,zp1)∉ E2:=fun h=>hnu (Z5.mpr ⟨hU1,Z5.mpr ⟨q99.2,h⟩⟩)
    exact (Z2.mp hR).2 (qc0 (Z5.mp (Z2.mp hR).1).1 ⟨c,hc,qfi⟩)
   have q91:zp1∈ Znew→ MC1_ns.Nonempty:=by
    intro qar
    have q8q:(L zp1).Nonempty:=(Z0.mp (Z2.mp qar).1).2
    by_contra q0g
    have q3o:e1_to_z1:=Or.inr (Or.inr q0g)
    rw [q6t,if_neg (fun h=>h.2 q3o)] at q8q
    exact q0g q8q
   have q7u:¬ (z1∈ R∧ zp1∈ R):=by
    rintro ⟨qnc,qin⟩
    have qar:zp1∈ Znew:=(Z5.mp (Z2.mp qin).1).1
    have qik:z1∈ Znew:=(Z5.mp (Z2.mp qnc).1).1
    obtain ⟨c,hc⟩:=q91 qar
    have qfj:MD1_ns.Nonempty:=by
     have q8q:(L z1).Nonempty:=(Z0.mp (Z2.mp qik).1).2
     by_contra q0g
     have qfk:¬ isOwn z1:=fun ho=>(Z2.mp qik).2 (Z0.mpr ⟨(Z2.mp qik).1,ho⟩)
     have qfl:¬ e1_to_z1:=fun h=>h.elim q0g (fun h=>h.elim qfk (fun h=>h ⟨c,hc⟩))
     rw [qcw,if_neg (fun h=>qfl h.2)] at q8q
     exact q0g q8q
    obtain ⟨d,hd⟩:=qfj
    have he1:=q3c qnc d hd
    have he2:=q2u qin c hc
    have qlx:s(z1,d)≠ s(c,zp1):=by
     intro heq;rw [Sym2.eq_iff] at heq
     rcases heq with ⟨rfl,_⟩ | ⟨_,h2'⟩
     ·exact (Finset.mem_erase.mp hc).1 rfl
     ·exact q02 ((z046 q03 hf1 (Z0.mp (Finset.mem_of_mem_erase hc)).1).symm.trans
       (by rw [← h2'];exact z047 q03 hf1 (Z0.mp (Finset.mem_of_mem_erase hd)).1))
    have hle:=Finset.card_le_card (Finset.insert_subset he1 (Finset.singleton_subset_iff.mpr he2))
    rw [Finset.card_pair qlx] at hle;omega
   have qly:R.card≤ 1:=by
    by_contra hgt;push Not at hgt
    have qnd:R={z1,zp1}:=Finset.eq_of_subset_of_card_le qas (by rw [Finset.card_pair q2h];omega)
    exact q7u ⟨by rw [qnd];simp,by rw [qnd];simp⟩
   by_cases qc1:MC1=C1∧ MD1=D1
   ·simp only [loss1,if_pos qc1]
    by_cases hR0:R.card=0
    ·omega
    ·
     obtain ⟨v,hvR⟩:=Finset.card_pos.mp (by omega:0 < R.card)
     have qji:1≤ U12.card:=by
      have hv:=qas hvR
      simp only [Z6,Z3] at hv
      rcases hv with q30 | q30
      ·rw [q30] at hvR
       obtain ⟨d,hd,q1e⟩:=z050 hf1
       have q7s:d∈ MD1_ns:=Finset.mem_erase.mpr ⟨q1e,by rw [qc1.2];exact hd⟩
       exact Finset.card_pos.mpr ⟨s(z1,d),q3c hvR d q7s⟩
      ·rw [q30] at hvR
       obtain ⟨c,hc,hcz⟩:=z049 hf1
       have q7t:c∈ MC1_ns:=Finset.mem_erase.mpr ⟨hcz,by rw [qc1.1];exact hc⟩
       exact Finset.card_pos.mpr ⟨s(c,zp1),q2u hvR c q7t⟩
     omega
   ·simp only [loss1,if_neg qc1];omega
  have qfm:=Finset.card_le_card q3e
  have qio:=z019 q3e
  omega
 have qjj:(Znew ∩ {z2,zp2}).card+loss2≤ A2.card+(Zconf ∩ {zp2}).card+1:=by
  have q57:A2 ∪ (Zconf ∩ {zp2})⊆ Znew ∩ {z2,zp2}:=by
   refine Finset.union_subset (Finset.filter_subset _ _) ?_
   intro v hv;have h1:=(Z5.mp hv).1;have h2:=(Z5.mp hv).2
   rw [Z3] at h2;subst h2
   exact Z5.mpr ⟨(Z2.mp (Z0.mp h1).1).1,by simp⟩
  have q1n:Disjoint A2 (Zconf ∩ {zp2}):=by
   rw [Finset.disjoint_left];intro v hv1 hv2
   exact (Z2.mp (Z0.mp (Z5.mp hv2).1).1).2 (Finset.mem_union_right _ hv1)
  have qfg:(A2 ∪ (Zconf ∩ {zp2})).card=A2.card+(Zconf ∩ {zp2}).card:=
   Finset.card_union_of_disjoint q1n
  set R:=(Znew ∩ {z2,zp2}) \ (A2 ∪ (Zconf ∩ {zp2}))
  have qas:R⊆ {z2,zp2}:=Finset.Subset.trans Finset.sdiff_subset Finset.inter_subset_right
  have qfn:zp2∉ R:=by
   intro hR
   have qip:zp2∈ Znew:=(Z5.mp (Z2.mp hR).1).1
   have q3l:MC2_ns.Nonempty:=by
    have q8q:(L zp2).Nonempty:=(Z0.mp (Z2.mp qip).1).2
    by_contra q0g
    have q3o:e2_to_z2:=Or.inr (Or.inr q0g)
    rw [q6u,if_neg (fun h=>h.2 q3o)] at q8q
    exact q0g q8q
   obtain ⟨c,hc⟩:=q3l
   have q99:=Z0.mp hc
   have q7v:s(c,zp2)∈ U2 \ E1:=Z2.mpr
    ⟨(Z2.mp q99.2).1,fun hE1=>(Z2.mp q99.2).2
     (Z5.mpr ⟨(Z5.mp (Z2.mp q99.2).1).1,hE1⟩)⟩
   rcases qaq zp2 (Z5.mpr ⟨qip,by simp⟩) (Or.inr ⟨rfl,c,q99.1,q7v⟩) with hA | hC
   ·exact (Z2.mp hR).2 (Finset.mem_union_left _ hA)
   ·exact (Z2.mp hR).2 (Finset.mem_union_right _ (Z5.mpr ⟨hC,by simp⟩))
  have q8i:R⊆ {z2}:=by
   intro v hv
   have hv':=qas hv;simp only [Z6,Z3] at hv' ⊢
   exact hv'.resolve_right (fun h=>qfn (h ▸ hv))
  have qly:R.card≤ 1:=(Finset.card_le_card q8i).trans (by simp)
  have qlz:R.card+loss2≤ 1:=by
   by_cases qm0:z2∈ R
   ·have qjk:z2∈ Znew:=(Z5.mp (Z2.mp qm0).1).1
    have q5t:¬ MD2_ns.Nonempty:=by
     rintro ⟨d,hd⟩
     have q98:=Z0.mp hd
     have q7v:s(z2,d)∈ U2 \ E1:=Z2.mpr
      ⟨(Z2.mp q98.2).1,fun hE1=>(Z2.mp q98.2).2
       (Z5.mpr ⟨(Z5.mp (Z2.mp q98.2).1).1,hE1⟩)⟩
     rcases qaq z2 (Z5.mpr ⟨qjk,by simp⟩) (Or.inl ⟨rfl,d,q98.1,q7v⟩) with hA | hC
     ·exact (Z2.mp qm0).2 (Finset.mem_union_left _ hA)
     ·exact absurd (hsz.trans (Z0.mp hC).2.1) q02
    have qc2:¬ MC2_ns.Nonempty:=by
     intro q3l
     have q8q:(L z2).Nonempty:=(Z0.mp (Z2.mp qjk).1).2
     have qfk:¬ isOwn z2:=fun ho=>(Z2.mp qjk).2 (Z0.mpr ⟨(Z2.mp qjk).1,ho⟩)
     have qfl:¬ e2_to_z2:=fun h=>h.elim q5t (fun h=>h.elim qfk (fun h=>h q3l))
     rw [qcx,if_neg (fun h=>qfl h.2)] at q8q
     exact q5t q8q
    have qne:loss2=0:=by
     simp only [loss2,ite_eq_right_iff];rintro ⟨q75,qba⟩
     exfalso
     obtain ⟨c,hc,hcz⟩:=z049 hf2
     obtain ⟨d,hd,q1e⟩:=z050 hf2
     have qnf:s(c,zp2)∈ U2:=Z5.mpr
      ⟨(Z0.mp (by rw [q75];exact hc:c∈ MC2)).2,Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc)⟩
     have qng:s(z2,d)∈ U2:=Z5.mpr
      ⟨(Z0.mp (by rw [qba];exact hd:d∈ MD2)).2,Finset.mem_union_left _ (Finset.mem_image_of_mem _ hd)⟩
     have qm1:s(c,zp2)∈ U1:=by
      by_contra hnu;exact qc2 ⟨c,Z0.mpr ⟨Finset.mem_erase.mpr ⟨hcz,hc⟩,Z2.mpr ⟨qnf,hnu⟩⟩⟩
     have qm2:s(z2,d)∈ U1:=by
      by_contra hnu;exact q5t ⟨d,Z0.mpr ⟨Finset.mem_erase.mpr ⟨q1e,hd⟩,Z2.mpr ⟨qng,hnu⟩⟩⟩
     have qiq:s(c,zp2)≠ s(z2,d):=by
      intro heq;rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl,_⟩ | ⟨h1',_⟩
      ·exact hcz rfl
      ·exact q03 z2 zp2 hf2.1 ((z046 q03 hf2 hc).symm.trans (by rw [h1'];exact z047 q03 hf2 hd))
     have hle:({s(c,zp2),s(z2,d)}:Finset (Sym2 (Fin n))).card≤ U12.card:=
      Finset.card_le_card (Finset.insert_subset (Z5.mpr ⟨qm1,qnf⟩)
       (Finset.singleton_subset_iff.mpr (Z5.mpr ⟨qm2,qng⟩)))
     rw [Finset.card_pair qiq] at hle;omega
    omega
   ·have hR0:R=∅:=by
     ext v;simp only [Finset.notMem_empty,iff_false];intro hv
     exact qm0 ((Z3.mp (q8i hv)) ▸ hv)
    rw [hR0,Z20];simp [loss2];split_ifs <;> omega
  have qfm:=Finset.card_le_card q57
  have qio:R.card=(Znew ∩ {z2,zp2}).card - (A2 ∪ (Zconf ∩ {zp2})).card:=z019 q57
  omega
 have qfo:Znew.card=(Znew ∩ {z1,zp1}).card+(Znew ∩ {z2,zp2}).card:=by
  have hU:Znew=(Znew ∩ {z1,zp1}) ∪ (Znew ∩ {z2,zp2}):=by
   ext v;simp only [Z4,Z5,Z6,Z3]
   constructor
   ·intro hv
    have hv4:=(Z0.mp (Z2.mp hv).1).1
    simp only [Z6,Z3] at hv4
    rcases hv4 with rfl | rfl | rfl | rfl
    ·exact Or.inl ⟨hv,Or.inl rfl⟩
    ·exact Or.inl ⟨hv,Or.inr rfl⟩
    ·exact Or.inr ⟨hv,Or.inl rfl⟩
    ·exact Or.inr ⟨hv,Or.inr rfl⟩
   ·rintro (⟨hv,_⟩ | ⟨hv,_⟩) <;> exact hv
  have hd:Disjoint (Znew ∩ {z1,zp1}) (Znew ∩ {z2,zp2}):=by
   rw [Finset.disjoint_left];intro v h1 h2
   have hv1:=(Z5.mp h1).2;have hv2:=(Z5.mp h2).2
   simp only [Z6,Z3] at hv1 hv2
   rcases hv1 with rfl | rfl <;> rcases hv2 with h | h
   ·exact q5z h
   ·exact q1z h
   ·exact q20 h.symm
   ·exact q0h h
  conv_lhs=>rw [hU]
  exact Finset.card_union_of_disjoint hd
 have qcy:Zconf.card=(Zconf ∩ {zp1}).card+(Zconf ∩ {zp2}).card:=by
  have q0c:Zconf⊆ {zp1,zp2}:=by
   intro v hv
   have hvf:=Z0.mp hv
   have hv4:=(Z0.mp (Z2.mp (Z2.mp hvf.1).1).1).1
   simp only [Z6,Z3] at hv4 ⊢
   rcases hv4 with rfl | rfl | rfl | rfl
   ·exact absurd hvf.2.1 q02
   ·exact Or.inl rfl
   ·exact absurd (hsz.trans hvf.2.1) q02
   ·exact Or.inr rfl
  have hU:Zconf=(Zconf ∩ {zp1}) ∪ (Zconf ∩ {zp2}):=by
   ext v;simp only [Z4,Z5,Z3]
   constructor
   ·intro hv
    have:=q0c hv;simp only [Z6,Z3] at this
    rcases this with rfl | rfl
    ·exact Or.inl ⟨hv,rfl⟩
    ·exact Or.inr ⟨hv,rfl⟩
   ·rintro (⟨hv,_⟩ | ⟨hv,_⟩) <;> exact hv
  have hd:Disjoint (Zconf ∩ {zp1}) (Zconf ∩ {zp2}):=by
   rw [Finset.disjoint_left];intro v h1 h2
   have hv1:=Z3.mp (Z5.mp h1).2
   have hv2:=Z3.mp (Z5.mp h2).2
   exact q0h (hv1.symm.trans hv2)
  conv_lhs=>rw [hU]
  exact Finset.card_union_of_disjoint hd
 have q7w:2 * (centreless G C).card+Extra.card≤ A1.card+A2.card+Zconf.card:=by omega
 have q3p:Disjoint A1 A2:=by
  rw [Finset.disjoint_left];intro v h1 h2
  have hv1:=(Z5.mp (Z0.mp h1).1).2
  have hv2:=(Z5.mp (Z0.mp h2).1).2
  simp only [Z6,Z3] at hv1 hv2
  rcases hv1 with rfl | rfl <;> rcases hv2 with h | h
  ·exact q5z h
  ·exact q1z h
  ·exact q20 h.symm
  ·exact q0h h
 have qc3:Disjoint (A1 ∪ A2) Zconf:=by
  rw [Finset.disjoint_left];intro v hA hZ
  exact (Z2.mp (Z0.mp hZ).1).2 hA
 have qjl:A1.card+A2.card+Zconf.card≤ 4:=by
  have q0c:(A1 ∪ A2) ∪ Zconf⊆ {z1,zp1,z2,zp2}:=by
   intro v hv
   have hvZ:v∈ Znew:=by
    rcases Z4.mp hv with hA | hZ
    ·rcases Z4.mp hA with h1 | h2
     ·exact (Z5.mp (Z0.mp h1).1).1
     ·exact (Z5.mp (Z0.mp h2).1).1
    ·exact (Z2.mp (Z0.mp hZ).1).1
   exact (Z0.mp (Z2.mp hvZ).1).1
  have hle:=Finset.card_le_card q0c
  rw [Finset.card_union_of_disjoint qc3,Finset.card_union_of_disjoint q3p,qbx] at hle
  exact hle
 let mixGate:Fin n→ ℕ:=fun v=>
  if h:∃ mv∈ Extra,orIn n C (n+mv)={v} then Classical.choose h else 0
 set SingleMix:=Zconf.image mixGate
 have q12:SingleMix⊆ Extra:=by
  intro k hk;simp only [SingleMix,Z19] at hk
  rcases hk with ⟨v,hv,rfl⟩
  have hex:∃ mv∈ Extra,orIn n C (n+mv)={v}:=by
   rcases (Z0.mp hv).2.2 with ⟨mv,hmv,hor,_⟩;exact ⟨mv,hmv,hor⟩
  simp only [mixGate,dif_pos hex];exact (Classical.choose_spec hex).1
 have q2l:∀ k∈ SingleMix,∃ v∈ Zconf,orIn n C (n+k)={v}:=by
  intro k hk;simp only [SingleMix,Z19] at hk
  rcases hk with ⟨v,hv,rfl⟩
  have hex:∃ mv∈ Extra,orIn n C (n+mv)={v}:=by
   rcases (Z0.mp hv).2.2 with ⟨mv,hmv,hor,_⟩;exact ⟨mv,hmv,hor⟩
  simp only [mixGate,dif_pos hex];exact ⟨v,hv,(Classical.choose_spec hex).2⟩
 have q0x:SingleMix.card=Zconf.card:=by
  apply Finset.card_image_of_injOn
  intro v1 hv1 v2 hv2 heq
  have q94:∃ mv∈ Extra,orIn n C (n+mv)={v1}:=by
   rcases (Z0.mp hv1).2.2 with ⟨mv,hmv,hor,_⟩;exact ⟨mv,hmv,hor⟩
  have qb2:∃ mv∈ Extra,orIn n C (n+mv)={v2}:=by
   rcases (Z0.mp hv2).2.2 with ⟨mv,hmv,hor,_⟩;exact ⟨mv,hmv,hor⟩
  simp only [mixGate,dif_pos q94,dif_pos qb2] at heq
  have h1:=(Classical.choose_spec q94).2
  have h2:=(Classical.choose_spec qb2).2
  rw [heq] at h1
  exact Finset.singleton_injective (h1.symm.trans h2)
 have q8j:∀ a∈ centreless G C,∀ b:Fin 2,side (n:=n) C a b=∅→
   ∀ A':Finset (Fin n),A'.Nonempty→ A'⊆ A1 ∪ A2→ A'⊆ side (n:=n) C a (1 - b)→
   let HW:=Extra.filter (fun k=>2≤ (orIn n C (n+k)).card)
   A'.card≤ HW.card+1:=by
  intro a haC b q0g A' ql1 q6v q4r HW
  have q25:a∈ tops G C:=(Z0.mp haC).1
  have ha':=z098.mp q25
  have q8k:OrReaches n C (opnd C a b) g1∨ OrReaches n C (opnd C a b) g2:=by
   have qaz:=(z103 hL q01 hne q00 (opnd C a b)
    (by have:=z104 hL.1 ha'.1 b;omega) (z130 hL hne q25 b) (fun _=>true)).mp
    (z138 hL.1 (opnd C a b) (by have:=z104 hL.1 ha'.1 b;omega))
   rcases qaz with ⟨u,hu,_⟩ | ⟨hr,_⟩ | ⟨hr,_⟩
   ·rw [show orIn n C (opnd C a b)=∅ from q0g] at hu;exact absurd hu (Finset.notMem_empty _)
   ·exact Or.inl hr
   ·exact Or.inr hr
  have q2n:∀ k,OrReaches n C (opnd C a (1 - b)) k→ k∈ lam G C ∪ FacAll→
    (orIn n C (n+k) ∩ A').card≤ 1:=by
   intro k _ hk
   by_contra hgt;push Not at hgt
   obtain ⟨u,hu,v,hv,huv⟩:=Finset.one_lt_card.mp hgt
   have hu':=Z5.mp hu;have hv':=Z5.mp hv
   have q15:s u=s v:=by
    rcases Z4.mp hk with qa5 | q6y
    ·rcases (Z0.mp qa5).2.2.2 with ⟨atp,q2v,btp,q0t,hrt⟩
     obtain ⟨w,hw⟩:=Finset.card_eq_one.mp q0t
     have q0c:=z109 hrt
     have hwm:w∈ side (n:=n) C atp (1 - btp):=by rw [hw];simp
     have hau:G.Adj w u:=by fin_cases btp;exact (z132 hL.1 q2v (q0c hu'.1) hwm).symm;exact z132 hL.1 q2v hwm (q0c hu'.1)
     have hav:G.Adj w v:=by fin_cases btp;exact (z132 hL.1 q2v (q0c hv'.1) hwm).symm;exact z132 hL.1 q2v hwm (q0c hv'.1)
     exact z015 (q03 w u hau).symm (q03 w v hav).symm
    ·simp only [FacAll,Z4] at q6y
     rcases q6y with (h | h) | (h | h)
     ·exact (z046 q03 hf1 ((q1j k h).2.2.1 hu'.1)).trans (z046 q03 hf1 ((q1j k h).2.2.1 hv'.1)).symm
     ·exact (z047 q03 hf1 ((q1s k h).2.2.1 hu'.1)).trans (z047 q03 hf1 ((q1s k h).2.2.1 hv'.1)).symm
     ·exact (z046 q03 hf2 ((q22 k h).2.2.1 hu'.1)).trans (z046 q03 hf2 ((q22 k h).2.2.1 hv'.1)).symm
     ·exact (z047 q03 hf2 ((q2j k h).2.2.1 hu'.1)).trans (z047 q03 hf2 ((q2j k h).2.2.1 hv'.1)).symm
   have q7x:((u=z1∧ v=z2)∨ (u=z2∧ v=z1))∨
     ((u=zp1∧ v=zp2)∨ (u=zp2∧ v=zp1)):=by
    have qir:∀ x∈ A',x=z1∨ x=zp1∨ x=z2∨ x=zp2:=fun x hx=>by
     rcases Z4.mp (q6v hx) with h1 | h2
     ·have:=(Z5.mp (Z0.mp h1).1).2
      simp only [Z6,Z3] at this
      rcases this with rfl | rfl;exact Or.inl rfl;exact Or.inr (Or.inl rfl)
     ·have:=(Z5.mp (Z0.mp h2).1).2
      simp only [Z6,Z3] at this
      rcases this with rfl | rfl;exact Or.inr (Or.inr (Or.inl rfl));exact Or.inr (Or.inr (Or.inr rfl))
    rcases qir u hu'.2 with rfl | rfl | rfl | rfl <;> rcases qir v hv'.2 with rfl | rfl | rfl | rfl
    ·exact absurd rfl huv
    ·exact absurd q15 q02
    ·exact Or.inl (Or.inl ⟨rfl,rfl⟩)
    ·exact absurd (q15.trans q1l.symm) q02
    ·exact absurd q15.symm q02
    ·exact absurd rfl huv
    ·exact absurd (hsz.trans q15.symm) q02
    ·exact Or.inr (Or.inl ⟨rfl,rfl⟩)
    ·exact Or.inl (Or.inr ⟨rfl,rfl⟩)
    ·exact absurd (hsz.trans q15) q02
    ·exact absurd rfl huv
    ·exact absurd (hsz.trans (q15.trans q1l.symm)) q02
    ·exact absurd (q15.symm.trans q1l.symm) q02
    ·exact Or.inr (Or.inr ⟨rfl,rfl⟩)
    ·exact absurd (hsz.trans (q15.symm.trans q1l.symm)) q02
    ·exact absurd rfl huv
   have qat:z1∈ orIn n C (n+k)→ z2∈ orIn n C (n+k)→ z1∈ A'→ z2∈ A'→ False:=by
    intro q7y qau qnh qni
    have qis:z1∈ A1:=(Z4.mp (q6v qnh)).resolve_right (fun h=>by
     have:=(Z5.mp (Z0.mp h).1).2;simp [q5z,q1z] at this)
    have qit:z2∈ A2:=(Z4.mp (q6v qni)).resolve_left (fun h=>by
     have:=(Z5.mp (Z0.mp h).1).2;simp [q5z.symm,q20] at this)
    rcases q8k with qm3 | qm4
    ·
     obtain ⟨d1,hd1,qnj⟩:∃ d1∈ D1.erase zp1,s(z1,d1)∈ U1 \ E2:=by
      rcases (Z0.mp qis).2.1 with ⟨_,h⟩ | ⟨heq,_⟩
      ·exact h
      ·exact absurd heq q2h
     have q6i:d1≠ zp1:=(Finset.mem_erase.mp hd1).1
     have qnk:d1∈ D1:=Finset.mem_of_mem_erase hd1
     have q3i:=z131 hL.1 q25 b qm3 (q4r qni)
     have q4s:G.Adj z2 d1:=z054 q03 h4 hf1 q3i hsz.symm qnk q6i
     have q4t:G.Adj z1 d1:=(hf1.2.2.2.2.1 d1 qnk).symm
     rcases Z4.mp hk with qa5 | q6y
     ·rcases (Z0.mp qa5).2.2.2 with ⟨atp,q2v,btp,q0t,hrt⟩
      obtain ⟨w,hw⟩:=Finset.card_eq_one.mp q0t
      have q0c:=z109 hrt
      have hwm:w∈ side (n:=n) C atp (1 - btp):=by rw [hw];simp
      have qfp:G.Adj z1 w:=by fin_cases btp;exact z132 hL.1 q2v (q0c q7y) hwm;exact (z132 hL.1 q2v hwm (q0c q7y)).symm
      have qfq:G.Adj z2 w:=by fin_cases btp;exact z132 hL.1 q2v (q0c qau) hwm;exact (z132 hL.1 q2v hwm (q0c qau)).symm
      have q8s:w=d1:=z102 h4 q5z qfp qfq q4t q4s
      subst q8s
      have q5g:s(z1,w)∈ starEdges G C:=by
       simp only [starEdges,Finset.mem_biUnion,Z19,Z18]
       fin_cases btp
       ·exact ⟨atp,q2v,(z1,w),⟨q0c q7y,hwm⟩,rfl⟩
       ·exact ⟨atp,q2v,(w,z1),⟨hwm,q0c q7y⟩,Sym2.eq_swap⟩
      exact (Z2.mp (Z5.mp (Z2.mp qnj).1).1).2 q5g
     ·simp only [FacAll,Z4] at q6y
      rcases q6y with (h | h) | (h | h)
      ·have q0c:=(q1j k h).2.2.1
       have heq:=z102 h4 q5z (hf1.2.2.2.1 z1 (q0c q7y)) (hf1.2.2.2.1 z2 (q0c qau)) q4t q4s
       exact q6i heq.symm
      ·exact q02 (z047 q03 hf1 ((q1s k h).2.2.1 q7y))
      ·have q0c:=(q22 k h).2.2.1
       have heq:=z102 h4 q5z (hf2.2.2.2.1 z1 (q0c q7y)) (hf2.2.2.2.1 z2 (q0c qau)) q4t q4s
       subst heq
       exact (Z2.mp qnj).2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (q0c q7y)))
      ·exact q02 ((z047 q03 hf2 ((q2j k h).2.2.1 q7y)).trans q1l.symm)
    ·
     obtain ⟨d2,hd2,qnl⟩:∃ d2∈ D2.erase zp2,s(z2,d2)∈ U2 \ E1:=by
      rcases (Z0.mp qit).2.1 with ⟨_,h⟩ | ⟨heq,_⟩
      ·exact h
      ·exact absurd heq q2i
     have q8y:d2≠ zp2:=(Finset.mem_erase.mp hd2).1
     have qnm:d2∈ D2:=Finset.mem_of_mem_erase hd2
     have q3i:=z131 hL.1 q25 b qm4 (q4r qnh)
     have q4u:G.Adj z1 d2:=z054 q03 h4 hf2 q3i hsz qnm q8y
     have q4v:G.Adj z2 d2:=(hf2.2.2.2.2.1 d2 qnm).symm
     rcases Z4.mp hk with qa5 | q6y
     ·rcases (Z0.mp qa5).2.2.2 with ⟨atp,q2v,btp,q0t,hrt⟩
      obtain ⟨w,hw⟩:=Finset.card_eq_one.mp q0t
      have q0c:=z109 hrt
      have hwm:w∈ side (n:=n) C atp (1 - btp):=by rw [hw];simp
      have qfp:G.Adj z1 w:=by fin_cases btp;exact z132 hL.1 q2v (q0c q7y) hwm;exact (z132 hL.1 q2v hwm (q0c q7y)).symm
      have qfq:G.Adj z2 w:=by fin_cases btp;exact z132 hL.1 q2v (q0c qau) hwm;exact (z132 hL.1 q2v hwm (q0c qau)).symm
      have q8s:w=d2:=z102 h4 q5z qfp qfq q4u q4v
      subst q8s
      have q5g:s(z2,w)∈ starEdges G C:=by
       simp only [starEdges,Finset.mem_biUnion,Z19,Z18]
       fin_cases btp
       ·exact ⟨atp,q2v,(z2,w),⟨q0c qau,hwm⟩,rfl⟩
       ·exact ⟨atp,q2v,(w,z2),⟨hwm,q0c qau⟩,Sym2.eq_swap⟩
      exact (Z2.mp (Z5.mp (Z2.mp qnl).1).1).2 q5g
     ·simp only [FacAll,Z4] at q6y
      rcases q6y with (h | h) | (h | h)
      ·have q0c:=(q1j k h).2.2.1
       have heq:=z102 h4 q5z (hf1.2.2.2.1 z1 (q0c q7y)) (hf1.2.2.2.1 z2 (q0c qau)) q4u q4v
       subst heq
       exact (Z2.mp qnl).2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (q0c qau)))
      ·exact q02 (z047 q03 hf1 ((q1s k h).2.2.1 q7y))
      ·have q0c:=(q22 k h).2.2.1
       have heq:=z102 h4 q5z (hf2.2.2.2.1 z1 (q0c q7y)) (hf2.2.2.2.1 z2 (q0c qau)) q4u q4v
       exact q8y heq.symm
      ·exact q02 ((z047 q03 hf2 ((q2j k h).2.2.1 q7y)).trans q1l.symm)
   have q8l:zp1∈ orIn n C (n+k)→ zp2∈ orIn n C (n+k)→ zp1∈ A'→ zp2∈ A'→ False:=by
    intro q31 q4w qiu qiv
    have qfr:zp1∈ A1:=(Z4.mp (q6v qiu)).resolve_right (fun h=>by
     have:=(Z5.mp (Z0.mp h).1).2;simp [q20.symm,q0h] at this)
    have qfs:zp2∈ A2:=(Z4.mp (q6v qiv)).resolve_left (fun h=>by
     have:=(Z5.mp (Z0.mp h).1).2;simp [q1z.symm,q0h.symm] at this)
    rcases q8k with qm3 | qm4
    ·obtain ⟨c1,hc1,qiw⟩:∃ c1∈ C1.erase z1,s(c1,zp1)∈ U1 \ E2:=by
      rcases (Z0.mp qfr).2.1 with ⟨heq,_⟩ | ⟨_,h⟩
      ·exact absurd heq q2h.symm
      ·exact h
     have q87:c1≠ z1:=(Finset.mem_erase.mp hc1).1
     have qnn:c1∈ C1:=Finset.mem_of_mem_erase hc1
     have q3i:=z131 hL.1 q25 b qm3 (q4r qiv)
     have q3q:G.Adj zp2 c1:=z053 q03 h4 hf1 q3i q1l.symm qnn q87
     have q3r:G.Adj zp1 c1:=(hf1.2.2.2.1 c1 qnn).symm
     rcases Z4.mp hk with qa5 | q6y
     ·rcases (Z0.mp qa5).2.2.2 with ⟨atp,q2v,btp,q0t,hrt⟩
      obtain ⟨w,hw⟩:=Finset.card_eq_one.mp q0t
      have q0c:=z109 hrt
      have hwm:w∈ side (n:=n) C atp (1 - btp):=by rw [hw];simp
      have qfp:G.Adj zp1 w:=by fin_cases btp;exact z132 hL.1 q2v (q0c q31) hwm;exact (z132 hL.1 q2v hwm (q0c q31)).symm
      have qfq:G.Adj zp2 w:=by fin_cases btp;exact z132 hL.1 q2v (q0c q4w) hwm;exact (z132 hL.1 q2v hwm (q0c q4w)).symm
      have q8s:w=c1:=z102 h4 q0h qfp qfq q3r q3q
      subst q8s
      have q5g:s(w,zp1)∈ starEdges G C:=by
       simp only [starEdges,Finset.mem_biUnion,Z19,Z18]
       fin_cases btp
       ·exact ⟨atp,q2v,(zp1,w),⟨q0c q31,hwm⟩,Sym2.eq_swap⟩
       ·exact ⟨atp,q2v,(w,zp1),⟨hwm,q0c q31⟩,rfl⟩
      exact (Z2.mp (Z5.mp (Z2.mp qiw).1).1).2 q5g
     ·simp only [FacAll,Z4] at q6y
      rcases q6y with (h | h) | (h | h)
      ·exact q02.symm (z046 q03 hf1 ((q1j k h).2.2.1 q31))
      ·have q0c:=(q1s k h).2.2.1
       have heq:=z102 h4 q0h (hf1.2.2.2.2.1 zp1 (q0c q31)) (hf1.2.2.2.2.1 zp2 (q0c q4w)) q3r q3q
       exact q87 heq.symm
      ·exact q02.symm ((z046 q03 hf2 ((q22 k h).2.2.1 q31)).trans hsz.symm)
      ·have q0c:=(q2j k h).2.2.1
       have heq:=z102 h4 q0h (hf2.2.2.2.2.1 zp1 (q0c q31)) (hf2.2.2.2.2.1 zp2 (q0c q4w)) q3r q3q
       subst heq
       exact (Z2.mp qiw).2 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (q0c q31)))
    ·obtain ⟨c2,hc2,qix⟩:∃ c2∈ C2.erase z2,s(c2,zp2)∈ U2 \ E1:=by
      rcases (Z0.mp qfs).2.1 with ⟨heq,_⟩ | ⟨_,h⟩
      ·exact absurd heq q2i.symm
      ·exact h
     have q6x:c2≠ z2:=(Finset.mem_erase.mp hc2).1
     have qno:c2∈ C2:=Finset.mem_of_mem_erase hc2
     have q3i:=z131 hL.1 q25 b qm4 (q4r qiu)
     have q3s:G.Adj zp1 c2:=z053 q03 h4 hf2 q3i q1l qno q6x
     have q3t:G.Adj zp2 c2:=(hf2.2.2.2.1 c2 qno).symm
     rcases Z4.mp hk with qa5 | q6y
     ·rcases (Z0.mp qa5).2.2.2 with ⟨atp,q2v,btp,q0t,hrt⟩
      obtain ⟨w,hw⟩:=Finset.card_eq_one.mp q0t
      have q0c:=z109 hrt
      have hwm:w∈ side (n:=n) C atp (1 - btp):=by rw [hw];simp
      have qfp:G.Adj zp1 w:=by fin_cases btp;exact z132 hL.1 q2v (q0c q31) hwm;exact (z132 hL.1 q2v hwm (q0c q31)).symm
      have qfq:G.Adj zp2 w:=by fin_cases btp;exact z132 hL.1 q2v (q0c q4w) hwm;exact (z132 hL.1 q2v hwm (q0c q4w)).symm
      have q8s:w=c2:=z102 h4 q0h qfp qfq q3s q3t
      subst q8s
      have q5g:s(w,zp2)∈ starEdges G C:=by
       simp only [starEdges,Finset.mem_biUnion,Z19,Z18]
       fin_cases btp
       ·exact ⟨atp,q2v,(zp2,w),⟨q0c q4w,hwm⟩,Sym2.eq_swap⟩
       ·exact ⟨atp,q2v,(w,zp2),⟨hwm,q0c q4w⟩,rfl⟩
      exact (Z2.mp (Z5.mp (Z2.mp qix).1).1).2 q5g
     ·simp only [FacAll,Z4] at q6y
      rcases q6y with (h | h) | (h | h)
      ·exact q02.symm (z046 q03 hf1 ((q1j k h).2.2.1 q31))
      ·have q0c:=(q1s k h).2.2.1
       have heq:=z102 h4 q0h (hf1.2.2.2.2.1 zp1 (q0c q31)) (hf1.2.2.2.2.1 zp2 (q0c q4w)) q3s q3t
       subst heq
       exact (Z2.mp qix).2 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (q0c q4w)))
      ·exact q02.symm ((z046 q03 hf2 ((q22 k h).2.2.1 q31)).trans hsz.symm)
      ·have q0c:=(q2j k h).2.2.1
       have heq:=z102 h4 q0h (hf2.2.2.2.2.1 zp1 (q0c q31)) (hf2.2.2.2.2.1 zp2 (q0c q4w)) q3s q3t
       exact q6x heq.symm
   rcases q7x with (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) | (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
   ·exact qat hu'.1 hv'.1 hu'.2 hv'.2
   ·exact qat hv'.1 hu'.1 hv'.2 hu'.2
   ·exact q8l hu'.1 hv'.1 hu'.2 hv'.2
   ·exact q8l hv'.1 hu'.1 hv'.2 hu'.2
  have hwb:=z136 hL q01 hne q00
   (by have:=z104 hL.1 ha'.1 (1 - b);omega) (z130 hL hne q25 (1 - b))
   A' ql1 q4r FacAll q2n
  have qft:(orN G C \ lam G C).filter (fun k=>
    OrReaches n C (opnd C a (1 - b)) k∧ k∉ FacAll∧ 2≤ (orIn n C (n+k) ∩ A').card)⊆ HW:=by
   intro k hk
   have hkf:=Z0.mp hk
   exact Z0.mpr ⟨Z2.mpr ⟨hkf.1,hkf.2.2.1⟩,
    le_trans hkf.2.2.2 (Finset.card_le_card Finset.inter_subset_left)⟩
  have qnp:=Finset.card_le_card qft
  omega
 by_cases qnq:3≤ (centreless G C).card
 ·omega
 ·by_cases q0m:(centreless G C).card=0
  ·have q29:centreless G C=∅:=Finset.card_eq_zero.mp q0m
   have qfu:A1=∅:=by
    ext v;simp only [Finset.notMem_empty,iff_false];intro hv
    rcases (Z0.mp hv).2.2 with ⟨a,haC,_⟩
    rw [q29] at haC;exact Finset.notMem_empty _ haC
   have qfv:A2=∅:=by
    ext v;simp only [Finset.notMem_empty,iff_false];intro hv
    rcases (Z0.mp hv).2.2 with ⟨a,haC,_⟩
    rw [q29] at haC;exact Finset.notMem_empty _ haC
   rw [qfu,qfv,Z20] at q7w
   by_cases qnr:Zconf=∅
   ·obtain ⟨m0,hm0,qcn⟩:=z037 hL q01 hne q0y q00 q29
    have qm5:m0∈ Extra:=Z2.mpr ⟨hm0,fun hkf=>by
     have:m0 < g2:=by
      simp only [FacAll,Z4] at hkf
      rcases hkf with (h | h) | (h | h)
      ·have:=z113 (Z0.mp h).2;have:=z104 hL.1 q5x.1 b1;omega
      ·have:=z113 (Z0.mp h).2;have:=z104 hL.1 q5x.1 (1 - b1);omega
      ·have:=z113 (Z0.mp h).2;have:=z104 hL.1 q2p.1 b2;omega
      ·have:=z113 (Z0.mp h).2;have:=z104 hL.1 q2p.1 (1 - b2);omega
     omega⟩
    have qpc:1≤ Extra.card:=Finset.card_pos.mpr ⟨m0,qm5⟩
    rw [qnr,Z20] at q7w;omega
   ·obtain ⟨v0,hv0⟩:=Finset.nonempty_iff_ne_empty.mpr qnr
    obtain ⟨_,_,_,u',q24,mu,qap,q06⟩:=(Z0.mp hv0).2.2
    have qfw:mu∉ SingleMix:=by
     intro hsm
     obtain ⟨v,hv,hor⟩:=q2l mu hsm
     rw [q06] at hor
     have qm6:u'=v:=Finset.singleton_injective hor
     have hsv:=(Z0.mp hv).2.1
     exact q02 (q24.symm.trans ((congrArg s qm6).trans hsv))
    have hle:=Finset.card_le_card (Finset.insert_subset qap q12)
    rw [Z24 qfw,q0x] at hle
    omega
  ·by_cases q6l:(centreless G C).card=1
   ·obtain ⟨a0,ha0⟩:=Finset.card_eq_one.mp q6l
    have qpd:a0∈ centreless G C:=by rw [ha0];simp
    by_cases qav:A1 ∪ A2=∅
    ·have qfu:A1=∅:=(Finset.union_eq_empty.mp qav).1
     have qfv:A2=∅:=(Finset.union_eq_empty.mp qav).2
     have hle:=Finset.card_le_card q12
     rw [q0x] at hle
     rw [qfu,qfv,Z20] at q7w
     omega
    ·obtain ⟨v0,hv0⟩:=Finset.nonempty_iff_ne_empty.mpr qav
     obtain ⟨b0,q6o,qcz⟩:∃ b0:Fin 2,side (n:=n) C a0 b0=∅∧ v0∈ side (n:=n) C a0 (1 - b0):=by
      rcases Z4.mp hv0 with h1 | h2
      ·rcases (Z0.mp h1).2.2 with ⟨a,haC,b,q0g,_,hvs⟩
       have q3z:a=a0:=Z3.mp (ha0 ▸ haC);subst q3z
       exact ⟨b,q0g,hvs⟩
      ·rcases (Z0.mp h2).2.2 with ⟨a,haC,b,q0g,_,hvs⟩
       have q3z:a=a0:=Z3.mp (ha0 ▸ haC);subst q3z
       exact ⟨b,q0g,hvs⟩
     have qfx:A1 ∪ A2⊆ side (n:=n) C a0 (1 - b0):=by
      intro v hv
      obtain ⟨b,q0g,hvs⟩:∃ b:Fin 2,side (n:=n) C a0 b=∅∧ v∈ side (n:=n) C a0 (1 - b):=by
       rcases Z4.mp hv with h1 | h2
       ·rcases (Z0.mp h1).2.2 with ⟨a,haC,b,q0g,_,hvs⟩
        have q3z:a=a0:=Z3.mp (ha0 ▸ haC);subst q3z
        exact ⟨b,q0g,hvs⟩
       ·rcases (Z0.mp h2).2.2 with ⟨a,haC,b,q0g,_,hvs⟩
        have q3z:a=a0:=Z3.mp (ha0 ▸ haC);subst q3z
        exact ⟨b,q0g,hvs⟩
      have hbe:b=b0:=by
       by_contra q2e
       have q51:1 - b0=b:=z044 (Ne.symm q2e)
       rw [q51,q0g] at qcz;exact Finset.notMem_empty _ qcz
      rwa [← hbe]
     set HW:=Extra.filter (fun k=>2≤ (orIn n C (n+k)).card)
     have qiy:=q8j a0 qpd b0 q6o (A1 ∪ A2) ⟨v0,hv0⟩ (Finset.Subset.refl _) qfx
     have q7z:Disjoint SingleMix HW:=by
      rw [Finset.disjoint_left];intro k hk1 hk2
      obtain ⟨v,_,hor⟩:=q2l k hk1
      have hc:=(Z0.mp hk2).2
      rw [hor,Finset.card_singleton] at hc;omega
     have qiz:=Finset.card_le_card (Finset.union_subset q12 (Finset.filter_subset _ _:HW⊆ Extra))
     rw [Finset.card_union_of_disjoint q7z,q0x] at qiz
     rw [Finset.card_union_of_disjoint q3p] at qiy
     omega
   ·
    have qaa:(centreless G C).card=2:=by omega
    by_cases qpe:1≤ Zconf.card
    ·have hle:=Finset.card_le_card q12
     rw [q0x] at hle
     omega
    ·by_cases qpf:A1.card+A2.card+Zconf.card≤ 3
     ·omega
     ·
      have qjm:(A1 ∪ A2).card=4:=by
       rw [Finset.card_union_of_disjoint q3p];omega
      obtain ⟨a1,a2,qpn,q5u⟩:=Finset.card_eq_two.mp qaa
      have qeh:a1∈ centreless G C:=by rw [q5u];simp
      have qhz:a2∈ centreless G C:=by rw [q5u];simp
      let S1:=(A1 ∪ A2).filter (fun v=>∃ b:Fin 2,side (n:=n) C a1 b=∅∧ v∈ side (n:=n) C a1 (1 - b))
      let S2:=(A1 ∪ A2).filter (fun v=>∃ b:Fin 2,side (n:=n) C a2 b=∅∧ v∈ side (n:=n) C a2 (1 - b))
      have qj0:A1 ∪ A2⊆ S1 ∪ S2:=by
       intro v hv
       obtain ⟨a,haC,b,q0g,hvs⟩:∃ a∈ centreless G C,∃ b:Fin 2,side (n:=n) C a b=∅∧ v∈ side (n:=n) C a (1 - b):=by
        rcases Z4.mp hv with h1 | h2
        ·rcases (Z0.mp h1).2.2 with ⟨a,haC,b,q0g,_,hvs⟩;exact ⟨a,haC,b,q0g,hvs⟩
        ·rcases (Z0.mp h2).2.2 with ⟨a,haC,b,q0g,_,hvs⟩;exact ⟨a,haC,b,q0g,hvs⟩
       rw [q5u,Z6,Z3] at haC
       rcases haC with rfl | rfl
       ·exact Finset.mem_union_left _ (Z0.mpr ⟨hv,b,q0g,hvs⟩)
       ·exact Finset.mem_union_right _ (Z0.mpr ⟨hv,b,q0g,hvs⟩)
      have qm7:4≤ S1.card+S2.card:=by
       have h1:=Finset.card_le_card qj0
       have h2:=Finset.card_union_le S1 S2
       omega
      have qm8:∃ a∈ centreless G C,∃ S':Finset (Fin n),2≤ S'.card∧ S'⊆ A1 ∪ A2∧
        ∃ b:Fin 2,side (n:=n) C a b=∅∧ S'⊆ side (n:=n) C a (1 - b):=by
       by_cases hS1:2≤ S1.card
       ·obtain ⟨v0,hv0⟩:=Finset.card_pos.mp (by omega:0 < S1.card)
        obtain ⟨b0,q6o,qcz⟩:=(Z0.mp hv0).2
        refine ⟨a1,qeh,S1,hS1,Finset.filter_subset _ _,b0,q6o,fun v hv=>?_⟩
        obtain ⟨b,q0g,hvs⟩:=(Z0.mp hv).2
        have hbe:b=b0:=by
         by_contra q2e
         have q51:1 - b0=b:=z044 (Ne.symm q2e)
         rw [q51,q0g] at qcz;exact Finset.notMem_empty _ qcz
        rwa [← hbe]
       ·have hS2:2≤ S2.card:=by omega
        obtain ⟨v0,hv0⟩:=Finset.card_pos.mp (by omega:0 < S2.card)
        obtain ⟨b0,q6o,qcz⟩:=(Z0.mp hv0).2
        refine ⟨a2,qhz,S2,hS2,Finset.filter_subset _ _,b0,q6o,fun v hv=>?_⟩
        obtain ⟨b,q0g,hvs⟩:=(Z0.mp hv).2
        have hbe:b=b0:=by
         by_contra q2e
         have q51:1 - b0=b:=z044 (Ne.symm q2e)
         rw [q51,q0g] at qcz;exact Finset.notMem_empty _ qcz
        rwa [← hbe]
      obtain ⟨a,haC,S',qpo,qj1,b,q0g,qfy⟩:=qm8
      set HW:=Extra.filter (fun k=>2≤ (orIn n C (n+k)).card)
      have qiy:S'.card≤ HW.card+1:=q8j a haC b q0g S' (Finset.card_pos.mp (by omega)) qj1 qfy
      have qiz:HW.card≤ Extra.card:=Finset.card_le_card (Finset.filter_subset _ _)
      omega
lemma main (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (s:Fin n→ Bool)
  (q03:∀ u v:Fin n,G.Adj u v→ s u≠ s v) (h4:NoFourCycle G)
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C):
  ¬ ∃ g1 g2:ℕ,g1≠ g2∧ (∀ k:ℕ,k∈ junk G C↔ k=g1∨ k=g2)∧
   (∃ (Ci Di:Finset (Fin n)) (z zp:Fin n),G.Adj z zp∧ z∈ Ci∧ zp∈ Di∧
    (∀ c∈ Ci,G.Adj c zp)∧ (∀ d∈ Di,G.Adj d z)∧ 2≤ Ci.card∧ 2≤ Di.card∧
    ∀ x:Fin n→ Bool,gateVal n C g1 x=(decide (∃ c∈ Ci,x c=true) && decide (∃ d∈ Di,x d=true)))∧
   (∃ (Ci Di:Finset (Fin n)) (z zp:Fin n),G.Adj z zp∧ z∈ Ci∧ zp∈ Di∧
    (∀ c∈ Ci,G.Adj c zp)∧ (∀ d∈ Di,G.Adj d z)∧ 2≤ Ci.card∧ 2≤ Di.card∧
    ∀ x:Fin n→ Bool,gateVal n C g2 x=(decide (∃ c∈ Ci,x c=true) && decide (∃ d∈ Di,x d=true))):=by
 have q3u:∀ g Ci Di z zp,z000 G C g Ci Di z zp→ z000 G C g Di Ci zp z:=by
  intro g Ci Di z zp hf
  refine ⟨hf.1.symm,hf.2.2.1,hf.2.1,hf.2.2.2.2.1,hf.2.2.2.1,hf.2.2.2.2.2.2.1,hf.2.2.2.2.2.1,fun x=>?_⟩
  rw [hf.2.2.2.2.2.2.2 x,Bool.and_comm]
 have q8m:∀ g1 g2,g1 < g2→ (∀ k,k∈ junk G C↔ k=g1∨ k=g2)→
   ∀ C1 D1 z1 zp1 C2 D2 z2 zp2,
   z000 G C g1 C1 D1 z1 zp1→ z000 G C g2 C2 D2 z2 zp2→ False:=by
  intro g1 g2 q0y q00 C1 D1 z1 zp1 C2 D2 z2 zp2 hf1 hf2
  have q8n:∀ C2' D2' z2' zp2',z000 G C g2 C2' D2' z2' zp2'→
    s z1=s z2'→ s zp1=s zp2'→ False:=by
   intro C2' D2' z2' zp2' qjn hsz q1l
   by_cases hz:z1=z2'
   ·subst hz
    by_cases hzp:zp1=zp2'
    ·subst hzp;exact z022 q03 h4 hL q01 q0y q00 hf1 qjn
    ·exact z021 q03 h4 hL q01 q0y q00 hzp hf1 qjn
   ·by_cases hzp:zp1=zp2'
    ·subst hzp
     exact z021 q03 h4 hL q01 q0y q00 hz
      (q3u g1 C1 D1 z1 zp1 hf1) (q3u g2 C2' D2' z2' zp1 qjn)
    ·exact z020 q03 h4 hL q01 q0y q00 hz hzp hsz q1l hf1 qjn
  by_cases hsz:s z1=s z2
  ·have q1l:s zp1=s zp2:=
    z015 (q03 z1 zp1 hf1.1).symm (by rw [hsz];exact (q03 z2 zp2 hf2.1).symm)
   exact q8n C2 D2 z2 zp2 hf2 hsz q1l
  ·have qpg:s z1=s zp2:=z015 hsz (q03 z2 zp2 hf2.1).symm
   have qm9:s zp1=s z2:=z015 (q03 z1 zp1 hf1.1).symm (Ne.symm hsz)
   exact q8n D2 C2 zp2 z2 (q3u g2 C2 D2 z2 zp2 hf2) qpg qm9
 rintro ⟨g1,g2,qma,q00,⟨C1,D1,z1,zp1,hf1⟩,⟨C2,D2,z2,zp2,hf2⟩⟩
 rcases Nat.lt_or_gt_of_ne qma with hlt | hgt
 ·exact q8m g1 g2 hlt q00 C1 D1 z1 zp1 C2 D2 z2 zp2 hf1 hf2
 ·exact q8m g2 g1 hgt (fun k=>by rw [q00 k,or_comm]) C2 D2 z2 zp2 C1 D1 z1 zp1 hf2 hf1
end N5
lemma N5:∀ (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:PEqualNP.CircuitLowerBounds.Circuit) (s:Fin n→ Bool),
 (∀ u v:Fin n,G.Adj u v→ s u≠ s v)→ PEqualNP.TopForm.NoFourCycle G→ PEqualNP.TopForm.IsLeastAO G C→
 PEqualNP.Core.IsLiftFixedPoint G C→
 ¬ ∃ g1 g2:ℕ,g1≠ g2∧ (∀ k:ℕ,k∈ PEqualNP.TopForm.junk G C↔ k=g1∨ k=g2)∧
  (∃ (Ci Di:Finset (Fin n)) (z zp:Fin n),G.Adj z zp∧ z∈ Ci∧ zp∈ Di∧ (∀ c∈ Ci,G.Adj c zp)∧ (∀ d∈ Di,G.Adj d z)∧ 2≤ Ci.card∧ 2≤ Di.card∧ ∀ x:Fin n→ Bool,PEqualNP.EdgeOwnership.gateVal n C g1 x=(decide (∃ c∈ Ci,x c=true) && decide (∃ d∈ Di,x d=true)))∧
  (∃ (Ci Di:Finset (Fin n)) (z zp:Fin n),G.Adj z zp∧ z∈ Ci∧ zp∈ Di∧ (∀ c∈ Ci,G.Adj c zp)∧ (∀ d∈ Di,G.Adj d z)∧ 2≤ Ci.card∧ 2≤ Di.card∧ ∀ x:Fin n→ Bool,PEqualNP.EdgeOwnership.gateVal n C g2 x=(decide (∃ c∈ Ci,x c=true) && decide (∃ d∈ Di,x d=true))):=by
 intro n G _ C s hbip h4 hL hLift
 exact N5.main n G C s hbip h4 hL hLift
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm
def setOr {n:ℕ} (A:Finset (Fin n)) (x:Fin n→ Bool):Bool:=
 decide (∃ a∈ A,x a=true)
def setProduct {n:ℕ} (A B:Finset (Fin n)) (x:Fin n→ Bool):Bool:=
 setOr A x && setOr B x
lemma q158 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
   (x:Fin n→ Bool):
   graphFun G ∅ x=true↔ ∃ u v:Fin n,G.Adj u v∧ x u=true∧ x v=true:=by
 apply @N5.z073
 all_goals assumption
lemma q79 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
   (u v:Fin n):graphFun G ∅ (pairInput u v)=true↔ G.Adj u v:=by
 apply @N5.z074
 all_goals assumption
lemma setOr_pair {n:ℕ} (A:Finset (Fin n)) (u v:Fin n):
   setOr A (pairInput u v)=true↔ u∈ A∨ v∈ A:=by
 simp only [setOr,Z1,pairInput]
 constructor
 · rintro ⟨a,ha,rfl | rfl⟩
   · exact Or.inl ha
   · exact Or.inr ha
 · rintro (hu | hv)
   · exact ⟨u,hu,Or.inl rfl⟩
   · exact ⟨v,hv,Or.inr rfl⟩
lemma q53 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] (h4:NoFourCycle G) {A B:Finset (Fin n)}
   (hAB:∀ a∈ A,∀ b∈ B,G.Adj a b):A.card≤ 1∨ B.card≤ 1:=by
 by_cases ha:A.card≤ 1
 · exact Or.inl ha
 · right
   obtain ⟨a,haA,c,hcA,hac⟩:=Finset.one_lt_card.mp (by omega:1 < A.card)
   have hsub:B⊆ Finset.univ.filter (fun w=> G.Adj a w∧ G.Adj c w):=by
     intro b hb
     simp only [Z0,Z7,true_and]
     exact ⟨hAB a haA b hb,hAB c hcA b hb⟩
   exact (Finset.card_le_card hsub).trans (h4 a c hac)
lemma q30 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] {A B C D:Finset (Fin n)}
   (hBD:∀ b∈ B,∀ d∈ D,¬ G.Adj b d)
   (hclean:∀ x:Fin n→ Bool,
     setProduct A B x=true→ setProduct C D x=true→ graphFun G ∅ x=true)
   {u:Fin n} (hu:u∈ A ∩ C):
   (∀ b∈ B,G.Adj u b)∨ (∀ d∈ D,G.Adj u d):=by
 by_contra h
 push Not at h
 obtain ⟨⟨b,hb,hub⟩,⟨d,hd,hud⟩⟩:=h
 let x:Fin n→ Bool:=fun v=> decide (v=u∨ v=b∨ v=d)
 have hxu:x u=true:=by simp [x]
 have hxb:x b=true:=by simp [x]
 have hxd:x d=true:=by simp [x]
 have hf:=hclean x
   (by simp only [setProduct,Z12,setOr,Z1]
       exact ⟨⟨u,(Z5.mp hu).1,hxu⟩,⟨b,hb,hxb⟩⟩)
   (by simp only [setProduct,Z12,setOr,Z1]
       exact ⟨⟨u,(Z5.mp hu).2,hxu⟩,⟨d,hd,hxd⟩⟩)
 obtain ⟨v,w,hvw,hv,hw⟩:=(q158 x).mp hf
 simp only [x,Z1] at hv hw
 rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
 · exact G.loopless.irrefl _ hvw
 · exact hub hvw
 · exact hud hvw
 · exact hub hvw.symm
 · exact G.loopless.irrefl _ hvw
 · exact hBD _ hb _ hd hvw
 · exact hud hvw.symm
 · exact hBD _ hb _ hd hvw.symm
 · exact G.loopless.irrefl _ hvw
def universalTo {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
   (B:Finset (Fin n)):Finset (Fin n):=
 Finset.univ.filter fun u=> ∀ b∈ B,G.Adj u b
lemma q58 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] (h4:NoFourCycle G) {B:Finset (Fin n)}
   (hB:2≤ B.card):(universalTo G B).card≤ 1:=by
 have h:=q53 h4 (A:=universalTo G B) (B:=B) (by
   intro a ha b hb
   exact (Z0.mp ha).2 b hb)
 omega
lemma q109 {n:ℕ} (A B:Finset (Fin n)) (x:Fin n→ Bool):
   setProduct A B x=setProduct B A x:=by
 exact Bool.and_comm _ _
lemma q29 {n:ℕ} {G:SimpleGraph (Fin n)}
   (s:Fin n→ Bool) (hs:∀ u v,G.Adj u v→ s u≠ s v)
   {u v:Fin n} (huv:s u=s v):¬ G.Adj u v:=by
 intro h
 exact hs u v h huv
lemma q81 {n:ℕ} {A B C D:Finset (Fin n)}
   (s:Fin n→ Bool)
   (hAs:∀ a∈ A,s a=false) (hBs:∀ b∈ B,s b=true)
   (hCs:∀ c∈ C,s c=false) (hDs:∀ d∈ D,s d=true)
   (u v:Fin n):
   (setProduct A B (pairInput u v)=true∧
     setProduct C D (pairInput u v)=true)↔
   (u∈ A ∩ C∧ v∈ B ∩ D)∨ (v∈ A ∩ C∧ u∈ B ∩ D):=by
 have hABu:¬ (u∈ A∧ u∈ B):=by
   rintro ⟨ha,hb⟩
   have:=(hAs u ha).symm.trans (hBs u hb)
   contradiction
 have hABv:¬ (v∈ A∧ v∈ B):=by
   rintro ⟨ha,hb⟩
   have:=(hAs v ha).symm.trans (hBs v hb)
   contradiction
 have hCDu:¬ (u∈ C∧ u∈ D):=by
   rintro ⟨hc,hd⟩
   have:=(hCs u hc).symm.trans (hDs u hd)
   contradiction
 have hCDv:¬ (v∈ C∧ v∈ D):=by
   rintro ⟨hc,hd⟩
   have:=(hCs v hc).symm.trans (hDs v hd)
   contradiction
 have hADu:¬ (u∈ A∧ u∈ D):=by
   rintro ⟨ha,hd⟩
   have:=(hAs u ha).symm.trans (hDs u hd)
   contradiction
 have hADv:¬ (v∈ A∧ v∈ D):=by
   rintro ⟨ha,hd⟩
   have:=(hAs v ha).symm.trans (hDs v hd)
   contradiction
 simp only [setProduct,Z12,setOr_pair,Z5]
 tauto
namespace N21
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.TopForm
lemma q59 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] (h4:NoFourCycle G) {u z t v:Fin n}
   (huz:u≠ z) (hut:G.Adj u t) (hzt:G.Adj z t)
   (huv:G.Adj u v) (hzv:G.Adj z v):v=t:=by
 apply Finset.card_le_one.mp (h4 u z huz)
 · exact Z0.mpr ⟨Z7 _,⟨huv,hzv⟩⟩
 · exact Z0.mpr ⟨Z7 _,⟨hut,hzt⟩⟩
lemma q10 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] (h4:NoFourCycle G) {A:Finset (Fin n)}
   {u z t a:Fin n} (hu:u∈ A) (hz:z∈ A) (ha:a∈ A)
   (huz:u≠ z) (hut:G.Adj u t) (hzt:G.Adj z t)
   (hat:¬ G.Adj a t):¬ ∃ v:Fin n,∀ w∈ A,G.Adj w v:=by
 rintro ⟨v,hv⟩
 have hvt:=q59 h4 huz hut hzt (hv u hu) (hv z hz)
 exact hat (hvt ▸ hv a ha)
lemma q45 {n:ℕ} {A:Finset (Fin n)}
   (hA:2≤ A.card) (z:Fin n):∃ a∈ A,a≠ z:=by
 obtain ⟨a,ha,b,hb,hab⟩:=Finset.one_lt_card.mp (by omega:1 < A.card)
 by_cases haz:a=z
 · exact ⟨b,hb,fun hbz=> hab (haz.trans hbz.symm)⟩
 · exact ⟨a,ha,haz⟩
lemma q23 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] (s:Fin n→ Bool)
   (hbip:∀ u v,G.Adj u v→ s u≠ s v) (h4:NoFourCycle G)
   {A C D:Finset (Fin n)} {u z t:Fin n}
   (hu:u∈ A) (huz:u≠ z) (hut:G.Adj u t) (hzt:G.Adj z t)
   (hC:2≤ C.card) (hD:2≤ D.card)
   (hCt:∀ c∈ C,G.Adj c t) (hzD:∀ d∈ D,G.Adj z d):
   ∃ x:Fin n→ Bool,setOr A x=true∧ setProduct C D x=true∧
     graphFun G ∅ x=false:=by
 obtain ⟨c,hc,hcz⟩:=q45 hC z
 obtain ⟨d,hd,hdt⟩:=q45 hD t
 have hct:=hCt c hc
 have hzd:=hzD d hd
 have hud:¬ G.Adj u d:=by
   intro hud
   exact hdt (q59 h4 huz hut hzt hud hzd)
 have hcd:¬ G.Adj c d:=by
   intro hcd
   exact hdt (q59 h4 hcz hct hzt hcd hzd)
 have huc:¬ G.Adj u c:=by
   intro huc
   have h1:=hbip u t hut
   have h2:=hbip c t hct
   have h3:=hbip u c huc
   cases hsu:s u <;> cases hsc:s c <;> cases hst:s t <;> simp_all
 let x:Fin n→ Bool:=fun v=> decide (v=u∨ v=c∨ v=d)
 have hxu:x u=true:=by simp [x]
 have hxc:x c=true:=by simp [x]
 have hxd:x d=true:=by simp [x]
 refine ⟨x,?_,?_,?_⟩
 · simp only [setOr,Z1]
   exact ⟨u,hu,hxu⟩
 · simp only [setProduct,Z12,setOr,Z1]
   exact ⟨⟨c,hc,hxc⟩,⟨d,hd,hxd⟩⟩
 · apply Z14.mpr
   intro hf
   obtain ⟨v,w,hvw,hv,hw⟩:=(q158 x).mp hf
   simp only [x,Z1] at hv hw
   rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
   · exact G.loopless.irrefl _ hvw
   · exact huc hvw
   · exact hud hvw
   · exact huc hvw.symm
   · exact G.loopless.irrefl _ hvw
   · exact hcd hvw
   · exact hud hvw.symm
   · exact hcd hvw.symm
   · exact G.loopless.irrefl _ hvw
lemma q28 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] (h4:NoFourCycle G) {B:Finset (Fin n)}
   {u z t:Fin n} (huz:u≠ z) (hut:G.Adj u t) (hzt:G.Adj z t)
   (hB:2≤ B.card) (huB:∀ b∈ B,G.Adj u b):
   ∃ x:Fin n→ Bool,setProduct {u,z} B x=true∧ graphFun G ∅ x=false:=by
 obtain ⟨b,hb,hbt⟩:=q45 hB t
 have hzb:¬ G.Adj z b:=by
   intro hzb
   exact hbt (q59 h4 huz hut hzt (huB b hb) hzb)
 refine ⟨pairInput z b,?_,?_⟩
 · simp only [setProduct,Z12,setOr_pair]
   exact ⟨Or.inl (by simp),Or.inr hb⟩
 · apply Z14.mpr
   intro hF
   exact hzb ((q79 z b).mp hF)
end N21
lemma q127 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
   {A:Finset (Fin n)} (v:Fin n):
   (∀ x:Fin n→ Bool,setOr A x=true→ x v=true→ graphFun G ∅ x=true)↔
     ∀ a∈ A,G.Adj a v:=by
 constructor
 · intro h a ha
   apply (q79 a v).mp
   exact h (pairInput a v) ((setOr_pair A a v).mpr (Or.inl ha)) (by simp [pairInput])
 · intro h x hx hv
   obtain ⟨a,ha,hxa⟩:=of_decide_eq_true hx
   exact (q158 x).mpr ⟨a,v,h a ha,hxa,hv⟩
lemma q167 {n:ℕ} (A B:Finset (Fin n)):
   (∀ x:Fin n→ Bool,setOr A x=true→ setOr B x=true)↔ A⊆ B:=by
 constructor
 · intro h a ha
   have hv:=h (fun v=> decide (v=a)) (by
     simp only [setOr,Z1]
     exact ⟨a,ha,by simp⟩)
   simp only [setOr,Z1] at hv
   obtain ⟨b,hb,rfl⟩:=hv
   exact hb
 · intro h x hx
   simp only [setOr,Z1] at hx ⊢
   obtain ⟨a,ha,hxa⟩:=hx
   exact ⟨a,h ha,hxa⟩
lemma q15 {n:ℕ} {G:SimpleGraph (Fin n)}
   {A B:Finset (Fin n)}
   (hA:¬ ∃ v:Fin n,∀ a∈ A,G.Adj a v)
   (hB:∃ v:Fin n,∀ b∈ B,G.Adj b v):
   ¬ ∀ x:Fin n→ Bool,setOr A x=true→ setOr B x=true:=by
 intro h
 obtain ⟨v,hv⟩:=hB
 exact hA ⟨v,fun a ha=> hv a ((q167 A B).mp h ha)⟩
lemma q4 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] {A:Finset (Fin n)}
   (hA:¬ ∃ v:Fin n,∀ a∈ A,G.Adj a v) (v:Fin n):
   ∃ x:Fin n→ Bool,setOr A x=true∧ x v=true∧ graphFun G ∅ x=false:=by
 have hex:∃ a∈ A,¬ G.Adj a v:=by
   by_contra h
   apply hA
   refine ⟨v,?_⟩
   intro a ha
   by_contra hav
   exact h ⟨a,ha,hav⟩
 obtain ⟨a,ha,hav⟩:=hex
 refine ⟨pairInput a v,(setOr_pair A a v).mpr (Or.inl ha),by simp [pairInput],?_⟩
 apply Z14.mpr
 intro hf
 exact hav ((q79 a v).mp hf)
namespace N18
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.TopForm
end N18
namespace N3
open PEqualNP.MetaComplexity.NestedCover
end N3
namespace N10
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
def stepWire (w:List Bool) (g:Gate):List Bool:=
 w++[g.op.eval (g.inputs.map fun i=> w.getD i false)]
lemma q131 (C:Circuit) (x:List Bool):
 C.wires x=C.gates.foldl stepWire x:=rfl
lemma q62 (gs:List Gate) (w:List Bool):
   (gs.foldl stepWire w).length=w.length+gs.length:=by
 apply @N5.z065
 all_goals assumption
lemma q60 (gs:List Gate) (w:List Bool) (i:ℕ) (hi:i < w.length):
   (gs.foldl stepWire w).getD i false=w.getD i false:=by
 apply @N5.z064
 all_goals assumption
lemma q117 (w:List Bool) (i:ℕ) (hi:w.length≤ i):
   w.getD i false=false:=by
 simp [Z8,List.getElem?_eq_none hi]
lemma q168 (n:ℕ) (C:Circuit) (x:Fin n→ Bool):
   (C.wires (List.ofFn x)).length=n+C.gates.length:=by
 rw [q131,q62,List.length_ofFn]
lemma split_gates (gs:List Gate) (j:ℕ) (hj:j < gs.length):
   ∃ (pre post:List Gate) (gj:Gate),
     gs=pre++gj::post∧ pre.length=j∧ gs[j]'hj=gj:=by
 refine ⟨gs.take j,gs.drop (j+1),gs[j]'hj,?_,by simp;omega,rfl⟩
 rw [List.cons_getElem_drop_succ,List.take_append_drop]
def W (n:ℕ) (C:Circuit) (x:Fin n→ Bool) (u:ℕ):Bool:=
 (C.wires (List.ofFn x)).getD u false
lemma gateAt_eq (C:Circuit) (k:ℕ) (hk:k < C.gates.length):gateAt C k=C.gates[k]:=by
 apply @N5.z068
 all_goals assumption
lemma W_gate (n:ℕ) (C:Circuit) (x:Fin n→ Bool) (k:ℕ) (hk:k < C.gates.length):
   W n C x (n+k)=(gateAt C k).op.eval ((gateAt C k).inputs.map fun i=>
     if i < n+k then W n C x i else false):=by
 obtain ⟨pre,post,gj,hgs,hpre_len,hgj⟩:=split_gates C.gates k hk
 have hga:gateAt C k=gj:=by rw [gateAt_eq C k hk];exact hgj
 rw [hga]
 let w0:=pre.foldl stepWire (List.ofFn x)
 have hw0_len:w0.length=n+k:=by
   simp [w0,q62,hpre_len]
 have hCj:W n C x (n+k)=gj.op.eval (gj.inputs.map fun i=> w0.getD i false):=by
   simp only [W]
   rw [q131,hgs,List.foldl_append,List.foldl_cons]
   rw [q60 post (stepWire w0 gj) (n+k) (by simp [stepWire];omega)]
   simp [stepWire,Z8,hw0_len]
 rw [hCj]
 congr 1
 refine List.map_congr_left fun i _=> ?_
 by_cases hi:i < n+k
 · simp only [hi,↓reduceIte]
   simp only [W]
   rw [q131,hgs,List.foldl_append]
   exact (q60 (gj::post) w0 i (by omega)).symm
 · simp only [hi,↓reduceIte]
   exact q117 w0 i (by omega)
lemma W_input (n:ℕ) (C:Circuit) (x:Fin n→ Bool) (u:ℕ) (hu:u < n):
   W n C x u=x ⟨u,hu⟩:=by
 apply @N5.z144
 all_goals assumption
open PEqualNP.CleanedNonEdge in
lemma q145 (n:ℕ) (gs:List Gate) (cs:List (List ℕ)):
   (gs.foldl (orStep n) cs).length=cs.length+gs.length:=by
 apply @N5.z062
 all_goals assumption
open PEqualNP.CleanedNonEdge in
lemma q102 (n:ℕ) (cs:List (List ℕ)) (g:Gate) (x:ℕ):
   x∈ (orStep n cs g).getD cs.length []↔ x=cs.length∨ (g.op=GateOp.or∧
     ∃ w∈ g.inputs,n≤ w∧ w < n+cs.length∧ x∈ cs.getD (w - n) []):=by
 by_cases h:g.op=GateOp.or
 · simp only [orStep,Z8,List.getElem?_append_right le_rfl,h,
     ↓reduceIte,true_and,Nat.sub_self,List.getElem?_cons_zero,Option.getD_some,
     Z10,List.mem_flatMap,List.mem_filter,Z1]
   constructor
   · rintro (h1 | ⟨w,⟨hw,hn,hlt⟩,hx⟩)
     · exact Or.inl h1
     · exact Or.inr ⟨w,hw,hn,hlt,hx⟩
   · rintro (h1 | ⟨w,hw,hn,hlt,hx⟩)
     · exact Or.inl h1
     · exact Or.inr ⟨w,⟨hw,hn,hlt⟩,hx⟩
 · simp [orStep,Z8,h]
open PEqualNP.CleanedNonEdge in
lemma q123 (n:ℕ) (cs:List (List ℕ)) (g:Gate) (m:ℕ) (hm:m < cs.length):
   (orStep n cs g).getD m []=cs.getD m []:=by
 simp [orStep,Z8,List.getElem?_append_left hm]
open PEqualNP.CleanedNonEdge in
lemma q121 (n:ℕ) (gs:List Gate) (cs:List (List ℕ)) (k:ℕ)
   (hk:k < cs.length):
   (gs.foldl (orStep n) cs).getD k []=cs.getD k []:=by
 apply @N5.z061
 all_goals assumption
open PEqualNP.CleanedNonEdge in
lemma q122 (n:ℕ) (C:Circuit) (k x:ℕ) (hk:k < C.gates.length):
   x∈ (orSets n C).getD k []↔ x=k∨ ((gateAt C k).op=GateOp.or∧
     ∃ w∈ (gateAt C k).inputs,n≤ w∧ w < n+k∧ x∈ (orSets n C).getD (w - n) []):=by
 obtain ⟨pre,post,gk,hgs,hpre_len,hgk⟩:=split_gates C.gates k hk
 have hga:gateAt C k=gk:=by rw [gateAt_eq C k hk];exact hgk
 rw [hga]
 have hc:orSets n C=post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk):=by
   simp only [orSets]
   rw [hgs,List.foldl_append,List.foldl_cons]
 have hl0:(pre.foldl (orStep n) []).length=k:=by
   rw [q145];simp [hpre_len]
 have hl1:(orStep n (pre.foldl (orStep n) []) gk).length=k+1:=by
   simp [orStep,hl0]
 have h1:(orSets n C).getD k []=(orStep n (pre.foldl (orStep n) []) gk).getD k []:=by
   rw [hc,q121 n post _ k (by omega)]
 have h2:∀ m,m < k→ (orSets n C).getD m []=(pre.foldl (orStep n) []).getD m []:=by
   intro m hm
   rw [hc,q121 n post _ m (by omega)]
   exact q123 n _ gk m (by omega)
 have h3:=q102 n (pre.foldl (orStep n) []) gk x
 rw [hl0] at h3
 rw [h1,h3]
 constructor
 · rintro (h | ⟨hop,w,hw,hn,hlt,hx⟩)
   · exact Or.inl h
   · exact Or.inr ⟨hop,w,hw,hn,hlt,by rw [h2 (w - n) (by omega)];exact hx⟩
 · rintro (h | ⟨hop,w,hw,hn,hlt,hx⟩)
   · exact Or.inl h
   · exact Or.inr ⟨hop,w,hw,hn,hlt,by rw [← h2 (w - n) (by omega)];exact hx⟩
lemma W_or (n:ℕ) (C:Circuit) (x:Fin n→ Bool) (r:ℕ) (hr:r < C.gates.length)
   (hop:(gateAt C r).op=GateOp.or) (i:ℕ) (hi:i∈ (gateAt C r).inputs)
   (hlt:i < n+r) (hv:W n C x i=true):W n C x (n+r)=true:=by
 rw [W_gate n C x r hr,hop]
 simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
 exact ⟨i,hi,by rw [ite_eq_left hlt];exact hv⟩
lemma W_and (n:ℕ) (C:Circuit) (x:Fin n→ Bool) (r:ℕ) (hr:r < C.gates.length)
   (hop:(gateAt C r).op=GateOp.and)
   (h:∀ i∈ (gateAt C r).inputs,i < n+r∧ W n C x i=true):
   W n C x (n+r)=true:=by
 rw [W_gate n C x r hr,hop]
 simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
 intro i hi
 rw [ite_eq_left (h i hi).1];exact (h i hi).2
open PEqualNP.CleanedNonEdge in
lemma reach_val (n:ℕ) (C:Circuit) (x:Fin n→ Bool) (g:ℕ)
   (hv:W n C x (n+g)=true):
   ∀ k,k < C.gates.length→ g∈ (orSets n C).getD k []→ W n C x (n+k)=true:=by
 intro k
 induction k using Nat.strong_induction_on with
 | _ k ih=>
   intro hk hmem
   rcases (q122 n C k g hk).mp hmem with h | ⟨hop,w,hw,hn,hlt,hx⟩
   · rw [← h];exact hv
   · have h3:=ih (w - n) (by omega) (by omega) hx
     have e:n+(w - n)=w:=by omega
     rw [e] at h3
     exact W_or n C x k hk hop w hw hlt h3
open PEqualNP.CleanedNonEdge in
lemma reach_up (n:ℕ) (C:Circuit) (x:Fin n→ Bool) (w g:ℕ)
   (h:OrReaches n C w g) (hv:W n C x (n+g)=true):W n C x w=true:=by
 obtain ⟨hn,hmem⟩:=h
 by_cases hk:w - n < C.gates.length
 · have h3:=reach_val n C x g hv (w - n) hk hmem
   have e:n+(w - n)=w:=by omega
   rw [e] at h3
   exact h3
 · exfalso
   have hlen:(orSets n C).length=C.gates.length:=by
     unfold orSets;rw [q145];simp
   have hge:(orSets n C).length≤ w - n:=by omega
   rw [Z8,List.getElem?_eq_none hge] at hmem
   simp at hmem
open PEqualNP.EdgeOwnership in
lemma cones_len (n:ℕ) (gs:List Gate) (cs:List (List ℕ)):
   (gs.foldl (coneStep n) cs).length=cs.length+gs.length:=by
 apply @N5.z059
 all_goals assumption
open PEqualNP.EdgeOwnership in
lemma cones_char (n:ℕ) (gs:List Gate):
   ∀ i j,i∈ (gs.foldl (coneStep n) []).getD j []↔
     j < gs.length∧ ∃ w∈ (gs.getD j ⟨GateOp.or,[]⟩).inputs,n≤ w∧ w < n+j∧
       (i=w - n∨ i∈ (gs.foldl (coneStep n) []).getD (w - n) []):=by
 induction gs using List.reverseRecOn with
 | nil=> intro i j;simp
 | append_singleton gs g ih=>
   intro i j
   rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
   have hlen:(gs.foldl (coneStep n) []).length=gs.length:=by
     rw [cones_len];simp
   have key:∀ k,k < gs.length→
       (coneStep n (gs.foldl (coneStep n) []) g).getD k []=
         (gs.foldl (coneStep n) []).getD k []:=by
     intro k hk
     simp only [coneStep,Z8]
     rw [List.getElem?_append_left (by omega)]
   rcases Nat.lt_trichotomy j gs.length with h | h | h
   · have e1:(gs++[g]).getD j ⟨GateOp.or,[]⟩=gs.getD j ⟨GateOp.or,[]⟩:=by
       simp only [Z8]
       rw [List.getElem?_append_left h]
     rw [key j h,ih i j,e1]
     constructor
     · rintro ⟨_,w,hw,h1,h2,h3⟩
       refine ⟨by simp;omega,w,hw,h1,h2,?_⟩
       rw [key (w - n) (by omega)]
       exact h3
     · rintro ⟨_,w,hw,h1,h2,h3⟩
       refine ⟨h,w,hw,h1,h2,?_⟩
       rw [key (w - n) (by omega)] at h3
       exact h3
   · subst h
     have e1:(gs++[g]).getD gs.length ⟨GateOp.or,[]⟩=g:=by
       simp [Z8]
     have e2:(coneStep n (gs.foldl (coneStep n) []) g).getD gs.length []=
         (g.inputs.filter (fun w=> decide (n≤ w∧ w < n+gs.length))).flatMap
           (fun w=> (w - n)::(gs.foldl (coneStep n) []).getD (w - n) []):=by
       simp only [coneStep,Z8]
       rw [List.getElem?_append_right (by omega)]
       simp [hlen]
     rw [e2,e1]
     simp only [List.mem_flatMap,List.mem_filter,Z10,Z1]
     constructor
     · rintro ⟨w,⟨hw,h1,h2⟩,h3⟩
       refine ⟨by simp,w,hw,h1,h2,?_⟩
       rw [key (w - n) (by omega)]
       exact h3
     · rintro ⟨_,w,hw,h1,h2,h3⟩
       rw [key (w - n) (by omega)] at h3
       exact ⟨w,⟨hw,h1,h2⟩,h3⟩
   · have e0:(coneStep n (gs.foldl (coneStep n) []) g).getD j []=[]:=by
       simp only [coneStep,Z8]
       rw [List.getElem?_eq_none (by simp;omega)]
       rfl
     rw [e0]
     constructor
     · intro h0;simp at h0
     · rintro ⟨h0,_⟩
       simp at h0
       omega
open PEqualNP.EdgeOwnership in
lemma inCone_iff (n:ℕ) (C:Circuit) (i j:ℕ):
   InCone n C i j↔ j < C.gates.length∧ ∃ k,k < j∧ n+k∈ (gateAt C j).inputs∧
     (i=k∨ InCone n C i k):=by
 have h:=cones_char n C.gates i j
 unfold InCone cones gateAt
 rw [h]
 constructor
 · rintro ⟨h0,w,hw,h1,h2,h3⟩
   refine ⟨h0,w - n,by omega,?_,h3⟩
   have:n+(w - n)=w:=by omega
   rw [this]
   exact hw
 · rintro ⟨h0,k,hk,hw,h3⟩
   refine ⟨h0,n+k,hw,by omega,by omega,?_⟩
   have:n+k - n=k:=by omega
   rw [this]
   exact h3
lemma gateAt_mem' (C:Circuit) (j:ℕ) (hj:j < C.gates.length):gateAt C j∈ C.gates:=by
 apply @N5.z069
 all_goals assumption
open PEqualNP.CleanedNonEdge in
lemma q146 (n:ℕ) (C:Circuit) (k:ℕ) (hk:k < C.gates.length)
   (hop:(gateAt C k).op=GateOp.or) (w:ℕ) (hw:w∈ (gateAt C k).inputs)
   (hlt:w < n+k) (g:ℕ) (h:OrReaches n C w g):OrReaches n C (n+k) g:=by
 obtain ⟨hn,hmem⟩:=h
 refine ⟨by omega,?_⟩
 have e:n+k - n=k:=by omega
 rw [e]
 exact (q122 n C k g hk).mpr (Or.inr ⟨hop,w,hw,hn,hlt,hmem⟩)
open PEqualNP.CleanedNonEdge in
lemma q161 (n:ℕ) (C:Circuit) (k:ℕ) (hk:k < C.gates.length):
   OrReaches n C (n+k) k:=by
 apply @N5.z115
 all_goals assumption
lemma orIn_mem (n:ℕ) (C:Circuit) (w:ℕ) (i:Fin n):
   i∈ PEqualNP.TopForm.orIn n C w↔ ((i:ℕ)=w∨ ∃ k < C.gates.length,
     PEqualNP.CleanedNonEdge.OrReaches n C w k∧ (gateAt C k).op=GateOp.or∧
       (i:ℕ)∈ (gateAt C k).inputs):=by
 unfold PEqualNP.TopForm.orIn
 simp only [Z0,Z7,true_and]
open PEqualNP.CleanedNonEdge in
lemma down (n:ℕ) (C:Circuit) (x:Fin n→ Bool)
   (hAO:∀ k < C.gates.length,(gateAt C k).op=GateOp.and∨ (gateAt C k).op=GateOp.or):
   ∀ w,W n C x w=true→ (∃ i:Fin n,i∈ PEqualNP.TopForm.orIn n C w∧ x i=true)∨
     ∃ k,k < C.gates.length∧ OrReaches n C w k∧ (gateAt C k).op=GateOp.and∧
       W n C x (n+k)=true:=by
 intro w
 induction w using Nat.strong_induction_on with
 | _ w ih=>
   intro hv
   by_cases hwn:w < n
   · left
     refine ⟨⟨w,hwn⟩,(orIn_mem n C w _).mpr (Or.inl rfl),?_⟩
     rw [← W_input n C x w hwn];exact hv
   · by_cases hk:w - n < C.gates.length
     · have hw:w=n+(w - n):=by omega
       set k:=w - n with hkdef
       rcases hAO k hk with hop | hop
       · right
         refine ⟨k,hk,?_,hop,?_⟩
         · rw [hw];exact q161 n C k hk
         · rw [← hw];exact hv
       · have hv2:=hv
         rw [hw,W_gate n C x k hk,hop] at hv2
         simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq] at hv2
         obtain ⟨i,hi,hiv⟩:=hv2
         split_ifs at hiv with hlt
         rcases ih i (by omega) hiv with ⟨j,hj,hxj⟩ | ⟨k',hk',hr,hop',hv'⟩
         · left
           refine ⟨j,?_,hxj⟩
           rw [orIn_mem] at hj ⊢
           right
           rcases hj with hj | ⟨k'',hk'',hr,hop'',hin⟩
           · refine ⟨k,hk,?_,hop,?_⟩
             · rw [hw];exact q161 n C k hk
             · rw [hj];exact hi
           · refine ⟨k'',hk'',?_,hop'',hin⟩
             rw [hw];exact q146 n C k hk hop i hi hlt k'' hr
         · right
           refine ⟨k',hk',?_,hop',hv'⟩
           rw [hw];exact q146 n C k hk hop i hi hlt k' hr
     · exfalso
       have hl:=q168 n C x
       have:W n C x w=false:=q117 _ w (by omega)
       rw [this] at hv;exact Bool.false_ne_true hv
open PEqualNP.EdgeOwnership in
lemma orSets_cone (n:ℕ) (C:Circuit):∀ m,m < C.gates.length→ ∀ k,
   k∈ (PEqualNP.CleanedNonEdge.orSets n C).getD m []→ k=m∨ InCone n C k m:=by
 intro m
 induction m using Nat.strong_induction_on with
 | _ m ih=>
   intro hm k hk
   rcases (q122 n C m k hm).mp hk with h | ⟨_,w,hw,hn,hlt,hx⟩
   · exact Or.inl h
   · right
     have h2:=ih (w - n) (by omega) (by omega) k hx
     have e:n+(w - n)=w:=by omega
     exact (inCone_iff n C k m).mpr ⟨hm,w - n,by omega,by rw [e];exact hw,h2⟩
open PEqualNP.EdgeOwnership in
lemma reach_cone (n:ℕ) (C:Circuit) (j:ℕ) (hj:j < C.gates.length) (o:ℕ)
   (ho:o∈ (gateAt C j).inputs) (hlt:o < n+j) (k:ℕ)
   (h:PEqualNP.CleanedNonEdge.OrReaches n C o k):InCone n C k j:=by
 obtain ⟨hn,hmem⟩:=h
 have h2:=orSets_cone n C (o - n) (by omega) k hmem
 have e:n+(o - n)=o:=by omega
 exact (inCone_iff n C k j).mpr ⟨hj,o - n,by omega,by rw [e];exact ho,h2⟩
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
lemma allOnes {n:ℕ} {C:Circuit} (hAO:IsAO2 n C):
   ∀ w < n+C.gates.length,W n C (fun _=> true) w=true:=by
 apply @N5.z138
 all_goals assumption
lemma orIn_val {n:ℕ} {C:Circuit} {w:ℕ} {u:Fin n}
   (hu:u∈ orIn n C w) (x:Fin n→ Bool) (hxu:x u=true):W n C x w=true:=by
 rcases (orIn_mem n C w u).mp hu with heq | ⟨k,hk,hr,hop,hin⟩
 · rw [← heq,W_input n C x u.val u.isLt]
   exact hxu
 · have hkv:W n C x (n+k)=true:=by
     apply W_or n C x k hk hop u.val hin (by have:=u.isLt;omega)
     rw [W_input n C x u.val u.isLt]
     exact hxu
   exact reach_up n C x w k hr hkv
lemma q72 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
   {C:Circuit} (hAO:IsAO2 n C) (hTF:TopForm G C)
   {g h j a b:ℕ} {f:(Fin n→ Bool)→ Bool}
   (hJ:∀ k∈ junk G C,k=g∨ k=h)
   (hj:j < C.gates.length) (hop:(gateAt C j).op=GateOp.and)
   (hinputs:(gateAt C j).inputs=[a,b]∨ (gateAt C j).inputs=[b,a])
   (hdom:∀ x,f x=true→ W n C x a=true)
   (hraw:∀ u:Fin n,∃ x,f x=true∧ x u=true∧ graphFun G ∅ x=false)
   (hg:∃ x,f x=true∧ gateVal n C g x=true∧ graphFun G ∅ x=false)
   (hh:∃ x,f x=true∧ gateVal n C h x=true∧ graphFun G ∅ x=false):
   ¬ BelowF G C j:=by
 intro hclean
 have hb:b∈ (gateAt C j).inputs:=by
   rcases hinputs with hlist | hlist <;> simp [hlist]
 have hback:=hAO.2.1 j hj
 have hbval:=allOnes hAO b (by have:=hback b hb;omega)
 have hwit:∃ x,f x=true∧ W n C x b=true∧ graphFun G ∅ x=false:=by
   rcases down n C (fun _=> true) (fun k hk=> hAO.1 _ (gateAt_mem' C k hk)) b hbval with
     ⟨u,hu,_⟩ | ⟨k,hk,hr,hopk,_⟩
   · obtain ⟨x,hfx,hxu,hneg⟩:=hraw u
     exact ⟨x,hfx,orIn_val hu x hxu,hneg⟩
   · have hnotbelow:¬ BelowF G C k:=by
       intro hkclean
       exact hTF k hk j hj hopk hkclean hop (reach_cone n C j hj b hb (hback b hb) k hr)
     have hkJ:k∈ junk G C:=by
       apply Z0.mpr
       refine ⟨Z9.mpr hk,hopk,hk,?_⟩
       unfold BelowF at hnotbelow
       push Not at hnotbelow
       obtain ⟨x,hx,hf⟩:=hnotbelow
       exact ⟨x,hx,by simpa using hf⟩
     rcases hJ k hkJ with rfl | rfl
     · obtain ⟨x,hfx,hgv,hneg⟩:=hg
       exact ⟨x,hfx,reach_up n C x b _ hr hgv,hneg⟩
     · obtain ⟨x,hfx,hhv,hneg⟩:=hh
       exact ⟨x,hfx,reach_up n C x b _ hr hhv,hneg⟩
 obtain ⟨x,hfx,hbx,hneg⟩:=hwit
 have hjx:gateVal n C j x=true:=by
   apply W_and n C x j hj hop
   intro i hi
   refine ⟨hback i hi,?_⟩
   have hi2:i=a∨ i=b:=by
     rcases hinputs with hlist | hlist
     · simpa only [hlist,Z10,Z11,or_false] using hi
     · have hi3:i=b∨ i=a:=by
         simpa only [hlist,Z10,Z11,or_false] using hi
       exact hi3.symm
   rcases hi2 with rfl | rfl
   · exact hdom x hfx
   · exact hbx
 have:=hclean x hjx
 rw [hneg] at this
 exact Bool.false_ne_true this
lemma q116 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C)
   {j:ℕ} (hj:j < C.gates.length):
   (gateAt C j).inputs=[opnd C j 0,opnd C j 1]:=by
 apply @N5.z071
 all_goals assumption
lemma q13 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] {C:Circuit} (hAO:IsAO2 n C) (hTF:TopForm G C)
   {g h p j w:ℕ}
   (hJ:∀ k∈ junk G C,k=g∨ k=h)
   (hj:j < C.gates.length) (hop:(gateAt C j).op=GateOp.and)
   (hw:w∈ (gateAt C j).inputs) (hreach:OrReaches n C w p)
   (hraw:∀ u:Fin n,∃ x,
     gateVal n C p x=true∧ x u=true∧ graphFun G ∅ x=false)
   (hg:∃ x,gateVal n C p x=true∧ gateVal n C g x=true∧ graphFun G ∅ x=false)
   (hh:∃ x,gateVal n C p x=true∧ gateVal n C h x=true∧ graphFun G ∅ x=false):
   j=g∨ j=h:=by
 have hinputs:=q116 hAO hj
 have hdom:∀ x,gateVal n C p x=true→ W n C x w=true:=by
   intro x hx
   exact reach_up n C x w p hreach hx
 have hnotbelow:¬ BelowF G C j:=by
   have hw2:w=opnd C j 0∨ w=opnd C j 1:=by
     simpa only [hinputs,Z10,Z11,or_false] using hw
   rcases hw2 with rfl | rfl
   · exact q72 hAO hTF hJ hj hop (Or.inl hinputs) hdom hraw hg hh
   · exact q72 hAO hTF hJ hj hop (Or.inr hinputs) hdom hraw hg hh
 apply hJ j
 apply Z0.mpr
 refine ⟨Z9.mpr hj,hop,hj,?_⟩
 unfold BelowF at hnotbelow
 push Not at hnotbelow
 obtain ⟨x,hx,hf⟩:=hnotbelow
 exact ⟨x,hx,by simpa using hf⟩
lemma q138 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C)
   {j:ℕ} (hj:j < C.gates.length):
   (gateAt C j).op=GateOp.and∨ (gateAt C j).op=GateOp.or:=by
 exact hAO.1 _ (gateAt_mem' C j hj)
lemma q150 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C)
   {i j:ℕ} (hj:j < C.gates.length)
   (hread:n+i∈ (gateAt C j).inputs):i < j:=by
 have h:=hAO.2.1 j hj (n+i) hread
 omega
lemma q57 {n:ℕ} {C:Circuit}
   (hAO:IsAO2 n C) {p g:ℕ} {P:ℕ→ Prop}
   (hp:p < C.gates.length) (hg:g < C.gates.length)
   (hpg:n+p∈ (gateAt C g).inputs) (hPp:P p)
   (hlive:∀ i < C.gates.length,
     C.output=n+i∨ ∃ j < C.gates.length,n+i∈ (gateAt C j).inputs)
   (houtput:∀ i < C.gates.length,P i→ C.output≠ n+i)
   (hor:∀ i < C.gates.length,P i→ ∀ j < C.gates.length,
     (gateAt C j).op=GateOp.or→ n+i∈ (gateAt C j).inputs→ P j)
   (hand:∀ i < C.gates.length,P i→ ∀ j < C.gates.length,
     (gateAt C j).op=GateOp.and→ n+i∈ (gateAt C j).inputs→ j=g)
   (hoperand:∀ i < C.gates.length,P i→ n+i∈ (gateAt C g).inputs→ i=p):
   readers n C p={g}:=by
 have noLater:∀ d i,C.gates.length - i=d→ i < C.gates.length→ p < i→ P i→ False:=by
   intro d
   induction d using Nat.strong_induction_on with
   | ind d ih=>
     intro i hdi hi hpi hPi
     rcases hlive i hi with hout | ⟨j,hj,hread⟩
     · exact houtput i hi hPi hout
     · have hij:=q150 hAO hj hread
       rcases q138 hAO hj with handj | horj
       · have hjg:=hand i hi hPi j hj handj hread
         subst j
         have:=hoperand i hi hPi hread
         omega
       · exact ih (C.gates.length - j) (by omega) j rfl hj (by omega)
           (hor i hi hPi j hj horj hread)
 apply Finset.ext
 intro j
 simp only [readers,Z0,Z9,Z3]
 constructor
 · rintro ⟨hj,hread⟩
   have hpj:=q150 hAO hj hread
   rcases q138 hAO hj with handj | horj
   · exact hand p hp hPp j hj handj hread
   · exact False.elim (noLater _ j rfl hj hpj (hor p hp hPp j hj horj hread))
 · rintro rfl
   exact ⟨hg,hpg⟩
lemma q16 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] {C:Circuit} {p w:ℕ}
   (hraw:∀ u:Fin n,∃ x,
     gateVal n C p x=true∧ x u=true∧ graphFun G ∅ x=false)
   (hfilter:∃ v:Fin n,∀ x,
     W n C x w=true→ x v=true→ graphFun G ∅ x=true):
   ¬ OrReaches n C w p:=by
 intro hreach
 obtain ⟨v,hfilter⟩:=hfilter
 obtain ⟨x,hpx,hxv,hneg⟩:=hraw v
 have hw:=reach_up n C x w p hreach hpx
 have hf:=hfilter x hw hxv
 rw [hneg] at hf
 exact Bool.false_ne_true hf
lemma q27 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] {C:Circuit} (hAO:IsAO2 n C) (hTF:TopForm G C)
   (hcompute:PEqualNP.MetaComplexity.circuitFun n C=graphFun G ∅)
   {g h p:ℕ} (c:Fin 2) (hp:p < C.gates.length) (hgN:g < C.gates.length)
   (hJ:∀ k∈ junk G C,k=g∨ k=h)
   (hroot:opnd C g c=n+p)
   (hlive:∀ i < C.gates.length,
     C.output=n+i∨ ∃ j < C.gates.length,n+i∈ (gateAt C j).inputs)
   (hraw:∀ u:Fin n,∃ x,
     gateVal n C p x=true∧ x u=true∧ graphFun G ∅ x=false)
   (hg:∃ x,gateVal n C p x=true∧ gateVal n C g x=true∧ graphFun G ∅ x=false)
   (hh:∃ x,gateVal n C p x=true∧ gateVal n C h x=true∧ graphFun G ∅ x=false)
   (hgfilter:∃ v:Fin n,∀ x,
     W n C x (opnd C g (1 - c))=true→ x v=true→ graphFun G ∅ x=true)
   (hhfilter:∀ b:Fin 2,∃ v:Fin n,∀ x,
     W n C x (opnd C h b)=true→ x v=true→ graphFun G ∅ x=true):
   readers n C p={g}:=by
 have hpg:n+p∈ (gateAt C g).inputs:=by
   rw [← hroot,q116 hAO hgN]
   fin_cases c <;> simp
 have hnoother:¬ OrReaches n C (opnd C g (1 - c)) p:=
   q16 hraw hgfilter
 have hnoh:∀ b:Fin 2,¬ OrReaches n C (opnd C h b) p:=fun b=>
   q16 hraw (hhfilter b)
 apply q57 hAO (P:=fun i=> OrReaches n C (n+i) p)
   hp hgN hpg (q161 n C p hp) hlive
 · intro i _ hPi hout
   obtain ⟨x,hpx,_,hneg⟩:=hg
   have hv:=reach_up n C x (n+i) p hPi hpx
   rw [← hout] at hv
   change PEqualNP.MetaComplexity.circuitFun n C x=true at hv
   rw [hcompute,hneg] at hv
   exact Bool.false_ne_true hv
 · intro i _ hPi j hj hop hread
   exact q146 n C j hj hop (n+i) hread (hAO.2.1 j hj _ hread) p hPi
 · intro i _ hPi j hj hop hread
   rcases q13 hAO hTF hJ hj hop hread hPi hraw hg hh with hjg | hjh
   · exact hjg
   · subst j
     have hmem:n+i=opnd C h 0∨ n+i=opnd C h 1:=by
       simpa only [q116 hAO hj,Z10,Z11,or_false] using hread
     rcases hmem with heq | heq
     · exact False.elim (hnoh 0 (by rw [← heq];exact hPi))
     · exact False.elim (hnoh 1 (by rw [← heq];exact hPi))
 · intro i _ hPi hread
   have hmem0:n+i=opnd C g 0∨ n+i=opnd C g 1:=by
     simpa only [q116 hAO hgN,Z10,Z11,or_false] using hread
   have hmem:n+i=opnd C g c∨ n+i=opnd C g (1 - c):=by
     fin_cases c
     · simpa using hmem0
     · simpa using hmem0.symm
   rcases hmem with heq | heq
   · rw [hroot] at heq
     omega
   · exact False.elim (hnoother (by rw [← heq];exact hPi))
end N10
namespace N25
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
lemma q44 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] (h4:NoFourCycle G) {B:Finset (Fin n)}
   (hB:2≤ B.card) {u z:Fin n}
   (hu:∀ b∈ B,G.Adj u b) (hz:∀ b∈ B,G.Adj z b):u=z:=by
 apply Finset.card_le_one.mp (q58 h4 hB)
 · exact Z0.mpr ⟨Z7 _,hu⟩
 · exact Z0.mpr ⟨Z7 _,hz⟩
lemma q26 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] (h4:NoFourCycle G) {A B C D:Finset (Fin n)}
   (hB:2≤ B.card) (hD:2≤ D.card) {u z:Fin n}
   (huB:∀ b∈ B,G.Adj u b) (hzD:∀ d∈ D,G.Adj z d)
   (hBD:∀ b∈ B,∀ d∈ D,¬ G.Adj b d)
   (hclean:∀ x:Fin n→ Bool,
     setProduct A B x=true→ setProduct C D x=true→ graphFun G ∅ x=true):
   A ∩ C⊆ {u,z}:=by
 intro a ha
 rcases q30 hBD hclean ha with h | h
 · have he:=q44 h4 hB h huB
   simp [he]
 · have he:=q44 h4 hD h hzD
   simp [he]
lemma q38 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] (h4:NoFourCycle G) {A B:Finset (Fin n)}
   (hA:¬ ∃ v:Fin n,∀ a∈ A,G.Adj a v)
   (hB:2≤ B.card) {u a b w:Fin n}
   (huB:∀ v∈ B,G.Adj u v) (ha:a∈ A) (hb:b∈ B)
   (hw:w=a∨ w=b)
   (hclean:∀ x:Fin n→ Bool,
     setProduct A B x=true→ x w=true→ graphFun G ∅ x=true):a=u:=by
 rcases hw with hwa | hwb
 · subst w
   apply q44 h4 hB ?_ huB
   intro d hd
   apply (q79 a d).mp
   apply hclean (pairInput a d)
   · simp only [setProduct,Z12,setOr_pair]
     exact ⟨Or.inl ha,Or.inr hd⟩
   · simp [pairInput]
 · subst w
   exfalso
   apply hA
   refine ⟨b,?_⟩
   intro d hd
   apply (q79 d b).mp
   apply hclean (pairInput d b)
   · simp only [setProduct,Z12,setOr_pair]
     exact ⟨Or.inl hd,Or.inr hb⟩
   · simp [pairInput]
lemma q7 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] (s:Fin n→ Bool)
   (h4:NoFourCycle G) {A B C D:Finset (Fin n)}
   (hB:2≤ B.card) (hD:2≤ D.card) {u z:Fin n}
   (huB:∀ b∈ B,G.Adj u b) (hzD:∀ d∈ D,G.Adj z d)
   (hBD:∀ b∈ B,∀ d∈ D,¬ G.Adj b d)
   (hAs:∀ a∈ A,s a=false) (hBs:∀ b∈ B,s b=true)
   (hCs:∀ c∈ C,s c=false) (hDs:∀ d∈ D,s d=true)
   (hclean:∀ x:Fin n→ Bool,
     setProduct A B x=true→ setProduct C D x=true→ graphFun G ∅ x=true)
   (a b:Fin n)
   (hg:setProduct A B (pairInput a b)=true)
   (hh:setProduct C D (pairInput a b)=true):
   setProduct {u,z} B (pairInput a b)=true:=by
 have hs:=q26 h4 hB hD huB hzD hBD hclean
 rcases (q81 s hAs hBs hCs hDs a b).mp ⟨hg,hh⟩ with h | h
 · simp only [setProduct,Z12,setOr_pair]
   exact ⟨Or.inl (hs h.1),Or.inr (Z5.mp h.2).1⟩
 · simp only [setProduct,Z12,setOr_pair]
   exact ⟨Or.inr (hs h.1),Or.inl (Z5.mp h.2).1⟩
lemma q5 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] (s:Fin n→ Bool) (h4:NoFourCycle G)
   {A B:Finset (Fin n)}
   (hA:¬ ∃ v:Fin n,∀ a∈ A,G.Adj a v)
   (hB:2≤ B.card) {u z:Fin n} (huB:∀ b∈ B,G.Adj u b)
   (hAs:∀ a∈ A,s a=false) (hBs:∀ b∈ B,s b=true)
   {w:Fin n}
   (hclean:∀ x:Fin n→ Bool,
     setProduct A B x=true→ x w=true→ graphFun G ∅ x=true)
   (a b:Fin n) (hg:setProduct A B (pairInput a b)=true)
   (hw:pairInput a b w=true):
   setProduct {u,z} B (pairInput a b)=true:=by
 have hw':w=a∨ w=b:=of_decide_eq_true hw
 have ht:=(q81 s hAs hBs hAs hBs a b).mp ⟨hg,hg⟩
 simp only [Z5,and_self] at ht
 rcases ht with ⟨ha,hb⟩ | ⟨hb,ha⟩
 · have he:=q38 h4 hA hB huB ha hb hw' hclean
   simp only [setProduct,Z12,setOr_pair]
   exact ⟨Or.inl (by simp [he]),Or.inr hb⟩
 · have he:=q38 h4 hA hB huB hb ha hw'.symm hclean
   simp only [setProduct,Z12,setOr_pair]
   exact ⟨Or.inr (by simp [he]),Or.inl ha⟩
end N25
namespace N19
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
def CrossStar {n:ℕ} (G:SimpleGraph (Fin n))
   (A B:Finset (Fin n)):Prop:=
 ∃ u∈ A,∃ v∈ B,(∀ a∈ A,G.Adj a v)∧ ∀ b∈ B,G.Adj u b
lemma q134 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
   {A B:Finset (Fin n)} {u:Fin n} (hu:∀ b∈ B,G.Adj u b):
   ∀ x:Fin n→ Bool,setProduct A B x=true→ x u=true→ graphFun G ∅ x=true:=by
 intro x hx hxu
 simp only [setProduct,Z12] at hx
 have hb:=hx.2
 obtain ⟨b,hb,hxb⟩:=of_decide_eq_true hb
 exact (q158 x).mpr ⟨u,b,hu b hb,hxu,hxb⟩
lemma q112 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
   {A B:Finset (Fin n)} {u:Fin n} (hu:∀ a∈ A,G.Adj a u):
   ∀ x:Fin n→ Bool,setProduct A B x=true→ x u=true→ graphFun G ∅ x=true:=by
 intro x hx hxu
 simp only [setProduct,Z12] at hx
 have ha:=hx.1
 obtain ⟨a,ha,hxa⟩:=of_decide_eq_true ha
 exact (q158 x).mpr ⟨a,u,hu a ha,hxa,hxu⟩
lemma q1 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] {A B C D:Finset (Fin n)}
   (hAC:∀ a∈ A,∀ c∈ C,¬ G.Adj a c)
   (hBD:∀ b∈ B,∀ d∈ D,¬ G.Adj b d)
   (hclean:∀ x:Fin n→ Bool,
     setProduct A B x=true→ setProduct C D x=true→ graphFun G ∅ x=true)
   (hnoflag:¬ CrossStar G C D) {u v:Fin n}
   (hu:u∈ A ∩ C) (hv:v∈ B ∩ D):
   (∀ x:Fin n→ Bool,setProduct A B x=true→ x u=true→ graphFun G ∅ x=true)∨
   (∀ x:Fin n→ Bool,setProduct A B x=true→ x v=true→ graphFun G ∅ x=true):=by
 rcases q30 hBD hclean hu with huB | huD
 · exact Or.inl (q134 huB)
 have hswap:∀ x:Fin n→ Bool,
     setProduct B A x=true→ setProduct D C x=true→ graphFun G ∅ x=true:=by
   intro x hx hy
   exact hclean x (by simpa only [q109 B A] using hx)
     (by simpa only [q109 D C] using hy)
 rcases q30 hAC hswap hv with hvA | hvC
 · exact Or.inr (q112 (fun a ha=> (hvA a ha).symm))
 · exfalso
   exact hnoflag ⟨u,(Z5.mp hu).2,v,(Z5.mp hv).2,
     (fun c hc=> (hvC c hc).symm),huD⟩
lemma q0 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] (s:Fin n→ Bool)
   (hbip:∀ u v,G.Adj u v→ s u≠ s v)
   {A B C D:Finset (Fin n)}
   (hAs:∀ a∈ A,s a=false) (hBs:∀ b∈ B,s b=true)
   (hCs:∀ c∈ C,s c=false) (hDs:∀ d∈ D,s d=true)
   (hclean:∀ x:Fin n→ Bool,
     setProduct A B x=true→ setProduct C D x=true→ graphFun G ∅ x=true)
   (hnoflag:¬ CrossStar G C D) (u v:Fin n)
   (hg:setProduct A B (pairInput u v)=true)
   (hh:setProduct C D (pairInput u v)=true):
   (∀ x:Fin n→ Bool,setProduct A B x=true→ x u=true→ graphFun G ∅ x=true)∨
   (∀ x:Fin n→ Bool,setProduct A B x=true→ x v=true→ graphFun G ∅ x=true):=by
 have hAC:∀ a∈ A,∀ c∈ C,¬ G.Adj a c:=by
   intro a ha c hc
   exact q29 s hbip ((hAs a ha).trans (hCs c hc).symm)
 have hBD:∀ b∈ B,∀ d∈ D,¬ G.Adj b d:=by
   intro b hb d hd
   exact q29 s hbip ((hBs b hb).trans (hDs d hd).symm)
 rcases (q81 s hAs hBs hCs hDs u v).mp ⟨hg,hh⟩ with ⟨hu,hv⟩ | ⟨hv,hu⟩
 · exact q1 hAC hBD hclean hnoflag hu hv
 · exact (q1 hAC hBD hclean hnoflag hv hu).symm
end N19
namespace N22
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
 PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
 PEqualNP.CleanedNonEdge PEqualNP.TopForm
end N22
namespace N7
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
 PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
 PEqualNP.CleanedNonEdge PEqualNP.TopForm
open N10
lemma q105 {n:ℕ} {K:Circuit} {U:ℕ→ Bool}
   (hor:∀ j < K.gates.length,(gateAt K j).op=GateOp.or→
     ∀ w∈ (gateAt K j).inputs,U w=true→ U (n+j)=true)
   {w p:ℕ} (hr:OrReaches n K w p) (hp:U (n+p)=true):U w=true:=by
 have go:∀ k,k < K.gates.length→ p∈ (orSets n K).getD k []→ U (n+k)=true:=by
   intro k
   induction k using Nat.strong_induction_on with
   | ind k ih=>
     intro hk hmem
     rcases (q122 n K k p hk).mp hmem with heq | ⟨hop,v,hv,hn,hlt,hsub⟩
     · rw [← heq]
       exact hp
     · have hvU:=ih (v - n) (by omega) (by omega) hsub
       have heq:n+(v - n)=v:=by omega
       rw [heq] at hvU
       exact hor k hk hop v hv hvU
 obtain ⟨hn,hmem⟩:=hr
 have hw:w - n < K.gates.length:=by
   by_contra h
   have hlen:(orSets n K).length=K.gates.length:=by
     unfold orSets
     rw [q145]
     simp
   have hge:(orSets n K).length≤ w - n:=by omega
   rw [Z8,List.getElem?_eq_none hge] at hmem
   simp at hmem
 have hv:=go (w - n) hw hmem
 have heq:n+(w - n)=w:=by omega
 rw [heq] at hv
 exact hv
lemma q164 {n:ℕ} {K:Circuit} {U:ℕ→ Bool}
   (hor:∀ j < K.gates.length,(gateAt K j).op=GateOp.or→
     ∀ w∈ (gateAt K j).inputs,U w=true→ U (n+j)=true)
   {w:ℕ} {u:Fin n} (hu:u∈ orIn n K w) (hUu:U u.val=true):U w=true:=by
 rcases (orIn_mem n K w u).mp hu with heq | ⟨j,hj,hr,hop,hinput⟩
 · rw [← heq]
   exact hUu
 · exact q105 hor hr (hor j hj hop u.val hinput hUu)
lemma q89 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
   {K:Circuit} (hAO:IsAO2 n K) (hTF:TopForm G K)
   {g h j w:ℕ} (hJ:∀ k∈ junk G K,k=g∨ k=h)
   (hj:j < K.gates.length) (hop:(gateAt K j).op=GateOp.and)
   (hw:w∈ (gateAt K j).inputs) (x:Fin n→ Bool) (hval:W n K x w=true):
   (∃ u:Fin n,u∈ orIn n K w∧ x u=true)∨
     (OrReaches n K w g∧ gateVal n K g x=true)∨
     (OrReaches n K w h∧ gateVal n K h x=true):=by
 rcases down n K x (fun k hk=> hAO.1 _ (gateAt_mem' K k hk)) w hval with
   hraw | ⟨k,hk,hr,hopk,hkv⟩
 · exact Or.inl hraw
 · have hnotbelow:¬ BelowF G K k:=by
     intro hclean
     exact hTF k hk j hj hopk hclean hop
       (reach_cone n K j hj w hw (hAO.2.1 j hj w hw) k hr)
   have hkJ:k∈ junk G K:=by
     apply Z0.mpr
     refine ⟨Z9.mpr hk,hopk,hk,?_⟩
     unfold BelowF at hnotbelow
     push Not at hnotbelow
     obtain ⟨y,hy,hf⟩:=hnotbelow
     exact ⟨y,hy,by simpa using hf⟩
   rcases hJ k hkJ with rfl | rfl
   · exact Or.inr (Or.inl ⟨hr,hkv⟩)
   · exact Or.inr (Or.inr ⟨hr,hkv⟩)
lemma q133 {n:ℕ} {K:Circuit} (hAO:IsAO2 n K)
   {j a b:ℕ} (hj:j < K.gates.length) (hop:(gateAt K j).op=GateOp.and)
   (hinputs:(gateAt K j).inputs=[a,b]∨ (gateAt K j).inputs=[b,a])
   (x:Fin n→ Bool) (ha:W n K x a=true) (hb:W n K x b=true):
   gateVal n K j x=true:=by
 apply W_and n K x j hj hop
 intro w hw
 refine ⟨hAO.2.1 j hj w hw,?_⟩
 rcases hinputs with hlist | hlist
 · simp only [hlist,Z10,Z11,or_false] at hw
   rcases hw with rfl | rfl
   · exact ha
   · exact hb
 · simp only [hlist,Z10,Z11,or_false] at hw
   rcases hw with rfl | rfl
   · exact hb
   · exact ha
lemma q85 {n:ℕ} {K:Circuit} (hAO:IsAO2 n K)
   {j:ℕ} (hj:j < K.gates.length) (x:Fin n→ Bool):
   gateVal n K j x=(gateAt K j).op.eval
     [W n K x (opnd K j 0),W n K x (opnd K j 1)]:=by
 change W n K x (n+j)=_
 rw [W_gate n K x j hj,q116 hAO hj]
 have h0:opnd K j 0 < n+j:=hAO.2.1 j hj _ (by rw [q116 hAO hj];simp)
 have h1:opnd K j 1 < n+j:=hAO.2.1 j hj _ (by rw [q116 hAO hj];simp)
 simp [h0,h1]
lemma q54 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
   {K:Circuit} (hAO:IsAO2 n K) (hTF:TopForm G K)
   {g h j a b:ℕ} (hJ:∀ k∈ junk G K,k=g∨ k=h)
   (hgdirty:∃ y,gateVal n K g y=true∧ graphFun G ∅ y=false)
   (hj:j < K.gates.length) (hop:(gateAt K j).op=GateOp.and)
   (hclean:BelowF G K j)
   (hinputs:(gateAt K j).inputs=[a,b]∨ (gateAt K j).inputs=[b,a])
   (x:Fin n→ Bool) (R:Bool)
   (hraw:∀ v:Fin n,
     (∀ y,gateVal n K g y=true→ y v=true→ graphFun G ∅ y=true)→
     gateVal n K g x=true→ x v=true→ R=true)
   (hmutual:(∀ y,gateVal n K g y=true→ gateVal n K h y=true→
       graphFun G ∅ y=true)→ gateVal n K g x=true→ gateVal n K h x=true→ R=true)
   (hag:OrReaches n K a g) (hgx:gateVal n K g x=true)
   (hbx:W n K x b=true):R=true:=by
 have hb:b∈ (gateAt K j).inputs:=by
   rcases hinputs with hlist | hlist <;> simp [hlist]
 rcases q89 hAO hTF hJ hj hop hb x hbx with
   ⟨v,hv,hxv⟩ | ⟨hbg,hgv⟩ | ⟨hbh,hhv⟩
 · apply hraw v _ hgx hxv
   intro y hgy hyv
   exact hclean y (q133 hAO hj hop hinputs y
     (reach_up n K y a g hag hgy) (orIn_val hv y hyv))
 · obtain ⟨y,hgy,hneg⟩:=hgdirty
   have hf:=hclean y (q133 hAO hj hop hinputs y
     (reach_up n K y a g hag hgy) (reach_up n K y b g hbg hgy))
   rw [hneg] at hf
   exact False.elim (Bool.false_ne_true hf)
 · apply hmutual _ hgx hhv
   intro y hgy hhy
   exact hclean y (q133 hAO hj hop hinputs y
     (reach_up n K y a g hag hgy) (reach_up n K y b h hbh hhy))
lemma q24 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] {K:Circuit} (hAO:IsAO2 n K) (hTF:TopForm G K)
   {g h j:ℕ} (hJ:∀ k∈ junk G K,k=g∨ k=h)
   (hgdirty:∃ y,gateVal n K g y=true∧ graphFun G ∅ y=false)
   (hj:j < K.gates.length) (hop:(gateAt K j).op=GateOp.and)
   (hclean:BelowF G K j) (x:Fin n→ Bool) (U:ℕ→ Bool)
   (hinput:∀ v:Fin n,x v=true→ U v.val=true)
   (hor:∀ k < K.gates.length,(gateAt K k).op=GateOp.or→
     ∀ w∈ (gateAt K k).inputs,U w=true→ U (n+k)=true)
   (hand:U (n+j)=(U (opnd K j 0) && U (opnd K j 1)))
   (hhkeep:gateVal n K h x=true→ U (n+h)=true)
   (hraw:∀ v:Fin n,
     (∀ y,gateVal n K g y=true→ y v=true→ graphFun G ∅ y=true)→
     gateVal n K g x=true→ x v=true→ U (n+g)=true)
   (hmutual:(∀ y,gateVal n K g y=true→ gateVal n K h y=true→
       graphFun G ∅ y=true)→ gateVal n K g x=true→ gateVal n K h x=true→ U (n+g)=true)
   (hjx:gateVal n K j x=true):U (n+j)=true:=by
 have keepSide:∀ a b,
     ((gateAt K j).inputs=[a,b]∨ (gateAt K j).inputs=[b,a])→
     W n K x a=true→ W n K x b=true→ U a=true:=by
   intro a b hinputs hax hbx
   have ha:a∈ (gateAt K j).inputs:=by
     rcases hinputs with hlist | hlist <;> simp [hlist]
   rcases q89 hAO hTF hJ hj hop ha x hax with
     ⟨v,hv,hxv⟩ | ⟨hag,hgx⟩ | ⟨hah,hhx⟩
   · exact q164 hor hv (hinput v hxv)
   · have hgU:=q54 hAO hTF hJ hgdirty hj hop hclean
       hinputs x (U (n+g)) hraw hmutual hag hgx hbx
     exact q105 hor hag hgU
   · exact q105 hor hah (hhkeep hhx)
 have hvals:W n K x (opnd K j 0)=true∧ W n K x (opnd K j 1)=true:=by
   rw [q85 hAO hj x,hop] at hjx
   simpa only [GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true,
     Z12] using hjx
 rw [hand,Z12]
 exact ⟨keepSide _ _ (Or.inl (q116 hAO hj)) hvals.1 hvals.2,
   keepSide _ _ (Or.inr (q116 hAO hj)) hvals.2 hvals.1⟩
lemma q21 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] {K:Circuit} (hAO:IsAO2 n K) (hTF:TopForm G K)
   {g h:ℕ} (hJ:∀ k∈ junk G K,k=g∨ k=h)
   (hgdirty:∃ y,gateVal n K g y=true∧ graphFun G ∅ y=false)
   (x:Fin n→ Bool) (U:ℕ→ Bool)
   (hinput:∀ v:Fin n,x v=true→ U v.val=true)
   (hor:∀ k < K.gates.length,(gateAt K k).op=GateOp.or→
     ∀ w∈ (gateAt K k).inputs,U w=true→ U (n+k)=true)
   (hand:∀ k < K.gates.length,(gateAt K k).op=GateOp.and→ BelowF G K k→
     U (n+k)=(U (opnd K k 0) && U (opnd K k 1)))
   (hhkeep:gateVal n K h x=true→ U (n+h)=true)
   (hraw:∀ v:Fin n,
     (∀ y,gateVal n K g y=true→ y v=true→ graphFun G ∅ y=true)→
     gateVal n K g x=true→ x v=true→ U (n+g)=true)
   (hmutual:(∀ y,gateVal n K g y=true→ gateVal n K h y=true→
       graphFun G ∅ y=true)→ gateVal n K g x=true→ gateVal n K h x=true→ U (n+g)=true):
   ∀ j < K.gates.length,BelowF G K j→ gateVal n K j x=true→ U (n+j)=true:=by
 intro j
 induction j using Nat.strong_induction_on with
 | ind j ih=>
   intro hj hclean hjx
   rcases hAO.1 _ (gateAt_mem' K j hj) with hop | hop
   · exact q24 hAO hTF hJ hgdirty hj hop hclean x U
       hinput hor (hand j hj hop hclean) hhkeep hraw hmutual hjx
   · change W n K x (n+j)=true at hjx
     rw [W_gate n K x j hj,hop] at hjx
     simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq] at hjx
     obtain ⟨w,hw,hwx⟩:=hjx
     have hback:=hAO.2.1 j hj w hw
     rw [ite_eq_left hback] at hwx
     apply hor j hj hop w hw
     by_cases hwn:w < n
     · apply hinput ⟨w,hwn⟩
       rw [W_input n K x w hwn] at hwx
       exact hwx
     · have heq:n+(w - n)=w:=by omega
       have hk:w - n < K.gates.length:=by omega
       have hkclean:BelowF G K (w - n):=by
         intro y hky
         have hwy:W n K y w=true:=by
           rw [← heq]
           exact hky
         exact hclean y (W_or n K y j hj hop w hw hback hwy)
       have hkv:gateVal n K (w - n) x=true:=by
         change W n K x (n+(w - n))=true
         rw [heq]
         exact hwx
       have hu:=ih (w - n) (by omega) hk hkclean hkv
       rw [heq] at hu
       exact hu
lemma q42 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] {K:Circuit} (hAO:IsAO2 n K) (hTF:TopForm G K)
   (hcompute:circuitFun n K=graphFun G ∅)
   {g h:ℕ} (hJ:∀ k∈ junk G K,k=g∨ k=h)
   (hgdirty:∃ y,gateVal n K g y=true∧ graphFun G ∅ y=false)
   (x:Fin n→ Bool) (U:ℕ→ Bool)
   (hinput:∀ v:Fin n,x v=true→ U v.val=true)
   (hor:∀ k < K.gates.length,(gateAt K k).op=GateOp.or→
     ∀ w∈ (gateAt K k).inputs,U w=true→ U (n+k)=true)
   (hand:∀ k < K.gates.length,(gateAt K k).op=GateOp.and→ BelowF G K k→
     U (n+k)=(U (opnd K k 0) && U (opnd K k 1)))
   (hhkeep:gateVal n K h x=true→ U (n+h)=true)
   (hraw:∀ v:Fin n,
     (∀ y,gateVal n K g y=true→ y v=true→ graphFun G ∅ y=true)→
     gateVal n K g x=true→ x v=true→ U (n+g)=true)
   (hmutual:(∀ y,gateVal n K g y=true→ gateVal n K h y=true→
       graphFun G ∅ y=true)→ gateVal n K g x=true→ gateVal n K h x=true→ U (n+g)=true)
   (hFx:graphFun G ∅ x=true):U K.output=true:=by
 have hval:W n K x K.output=true:=by
   change circuitFun n K x=true
   rw [hcompute]
   exact hFx
 have hbound:K.output < n+K.gates.length:=by
   by_contra hge
   have hlen:=q168 n K x
   have hfalse:W n K x K.output=false:=q117 _ K.output (by omega)
   rw [hfalse] at hval
   exact Bool.false_ne_true hval
 by_cases hout:K.output < n
 · apply hinput ⟨K.output,hout⟩
   rw [W_input n K x K.output hout] at hval
   exact hval
 · have heq:n+(K.output - n)=K.output:=by omega
   have hj:K.output - n < K.gates.length:=by omega
   have hclean:BelowF G K (K.output - n):=by
     intro y hy
     have houty:circuitFun n K y=true:=by
       change W n K y K.output=true
       rw [← heq]
       exact hy
     rw [hcompute] at houty
     exact houty
   have hgate:gateVal n K (K.output - n) x=true:=by
     change W n K x (n+(K.output - n))=true
     rw [heq]
     exact hval
   have hu:=q21 hAO hTF hJ hgdirty x U
     hinput hor hand hhkeep hraw hmutual _ hj hclean hgate
   rw [heq] at hu
   exact hu
lemma q3 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] {K:Circuit} (hAO:IsAO2 n K) (hTF:TopForm G K)
   (hcompute:circuitFun n K=graphFun G ∅)
   {g h:ℕ} (hJ:∀ k∈ junk G K,k=g∨ k=h)
   (hgop:(gateAt K g).op=GateOp.and)
   (hgdirty:∃ y,gateVal n K g y=true∧ graphFun G ∅ y=false)
   (x:Fin n→ Bool) (U:ℕ→ Bool)
   (hinput:∀ v:Fin n,U v.val=x v)
   (hgate:∀ k < K.gates.length,k≠ g→
     U (n+k)=(gateAt K k).op.eval ((gateAt K k).inputs.map U))
   (hhkeep:gateVal n K h x=true→ U (n+h)=true)
   (hraw:∀ v:Fin n,
     (∀ y,gateVal n K g y=true→ y v=true→ graphFun G ∅ y=true)→
     gateVal n K g x=true→ x v=true→ U (n+g)=true)
   (hmutual:(∀ y,gateVal n K g y=true→ gateVal n K h y=true→
       graphFun G ∅ y=true)→ gateVal n K g x=true→ gateVal n K h x=true→ U (n+g)=true)
   (hFx:graphFun G ∅ x=true):U K.output=true:=by
 apply q42 hAO hTF hcompute hJ hgdirty x U
 · intro v hv
   rw [hinput]
   exact hv
 · intro k hk hop w hw hUw
   have hkg:k≠ g:=by
     intro heq
     rw [heq,hgop] at hop
     contradiction
   rw [hgate k hk hkg,hop]
   simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
   exact ⟨w,hw,hUw⟩
 · intro k hk hop hclean
   have hkg:k≠ g:=by
     rintro rfl
     obtain ⟨y,hgy,hneg⟩:=hgdirty
     have hf:=hclean y hgy
     rw [hneg] at hf
     exact Bool.false_ne_true hf
   rw [hgate k hk hkg,hop,q116 hAO hk]
   simp [GateOp.eval]
 · exact hhkeep
 · exact hraw
 · exact hmutual
 · exact hFx
lemma q37 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] {K:Circuit} (hAO:IsAO2 n K) (hTF:TopForm G K)
   (hcompute:circuitFun n K=graphFun G ∅)
   {g h:ℕ} (hJ:∀ k∈ junk G K,k=g∨ k=h)
   (hgop:(gateAt K g).op=GateOp.and)
   (hgdirty:∃ y,gateVal n K g y=true∧ graphFun G ∅ y=false)
   (U:(Fin n→ Bool)→ ℕ→ Bool)
   (hinput:∀ x (v:Fin n),U x v.val=x v)
   (hgate:∀ x k,k < K.gates.length→ k≠ g→
     U x (n+k)=(gateAt K k).op.eval ((gateAt K k).inputs.map (U x)))
   (hhkeep:∀ x,gateVal n K h x=true→ U x (n+h)=true)
   (hraw:∀ u v:Fin n,G.Adj u v→ ∀ w:Fin n,
     (∀ y,gateVal n K g y=true→ y w=true→ graphFun G ∅ y=true)→
     gateVal n K g (pairInput u v)=true→ pairInput u v w=true→
     U (pairInput u v) (n+g)=true)
   (hmutual:∀ u v:Fin n,G.Adj u v→
     (∀ y,gateVal n K g y=true→ gateVal n K h y=true→ graphFun G ∅ y=true)→
     gateVal n K g (pairInput u v)=true→ gateVal n K h (pairInput u v)=true→
     U (pairInput u v) (n+g)=true)
   (hmono:∀ x y:Fin n→ Bool,(∀ v,x v=true→ y v=true)→
     U x K.output=true→ U y K.output=true)
   (hunder:∀ x,U x K.output=true→ graphFun G ∅ x=true):
   ∀ x,U x K.output=graphFun G ∅ x:=by
 intro x
 rw [Bool.eq_iff_iff]
 constructor
 · exact hunder x
 · intro hFx
   obtain ⟨u,v,huv,hxu,hxv⟩:=(q158 x).mp hFx
   have hpair:U (pairInput u v) K.output=true:=
     q3 hAO hTF hcompute hJ hgop hgdirty
       (pairInput u v) (U (pairInput u v)) (hinput _) (hgate _) (hhkeep _)
       (hraw u v huv) (hmutual u v huv) ((q79 u v).mpr huv)
   apply hmono (pairInput u v) x _ hpair
   intro w hw
   simp only [pairInput,Z1] at hw
   rcases hw with rfl | rfl
   · exact hxu
   · exact hxv
end N7
namespace N27
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.TopForm
open N10
def patch (C:Circuit) (j:ℕ) (g:Gate):Circuit:=⟨C.gates.set j g,C.output⟩
lemma q162 (C:Circuit) (j:ℕ) (g:Gate):
   (patch C j g).gates.length=C.gates.length:=by
 simp [patch]
lemma q96 (C:Circuit) (j k:ℕ) (g:Gate) (hne:j≠ k):
   gateAt (patch C j g) k=gateAt C k:=by
 simp [patch,gateAt,Z8,List.getElem?_set_ne hne]
lemma q95 {C:Circuit} {j:ℕ} (hj:j < C.gates.length) (g:Gate):
   gateAt (patch C j g) j=g:=by
 simp [patch,gateAt,Z8,hj]
lemma patch_isAO2 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (j:ℕ) (g:Gate)
   (hOp:g.op=GateOp.and∨ g.op=GateOp.or) (hLen:g.inputs.length=2)
   (hBack:∀ w∈ g.inputs,w < n+j):IsAO2 n (patch C j g):=by
 refine ⟨?_,?_,?_⟩
 · intro k hk
   change k∈ C.gates.set j g at hk
   rcases List.mem_or_eq_of_mem_set hk with hk | rfl
   · exact hAO.1 k hk
   · exact hOp
 · intro k hk w hw
   have hkC:k < C.gates.length:=by simpa only [q162] using hk
   by_cases hkj:k=j
   · subst k
     rw [q95 hkC] at hw
     exact hBack w hw
   · rw [q96 C j k g (Ne.symm hkj)] at hw
     exact hAO.2.1 k hkC w hw
 · intro k hk
   change k∈ C.gates.set j g at hk
   rcases List.mem_or_eq_of_mem_set hk with hk | rfl
   · exact hAO.2.2 k hk
   · exact hLen
lemma patch_size (C:Circuit) (p:ℕ) (r:Gate):(patch C p r).size=C.size:=by
 apply @N27.q162
 all_goals assumption
lemma W_gate_eq {n:ℕ} {C:Circuit} (hAO:IsAO2 n C)
   (x:Fin n→ Bool) {k:ℕ} (hk:k < C.gates.length):
   W n C x (n+k)=(gateAt C k).op.eval ((gateAt C k).inputs.map (W n C x)):=by
 rw [W_gate n C x k hk]
 congr 1
 apply List.map_congr_left
 intro w hw
 rw [ite_eq_left (hAO.2.1 k hk w hw)]
lemma q82 {n:ℕ} {C:Circuit} {p:ℕ} {r:Gate}
   (hAO:IsAO2 n C) (hAO':IsAO2 n (patch C p r)) (x:Fin n→ Bool)
   (w:ℕ) (hwp:w < n+p) (hwN:w < n+C.gates.length):
   W n (patch C p r) x w=W n C x w:=by
 induction w using Nat.strong_induction_on with
 | ind w ih=>
   by_cases hw:w < n
   · rw [W_input n (patch C p r) x w hw,W_input n C x w hw]
   · have hn:n≤ w:=by omega
     have hk:w - n < C.gates.length:=by omega
     have hk':w - n < (patch C p r).gates.length:=by simpa [q162] using hk
     have hne:p≠ w - n:=by omega
     have he:n+(w - n)=w:=by omega
     conv_lhs=> rw [← he]
     conv_rhs=> rw [← he]
     rw [W_gate_eq hAO' x hk',W_gate_eq hAO x hk,
       q96 C p (w - n) r hne]
     congr 1
     apply List.map_congr_left
     intro v hv
     have hvw:=hAO.2.1 (w - n) hk v hv
     exact ih v (by omega) (by omega) (by omega)
def restored (n:ℕ) (C:Circuit) (p:ℕ) (r:Gate)
   (x:Fin n→ Bool) (w:ℕ):Bool:=
 if w=n+p then W n C x w else W n (patch C p r) x w
lemma q129 {n:ℕ} (C:Circuit) (p:ℕ) (r:Gate)
   (x:Fin n→ Bool) (v:Fin n):restored n C p r x v.val=x v:=by
 rw [restored,ite_eq_right (by omega),W_input n (patch C p r) x v.val v.isLt]
lemma q84 {n:ℕ} (C:Circuit) (p:ℕ) (r:Gate)
   (x:Fin n→ Bool) {w:ℕ} (hw:w≠ n+p):
   restored n C p r x w=W n (patch C p r) x w:=by
 exact ite_eq_right hw
lemma q91 {n:ℕ} {C:Circuit} {p g:ℕ} {r:Gate}
   (hAO:IsAO2 n C) (hAO':IsAO2 n (patch C p r))
   (hread:∀ k,k < C.gates.length→ n+p∈ (gateAt C k).inputs→ k=g)
   (x:Fin n→ Bool) {k:ℕ} (hk:k < C.gates.length) (hkg:k≠ g):
   restored n C p r x (n+k)=
     (gateAt C k).op.eval ((gateAt C k).inputs.map (restored n C p r x)):=by
 by_cases hkp:k=p
 · subst k
   rw [restored,ite_eq_left rfl,W_gate_eq hAO x hk]
   congr 1
   apply List.map_congr_left
   intro v hv
   have hvp:=hAO.2.1 p hk v hv
   rw [restored,ite_eq_right (by omega)]
   exact (q82 hAO hAO' x v hvp (by omega)).symm
 · have hk':k < (patch C p r).gates.length:=by simpa [q162] using hk
   rw [q84 C p r x (by omega),W_gate_eq hAO' x hk',
     q96 C p k r (Ne.symm hkp)]
   congr 1
   apply List.map_congr_left
   intro v hv
   have hvp:v≠ n+p:=by
     intro e
     subst v
     exact hkg (hread k hk hv)
   exact (q84 C p r x hvp).symm
lemma q69 {n:ℕ} {C:Circuit} {p g:ℕ}
   (hread:readers n C p={g}):
   ∀ k,k < C.gates.length→ n+p∈ (gateAt C k).inputs→ k=g:=by
 intro k hk hw
 have hm:k∈ readers n C p:=by simp [readers,hk,hw]
 rw [hread,Z3] at hm
 exact hm
lemma q47 {n:ℕ} {C:Circuit} {p g:ℕ} {r:Gate}
   (hAO:IsAO2 n C) (hAO':IsAO2 n (patch C p r))
   (hread:∀ k,k < C.gates.length→ n+p∈ (gateAt C k).inputs→ k=g)
   (x:Fin n→ Bool) (w:ℕ) (hwg:w < n+g)
   (hwN:w < n+C.gates.length) (hwp:w≠ n+p):
   W n (patch C p r) x w=W n C x w:=by
 induction w using Nat.strong_induction_on with
 | ind w ih=>
   by_cases hw:w < n
   · rw [W_input n (patch C p r) x w hw,W_input n C x w hw]
   · have hn:n≤ w:=by omega
     have hk:w - n < C.gates.length:=by omega
     have hk':w - n < (patch C p r).gates.length:=by simpa [q162] using hk
     have hne:p≠ w - n:=by omega
     have he:n+(w - n)=w:=by omega
     conv_lhs=> rw [← he]
     conv_rhs=> rw [← he]
     rw [W_gate_eq hAO' x hk',W_gate_eq hAO x hk,
       q96 C p (w - n) r hne]
     congr 1
     apply List.map_congr_left
     intro v hv
     have hvw:=hAO.2.1 (w - n) hk v hv
     have hvp:v≠ n+p:=by
       intro e
       subst v
       have:=hread (w - n) hk hv
       omega
     exact ih v (by omega) (by omega) (by omega) hvp
def rawOr {n:ℕ} (u z:Fin n):Gate:=⟨GateOp.or,[u.val,z.val]⟩
lemma q107 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C)
   (p:ℕ) (u z:Fin n):IsAO2 n (patch C p (rawOr u z)):=by
 apply patch_isAO2 hAO p (rawOr u z)
 · exact Or.inr rfl
 · rfl
 · intro w hw
   simp only [rawOr,Z10,Z11,or_false] at hw
   rcases hw with rfl | rfl <;> omega
lemma q83 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C)
   {p:ℕ} (hp:p < C.gates.length) (u z:Fin n) (x:Fin n→ Bool):
   W n (patch C p (rawOr u z)) x (n+p)=(x u || x z):=by
 rw [W_gate_eq (q107 hAO p u z) x (by simpa [q162] using hp),
   q95 hp]
 simp only [rawOr,Z15,Z16,GateOp.eval,List.any_cons,List.any_nil,
   Bool.or_false,id_eq]
 rw [W_input n _ x u.val u.isLt,W_input n _ x z.val z.isLt]
lemma q76 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C)
   {p g t:ℕ} (hp:p < C.gates.length) (hg:g < C.gates.length)
   (hread:∀ k,k < C.gates.length→ n+p∈ (gateAt C k).inputs→ k=g)
   (hop:(gateAt C g).op=GateOp.and)
   (hins:(gateAt C g).inputs=[n+p,t]∨ (gateAt C g).inputs=[t,n+p])
   (ht:t≠ n+p) (u z:Fin n) (x:Fin n→ Bool):
   restored n C p (rawOr u z) x (n+g)=((x u || x z) && W n C x t):=by
 have hpm:n+p∈ (gateAt C g).inputs:=by rcases hins with h | h <;> simp [h]
 have htm:t∈ (gateAt C g).inputs:=by rcases hins with h | h <;> simp [h]
 have hpg:=hAO.2.1 g hg (n+p) hpm
 have htg:=hAO.2.1 g hg t htm
 have hAO':=q107 hAO p u z
 have htv:=q47 hAO hAO' hread x t htg (by omega) ht
 rw [q84 C p (rawOr u z) x (by omega),
   W_gate_eq hAO' x (by simpa [q162] using hg),
   q96 C p g (rawOr u z) (by omega),hop]
 rcases hins with hins | hins
 · simp only [hins,Z15,Z16,GateOp.eval,List.all_cons,
     List.all_nil,Bool.and_true,id_eq]
   rw [q83 hAO hp,htv]
 · simp only [hins,Z15,Z16,GateOp.eval,List.all_cons,
     List.all_nil,Bool.and_true,id_eq]
   rw [q83 hAO hp,htv,Bool.and_comm]
lemma q64 {n:ℕ} {C:Circuit} {p:ℕ} {r:Gate}
   (hAO:IsAO2 n C) (hAO':IsAO2 n (patch C p r))
   (x:Fin n→ Bool) (k:ℕ) (hk:k < C.gates.length)
   (hkp:k≠ p) (hnc:¬ InCone n C p k):
   W n (patch C p r) x (n+k)=W n C x (n+k):=by
 induction k using Nat.strong_induction_on with
 | ind k ih=>
   rw [W_gate_eq hAO' x (by simpa [q162] using hk),W_gate_eq hAO x hk,
     q96 C p k r (Ne.symm hkp)]
   congr 1
   apply List.map_congr_left
   intro w hw
   by_cases hwn:w < n
   · rw [W_input n _ x w hwn,W_input n _ x w hwn]
   · have hlow:n≤ w:=by omega
     have hhigh:=hAO.2.1 k hk w hw
     have he:n+(w - n)=w:=by omega
     have hne:w - n≠ p:=by
       intro e
       exact hnc ((inCone_iff n C p k).mpr
         ⟨hk,w - n,by omega,by simpa [he] using hw,Or.inl e.symm⟩)
     have hnc':¬ InCone n C p (w - n):=by
       intro h
       exact hnc ((inCone_iff n C p k).mpr
         ⟨hk,w - n,by omega,by simpa [he] using hw,Or.inr h⟩)
     have hv:=ih (w - n) (by omega) (by omega) hne hnc'
     simpa [he] using hv
lemma q50 {n:ℕ} {C:Circuit} {p k:ℕ} {r:Gate}
   (hAO:IsAO2 n C) (hAO':IsAO2 n (patch C p r))
   (x:Fin n→ Bool) (hk:k < C.gates.length) (hkp:k≠ p)
   (hnc:¬ InCone n C p k):
   restored n C p r x (n+k)=W n C x (n+k):=by
 rw [q84 C p r x (by omega)]
 exact q64 hAO hAO' x k hk hkp hnc
lemma q114 (gate:Gate) (hop:gate.op=GateOp.and∨ gate.op=GateOp.or)
   (f h:ℕ→ Bool) (hfh:∀ w∈ gate.inputs,f w=true→ h w=true)
   (hf:gate.op.eval (gate.inputs.map f)=true):
   gate.op.eval (gate.inputs.map h)=true:=by
 rcases hop with hop | hop
 · simp only [hop,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq] at hf ⊢
   intro w hw
   exact hfh w hw (hf w hw)
 · simp only [hop,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq] at hf ⊢
   obtain ⟨w,hw,hfw⟩:=hf
   exact ⟨w,hw,hfh w hw hfw⟩
lemma W_large (n:ℕ) (C:Circuit) (x:Fin n→ Bool) (w:ℕ)
   (hw:n+C.gates.length≤ w):W n C x w=false:=by
 apply @N5.z143
 all_goals assumption
lemma W_true_mono {n:ℕ} {C:Circuit} (hAO:IsAO2 n C)
   (x y:Fin n→ Bool) (hxy:∀ v,x v=true→ y v=true) (w:ℕ)
   (hx:W n C x w=true):W n C y w=true:=by
 induction w using Nat.strong_induction_on with
 | ind w ih=>
   by_cases hwn:w < n
   · rw [W_input n C x w hwn] at hx
     rw [W_input n C y w hwn]
     exact hxy ⟨w,hwn⟩ hx
   · by_cases hwN:w < n+C.gates.length
     · have hk:w - n < C.gates.length:=by omega
       have he:n+(w - n)=w:=by omega
       have hx':W n C x (n+(w - n))=true:=by simpa [he] using hx
       rw [W_gate_eq hAO x hk] at hx'
       have hy:=q114 (gateAt C (w - n))
         (hAO.1 _ (gateAt_mem' C _ hk)) (W n C x) (W n C y) (by
           intro v hv hvx
           exact ih v (by have:=hAO.2.1 (w - n) hk v hv;omega) hvx) hx'
       rw [← W_gate_eq hAO y hk,he] at hy
       exact hy
     · rw [W_large n C x w (by omega)] at hx
       contradiction
lemma q77 {n:ℕ} {C:Circuit} {p:ℕ} {r:Gate}
   (hAO:IsAO2 n C) (hAO':IsAO2 n (patch C p r))
   (x y:Fin n→ Bool) (hxy:∀ v,x v=true→ y v=true) (w:ℕ)
   (hx:restored n C p r x w=true):restored n C p r y w=true:=by
 unfold restored at hx ⊢
 split_ifs at hx ⊢ with h
 · exact W_true_mono hAO x y hxy w hx
 · exact W_true_mono hAO' x y hxy w hx
lemma patch_under {n:ℕ} {C:Circuit} {p:ℕ} {r:Gate}
   (hAO:IsAO2 n C) (hAO':IsAO2 n (patch C p r))
   (x:Fin n→ Bool)
   (hroot:W n (patch C p r) x (n+p)=true→ W n C x (n+p)=true)
   (w:ℕ) (hx:W n (patch C p r) x w=true):W n C x w=true:=by
 induction w using Nat.strong_induction_on with
 | ind w ih=>
   by_cases hwn:w < n
   · rw [W_input n (patch C p r) x w hwn] at hx
     rw [W_input n C x w hwn]
     exact hx
   · by_cases hwN:w < n+C.gates.length
     · by_cases hwp:w=n+p
       · subst w
         exact hroot hx
       · have hk:w - n < C.gates.length:=by omega
         have hk':w - n < (patch C p r).gates.length:=by simpa [q162] using hk
         have he:n+(w - n)=w:=by omega
         have hx':W n (patch C p r) x (n+(w - n))=true:=by simpa [he] using hx
         rw [W_gate_eq hAO' x hk',q96 C p (w - n) r (by omega)] at hx'
         have hy:=q114 (gateAt C (w - n))
           (hAO.1 _ (gateAt_mem' C _ hk)) (W n (patch C p r) x) (W n C x) (by
             intro v hv hvx
             exact ih v (by have:=hAO.2.1 (w - n) hk v hv;omega) hvx) hx'
         rw [← W_gate_eq hAO x hk,he] at hy
         exact hy
     · rw [W_large n (patch C p r) x w (by rw [q162];omega)] at hx
       contradiction
lemma q130 {n:ℕ} {C:Circuit} {p:ℕ} {r:Gate}
   (hAO:IsAO2 n C) (hAO':IsAO2 n (patch C p r))
   (x:Fin n→ Bool)
   (hroot:W n (patch C p r) x (n+p)=true→ W n C x (n+p)=true)
   (w:ℕ) (hx:restored n C p r x w=true):W n C x w=true:=by
 unfold restored at hx
 split_ifs at hx with h
 · exact hx
 · exact patch_under hAO hAO' x hroot w hx
lemma q92 {n:ℕ} {C:Circuit} {p g:ℕ}
   (hread:∀ k,k < C.gates.length→ n+p∈ (gateAt C k).inputs→ k=g)
   (k:ℕ) (hp:InCone n C p k):k=g∨ InCone n C g k:=by
 induction k using Nat.strong_induction_on with
 | ind k ih=>
   obtain ⟨hk,j,hjk,hjin,hpj⟩:=(inCone_iff n C p k).mp hp
   rcases hpj with h | h
   · subst j
     exact Or.inl (hread k hk hjin)
   · rcases ih j hjk h with e | hgj
     · exact Or.inr ((inCone_iff n C g k).mpr ⟨hk,j,hjk,hjin,Or.inl e.symm⟩)
     · exact Or.inr ((inCone_iff n C g k).mpr ⟨hk,j,hjk,hjin,Or.inr hgj⟩)
lemma q33 {n:ℕ} {C:Circuit} {p g k:ℕ} {r:Gate}
   (hAO:IsAO2 n C) (hAO':IsAO2 n (patch C p r))
   (hread:∀ j,j < C.gates.length→ n+p∈ (gateAt C j).inputs→ j=g)
   (x:Fin n→ Bool) (hk:k < C.gates.length) (hkp:k≠ p)
   (hkg:k≠ g) (hnc:¬ InCone n C g k):
   restored n C p r x (n+k)=W n C x (n+k):=by
 apply q50 hAO hAO' x hk hkp
 intro h
 exact (q92 hread k h).elim hkg hnc
end N27
namespace N17
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo
lemma wval_input {n:ℕ} (C:Circuit) (x:Fin n→ Bool) (i:ℕ) (hi:i < n):
   wval C x i=x ⟨i,hi⟩:=by
 apply @N5.z144
 all_goals assumption
lemma q97 {n:ℕ} (C:Circuit) (j:ℕ) (x:Fin n→ Bool):
   gateVal n C j x=wval C x (n+j):=by
 apply @N5.z070
 all_goals assumption
lemma wval_ge_len {n:ℕ} (C:Circuit) (x:Fin n→ Bool) {w:ℕ} (hw:n+C.gates.length≤ w):
   wval C x w=false:=by
 apply @N5.z143
 all_goals assumption
lemma gateAt_mem {C:Circuit} {j:ℕ} (hj:j < C.gates.length):
   gateAt C j∈ C.gates:=by
 apply @N5.z069
 all_goals assumption
lemma q116 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) {j:ℕ} (hj:j < C.gates.length):
   (gateAt C j).inputs=[opnd C j 0,opnd C j 1]:=by
 apply @N5.z071
 all_goals assumption
lemma opnd_mem {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) {j:ℕ} (hj:j < C.gates.length) (b:Fin 2):
   opnd C j b∈ (gateAt C j).inputs:=by
 apply @N5.z105
 all_goals assumption
lemma opnd_lt {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) {j:ℕ} (hj:j < C.gates.length) (b:Fin 2):
   opnd C j b < n+j:=by
 apply @N5.z104
 all_goals assumption
lemma q132 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (x:Fin n→ Bool)
   {j:ℕ} (hj:j < C.gates.length):
   wval C x (n+j)=(gateAt C j).op.eval [wval C x (opnd C j 0),wval C x (opnd C j 1)]:=by
 apply @N5.z141
 all_goals assumption
lemma q169 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (x:Fin n→ Bool)
   {j:ℕ} (hj:j < C.gates.length) (hop:(gateAt C j).op=GateOp.or):
   wval C x (n+j)=(wval C x (opnd C j 0) || wval C x (opnd C j 1)):=by
 apply @N5.z142
 all_goals assumption
lemma q140 {n:ℕ} {C:Circuit} {i j:ℕ} (h:InCone n C i j):j < C.gates.length:=by
 apply @N5.z080
 all_goals assumption
lemma inCone_iff {n:ℕ} {C:Circuit} {i j:ℕ} (hj:j < C.gates.length):
   InCone n C i j↔
     ∃ w∈ (gateAt C j).inputs,n≤ w∧ w < n+j∧ (i=w - n∨ InCone n C i (w - n)):=by
 apply @N5.z078
 all_goals assumption
lemma q159 {n:ℕ} {C:Circuit} {i j k:ℕ} (h1:InCone n C i j) (h2:InCone n C j k):
   InCone n C i k:=by
 induction k using Nat.strong_induction_on with
 | ind k ih=>
   have hk:=q140 h2
   rw [inCone_iff hk] at h2 ⊢
   rcases h2 with ⟨w,hw,hnw,hwnk,rfl | hsub⟩
   · exact ⟨w,hw,hnw,hwnk,Or.inr h1⟩
   · exact ⟨w,hw,hnw,hwnk,Or.inr (ih (w - n) (by omega) hsub)⟩
lemma q86 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
   {w:ℕ} (hw:w < n):
   ¬ ∀ x:Fin n→ Bool,wval C x w=true→ graphFun G ∅ x=true:=by
 apply @N5.z081
 all_goals assumption
lemma q52 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
   {C:Circuit} (hAO:IsAO2 n C) (w:ℕ) (hw:w < n+C.gates.length)
   (hb:∀ x:Fin n→ Bool,wval C x w=true→ graphFun G ∅ x=true):
   ∃ r,r < C.gates.length∧ (gateAt C r).op=GateOp.and∧ BelowF G C r∧
     (r=w - n∨ InCone n C r (w - n)):=by
 induction w using Nat.strong_induction_on with
 | ind w ih=>
   have hn:n≤ w:=by
     by_contra h
     exact q86 (by omega:w < n) hb
   obtain ⟨j,rfl⟩:=Nat.exists_eq_add_of_le hn
   have hj:j < C.gates.length:=by omega
   have hjb:BelowF G C j:=hb
   rcases hAO.1 _ (gateAt_mem hj) with hand | hor
   · exact ⟨j,hj,hand,hjb,Or.inl (by omega)⟩
   · have hwb:∀ x:Fin n→ Bool,wval C x (opnd C j 0)=true→ graphFun G ∅ x=true:=by
       intro x hx
       apply hjb x
       rw [q97,q169 hAO x hj hor,Z13]
       exact Or.inl hx
     have hlt:=opnd_lt hAO hj 0
     have hn0:n≤ opnd C j 0:=by
       by_contra h
       exact q86 (by omega:opnd C j 0 < n) hwb
     obtain ⟨r,hr,hro,hrb,hrc⟩:=ih (opnd C j 0) hlt (by omega) hwb
     refine ⟨r,hr,hro,hrb,Or.inr ?_⟩
     simp only [Nat.add_sub_cancel_left]
     exact (inCone_iff hj).mpr ⟨opnd C j 0,opnd_mem hAO hj 0,hn0,hlt,hrc⟩
lemma q34 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C)
   {i j:ℕ} (hcone:InCone n C i j)
   (hor:∀ k,InCone n C i k→ (gateAt C k).op=GateOp.or)
   (x:Fin n→ Bool) (hi:gateVal n C i x=true):gateVal n C j x=true:=by
 induction j using Nat.strong_induction_on with
 | ind j ih=>
   have hj:=q140 hcone
   have hop:=hor j hcone
   obtain ⟨w,hw,hnw,hwj,hsub⟩:=(inCone_iff hj).mp hcone
   have hwv:wval C x w=true:=by
     rcases hsub with he | hsub
     · rw [he,q97,Nat.add_sub_of_le hnw] at hi
       exact hi
     · have hg:=ih (w - n) (by omega) hsub
       rw [q97,Nat.add_sub_of_le hnw] at hg
       exact hg
   rw [q97,q169 hAO x hj hop,Z13]
   rw [q116 hAO hj] at hw
   simp only [Z10,Z11,or_false] at hw
   rcases hw with rfl | rfl
   · exact Or.inl hwv
   · exact Or.inr hwv
lemma q51 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
   {C:Circuit} (hAO:IsAO2 n C) (hF:circuitFun n C=graphFun G ∅)
   (hT:TopForm G C):IsLiftFixedPoint G C:=by
 rintro ⟨h,hh,b,hLive,_,hNot,hImp⟩
 have hwlt:=opnd_lt hAO hh b
 obtain ⟨r,hr,hro,hrb,hrc⟩:=
   q52 hAO (opnd C h b) (by omega) hImp.1
 have hwn:n≤ opnd C h b:=by
   by_contra hlt
   exact q86 (by omega:opnd C h b < n) hImp.1
 have hrh:InCone n C r h:=
   (inCone_iff hh).mpr ⟨opnd C h b,opnd_mem hAO hh b,hwn,hwlt,hrc⟩
 have hor:∀ k,InCone n C h k→ (gateAt C k).op=GateOp.or:=by
   intro k hk
   have hkl:=q140 hk
   rcases hAO.1 _ (gateAt_mem hkl) with hand | hkor
   · exact False.elim (hT r hr k hkl hro hrb hand (q159 hrh hk))
   · exact hkor
 apply hNot
 intro x hx
 have hout:wval C x C.output=true:=by
   rcases hLive.2 with hout | ⟨houtn,hcone⟩
   · rw [hout]
     exact hx
   · have hc:=q34 hAO hcone hor x hx
     rw [q97,Nat.add_sub_of_le houtn] at hc
     exact hc
 change circuitFun n C x=true at hout
 rwa [hF] at hout
end N17
namespace N24
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo
open N17
def patch (C:Circuit) (j:ℕ) (g:Gate):Circuit:=⟨C.gates.set j g,C.output⟩
lemma q162 (C:Circuit) (j:ℕ) (g:Gate):
   (patch C j g).gates.length=C.gates.length:=by
 apply @N27.q162
 all_goals assumption
lemma q96 (C:Circuit) (j k:ℕ) (g:Gate) (hne:j≠ k):
   gateAt (patch C j g) k=gateAt C k:=by
 apply @N27.q96
 all_goals assumption
lemma patch_isAO2 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (j:ℕ) (g:Gate)
   (hOp:g.op=GateOp.and∨ g.op=GateOp.or) (hLen:g.inputs.length=2)
   (hBack:∀ w∈ g.inputs,w < n+j):IsAO2 n (patch C j g):=by
 apply @N27.patch_isAO2
 all_goals assumption
lemma q20 {n:ℕ} {C:Circuit} {j:ℕ} {g:Gate}
   (hAO:IsAO2 n C) (hAO':IsAO2 n (patch C j g)) (k:ℕ)
   (hne:j≠ k) (hCone:¬ InCone n C j k) (x:Fin n→ Bool):
   gateVal n (patch C j g) k x=gateVal n C k x:=by
 induction k using Nat.strong_induction_on with
 | ind k ih=>
   by_cases hk:k < C.gates.length
   · have hk':k < (patch C j g).gates.length:=by simpa only [q162] using hk
     have hgate:=q96 C j k g hne
     have hopnd (b:Fin 2):opnd (patch C j g) k b=opnd C k b:=by
       unfold opnd
       rw [hgate]
     have hval (b:Fin 2):wval (patch C j g) x (opnd C k b)=
         wval C x (opnd C k b):=by
       by_cases hw:opnd C k b < n
       · rw [wval_input _ _ _ hw,wval_input _ _ _ hw]
       · have hw':n≤ opnd C k b:=by omega
         have hlt:=opnd_lt hAO hk b
         have hsub_ne:j≠ opnd C k b - n:=by
           intro he
           apply hCone
           exact (inCone_iff hk).mpr ⟨opnd C k b,opnd_mem hAO hk b,hw',hlt,Or.inl he⟩
         have hsub_cone:¬ InCone n C j (opnd C k b - n):=by
           intro he
           apply hCone
           exact (inCone_iff hk).mpr ⟨opnd C k b,opnd_mem hAO hk b,hw',hlt,Or.inr he⟩
         have hv:=ih (opnd C k b - n) (by omega) hsub_ne hsub_cone
         rw [q97,q97,Nat.add_sub_of_le hw'] at hv
         exact hv
     rw [q97,q97,q132 hAO' x hk',
       q132 hAO x hk,hgate,hopnd 0,hopnd 1,hval 0,hval 1]
   · rw [q97,q97,wval_ge_len _ _ (by rw [q162];omega),
       wval_ge_len _ _ (by omega)]
lemma patch_size (C:Circuit) (j:ℕ) (g:Gate):(patch C j g).size=C.size:=by
 apply @N27.q162
 all_goals assumption
lemma q104 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
   {C:Circuit} {j:ℕ} {g:Gate} (hL:IsLeastAO G C)
   (hAO':IsAO2 n (patch C j g)) (hF':circuitFun n (patch C j g)=graphFun G ∅):
   IsLeastAO G (patch C j g):=by
 refine ⟨hAO',hF',?_⟩
 intro D hD hDF
 rw [patch_size]
 exact hL.2.2 D hD hDF
lemma q11 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
   {C:Circuit} {j:ℕ} {g:Gate} (hAO:IsAO2 n C) (hAO':IsAO2 n (patch C j g))
   {k:ℕ} (hne:j≠ k) (hCone:¬ InCone n C j k):
   k∈ junk G (patch C j g)↔ k∈ junk G C:=by
 change (k∈ (Finset.range (patch C j g).gates.length).filter (fun i=> IsDirtyAnd n G (patch C j g) i))↔
   k∈ (Finset.range C.gates.length).filter (fun i=> IsDirtyAnd n G C i)
 rw [Z0,Z0]
 simp only [Z9,IsDirtyAnd,IsDirty,q162,
   q96 C j k g hne,q20 hAO hAO' k hne hCone]
end N24
namespace N29
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo
open N17
end N29
namespace N15
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
def product {n:ℕ} (P Q:Finset (Fin n)) (x:Fin n→ Bool):Bool:=
 decide (∃ p∈ P,x p=true) && decide (∃ q∈ Q,x q=true)
def Safe {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
   (P Q:Finset (Fin n)) (w:Fin n):Prop:=
 ∀ x:Fin n→ Bool,product P Q x=true→ x w=true→ graphFun G ∅ x=true
def leftCenters {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
   (P Q:Finset (Fin n)):Finset (Fin n):=
 P.filter fun p=> ∀ q∈ Q,G.Adj p q
def q166 {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
   (P Q:Finset (Fin n)):Finset (Fin n):=
 Q.filter fun q=> ∀ p∈ P,G.Adj p q
def Useful {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
   (P Q:Finset (Fin n)) (u v:Fin n):Prop:=
 G.Adj u v∧ product P Q (pairInput u v)=true∧
   (Safe G P Q u∨ Safe G P Q v)
lemma q163 {n:ℕ} (P Q:Finset (Fin n)) (x:Fin n→ Bool):
   product P Q x=true↔ (∃ p∈ P,x p=true)∧ ∃ q∈ Q,x q=true:=by
 simp [product]
lemma wmax_iff {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
   (C:PEqualNP.CircuitLowerBounds.Circuit) (g:ℕ) (P Q:Finset (Fin n))
   (heval:∀ x:Fin n→ Bool,gateVal n C g x=product P Q x) (w:Fin n):
   w∈ wmax G C g↔ Safe G P Q w:=by
 simp only [wmax,Z0,Z7,true_and,Safe]
 simp_rw [heval]
lemma graph_pair {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v:Fin n):
   graphFun G ∅ (pairInput u v)=true↔ G.Adj u v:=by
 apply @N5.z074
 all_goals assumption
lemma safe_left {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
   (P Q:Finset (Fin n)) {z:Fin n} (hz:z∈ P):
   Safe G P Q z↔ ∀ q∈ Q,G.Adj z q:=by
 constructor
 · intro hs q hq
   apply (graph_pair G z q).mp
   apply hs
   · exact (q163 P Q _).mpr ⟨⟨z,hz,by simp [pairInput]⟩,
       q,hq,by simp [pairInput]⟩
   · simp [pairInput]
 · intro hadj x hp hxz
   obtain ⟨_,q,hq,hxq⟩:=(q163 P Q x).mp hp
   simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,
     Bool.false_or,Z1]
   exact ⟨z,q,hadj q hq,hxz,hxq⟩
lemma safe_right {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
   (P Q:Finset (Fin n)) {z:Fin n} (hz:z∈ Q):
   Safe G P Q z↔ ∀ p∈ P,G.Adj p z:=by
 constructor
 · intro hs p hp
   apply (graph_pair G p z).mp
   apply hs
   · exact (q163 P Q _).mpr ⟨⟨p,hp,by simp [pairInput]⟩,
       z,hz,by simp [pairInput]⟩
   · simp [pairInput]
 · intro hadj x hp hxz
   obtain ⟨⟨p,hp,hxp⟩,_⟩:=(q163 P Q x).mp hp
   simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,
     Bool.false_or,Z1]
   exact ⟨p,z,hadj p hp,hxp,hxz⟩
lemma q80 {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
   (P Q:Finset (Fin n)) (h4:NoFourCycle G) (hQ:2≤ Q.card):
   (leftCenters G P Q).card≤ 1:=by
 apply Finset.card_le_one.mpr
 intro u hu v hv
 by_contra hne
 obtain ⟨_,huQ⟩:=Z0.mp hu
 obtain ⟨_,hvQ⟩:=Z0.mp hv
 have hsub:Q⊆ Finset.univ.filter fun w=> G.Adj u w∧ G.Adj v w:=by
   intro w hw
   exact Z0.mpr ⟨Z7 _,huQ w hw,hvQ w hw⟩
 have hc:=(Finset.card_le_card hsub).trans (h4 u v hne)
 omega
lemma q78 {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
   (P Q:Finset (Fin n)) (h4:NoFourCycle G) (hP:2≤ P.card):
   (q166 G P Q).card≤ 1:=by
 apply Finset.card_le_one.mpr
 intro u hu v hv
 by_contra hne
 obtain ⟨_,huP⟩:=Z0.mp hu
 obtain ⟨_,hvP⟩:=Z0.mp hv
 have hsub:P⊆ Finset.univ.filter fun w=> G.Adj u w∧ G.Adj v w:=by
   intro w hw
   exact Z0.mpr ⟨Z7 _,(huP w hw).symm,(hvP w hw).symm⟩
 have hc:=(Finset.card_le_card hsub).trans (h4 u v hne)
 omega
lemma pair_cross {n:ℕ} (P Q:Finset (Fin n)) (hdis:Disjoint P Q)
   (u v:Fin n) (hprod:product P Q (pairInput u v)=true):
   (u∈ P∧ v∈ Q)∨ (v∈ P∧ u∈ Q):=by
 obtain ⟨⟨p,hp,hxp⟩,q,hq,hxq⟩:=(q163 P Q _).mp hprod
 simp only [pairInput,Z1] at hxp hxq
 rcases hxp with rfl | rfl <;> rcases hxq with rfl | rfl
 · exact (Finset.disjoint_left.mp hdis hp hq).elim
 · exact Or.inl ⟨hp,hq⟩
 · exact Or.inr ⟨hp,hq⟩
 · exact (Finset.disjoint_left.mp hdis hp hq).elim
lemma q152 {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
   (P Q:Finset (Fin n)) (hdis:Disjoint P Q) (u v:Fin n)
   (huv:Useful G P Q u v):
   ∃ z,(z=u∨ z=v)∧
     (z∈ leftCenters G P Q∨ z∈ q166 G P Q):=by
 obtain ⟨_,hp,hu | hv⟩:=huv
 · rcases pair_cross P Q hdis u v hp with ⟨hup,hvq⟩ | ⟨hvp,huq⟩
   · exact ⟨u,Or.inl rfl,Or.inl (Z0.mpr
       ⟨hup,(safe_left G P Q hup).mp hu⟩)⟩
   · exact ⟨u,Or.inl rfl,Or.inr (Z0.mpr
       ⟨huq,(safe_right G P Q huq).mp hu⟩)⟩
 · rcases pair_cross P Q hdis u v hp with ⟨hup,hvq⟩ | ⟨hvp,huq⟩
   · exact ⟨v,Or.inr rfl,Or.inr (Z0.mpr
       ⟨hvq,(safe_right G P Q hvq).mp hv⟩)⟩
   · exact ⟨v,Or.inr rfl,Or.inl (Z0.mpr
       ⟨hvp,(safe_left G P Q hvp).mp hv⟩)⟩
lemma q135 {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
   (P Q:Finset (Fin n)) (h4:NoFourCycle G) (hdis:Disjoint P Q)
   (hP:2≤ P.card) (hQ:2≤ Q.card):
   (∃ z∈ P,∃ zp∈ Q,G.Adj z zp∧
     (∀ p∈ P,G.Adj p zp)∧ (∀ q∈ Q,G.Adj z q))∨
   (∃ z∈ P,(∀ q∈ Q,G.Adj z q)∧
     ∀ u v,Useful G P Q u v→ pairInput u v z=true)∨
   (∃ z∈ Q,(∀ p∈ P,G.Adj p z)∧
     ∀ u v,Useful G P Q u v→ pairInput u v z=true)∨
   (∀ u v,¬ Useful G P Q u v):=by
 classical
 by_cases hL:(leftCenters G P Q).Nonempty
 · obtain ⟨z,hz⟩:=hL
   obtain ⟨hzP,hzQ⟩:=Z0.mp hz
   by_cases hR:(q166 G P Q).Nonempty
   · obtain ⟨zp,hzp⟩:=hR
     obtain ⟨hzpQ,hzpP⟩:=Z0.mp hzp
     exact Or.inl ⟨z,hzP,zp,hzpQ,hzQ zp hzpQ,hzpP,hzQ⟩
   · refine Or.inr (Or.inl ⟨z,hzP,hzQ,?_⟩)
     intro u v huv
     obtain ⟨w,hw,hwL | hwR⟩:=q152 G P Q hdis u v huv
     · have heq:w=z:=Finset.card_le_one.mp (q80 G P Q h4 hQ) w hwL z hz
       subst w
       simpa [pairInput] using hw
     · exact (hR ⟨w,hwR⟩).elim
 · by_cases hR:(q166 G P Q).Nonempty
   · obtain ⟨z,hz⟩:=hR
     obtain ⟨hzQ,hzP⟩:=Z0.mp hz
     refine Or.inr (Or.inr (Or.inl ⟨z,hzQ,hzP,?_⟩))
     intro u v huv
     obtain ⟨w,hw,hwL | hwR⟩:=q152 G P Q hdis u v huv
     · exact (hL ⟨w,hwL⟩).elim
     · have heq:w=z:=Finset.card_le_one.mp (q78 G P Q h4 hP) w hwR z hz
       subst w
       simpa [pairInput] using hw
   · refine Or.inr (Or.inr (Or.inr ?_))
     intro u v huv
     obtain ⟨w,_,hwL | hwR⟩:=q152 G P Q hdis u v huv
     · exact hL ⟨w,hwL⟩
     · exact hR ⟨w,hwR⟩
lemma clean_left {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
   (P Q:Finset (Fin n)) (z:Fin n) (hzP:z∈ P)
   (hzQ:∀ q∈ Q,G.Adj z q):
   (∀ x,product {z} Q x=true→ product P Q x=true)∧
   (∀ x,product {z} Q x=true→ graphFun G ∅ x=true)∧
   (∀ u v,product P Q (pairInput u v)=true→ pairInput u v z=true→
     product {z} Q (pairInput u v)=true):=by
 have hf:∀ x,product {z} Q x=true↔ x z=true∧ ∃ q∈ Q,x q=true:=by
   intro x
   simp [q163]
 refine ⟨?_,?_,?_⟩
 · intro x hx
   obtain ⟨hxz,hq⟩:=(hf x).mp hx
   exact (q163 P Q x).mpr ⟨⟨z,hzP,hxz⟩,hq⟩
 · intro x hx
   obtain ⟨hxz,q,hq,hxq⟩:=(hf x).mp hx
   simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,
     Bool.false_or,Z1]
   exact ⟨z,q,hzQ q hq,hxz,hxq⟩
 · intro u v hp hz
   exact (hf _).mpr ⟨hz,((q163 P Q _).mp hp).2⟩
lemma clean_right {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
   (P Q:Finset (Fin n)) (z:Fin n) (hzQ:z∈ Q)
   (hzP:∀ p∈ P,G.Adj p z):
   (∀ x,product P {z} x=true→ product P Q x=true)∧
   (∀ x,product P {z} x=true→ graphFun G ∅ x=true)∧
   (∀ u v,product P Q (pairInput u v)=true→ pairInput u v z=true→
     product P {z} (pairInput u v)=true):=by
 have hf:∀ x,product P {z} x=true↔ (∃ p∈ P,x p=true)∧ x z=true:=by
   intro x
   simp [q163]
 refine ⟨?_,?_,?_⟩
 · intro x hx
   obtain ⟨hp,hxz⟩:=(hf x).mp hx
   exact (q163 P Q x).mpr ⟨hp,z,hzQ,hxz⟩
 · intro x hx
   obtain ⟨⟨p,hp,hxp⟩,hxz⟩:=(hf x).mp hx
   simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,
     Bool.false_or,Z1]
   exact ⟨p,z,hzP p hp,hxp,hxz⟩
 · intro u v hp hz
   exact (hf _).mpr ⟨((q163 P Q _).mp hp).1,hz⟩
end N15
namespace N16
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.TopForm
end N16
namespace N20
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
end N20
namespace N2
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core
lemma q18 {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
   (C:Circuit) (hL:IsLeastAO G C) (hJ:(junk G C).Nonempty):
   G.edgeFinset.Nonempty:=by
 by_contra hE
 have hnone:∀ u v:Fin n,¬ G.Adj u v:=by
   intro u v huv
   exact hE ⟨s(u,v),by simpa using huv⟩
 let D:Circuit:=⟨[],n⟩
 have hD:IsAO2 n D:=by simp [IsAO2,AndOrOnly,ReadsBack,D]
 have hDF:circuitFun n D=graphFun G ∅:=by
   funext x
   simp [circuitFun,Circuit.eval,Circuit.wires,D,graphFun,hnone]
 have hsize:=hL.2.2 D hD hDF
 obtain ⟨j,hj⟩:=hJ
 have hjlt:j < C.gates.length:=by
   exact Z9.mp (Z0.mp hj).1
 simp only [Circuit.size,D,List.length_nil] at hsize
 omega
end N2
namespace N4
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
 PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
 PEqualNP.CleanedNonEdge PEqualNP.TopForm
def gateBit (w:List Bool) (g:Gate):Bool:=
 g.op.eval (g.inputs.map fun i=> w.getD i false)
def stepWire (w:List Bool) (g:Gate):List Bool:=w++[gateBit w g]
def WiresLE (w z:List Bool):Prop:=
 w.length=z.length∧ ∀ i,w.getD i false=true→ z.getD i false=true
def IsMonoGate (g:Gate):Prop:=g.op=GateOp.and∨ g.op=GateOp.or
lemma q98 {C:Circuit} (hC:Monotone2 C) {g:Gate} (hg:g∈ C.gates):
   IsMonoGate g:=by
 simpa [IsMonoGate] using (hC g hg).1
lemma bit_mono {w z:List Bool} (h:WiresLE w z) {g:Gate} (hg:IsMonoGate g)
   (hw:gateBit w g=true):gateBit z g=true:=by
 rcases hg with hop | hop
 · simp only [gateBit,hop,GateOp.eval,List.all_map,List.all_eq_true,
     Function.comp_apply,id_eq] at hw ⊢
   exact fun i hi=> h.2 i (hw i hi)
 · simp only [gateBit,hop,GateOp.eval,List.any_map,List.any_eq_true,
     Function.comp_apply,id_eq] at hw ⊢
   obtain ⟨i,hi,hv⟩:=hw
   exact ⟨i,hi,h.2 i hv⟩
lemma append_mono {w z:List Bool} {a b:Bool} (h:WiresLE w z)
   (hab:a=true→ b=true):WiresLE (w++[a]) (z++[b]):=by
 refine ⟨by simp [h.1],?_⟩
 intro i hi
 rw [Z8] at hi ⊢
 by_cases hlt:i < w.length
 · rw [List.getElem?_append_left hlt] at hi
   rw [List.getElem?_append_left (by rwa [← h.1])]
   simpa only [Z8] using h.2 i
     (by simpa only [Z8] using hi)
 · rw [List.getElem?_append_right (Nat.le_of_not_gt hlt)] at hi
   rw [List.getElem?_append_right (by rw [← h.1];omega),← h.1]
   cases hd:i - w.length with
   | zero=>
     simp only [hd,List.getElem?_cons_zero,Option.getD_some] at hi ⊢
     exact hab hi
   | succ k=> simp [hd] at hi
lemma fold_mono (gs:List Gate) (hg:∀ g∈ gs,IsMonoGate g)
   {w z:List Bool} (h:WiresLE w z):
   WiresLE (gs.foldl stepWire w) (gs.foldl stepWire z):=by
 induction gs generalizing w z with
 | nil=> exact h
 | cons g gs ih=>
   exact ih (fun k hk=> hg k (List.mem_cons_of_mem _ hk))
     (append_mono h (bit_mono h (hg g (by simp))))
lemma fold_length (gs:List Gate) (w:List Bool):
   (gs.foldl stepWire w).length=w.length+gs.length:=by
 apply @N5.z065
 all_goals assumption
lemma q156 (gs:List Gate) (w:List Bool) (i:ℕ) (hi:i < w.length):
   (gs.foldl stepWire w).getD i false=w.getD i false:=by
 apply @N5.z064
 all_goals assumption
lemma ofFn_getD {n:ℕ} (x:Fin n→ Bool) (u:Fin n):
   (List.ofFn x).getD u.val false=x u:=by
 simp [Z8]
lemma ofFn_mono {n:ℕ} {x y:Fin n→ Bool} (h:∀ u,x u=true→ y u=true):
   WiresLE (List.ofFn x) (List.ofFn y):=by
 refine ⟨by simp,?_⟩
 intro i hi
 by_cases hlt:i < n
 · rw [ofFn_getD y ⟨i,hlt⟩]
   exact h ⟨i,hlt⟩ (by simpa only [ofFn_getD x ⟨i,hlt⟩] using hi)
 · rw [Z8,List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hlt)] at hi
   cases hi
def patch (C:Circuit) (j:ℕ) (g:Gate):Circuit:=⟨C.gates.set j g,C.output⟩
def q155 (C:Circuit) (j:ℕ) (w:List Bool):List Bool:=
 (C.gates.take j).foldl stepWire w
def off:Gate:=⟨GateOp.or,[]⟩
def edgeGate {n:ℕ} (u v:Fin n):Gate:=⟨GateOp.and,[u.val,v.val]⟩
lemma edge_bit {n:ℕ} (C:Circuit) (j:ℕ) (x:Fin n→ Bool) (u v:Fin n):
   gateBit (q155 C j (List.ofFn x)) (edgeGate u v)=(x u && x v):=by
 simp only [gateBit,edgeGate,GateOp.eval,Z15,Z16,List.all_cons,
   List.all_nil,id_eq,Bool.and_true]
 unfold q155
 rw [q156 _ _ _ (by simp),q156 _ _ _ (by simp),
   ofFn_getD,ofFn_getD]
lemma wires_patch {C:Circuit} {j:ℕ} (hj:j < C.gates.length) (g:Gate) (w:List Bool):
   (patch C j g).wires w=(C.gates.drop (j+1)).foldl stepWire (stepWire (q155 C j w) g):=by
 change (C.gates.set j g).foldl stepWire w=_
 rw [List.set_eq_take_append_cons_drop,ite_eq_left hj,List.foldl_append,List.foldl_cons]
 rfl
lemma q124 {C:Circuit} {j:ℕ} (hj:j < C.gates.length):
   patch C j C.gates[j]=C:=by
 cases C with
 | mk gates output=>
   change Circuit.mk (gates.set j gates[j]) output=Circuit.mk gates output
   congr 1
   exact List.set_getElem_self hj
lemma patch_mono {C:Circuit} (hC:Monotone2 C) {j:ℕ} (hj:j < C.gates.length)
   (g h:Gate) (w:List Bool)
   (hbit:gateBit (q155 C j w) g=true→ gateBit (q155 C j w) h=true):
   WiresLE ((patch C j g).wires w) ((patch C j h).wires w):=by
 rw [wires_patch hj,wires_patch hj]
 apply fold_mono _ (fun k hk=> q98 hC (List.mem_of_mem_drop hk))
 exact append_mono ⟨rfl,fun _ h=> h⟩ hbit
lemma patch_bit {n:ℕ} {C:Circuit} {j:ℕ} (hj:j < C.gates.length)
   (g:Gate) (x:Fin n→ Bool):
   gateVal n (patch C j g) j x=gateBit (q155 C j (List.ofFn x)) g:=by
 have hlen:(q155 C j (List.ofFn x)).length=n+j:=by
   unfold q155
   rw [fold_length]
   simp [Nat.min_eq_left (Nat.le_of_lt hj)]
 unfold gateVal
 rw [wires_patch hj,q156 _ _ _ (by simp [stepWire,hlen]),← hlen]
 simp [stepWire,Z8]
lemma q96 (C:Circuit) (j k:ℕ) (g:Gate) (hne:j≠ k):
   gateAt (patch C j g) k=gateAt C k:=by
 apply @N27.q96
 all_goals assumption
lemma graph_true {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
   (x:Fin n→ Bool):
   graphFun G ∅ x=true↔ ∃ u v,G.Adj u v∧ x u=true∧ x v=true:=by
 apply @N5.z073
 all_goals assumption
lemma pair_le {n:ℕ} {x:Fin n→ Bool} {u v:Fin n}
   (hu:x u=true) (hv:x v=true) (k:Fin n):
   pairInput u v k=true→ x k=true:=by
 simp only [pairInput,Z1]
 rintro (rfl | rfl)
 · exact hu
 · exact hv
lemma q154 {n:ℕ} {C:Circuit} (hC:Monotone2 C) {x y:Fin n→ Bool}
   (hxy:∀ u,x u=true→ y u=true):
   circuitFun n C x=true→ circuitFun n C y=true:=
 (fold_mono C.gates (fun _ hg=> q98 hC hg) (ofFn_mono hxy)).2 C.output
lemma mem_junk {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit} {j:ℕ}:
   j∈ junk G C↔ j < C.gates.length∧ IsDirtyAnd n G C j:=by
 unfold junk gatesWhere
 rw [Z0,Z9]
lemma ao2_mono {n:ℕ} {C:Circuit} (hAO:IsAO2 n C):Monotone2 C:=by
 intro g hg
 exact ⟨by simpa using hAO.1 g hg,Nat.le_of_eq (hAO.2.2 g hg)⟩
lemma q9 {n:ℕ} (G:SimpleGraph (Fin n))
   [DecidableRel G.Adj] (C:Circuit) (hL:IsLeastAO G C)
   (hOne:∀ D:Circuit,IsLeastAO G D→ (junk G D).card≠ 1)
   {j k:ℕ} (hne:j≠ k) (hJ:junk G C={j,k})
   (hCone:¬ InCone n C j k) (R:Gate)
   (hOp:R.op=GateOp.and∨ R.op=GateOp.or)
   (hLen:R.inputs.length=2) (hBack:∀ w∈ R.inputs,w < n+j)
   (hClean:∀ x:Fin n→ Bool,graphFun G ∅ x=false→
     gateBit (q155 C j (List.ofFn x)) R=false)
   (hCover:∀ u v:Fin n,G.Adj u v→
     circuitFun n (patch C j off) (pairInput u v)=false→
     gateBit (q155 C j (List.ofFn (pairInput u v))) R=true):False:=by
 have hjmem:j∈ junk G C:=by rw [hJ];simp
 have hkmem:k∈ junk G C:=by rw [hJ];simp
 have hj:j < C.gates.length:=(mem_junk.mp hjmem).1
 have hmono:Monotone2 C:=ao2_mono hL.1
 let D:=patch C j R
 have hDAO:IsAO2 n D:=N24.patch_isAO2 hL.1 j R hOp hLen hBack
 have hDM:Monotone2 D:=ao2_mono hDAO
 have hnegative (x:Fin n→ Bool) (hf:graphFun G ∅ x=false):
     WiresLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x)):=by
   have h:=patch_mono hmono hj R C.gates[j] (List.ofFn x)
     (by intro hh;rw [hClean x hf] at hh;cases hh)
   rwa [q124 hj] at h
 have hEdges (u v:Fin n) (huv:G.Adj u v):
     circuitFun n D (pairInput u v)=true:=by
   have hF:circuitFun n C (pairInput u v)=true:=by
     rw [hL.2.1]
     exact (graph_true G _).mpr ⟨u,v,huv,by simp [pairInput],by simp [pairInput]⟩
   cases hCut:circuitFun n (patch C j off) (pairInput u v) with
   | false=>
     have h:=patch_mono hmono hj C.gates[j] R (List.ofFn (pairInput u v))
       (fun _=> hCover u v huv hCut)
     rw [q124 hj] at h
     exact h.2 C.output hF
   | true=>
     exact (patch_mono hmono hj off R (List.ofFn (pairInput u v))
       (by intro hh;simp [off,gateBit,GateOp.eval] at hh)).2 C.output hCut
 have hDF:circuitFun n D=graphFun G ∅:=by
   funext x
   cases hf:graphFun G ∅ x with
   | false=>
     cases hd:circuitFun n D x with
     | false=> rfl
     | true=>
       have hh:circuitFun n C x=true:=(hnegative x hf).2 C.output hd
       rw [hL.2.1,hf] at hh
       cases hh
   | true=>
     obtain ⟨u,v,huv,hu,hv⟩:=(graph_true G x).mp hf
     exact q154 hDM (pair_le hu hv) (hEdges u v huv)
 have hNoJ:j∉ junk G D:=by
   intro hmem
   obtain ⟨_,_,_,x,hx,hf⟩:=mem_junk.mp hmem
   change gateVal n (patch C j R) j x=true at hx
   rw [patch_bit hj,hClean x hf] at hx
   cases hx
 have hSub:junk G D⊆ junk G C:=by
   intro a ha
   have hja:j≠ a:=by intro he;exact hNoJ (he.symm ▸ ha)
   obtain ⟨haLen,haAnd,_,x,hx,hf⟩:=mem_junk.mp ha
   have haC:a < C.gates.length:=by simpa [D,patch] using haLen
   have haOp:(gateAt C a).op=GateOp.and:=by
     change (gateAt (patch C j R) a).op=GateOp.and at haAnd
     rwa [q96 C j a R hja] at haAnd
   exact mem_junk.mpr ⟨haC,haOp,haC,x,(hnegative x hf).2 (n+a) hx,hf⟩
 have hkD:k∈ junk G D:=
   (N24.q11 hL.1 hDAO hne hCone).mpr hkmem
 have hJD:junk G D={k}:=by
   apply Finset.ext
   intro a
   constructor
   · intro ha
     have hao:=hSub ha
     rw [hJ] at hao
     simp only [Z6,Z3] at hao ⊢
     rcases hao with rfl | he
     · exact (hNoJ ha).elim
     · exact he
   · intro ha
     have he:=Z3.mp ha
     exact he ▸ hkD
 have hDL:IsLeastAO G D:=N24.q104 hL hDAO hDF
 exact hOne D hDL (by rw [hJD];simp)
end N4
namespace N9
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo
open N4 N15
lemma q93 {n:ℕ} (C:Circuit) (j:ℕ) (hj:j≤ C.gates.length)
   (x:Fin n→ Bool) {w:ℕ} (hw:w < n+j):
   (q155 C j (List.ofFn x)).getD w false=wval C x w:=by
 have hlen:(q155 C j (List.ofFn x)).length=n+j:=by
   unfold q155
   rw [fold_length]
   simp [Nat.min_eq_left hj]
 have hsplit:C.wires (List.ofFn x)=
     (C.gates.drop j).foldl stepWire (q155 C j (List.ofFn x)):=by
   change C.gates.foldl stepWire _=_
   conv_lhs=> rw [← List.take_append_drop j C.gates,List.foldl_append]
   rfl
 unfold wval
 rw [hsplit,q156 _ _ _ (by omega)]
lemma q151 {n:ℕ} (C:Circuit) (j:ℕ) (hj:j≤ C.gates.length)
   (z:Fin n) (w:ℕ) (hw:w < n+j) (x:Fin n→ Bool):
   gateBit (q155 C j (List.ofFn x)) ⟨GateOp.and,[z.val,w]⟩=
     (x z && wval C x w):=by
 simp only [gateBit,GateOp.eval,Z15,Z16,List.all_cons,
   List.all_nil,id_eq,Bool.and_true]
 rw [q93 C j hj x (by have:=z.isLt;omega),
   q93 C j hj x hw,N17.wval_input C x z.val z.isLt]
lemma q6 {n:ℕ} (G:SimpleGraph (Fin n))
   [DecidableRel G.Adj] (C:Circuit) (hL:IsLeastAO G C)
   (hOne:∀ D:Circuit,IsLeastAO G D→ (junk G D).card≠ 1)
   {j k:ℕ} (hne:j≠ k) (hJ:junk G C={j,k})
   (hCone:¬ InCone n C j k) (P Q:Finset (Fin n))
   (h4:NoFourCycle G) (hdis:Disjoint P Q) (hP:2≤ P.card) (hQ:2≤ Q.card)
   (hRawP:∀ x:Fin n→ Bool,
     wval C x (opnd C j 0)=decide (∃ p∈ P,x p=true))
   (hRawQ:∀ x:Fin n→ Bool,
     wval C x (opnd C j 1)=decide (∃ q∈ Q,x q=true))
   (hCritical:∀ u v:Fin n,G.Adj u v→
     circuitFun n (patch C j off) (pairInput u v)=false→ Useful G P Q u v):
   ∃ z∈ P,∃ zp∈ Q,G.Adj z zp∧
     (∀ p∈ P,G.Adj p zp)∧ (∀ q∈ Q,G.Adj z q):=by
 have hjmem:j∈ junk G C:=by rw [hJ];simp
 have hj:j < C.gates.length:=(mem_junk.mp hjmem).1
 have hOpnd (b:Fin 2):opnd C j b < n+j:=N17.opnd_lt hL.1 hj b
 rcases q135 G P Q h4 hdis hP hQ with
   hFlag | ⟨z,hzP,hzQ,hzCover⟩ | ⟨z,hzQ,hzP,hzCover⟩ | hNone
 · exact hFlag
 · exfalso
   apply q9 G C hL hOne hne hJ hCone
     ⟨GateOp.and,[z.val,opnd C j 1]⟩ (Or.inl rfl) rfl
   · intro w hw
     simp only [Z10,Z11,or_false] at hw
     rcases hw with rfl | rfl
     · have:=z.isLt;omega
     · exact hOpnd 1
   · intro x hf
     rw [q151 C j (Nat.le_of_lt hj) z _ (hOpnd 1) x,hRawQ x]
     apply Z14.mpr
     intro ht
     have hc:=(clean_left G P Q z hzP hzQ).2.1 x
     have hp:product {z} Q x=true:=by simpa [product] using ht
     have:=hc hp
     rw [hf] at this
     cases this
   · intro u v huv hCut
     have hUse:=hCritical u v huv hCut
     rw [q151 C j (Nat.le_of_lt hj) z _ (hOpnd 1) _,hRawQ]
     have hp:=(clean_left G P Q z hzP hzQ).2.2 u v hUse.2.1 (hzCover u v hUse)
     simpa [product] using hp
 · exfalso
   apply q9 G C hL hOne hne hJ hCone
     ⟨GateOp.and,[z.val,opnd C j 0]⟩ (Or.inl rfl) rfl
   · intro w hw
     simp only [Z10,Z11,or_false] at hw
     rcases hw with rfl | rfl
     · have:=z.isLt;omega
     · exact hOpnd 0
   · intro x hf
     rw [q151 C j (Nat.le_of_lt hj) z _ (hOpnd 0) x,hRawP x]
     apply Z14.mpr
     intro ht
     have hc:=(clean_right G P Q z hzQ hzP).2.1 x
     have hp:product P {z} x=true:=by simpa [product,Bool.and_comm] using ht
     have:=hc hp
     rw [hf] at this
     cases this
   · intro u v huv hCut
     have hUse:=hCritical u v huv hCut
     rw [q151 C j (Nat.le_of_lt hj) z _ (hOpnd 0) _,hRawP]
     have hp:=(clean_right G P Q z hzQ hzP).2.2 u v hUse.2.1 (hzCover u v hUse)
     simpa [product,Bool.and_comm] using hp
 · exfalso
   obtain ⟨e,he⟩:=N2.q18 G C hL ⟨j,hjmem⟩
   obtain ⟨u,v,huv⟩:∃ u v:Fin n,G.Adj u v:=by
     revert he
     refine Sym2.inductionOn e ?_
     intro u v he
     exact ⟨u,v,by simpa using he⟩
   apply q9 G C hL hOne hne hJ hCone
     (edgeGate u v) (Or.inl rfl) rfl
   · intro w hw
     simp only [edgeGate,Z10,Z11,or_false] at hw
     rcases hw with rfl | rfl <;> omega
   · intro x hf
     rw [edge_bit]
     apply Z14.mpr
     intro ht
     simp only [Z12] at ht
     obtain ⟨hu,hv⟩:=ht
     have:=(graph_true G x).mpr ⟨u,v,huv,hu,hv⟩
     rw [hf] at this
     cases this
   · intro a b hab hCut
     exact (hNone a b (hCritical a b hab hCut)).elim
end N9
namespace N26
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
def W (n:ℕ) (C:Circuit) (x:Fin n→ Bool) (u:ℕ):Bool:=
 (C.wires (List.ofFn x)).getD u false
lemma W_gate (n:ℕ) (C:Circuit) (x:Fin n→ Bool) (k:ℕ) (hk:k < C.gates.length):
   W n C x (n+k)=(gateAt C k).op.eval ((gateAt C k).inputs.map fun i=>
     if i < n+k then W n C x i else false):=by
 apply @N10.W_gate
 all_goals assumption
lemma W_input (n:ℕ) (C:Circuit) (x:Fin n→ Bool) (u:ℕ) (hu:u < n):
   W n C x u=x ⟨u,hu⟩:=by
 apply @N5.z144
 all_goals assumption
lemma W_or (n:ℕ) (C:Circuit) (x:Fin n→ Bool) (r:ℕ) (hr:r < C.gates.length)
   (hop:(gateAt C r).op=GateOp.or) (i:ℕ) (hi:i∈ (gateAt C r).inputs)
   (hlt:i < n+r) (hv:W n C x i=true):W n C x (n+r)=true:=by
 apply @N10.W_or
 all_goals assumption
open PEqualNP.CleanedNonEdge in
lemma reach_up (n:ℕ) (C:Circuit) (x:Fin n→ Bool) (w g:ℕ)
   (h:OrReaches n C w g) (hv:W n C x (n+g)=true):W n C x w=true:=by
 apply @N10.reach_up
 all_goals assumption
lemma q118 {α:Type} (p:α→ Prop) (d:DecidablePred p) (s:Finset α) (a:α)
   (h:a∈ @Finset.filter α p d s):p a:=
 ((@Z0 α p d s a).mp h).2
lemma side_val (n:ℕ) (C:Circuit) (x:Fin n→ Bool) (j:ℕ) (b:Fin 2) (i:Fin n)
   (hi:i∈ PEqualNP.TopForm.side (n:=n) C j b) (hx:x i=true):
   W n C x (PEqualNP.TopForm.opnd C j b)=true:=by
 unfold PEqualNP.TopForm.side PEqualNP.TopForm.orIn at hi
 have hi2:=q118 _ _ _ _ hi
 rcases hi2 with h | ⟨k,hk,hreach,hop,hin⟩
 · rw [← h,W_input n C x i.val i.isLt];exact hx
 · have hk1:W n C x (n+k)=true:=by
     apply W_or n C x k hk hop i.val hin (by have:=i.isLt;omega)
     rw [W_input n C x i.val i.isLt];exact hx
   exact reach_up n C x _ k hreach hk1
open PEqualNP.EdgeOwnership in
lemma inCone_iff (n:ℕ) (C:Circuit) (i j:ℕ):
   InCone n C i j↔ j < C.gates.length∧ ∃ k,k < j∧ n+k∈ (gateAt C j).inputs∧
     (i=k∨ InCone n C i k):=by
 apply @N10.inCone_iff
 all_goals assumption
lemma gateAt_mem' (C:Circuit) (j:ℕ) (hj:j < C.gates.length):gateAt C j∈ C.gates:=by
 apply @N5.z069
 all_goals assumption
open PEqualNP.EdgeOwnership in
lemma inCone_lt (n:ℕ) (C:Circuit):∀ j i,InCone n C i j→ i < j:=by
 intro j
 induction j using Nat.strong_induction_on with
 | _ j ih=>
   intro i h
   obtain ⟨_,k,hk,_,h3⟩:=(inCone_iff n C i j).mp h
   rcases h3 with h3 | h3
   · omega
   · have:=ih k hk i h3;omega
open PEqualNP.CleanedNonEdge in
lemma down (n:ℕ) (C:Circuit) (x:Fin n→ Bool)
   (hAO:∀ k < C.gates.length,(gateAt C k).op=GateOp.and∨ (gateAt C k).op=GateOp.or):
   ∀ w,W n C x w=true→ (∃ i:Fin n,i∈ PEqualNP.TopForm.orIn n C w∧ x i=true)∨
     ∃ k,k < C.gates.length∧ OrReaches n C w k∧ (gateAt C k).op=GateOp.and∧
       W n C x (n+k)=true:=by
 apply @N10.down
 all_goals assumption
open PEqualNP.EdgeOwnership in
lemma reach_cone (n:ℕ) (C:Circuit) (j:ℕ) (hj:j < C.gates.length) (o:ℕ)
   (ho:o∈ (gateAt C j).inputs) (hlt:o < n+j) (k:ℕ)
   (h:PEqualNP.CleanedNonEdge.OrReaches n C o k):InCone n C k j:=by
 apply @N10.reach_cone
 all_goals assumption
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
lemma junk_data {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
   (C:Circuit) (j:ℕ) (hj:j∈ junk G C):
   j < C.gates.length∧ (gateAt C j).op=GateOp.and:=by
 obtain ⟨hjl,hja,_⟩:=Z0.mp hj
 exact ⟨Z9.mp hjl,hja⟩
lemma operand_mem {n:ℕ} (C:Circuit) (hAO:IsAO2 n C)
   (j:ℕ) (hj:j < C.gates.length) (b:Fin 2):
   opnd C j b∈ (gateAt C j).inputs:=by
 apply @N5.z105
 all_goals assumption
lemma q32 {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
   (C:Circuit) (hAO:IsAO2 n C) (hTop:TopForm G C)
   (j:ℕ) (hj:j < C.gates.length) (hand:(gateAt C j).op=GateOp.and)
   (hno:∀ k∈ junk G C,¬ InCone n C k j) (b:Fin 2) (x:Fin n→ Bool):
   PEqualNP.ReadTwo.wval C x (opnd C j b)=
     decide (∃ u∈ side (n:=n) C j b,x u=true):=by
 have hm:=operand_mem C hAO j hj b
 have hlt:=hAO.2.1 j hj _ hm
 have hi:W n C x (opnd C j b)=true↔
     ∃ u∈ side (n:=n) C j b,x u=true:=by
   constructor
   · intro hv
     have hops:∀ k < C.gates.length,
         (gateAt C k).op=GateOp.and∨ (gateAt C k).op=GateOp.or:=
       fun k hk=> hAO.1 _ (gateAt_mem' C k hk)
     rcases down n C x hops _ hv with hraw | ⟨k,hk,hr,hop,_⟩
     · exact hraw
     · have hc:=reach_cone n C j hj _ hm hlt k hr
       have hnb:¬ BelowF G C k:=fun hb=> hTop k hk j hj hop hb hand hc
       have hd:∃ y:Fin n→ Bool,gateVal n C k y=true∧ graphFun G ∅ y=false:=by
         by_contra hn
         apply hnb
         intro y hy
         by_contra hf
         exact hn ⟨y,hy,Z14.mpr hf⟩
       have hkj:k∈ junk G C:=
         Z0.mpr ⟨Z9.mpr hk,hop,hk,hd⟩
       exact (hno k hkj hc).elim
   · rintro ⟨u,hu,hxu⟩
     exact side_val n C x j b u hu hxu
 change W n C x (opnd C j b)=_
 by_cases hv:W n C x (opnd C j b)=true
 · simp [hv,hi.mp hv]
 · have hn:¬ ∃ u∈ side (n:=n) C j b,x u=true:=fun h=> hv (hi.mpr h)
   simp [Z14.mpr hv,hn]
lemma q22 {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
   (C:Circuit) (g h:ℕ) (hJ:junk G C={g,h})
   (hgh:¬ InCone n C g h) (hhg:¬ InCone n C h g)
   (j:ℕ) (hj:j=g∨ j=h):
   ∀ k∈ junk G C,¬ InCone n C k j:=by
 intro k hk hc
 have hkm:k=g∨ k=h:=by simpa [hJ] using hk
 rcases hj with rfl | rfl <;> rcases hkm with rfl | rfl
 · have:=inCone_lt n C _ _ hc
   omega
 · exact hhg hc
 · exact hgh hc
 · have:=inCone_lt n C _ _ hc
   omega
lemma q70 {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
   (C:Circuit) (hAO:IsAO2 n C) (hTop:TopForm G C)
   (g h:ℕ) (hJ:junk G C={g,h})
   (hgh:¬ InCone n C g h) (hhg:¬ InCone n C h g)
   (j:ℕ) (hj:j=g∨ j=h) (b:Fin 2) (x:Fin n→ Bool):
   PEqualNP.ReadTwo.wval C x (opnd C j b)=
     decide (∃ u∈ side (n:=n) C j b,x u=true):=by
 have hjm:j∈ junk G C:=by simpa [hJ] using hj
 obtain ⟨hjl,hja⟩:=junk_data G C j hjm
 exact q32 G C hAO hTop j hjl hja
   (q22 G C g h hJ hgh hhg j hj) b x
lemma and_gate_eq {n:ℕ} (C:Circuit) (hAO:IsAO2 n C)
   (j:ℕ) (hj:j < C.gates.length) (hand:(gateAt C j).op=GateOp.and)
   (x:Fin n→ Bool):
   gateVal n C j x=
     (PEqualNP.ReadTwo.wval C x (opnd C j 0) && PEqualNP.ReadTwo.wval C x (opnd C j 1)):=by
 obtain ⟨a,b,hab⟩:=List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem' C j hj))
 have ham:a∈ (gateAt C j).inputs:=by simp [hab]
 have hbm:b∈ (gateAt C j).inputs:=by simp [hab]
 have hba:=hAO.2.1 j hj a ham
 have hbb:=hAO.2.1 j hj b hbm
 change W n C x (n+j)=_
 rw [W_gate n C x j hj,hand,hab]
 simp [GateOp.eval,opnd,hab,hba,hbb,W,PEqualNP.ReadTwo.wval]
lemma q71 {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
   (C:Circuit) (hAO:IsAO2 n C) (hTop:TopForm G C)
   (g h:ℕ) (hJ:junk G C={g,h})
   (hgh:¬ InCone n C g h) (hhg:¬ InCone n C h g)
   (j:ℕ) (hj:j=g∨ j=h) (x:Fin n→ Bool):
   gateVal n C j x=
     (decide (∃ u∈ side (n:=n) C j 0,x u=true) &&
       decide (∃ u∈ side (n:=n) C j 1,x u=true)):=by
 have hjm:j∈ junk G C:=by simpa [hJ] using hj
 obtain ⟨hjl,hja⟩:=junk_data G C j hjm
 rw [and_gate_eq C hAO j hjl hja x,
   q70 G C hAO hTop g h hJ hgh hhg j hj 0 x,
   q70 G C hAO hTop g h hJ hgh hhg j hj 1 x]
end N26
namespace N6.N1
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
def stepWire (w:List Bool) (g:Gate):List Bool:=
 w++[g.op.eval (g.inputs.map fun i=> w.getD i false)]
lemma q131 (C:Circuit) (x:List Bool):
   C.wires x=C.gates.foldl stepWire x:=by
 apply @N10.q131
 all_goals assumption
lemma q157 (gs:List Gate) (w:List Bool):
   (gs.foldl stepWire w).length=w.length+gs.length:=by
 apply @N5.z065
 all_goals assumption
lemma q137 (gs:List Gate) (w:List Bool) (i:ℕ) (hi:i < w.length):
   (gs.foldl stepWire w).getD i false=w.getD i false:=by
 apply @N5.z064
 all_goals assumption
lemma getD_ge (w:List Bool) (i:ℕ) (hi:w.length≤ i):w.getD i false=false:=by
 apply @N10.q117
 all_goals assumption
lemma q94 (gs:List Gate) (w:List Bool) (j:ℕ) (hj:j < gs.length):
   (gs.foldl stepWire w).getD (w.length+j) false=
     (gs[j]).op.eval ((gs[j]).inputs.map fun i=>
       if i < w.length+j then (gs.foldl stepWire w).getD i false else false):=by
 induction gs generalizing w j with
 | nil=> simp at hj
 | cons g gs ih=>
   rw [List.foldl_cons]
   cases j with
   | zero=>
     have h1:w.length < (stepWire w g).length:=by simp [stepWire]
     rw [Nat.add_zero,q137 gs (stepWire w g) w.length h1]
     simp only [List.getElem_cons_zero]
     have h2:(stepWire w g).getD w.length false=
         g.op.eval (g.inputs.map fun i=> w.getD i false):=by
       simp [stepWire,Z8]
     rw [h2]
     congr 1
     apply List.map_congr_left
     intro i _
     by_cases hi:i < w.length
     · rw [ite_eq_left hi,q137 gs (stepWire w g) i (by simp [stepWire];omega)]
       simp [stepWire,Z8,List.getElem?_append_left hi]
     · rw [ite_eq_right hi];exact getD_ge w i (by omega)
   | succ j=>
     have hj':j < gs.length:=by simpa using hj
     have key:=ih (stepWire w g) j hj'
     have hl:(stepWire w g).length=w.length+1:=by simp [stepWire]
     rw [hl] at key
     have e:w.length+(j+1)=w.length+1+j:=by omega
     simp only [List.getElem_cons_succ]
     rw [e]
     exact key
def val (C:Circuit) (x:List Bool) (u:ℕ):Bool:=(C.wires x).getD u false
lemma gateAt_eq {C:Circuit} {j:ℕ} (hj:j < C.gates.length):gateAt C j=C.gates[j]:=by
 apply @N5.z068
 all_goals assumption
lemma gateAt_mem {C:Circuit} {j:ℕ} (hj:j < C.gates.length):gateAt C j∈ C.gates:=by
 apply @N5.z069
 all_goals assumption
lemma val_input {n:ℕ} {C:Circuit} {x:List Bool} (hx:x.length=n) {u:ℕ} (hu:u < n):
   val C x u=x.getD u false:=by
 unfold val;rw [q131];exact q137 _ _ _ (by omega)
lemma val_ge {n:ℕ} {C:Circuit} {x:List Bool} (hx:x.length=n) {u:ℕ}
   (hu:n+C.gates.length≤ u):val C x u=false:=by
 unfold val;apply getD_ge;rw [q131,q157];omega
lemma val_gate {n:ℕ} {C:Circuit} {x:List Bool} (hx:x.length=n) {j:ℕ}
   (hj:j < C.gates.length):
   val C x (n+j)=(gateAt C j).op.eval ((gateAt C j).inputs.map fun i=>
     if i < n+j then val C x i else false):=by
 subst hx
 rw [gateAt_eq hj]
 exact q94 C.gates x j hj
lemma val_or {n:ℕ} {C:Circuit} {x:List Bool} (hx:x.length=n) {r:ℕ}
   (hr:r < C.gates.length) (hop:(gateAt C r).op=GateOp.or):
   val C x (n+r)=true↔ ∃ i∈ (gateAt C r).inputs,i < n+r∧ val C x i=true:=by
 rw [val_gate hx hr,hop]
 simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
 constructor
 · rintro ⟨i,hi,h⟩
   by_cases hlt:i < n+r
   · rw [ite_eq_left hlt] at h;exact ⟨i,hi,hlt,h⟩
   · rw [ite_eq_right hlt] at h;cases h
 · rintro ⟨i,hi,hlt,h⟩
   exact ⟨i,hi,by rw [ite_eq_left hlt];exact h⟩
lemma val_and {n:ℕ} {C:Circuit} {x:List Bool} (hx:x.length=n) {r:ℕ}
   (hr:r < C.gates.length) (hop:(gateAt C r).op=GateOp.and):
   val C x (n+r)=true↔ ∀ i∈ (gateAt C r).inputs,i < n+r∧ val C x i=true:=by
 rw [val_gate hx hr,hop]
 simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
 constructor
 · intro h i hi
   have h':=h i hi
   by_cases hlt:i < n+r
   · rw [ite_eq_left hlt] at h';exact ⟨hlt,h'⟩
   · rw [ite_eq_right hlt] at h';cases h'
 · intro h i hi
   rw [ite_eq_left (h i hi).1];exact (h i hi).2
lemma val_ofFn {n:ℕ} (C:Circuit) (x:Fin n→ Bool) (u:Fin n):
   val C (List.ofFn x) u.val=x u:=by
 rw [val_input (n:=n) (by simp) u.isLt]
 simp [Z8]
lemma q115 (n:ℕ) (C:Circuit) (j:ℕ) (x:Fin n→ Bool):
   PEqualNP.EdgeOwnership.gateVal n C j x=val C (List.ofFn x) (n+j):=by
 apply @N5.z070
 all_goals assumption
def OrStep (n:ℕ) (C:Circuit) (w w':ℕ):Prop:=
 ∃ k,k < C.gates.length∧ w=n+k∧ (gateAt C k).op=GateOp.or∧
   w'∈ (gateAt C k).inputs∧ w' < n+k
lemma orStep_up {n:ℕ} {C:Circuit} {x:List Bool} (hx:x.length=n) {w w':ℕ}
   (h:Relation.ReflTransGen (OrStep n C) w w') (hv:val C x w'=true):
   val C x w=true:=by
 induction h using Relation.ReflTransGen.head_induction_on with
 | refl=> exact hv
 | head hstep _ ih=>
   obtain ⟨k,hk,rfl,hop,hin,hlt⟩:=hstep
   exact (val_or hx hk hop).mpr ⟨_,hin,hlt,ih⟩
lemma or_trace {n:ℕ} {C:Circuit} {x:List Bool} (hx:x.length=n):
   ∀ w:ℕ,val C x w=true→
     ∃ w',Relation.ReflTransGen (OrStep n C) w w'∧ val C x w'=true∧
       (w' < n∨ ∃ h,h < C.gates.length∧ w'=n+h∧ (gateAt C h).op≠ GateOp.or):=by
 intro w
 induction w using Nat.strong_induction_on with
 | _ w ih=>
   intro hv
   by_cases hw:w < n
   · exact ⟨w,Relation.ReflTransGen.refl,hv,Or.inl hw⟩
   · by_cases hlen:n+C.gates.length≤ w
     · rw [val_ge hx hlen] at hv;cases hv
     · obtain ⟨k,rfl⟩:∃ k,w=n+k:=⟨w - n,by omega⟩
       have hk:k < C.gates.length:=by omega
       by_cases hop:(gateAt C k).op=GateOp.or
       · obtain ⟨i,hin,hlt,hi⟩:=(val_or hx hk hop).mp hv
         obtain ⟨w',hr,hv',hw'⟩:=ih i hlt hi
         exact ⟨w',Relation.ReflTransGen.head ⟨k,hk,rfl,hop,hin,hlt⟩ hr,hv',hw'⟩
       · exact ⟨n+k,Relation.ReflTransGen.refl,hv,Or.inr ⟨k,hk,rfl,hop⟩⟩
lemma q125 {n:ℕ} (u v:Fin n):pairInput u v u=true:=by
 simp [pairInput]
lemma q126 {n:ℕ} (u v w:Fin n):pairInput u v w=true↔ w=u∨ w=v:=by
 simp [pairInput]
lemma q139 {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v:Fin n):
   graphFun G ∅ (pairInput u v)=true↔ G.Adj u v:=by
 apply @N5.z074
 all_goals assumption
lemma q143 {n:ℕ} {C:Circuit} (u v:Fin n) (p:ℕ)
   (hv:val C (List.ofFn (pairInput u v)) p=true):
   (∃ t:Fin n,(t=u∨ t=v)∧ Relation.ReflTransGen (OrStep n C) p t.val)∨
   (∃ h,h < C.gates.length∧ (gateAt C h).op≠ GateOp.or∧
     Relation.ReflTransGen (OrStep n C) p (n+h)∧
     val C (List.ofFn (pairInput u v)) (n+h)=true):=by
 obtain ⟨w',hr,hv',hw'⟩:=or_trace (n:=n) (C:=C) (x:=List.ofFn (pairInput u v))
   (by simp) p hv
 rcases hw' with hlt | ⟨h,hh,rfl,hop⟩
 · left
   refine ⟨⟨w',hlt⟩,?_,hr⟩
   have h1:=val_ofFn C (pairInput u v) ⟨w',hlt⟩
   rw [show (⟨w',hlt⟩:Fin n).val=w' from rfl,hv'] at h1
   exact (q126 u v _).mp h1.symm
 · right
   exact ⟨h,hh,hop,hr,hv'⟩
lemma q149 {n:ℕ} {C:Circuit} (x:Fin n→ Bool) (p:ℕ) (t:Fin n)
   (hr:Relation.ReflTransGen (OrStep n C) p t.val) (ht:x t=true):
   val C (List.ofFn x) p=true:=
 orStep_up (n:=n) (by simp) hr (by rw [val_ofFn];exact ht)
lemma edge_trace {n:ℕ} (G:SimpleGraph (Fin n)) {C:Circuit} (F:(Fin n→ Bool)→ Bool)
   (hF:∀ u v:Fin n,F (pairInput u v)=true→ G.Adj u v)
   (hout:∀ x:Fin n→ Bool,val C (List.ofFn x) C.output=F x)
   (u v:Fin n) (huv:F (pairInput u v)=true):
   ∃ a,a < C.gates.length∧ (gateAt C a).op≠ GateOp.or∧
     Relation.ReflTransGen (OrStep n C) C.output (n+a)∧
     val C (List.ofFn (pairInput u v)) (n+a)=true:=by
 rcases q143 (C:=C) u v C.output (by rw [hout];exact huv) with
   ⟨t,_,hr⟩ | h
 · exfalso
   have h1:=q149 (pairInput t t) _ t hr (q125 t t)
   rw [hout] at h1
   exact G.irrefl (hF t t h1)
 · exact h
lemma q111 {n:ℕ} {C:Circuit} (F:(Fin n→ Bool)→ Bool)
   (hout:∀ x:Fin n→ Bool,val C (List.ofFn x) C.output=F x) (a:ℕ)
   (hr:Relation.ReflTransGen (OrStep n C) C.output (n+a)) (x:Fin n→ Bool)
   (hv:val C (List.ofFn x) (n+a)=true):F x=true:=by
 rw [← hout]
 exact orStep_up (n:=n) (by simp) hr hv
lemma inCone_iff (n:ℕ) (C:Circuit) (i j:ℕ):
   InCone n C i j↔ j < C.gates.length∧ ∃ k,k < j∧ n+k∈ (gateAt C j).inputs∧
     (i=k∨ InCone n C i k):=by
 apply @N10.inCone_iff
 all_goals assumption
lemma orStep_le {n:ℕ} {C:Circuit} {w w':ℕ}
   (h:Relation.ReflTransGen (OrStep n C) w w'):w'≤ w:=by
 induction h using Relation.ReflTransGen.head_induction_on with
 | refl=> exact le_rfl
 | head hstep _ ih=>
   obtain ⟨k,_,rfl,_,_,hlt⟩:=hstep
   omega
lemma orStep_cone {n:ℕ} {C:Circuit} {w w':ℕ}
   (h:Relation.ReflTransGen (OrStep n C) w w'):
   ∀ k h',w=n+k→ w'=n+h'→ h'=k∨ InCone n C h' k:=by
 induction h using Relation.ReflTransGen.head_induction_on with
 | refl=> intro k h' h1 h2;left;omega
 | @head a c hstep hrest ih=>
   intro k h' h1 h2
   obtain ⟨k0,hk0,e,_,hin,hlt⟩:=hstep
   have hk:k0=k:=by omega
   subst hk
   have hle:=orStep_le hrest
   obtain ⟨k1,hk1⟩:∃ k1,c=n+k1:=⟨c - n,by omega⟩
   subst hk1
   right
   rw [inCone_iff]
   exact ⟨hk0,k1,by omega,hin,ih k1 h' rfl h2⟩
lemma q160 {n:ℕ} {C:Circuit} {a p h:ℕ} (ha:a < C.gates.length)
   (hin:p∈ (gateAt C a).inputs) (hp:p < n+a)
   (hr:Relation.ReflTransGen (OrStep n C) p (n+h)):InCone n C h a:=by
 have hle:=orStep_le hr
 obtain ⟨k1,rfl⟩:∃ k1,p=n+k1:=⟨p - n,by omega⟩
 rw [inCone_iff]
 exact ⟨ha,k1,by omega,hin,orStep_cone hr k1 h rfl rfl⟩
lemma orSets_len (n:ℕ) (gs:List Gate) (cs:List (List ℕ)):
   (gs.foldl (orStep n) cs).length=cs.length+gs.length:=by
 apply @N5.z062
 all_goals assumption
lemma orSets_char (n:ℕ) (gs:List Gate):
   ∀ i j,i∈ (gs.foldl (orStep n) []).getD j []↔
     j < gs.length∧ (i=j∨ ((gs.getD j ⟨GateOp.or,[]⟩).op=GateOp.or∧
       ∃ w∈ (gs.getD j ⟨GateOp.or,[]⟩).inputs,n≤ w∧ w < n+j∧
         i∈ (gs.foldl (orStep n) []).getD (w - n) [])):=by
 induction gs using List.reverseRecOn with
 | nil=> intro i j;simp
 | append_singleton gs g ih=>
   intro i j
   rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
   have hlen:(gs.foldl (orStep n) []).length=gs.length:=by
     rw [orSets_len];simp
   have key:∀ k,k < gs.length→
       (orStep n (gs.foldl (orStep n) []) g).getD k []=
         (gs.foldl (orStep n) []).getD k []:=by
     intro k hk
     simp only [orStep,Z8]
     rw [List.getElem?_append_left (by omega)]
   rcases Nat.lt_trichotomy j gs.length with h | h | h
   · have e1:(gs++[g]).getD j ⟨GateOp.or,[]⟩=gs.getD j ⟨GateOp.or,[]⟩:=by
       simp only [Z8]
       rw [List.getElem?_append_left h]
     rw [key j h,ih i j,e1]
     constructor
     · rintro ⟨_,h3⟩
       refine ⟨by simp;omega,?_⟩
       rcases h3 with h3 | ⟨hop,w,hw,h1,h2,h3⟩
       · exact Or.inl h3
       · refine Or.inr ⟨hop,w,hw,h1,h2,?_⟩
         rw [key (w - n) (by omega)]
         exact h3
     · rintro ⟨_,h3⟩
       refine ⟨h,?_⟩
       rcases h3 with h3 | ⟨hop,w,hw,h1,h2,h3⟩
       · exact Or.inl h3
       · rw [key (w - n) (by omega)] at h3
         exact Or.inr ⟨hop,w,hw,h1,h2,h3⟩
   · subst h
     have e1:(gs++[g]).getD gs.length ⟨GateOp.or,[]⟩=g:=by
       simp [Z8]
     rw [e1]
     by_cases hop:g.op=GateOp.or
     · have e2:(orStep n (gs.foldl (orStep n) []) g).getD gs.length []=
           gs.length::(g.inputs.filter (fun w=> decide (n≤ w∧ w < n+gs.length))).flatMap
             (fun w=> (gs.foldl (orStep n) []).getD (w - n) []):=by
         simp only [orStep,Z8]
         rw [List.getElem?_append_right (by omega)]
         simp [hlen,hop]
       rw [e2]
       simp only [Z10,List.mem_flatMap,List.mem_filter,Z1]
       constructor
       · rintro (h3 | ⟨w,⟨hw,h1,h2⟩,h3⟩)
         · exact ⟨by simp,Or.inl h3⟩
         · refine ⟨by simp,Or.inr ⟨hop,w,hw,h1,h2,?_⟩⟩
           rw [key (w - n) (by omega)]
           exact h3
       · rintro ⟨_,h3 | ⟨_,w,hw,h1,h2,h3⟩⟩
         · exact Or.inl h3
         · rw [key (w - n) (by omega)] at h3
           exact Or.inr ⟨w,⟨hw,h1,h2⟩,h3⟩
     · have e2:(orStep n (gs.foldl (orStep n) []) g).getD gs.length []=[gs.length]:=by
         simp only [orStep,Z8]
         rw [List.getElem?_append_right (by omega)]
         simp [hlen,hop]
       rw [e2]
       simp only [List.mem_singleton]
       constructor
       · intro h3
         exact ⟨by simp,Or.inl h3⟩
       · rintro ⟨_,h3 | ⟨hop2,_⟩⟩
         · exact h3
         · exact (hop hop2).elim
   · have e0:(orStep n (gs.foldl (orStep n) []) g).getD j []=[]:=by
       simp only [orStep,Z8]
       rw [List.getElem?_eq_none (by simp;omega)]
       rfl
     rw [e0]
     constructor
     · intro h0;simp at h0
     · rintro ⟨h0,_⟩
       simp at h0
       omega
lemma q147 (n:ℕ) (C:Circuit) (k g:ℕ):
   OrReaches n C (n+k) g↔ k < C.gates.length∧ (g=k∨ ((gateAt C k).op=GateOp.or∧
     ∃ i∈ (gateAt C k).inputs,i < n+k∧ OrReaches n C i g)):=by
 have h:=orSets_char n C.gates g k
 unfold OrReaches orSets gateAt
 have e:n+k - n=k:=by omega
 rw [e,h]
 constructor
 · rintro ⟨_,hk,h3⟩
   refine ⟨hk,?_⟩
   rcases h3 with h3 | ⟨hop,w,hw,h1,h2,h3⟩
   · exact Or.inl h3
   · exact Or.inr ⟨hop,w,hw,h2,h1,h3⟩
 · rintro ⟨hk,h3⟩
   refine ⟨by omega,hk,?_⟩
   rcases h3 with h3 | ⟨hop,w,hw,h2,h1,h3⟩
   · exact Or.inl h3
   · exact Or.inr ⟨hop,w,hw,h1,h2,h3⟩
lemma q108 {n:ℕ} {C:Circuit} {w w2:ℕ}
   (h:Relation.ReflTransGen (OrStep n C) w w2):
   ∀ g,w2=n+g→ g < C.gates.length→ OrReaches n C w g:=by
 induction h using Relation.ReflTransGen.head_induction_on with
 | refl=>
   intro g h1 hg
   subst h1
   exact (q147 n C g g).mpr ⟨hg,Or.inl rfl⟩
 | @head a c hstep hrest ih=>
   intro g h1 hg
   obtain ⟨k,hk,rfl,hop,hin,hlt⟩:=hstep
   exact (q147 n C k g).mpr ⟨hk,Or.inr ⟨hop,c,hin,hlt,ih g h1 hg⟩⟩
lemma q101 {n:ℕ} {C:Circuit} (g:ℕ):
   ∀ w,OrReaches n C w g→
     Relation.ReflTransGen (OrStep n C) w (n+g)∧ g < C.gates.length:=by
 intro w
 induction w using Nat.strong_induction_on with
 | _ w ih=>
   intro h
   have hnw:n≤ w:=h.1
   obtain ⟨k,rfl⟩:∃ k,w=n+k:=⟨w - n,by omega⟩
   obtain ⟨hk,h3⟩:=(q147 n C k g).mp h
   rcases h3 with rfl | ⟨hop,i,hi,hlt,hr⟩
   · exact ⟨Relation.ReflTransGen.refl,hk⟩
   · obtain ⟨hr2,hg⟩:=ih i hlt hr
     exact ⟨Relation.ReflTransGen.head ⟨k,hk,rfl,hop,hi,hlt⟩ hr2,hg⟩
lemma q119 {n:ℕ} {C:Circuit} {p:ℕ} (u:Fin n)
   (hu:u∈ PEqualNP.TopForm.orIn n C p):
   Relation.ReflTransGen (OrStep n C) p u.val:=by
 simp only [PEqualNP.TopForm.orIn,Z0,Z7,true_and] at hu
 rcases hu with h | ⟨k,hk,hr,hop,hin⟩
 · rw [h]
 · exact (q101 k p hr).1.tail ⟨k,hk,rfl,hop,hin,by omega⟩
lemma q128 {n:ℕ} {C:Circuit} {p:ℕ} (u:Fin n)
   (hr:Relation.ReflTransGen (OrStep n C) p u.val):
   u∈ PEqualNP.TopForm.orIn n C p:=by
 simp only [PEqualNP.TopForm.orIn,Z0,Z7,true_and]
 rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c,hpc,hstep⟩
 · exact Or.inl h
 · obtain ⟨k,hk,rfl,hop,hin,_⟩:=hstep
   exact Or.inr ⟨k,hk,q108 hpc k rfl hk,hop,hin⟩
variable {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
lemma topData {a:ℕ} (ha:a∈ tops G C):
   a < C.gates.length∧ (gateAt C a).op=GateOp.and∧ BelowF G C a:=by
 simpa only [tops,gatesWhere,Z0,Z9] using ha
lemma junkData {a:ℕ} (ha:a∈ junk G C):
   a < C.gates.length∧ (gateAt C a).op=GateOp.and∧
     ∃ x:Fin n→ Bool,gateVal n C a x=true∧ graphFun G ∅ x=false:=by
 rcases Z0.mp ha with ⟨hr,hop,hal,hd⟩
 exact ⟨hal,hop,hd⟩
lemma q153 (hAO:IsAO2 n C) {a:ℕ} (ha:a < C.gates.length):
   ∃ p q,(gateAt C a).inputs=[p,q]:=
 List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
lemma opndMem (hAO:IsAO2 n C) {a:ℕ} (ha:a < C.gates.length) (b:Fin 2):
   opnd C a b∈ (gateAt C a).inputs:=by
 apply @N5.z105
 all_goals assumption
lemma opndBound (hAO:IsAO2 n C) {a:ℕ} (ha:a < C.gates.length) (b:Fin 2):
   opnd C a b < n+a:=by
 apply @N5.z104
 all_goals assumption
lemma andValBoth (hAO:IsAO2 n C) {a:ℕ} (ha:a < C.gates.length)
   (hop:(gateAt C a).op=GateOp.and) (x:Fin n→ Bool):
   gateVal n C a x=true↔
     val C (List.ofFn x) (opnd C a 0)=true∧
     val C (List.ofFn x) (opnd C a 1)=true:=by
 rw [q115,val_and (n:=n) (by simp) ha hop]
 constructor
 · intro h
   exact ⟨(h _ (opndMem hAO ha 0)).2,(h _ (opndMem hAO ha 1)).2⟩
 · intro h i hi
   refine ⟨hAO.2.1 a ha i hi,?_⟩
   obtain ⟨p,q,hpq⟩:=q153 hAO ha
   rcases Z10.mp (hpq ▸ hi) with rfl | hq
   · simpa [opnd,hpq] using h.1
   · have e:i=q:=List.mem_singleton.mp hq
     subst i
     simpa [opnd,hpq] using h.2
lemma q110 (hAO:IsAO2 n C) {a:ℕ} (ha:a < C.gates.length)
   (hop:(gateAt C a).op=GateOp.and) (x:Fin n→ Bool):
   gateVal n C a x=true↔ ∀ b:Fin 2,val C (List.ofFn x) (opnd C a b)=true:=by
 rw [andValBoth hAO ha hop]
 constructor
 · intro h b
   fin_cases b
   · exact h.1
   · exact h.2
 · intro h
   exact ⟨h 0,h 1⟩
lemma q88 (hAO:IsAO2 n C) {a h:ℕ} (ha:a < C.gates.length)
   {b:Fin 2} (hr:OrReaches n C (opnd C a b) h):
   InCone n C h a:=
 q160 ha (opndMem hAO ha b) (opndBound hAO ha b)
   (q101 h _ hr).1
lemma q87 (hAO:IsAO2 n C) (hT:TopForm G C) {a h:ℕ}
   (ha:a < C.gates.length) (hop:(gateAt C a).op=GateOp.and)
   {b:Fin 2} (hr:OrReaches n C (opnd C a b) h)
   (hh:(gateAt C h).op=GateOp.and):h∈ junk G C:=by
 have hlen:=(q101 h _ hr).2
 have hnb:¬ BelowF G C h:=
   fun hb=> hT h hlen a ha hh hb hop (q88 hAO ha hr)
 have hdirty:∃ x:Fin n→ Bool,gateVal n C h x=true∧ graphFun G ∅ x=false:=by
   by_contra hne
   apply hnb
   intro x hx
   by_contra hf
   exact hne ⟨x,hx,Z14.mpr hf⟩
 exact Z0.mpr ⟨Z9.mpr hlen,hh,hlen,hdirty⟩
lemma reachVal {w h:ℕ} {x:Fin n→ Bool} (hr:OrReaches n C w h)
   (hh:gateVal n C h x=true):val C (List.ofFn x) w=true:=
 orStep_up (n:=n) (by simp) (q101 h _ hr).1 hh
lemma q136 (b c:Fin 2):c=b∨ c=1 - b:=by
 fin_cases b <;> fin_cases c <;> decide
lemma q90 (hAO:IsAO2 n C) {a j:ℕ} (ha:a∈ tops G C) {b:Fin 2}
   (hr:OrReaches n C (opnd C a b) j):
   side (n:=n) C a (1 - b)⊆ wmax G C j:=by
 intro t ht
 obtain ⟨hal,hao,hab⟩:=topData ha
 simp only [wmax,Z0,Z7,true_and]
 intro x hj hx
 apply hab x
 apply (q110 hAO hal hao x).mpr
 intro c
 rcases q136 b c with rfl | rfl
 · exact reachVal hr hj
 · exact q149 x _ t (q119 t ht) hx
lemma q120 (hAO:IsAO2 n C) (hT:TopForm G C) {a:ℕ}
   (ha:a < C.gates.length) (ho:(gateAt C a).op=GateOp.and) {b:Fin 2}
   {u v:Fin n} (h:val C (List.ofFn (pairInput u v)) (opnd C a b)=true):
   (∃ t∈ side (n:=n) C a b,t=u∨ t=v)∨
     ∃ j∈ junk G C,OrReaches n C (opnd C a b) j∧
       gateVal n C j (pairInput u v)=true:=by
 rcases q143 (C:=C) u v _ h with ⟨t,ht,hr⟩ | ⟨j,hj,hn,hr,hv⟩
 · exact .inl ⟨t,q128 t hr,ht⟩
 · have hr':=q108 hr j rfl hj
   exact .inr ⟨j,q87 hAO hT ha ho hr'
     ((hAO.1 _ (gateAt_mem hj)).resolve_right hn),hr',hv⟩
lemma memJunkPair {j k a:ℕ} (hs:junk G C={j,k}) (ha:a∈ junk G C):
   a=j∨ a=k:=by
 simpa only [hs,Z6,Z3] using ha
end N6.N1
namespace N6.N24
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo
lemma q63 (gs:List Gate) (acc:List Bool) (j:ℕ) (hj:j < gs.length)
   (hback:∀ k∈ gs[j].inputs,k < acc.length+j):
   (gs.foldl (fun w g=> w++[g.op.eval (g.inputs.map fun k=> w.getD k false)]) acc).getD
       (acc.length+j) false=
     gs[j].op.eval (gs[j].inputs.map fun k=>
       (gs.foldl (fun w g=> w++[g.op.eval (g.inputs.map fun m=> w.getD m false)]) acc).getD
         k false):=by
 apply @N5.z063
 all_goals assumption
lemma wval_input {n:ℕ} (C:Circuit) (x:Fin n→ Bool) (i:ℕ) (hi:i < n):
   wval C x i=x ⟨i,hi⟩:=by
 apply @N5.z144
 all_goals assumption
lemma q97 {n:ℕ} (C:Circuit) (j:ℕ) (x:Fin n→ Bool):
   gateVal n C j x=wval C x (n+j):=by
 apply @N5.z070
 all_goals assumption
lemma wval_ge_len {n:ℕ} (C:Circuit) (x:Fin n→ Bool) {w:ℕ} (hw:n+C.gates.length≤ w):
   wval C x w=false:=by
 apply @N5.z143
 all_goals assumption
lemma gateAt_eq {C:Circuit} {j:ℕ} (hj:j < C.gates.length):
   gateAt C j=C.gates[j]:=by
 apply @N5.z068
 all_goals assumption
lemma q116 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) {j:ℕ} (hj:j < C.gates.length):
   (gateAt C j).inputs=[opnd C j 0,opnd C j 1]:=by
 apply @N5.z071
 all_goals assumption
lemma opnd_mem {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) {j:ℕ} (hj:j < C.gates.length) (b:Fin 2):
   opnd C j b∈ (gateAt C j).inputs:=by
 apply @N5.z105
 all_goals assumption
lemma opnd_lt {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) {j:ℕ} (hj:j < C.gates.length) (b:Fin 2):
   opnd C j b < n+j:=by
 apply @N5.z104
 all_goals assumption
lemma q132 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (x:Fin n→ Bool)
   {j:ℕ} (hj:j < C.gates.length):
   wval C x (n+j)=(gateAt C j).op.eval [wval C x (opnd C j 0),wval C x (opnd C j 1)]:=by
 apply @N5.z141
 all_goals assumption
lemma inCone_iff {n:ℕ} {C:Circuit} {i j:ℕ} (hj:j < C.gates.length):
   InCone n C i j↔
     ∃ w∈ (gateAt C j).inputs,n≤ w∧ w < n+j∧ (i=w - n∨ InCone n C i (w - n)):=by
 apply @N5.z078
 all_goals assumption
def patch (C:Circuit) (j:ℕ) (g:Gate):Circuit:=⟨C.gates.set j g,C.output⟩
lemma q162 (C:Circuit) (j:ℕ) (g:Gate):
   (patch C j g).gates.length=C.gates.length:=by
 apply @N27.q162
 all_goals assumption
lemma q96 (C:Circuit) (j k:ℕ) (g:Gate) (hne:j≠ k):
   gateAt (patch C j g) k=gateAt C k:=by
 apply @N27.q96
 all_goals assumption
lemma q68 {n:ℕ} {C:Circuit} {j:ℕ} {g:Gate}
   (hAO:IsAO2 n C) (x:Fin n→ Bool) {k:ℕ} (hk:k < C.gates.length)
   (hne:j≠ k):
   wval (patch C j g) x (n+k)=(gateAt C k).op.eval
     [wval (patch C j g) x (opnd C k 0),wval (patch C j g) x (opnd C k 1)]:=by
 have hk':k < (patch C j g).gates.length:=by simpa only [q162] using hk
 have hgate:=q96 C j k g hne
 have hlen:(List.ofFn x).length=n:=List.length_ofFn
 have hback:∀ w∈ (patch C j g).gates[k].inputs,w < (List.ofFn x).length+k:=by
   intro w hw
   rw [← gateAt_eq hk',hgate] at hw
   rw [hlen]
   exact hAO.2.1 k hk w hw
 have heval:=q63 (patch C j g).gates (List.ofFn x) k hk' hback
 rw [hlen,← gateAt_eq hk',hgate,q116 hAO hk] at heval
 simpa only [wval,Circuit.wires,Z15,Z16] using heval
lemma q20 {n:ℕ} {C:Circuit} {j:ℕ} {g:Gate}
   (hAO:IsAO2 n C) (k:ℕ) (hne:j≠ k) (hCone:¬ InCone n C j k)
   (x:Fin n→ Bool):gateVal n (patch C j g) k x=gateVal n C k x:=by
 induction k using Nat.strong_induction_on with
 | ind k ih=>
   by_cases hk:k < C.gates.length
   · have hval (b:Fin 2):wval (patch C j g) x (opnd C k b)=
         wval C x (opnd C k b):=by
       by_cases hw:opnd C k b < n
       · rw [wval_input _ _ _ hw,wval_input _ _ _ hw]
       · have hw':n≤ opnd C k b:=by omega
         have hlt:=opnd_lt hAO hk b
         have hsub_ne:j≠ opnd C k b - n:=by
           intro he
           apply hCone
           exact (inCone_iff hk).mpr ⟨opnd C k b,opnd_mem hAO hk b,hw',hlt,Or.inl he⟩
         have hsub_cone:¬ InCone n C j (opnd C k b - n):=by
           intro he
           apply hCone
           exact (inCone_iff hk).mpr ⟨opnd C k b,opnd_mem hAO hk b,hw',hlt,Or.inr he⟩
         have hv:=ih (opnd C k b - n) (by omega) hsub_ne hsub_cone
         rw [q97,q97,Nat.add_sub_of_le hw'] at hv
         exact hv
     rw [q97,q97,q68 hAO x hk hne,
       q132 hAO x hk,hval 0,hval 1]
   · rw [q97,q97,wval_ge_len _ _ (by rw [q162];omega),
       wval_ge_len _ _ (by omega)]
end N6.N24
namespace N6
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
def offPatch (C:Circuit) (h:ℕ):Circuit:=⟨C.gates.set h ⟨GateOp.or,[]⟩,C.output⟩
lemma q99 (C:Circuit) (h:ℕ):(offPatch C h).gates.length=C.gates.length:=by
 simp [offPatch]
lemma q75 (C:Circuit) (h k:ℕ) (hne:h≠ k):
   gateAt (offPatch C h) k=gateAt C k:=by
 simp [offPatch,gateAt,Z8,List.getElem?_set_ne hne]
lemma q103 {n:ℕ} {C:Circuit} {h w w':ℕ}
   (hAnd:(gateAt C h).op=GateOp.and) (hs:N1.OrStep n C w w'):
   N1.OrStep n (offPatch C h) w w':=by
 obtain ⟨k,hk,rfl,hOr,hi,hb⟩:=hs
 have hne:h≠ k:=by
   intro he
   rw [← he,hAnd] at hOr
   cases hOr
 refine ⟨k,by simpa only [q99] using hk,rfl,?_,?_,hb⟩
 · simpa only [q75 C h k hne] using hOr
 · simpa only [q75 C h k hne] using hi
lemma q100 {n:ℕ} {C:Circuit} {h w w':ℕ}
   (hAnd:(gateAt C h).op=GateOp.and)
   (hs:Relation.ReflTransGen (N1.OrStep n C) w w'):
   Relation.ReflTransGen (N1.OrStep n (offPatch C h)) w w':=by
 induction hs using Relation.ReflTransGen.head_induction_on with
 | refl=> exact Relation.ReflTransGen.refl
 | head hs _ ih=> exact Relation.ReflTransGen.head (q103 hAnd hs) ih
lemma q40 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C)
   {h:ℕ} (hAnd:(gateAt C h).op=GateOp.and) (x:Fin n→ Bool):
   ∀ w,N1.val C (List.ofFn x) w=true→ N1.val (offPatch C h) (List.ofFn x) w=false→
   ∃ j,j < C.gates.length∧ (gateAt C j).op=GateOp.and∧ OrReaches n C w j∧
     gateVal n C j x=true∧ gateVal n (offPatch C h) j x=false:=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih=>
   intro hw hw'
   by_cases hwInput:w < n
   · rw [N1.val_input (n:=n) (by simp) hwInput] at hw hw'
     rw [hw] at hw'
     cases hw'
   · by_cases hwLarge:n+C.gates.length≤ w
     · rw [N1.val_ge (n:=n) (by simp) hwLarge] at hw
       cases hw
     · obtain ⟨k,rfl⟩:∃ k,w=n+k:=⟨w - n,by omega⟩
       have hk:k < C.gates.length:=by omega
       by_cases hOr:(gateAt C k).op=GateOp.or
       · have hne:h≠ k:=by
           intro he
           rw [← he,hAnd] at hOr
           cases hOr
         obtain ⟨v,hvMem,hvLt,hv⟩:=(N1.val_or (n:=n) (by simp) hk hOr).mp hw
         have hv':N1.val (offPatch C h) (List.ofFn x) v=false:=by
           cases hv':N1.val (offPatch C h) (List.ofFn x) v
           · rfl
           · have hk':k < (offPatch C h).gates.length:=by simpa only [q99] using hk
             have hOr':(gateAt (offPatch C h) k).op=GateOp.or:=by
               simpa only [q75 C h k hne] using hOr
             have hMem':v∈ (gateAt (offPatch C h) k).inputs:=by
               simpa only [q75 C h k hne] using hvMem
             have ht:=(N1.val_or (n:=n) (by simp) hk' hOr').mpr ⟨v,hMem',hvLt,hv'⟩
             rw [hw'] at ht
             cases ht
         obtain ⟨j,hj,hjAnd,hReach,hjv,hjv'⟩:=ih v hvLt hv hv'
         refine ⟨j,hj,hjAnd,?_,hjv,hjv'⟩
         exact (N1.q147 n C k j).mpr ⟨hk,Or.inr ⟨hOr,v,hvMem,hvLt,hReach⟩⟩
       · have hAndK:(gateAt C k).op=GateOp.and:=(hAO.1 _ (N1.gateAt_mem hk)).resolve_right hOr
         exact ⟨k,hk,hAndK,(N1.q147 n C k k).mpr ⟨hk,Or.inl rfl⟩,hw,hw'⟩
end N6
namespace N0
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo
end N0
namespace N6
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
lemma q17 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
   {C:Circuit} (hAO:IsAO2 n C) (hF:circuitFun n C=graphFun G ∅)
   (hT:TopForm G C) {g h:ℕ} (hJ:junk G C={g,h}) (hne:g≠ h)
   (hIndependent:¬ InCone n C h g)
   (u v:Fin n) (hAdj:G.Adj u v)
   (hLost:circuitFun n (offPatch C h) (pairInput u v)=false):
   (gateVal n C h (pairInput u v)=true∧ (u∈ wmax G C h∨ v∈ wmax G C h))∨
   (gateVal n C h (pairInput u v)=true∧ gateVal n C g (pairInput u v)=true∧
     ∀ x:Fin n→ Bool,gateVal n C h x=true→ gateVal n C g x=true→
       graphFun G ∅ x=true):=by
 have hhJ:h∈ junk G C:=by rw [hJ];simp
 obtain ⟨hhLen,hhAnd,hx,hhx,hFx⟩:=N1.junkData hhJ
 have hout (x:Fin n→ Bool):N1.val C (List.ofFn x) C.output=graphFun G ∅ x:=
   congrFun hF x
 obtain ⟨a,haLen,haNotOr,haPath,haVal⟩:=
   N1.edge_trace G (graphFun G ∅) (fun x y hxy=> (N1.q139 G x y).mp hxy)
     hout u v ((N1.q139 G u v).mpr hAdj)
 have haAnd:(gateAt C a).op=GateOp.and:=
   (hAO.1 _ (N1.gateAt_mem haLen)).resolve_right haNotOr
 have haBelow:BelowF G C a:=fun x hv=>
   N1.q111 (graphFun G ∅) hout a haPath x hv
 have haTop:a∈ tops G C:=by
   simpa only [tops,gatesWhere,Z0,Z9] using
     And.intro haLen (And.intro haAnd haBelow)
 have hha:h≠ a:=by
   intro he
   subst a
   have ht:=haBelow hx hhx
   rw [hFx] at ht
   cases ht
 have haOff:gateVal n (offPatch C h) a (pairInput u v)=false:=by
   cases hc:gateVal n (offPatch C h) a (pairInput u v)
   · rfl
   · have ho:=N1.orStep_up (n:=n) (by simp) (q100 hhAnd haPath) hc
     change circuitFun n (offPatch C h) (pairInput u v)=true at ho
     rw [hLost] at ho
     cases ho
 have hEval:gateVal n (offPatch C h) a (pairInput u v)=
     (N1.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 0) &&
      N1.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 1)):=by
   have he:=N24.q68 (j:=h) (g:=⟨GateOp.or,[]⟩) hAO (pairInput u v) haLen hha
   change gateVal n (offPatch C h) a (pairInput u v)=(gateAt C a).op.eval
     [N1.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 0),
      N1.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 1)] at he
   simpa only [haAnd,GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true] using he
 obtain ⟨b,hbOff⟩:∃ b:Fin 2,
     N1.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a b)=false:=by
   by_cases h0:N1.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 0)=false
   · exact ⟨0,h0⟩
   · have h0t:=Bool.eq_true_of_not_eq_false h0
     refine ⟨1,?_⟩
     rw [haOff,h0t,Bool.true_and] at hEval
     exact hEval.symm
 have hbVal:=((N1.q110 hAO haLen haAnd (pairInput u v)).mp haVal) b
 obtain ⟨j,hjLen,hjAnd,hjReach,hjVal,hjOff⟩:=
   q40 hAO hhAnd (pairInput u v) (opnd C a b) hbVal hbOff
 have hjJ:=N1.q87 hAO hT haLen haAnd hjReach hjAnd
 have hjh:j=h:=by
   rcases N1.memJunkPair hJ hjJ with hjg | hjh
   · subst j
     have he:=N24.q20 (j:=h) (g:=⟨GateOp.or,[]⟩)
       hAO g (Ne.symm hne) hIndependent (pairInput u v)
     change gateVal n (offPatch C h) g (pairInput u v)=gateVal n C g (pairInput u v) at he
     rw [he,hjVal] at hjOff
     cases hjOff
   · exact hjh
 subst j
 have hoVal:=((N1.q110 hAO haLen haAnd (pairInput u v)).mp haVal) (1 - b)
 rcases N1.q120 hAO hT haLen haAnd hoVal with ⟨t,ht,htu⟩ | ⟨k,hkJ,hkReach,hkVal⟩
 · have htw:=N1.q90 hAO haTop hjReach ht
   rcases htu with rfl | rfl
   · exact Or.inl ⟨hjVal,Or.inl htw⟩
   · exact Or.inl ⟨hjVal,Or.inr htw⟩
 · rcases N1.memJunkPair hJ hkJ with hkg | hkh
   · subst k
     refine Or.inr ⟨hjVal,hkVal,?_⟩
     intro y hhy hgy
     apply haBelow y
     apply (N1.q110 hAO haLen haAnd y).mpr
     intro c
     rcases N1.q136 b c with rfl | rfl
     · exact N1.reachVal hjReach hhy
     · exact N1.reachVal hkReach hgy
   · subst k
     have ht:gateVal n C a hx=true:=by
       apply (N1.q110 hAO haLen haAnd hx).mpr
       intro c
       rcases N1.q136 b c with rfl | rfl
       · exact N1.reachVal hjReach hhx
       · exact N1.reachVal hkReach hhx
     have hf:=haBelow hx ht
     rw [hFx] at hf
     cases hf
end N6
namespace N28
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
lemma q8 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] {K:Circuit} (s:Fin n→ Bool)
   (hbip:∀ u v,G.Adj u v→ s u≠ s v)
   (hAO:IsAO2 n K) (hF:circuitFun n K=graphFun G ∅) (hT:TopForm G K)
   {g h:ℕ} (hJ:junk G K={g,h}) (hne:g≠ h) (hind:¬ InCone n K h g)
   {A B C D:Finset (Fin n)}
   (hhval:∀ x,gateVal n K h x=setProduct A B x)
   (hgval:∀ x,gateVal n K g x=setProduct C D x)
   (hAs:∀ a∈ A,s a=false) (hBs:∀ b∈ B,s b=true)
   (hCs:∀ c∈ C,s c=false) (hDs:∀ d∈ D,s d=true)
   (hnoflag:¬ N19.CrossStar G C D)
   (u v:Fin n) (huv:G.Adj u v)
   (hlost:circuitFun n (N6.offPatch K h) (pairInput u v)=false):
   gateVal n K h (pairInput u v)=true∧ (u∈ wmax G K h∨ v∈ wmax G K h):=by
 rcases N6.q17 hAO hF hT hJ hne hind u v huv hlost with
   hf | ⟨hh,hg,hc⟩
 · exact hf
 have hm:=N19.q0 s hbip hAs hBs hCs hDs
   (by intro x hx hy;exact hc x (by rw [hhval];exact hx) (by rw [hgval];exact hy))
   hnoflag u v (by rw [← hhval];exact hh) (by rw [← hgval];exact hg)
 refine ⟨hh,?_⟩
 rcases hm with hu | hv
 · left
   apply Z0.mpr
   refine ⟨Z7 _,?_⟩
   intro x hx hxu
   exact hu x (by rw [← hhval];exact hx) hxu
 · right
   apply Z0.mpr
   refine ⟨Z7 _,?_⟩
   intro x hx hxv
   exact hv x (by rw [← hhval];exact hx) hxv
lemma q2 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] {K:Circuit} (s:Fin n→ Bool)
   (hbip:∀ u v,G.Adj u v→ s u≠ s v)
   (hAO:IsAO2 n K) (hF:circuitFun n K=graphFun G ∅) (hT:TopForm G K)
   {g h:ℕ} (hJ:junk G K={g,h}) (hne:g≠ h)
   (hgh:¬ InCone n K g h) (hhg:¬ InCone n K h g)
   (hpure:∀ j∈ junk G K,∃ b:Fin 2,
     (∀ a∈ side (n:=n) K j b,s a=false)∧
     (∀ a∈ side (n:=n) K j (1-b),s a=true))
   (hnoflag:¬ N19.CrossStar G (side (n:=n) K g 0) (side (n:=n) K g 1))
   (u v:Fin n) (huv:G.Adj u v)
   (hlost:circuitFun n (N6.offPatch K h) (pairInput u v)=false):
   gateVal n K h (pairInput u v)=true∧ (u∈ wmax G K h∨ v∈ wmax G K h):=by
 obtain ⟨b,hbL,hbR⟩:=hpure h (by rw [hJ];simp)
 obtain ⟨c,hcL,hcR⟩:=hpure g (by rw [hJ];simp)
 have hv0:=N26.q71 G K hAO hT g h hJ hgh hhg h (Or.inr rfl)
 have hv1:=N26.q71 G K hAO hT g h hJ hgh hhg g (Or.inl rfl)
 have hhval:∀ x,gateVal n K h x=
     setProduct (side (n:=n) K h b) (side (n:=n) K h (1-b)) x:=by
   intro x
   fin_cases b
   · exact hv0 x
   · change gateVal n K h x=setProduct (side K h 1) (side K h 0) x
     rw [q109]
     exact hv0 x
 have hgval:∀ x,gateVal n K g x=
     setProduct (side (n:=n) K g c) (side (n:=n) K g (1-c)) x:=by
   intro x
   fin_cases c
   · exact hv1 x
   · change gateVal n K g x=setProduct (side K g 1) (side K g 0) x
     rw [q109]
     exact hv1 x
 have hn:¬ N19.CrossStar G (side (n:=n) K g c) (side (n:=n) K g (1-c)):=by
   intro ht
   apply hnoflag
   fin_cases c
   · exact ht
   · obtain ⟨a,ha,d,hd,hA,hD⟩:=ht
     exact ⟨d,hd,a,ha,(fun p hp=> (hD p hp).symm),(fun q hq=> (hA q hq).symm)⟩
 exact q8 s hbip hAO hF hT hJ hne hhg hhval hgval
   hbL hbR hcL hcR hn u v huv hlost
lemma q12 {n:ℕ} (G:SimpleGraph (Fin n))
   [DecidableRel G.Adj] (K:Circuit) (s:Fin n→ Bool)
   (hbip:∀ u v,G.Adj u v→ s u≠ s v)
   (hL:IsLeastAO G K)
   (hOne:∀ E:Circuit,IsLeastAO G E→ (junk G E).card≠ 1)
   (hT:TopForm G K) {j k:ℕ} (hne:j≠ k) (hJ:junk G K={j,k})
   (hjk:¬ InCone n K j k) (hkj:¬ InCone n K k j) (h4:NoFourCycle G)
   (hP:2≤ (side (n:=n) K j 0).card) (hQ:2≤ (side (n:=n) K j 1).card)
   (hpure:∀ i∈ junk G K,∃ b:Fin 2,
     (∀ a∈ side (n:=n) K i b,s a=false)∧
     (∀ a∈ side (n:=n) K i (1-b),s a=true))
   (hnoflag:¬ N19.CrossStar G (side (n:=n) K k 0) (side (n:=n) K k 1)):
   N19.CrossStar G (side (n:=n) K j 0) (side (n:=n) K j 1):=by
 obtain ⟨b,hbL,hbR⟩:=hpure j (by rw [hJ];simp)
 have hd:Disjoint (side (n:=n) K j 0) (side (n:=n) K j 1):=by
   apply Finset.disjoint_left.mpr
   intro a ha hb
   have h1:s a=false:=hbL a (by fin_cases b <;> assumption)
   have h2:s a=true:=hbR a (by fin_cases b <;> assumption)
   rw [h1] at h2
   contradiction
 have hf:∃ z∈ side (n:=n) K j 0,∃ zp∈ side (n:=n) K j 1,
     G.Adj z zp∧ (∀ p∈ side (n:=n) K j 0,G.Adj p zp)∧
       (∀ q∈ side (n:=n) K j 1,G.Adj z q):=by
   apply N9.q6 G K hL hOne hne hJ hjk
     (side (n:=n) K j 0) (side (n:=n) K j 1) h4 hd hP hQ
   · exact N26.q70 G K hL.1 hT j k hJ hjk hkj j (Or.inl rfl) 0
   · exact N26.q70 G K hL.1 hT j k hJ hjk hkj j (Or.inl rfl) 1
   · intro u v huv hLost
     have hJ':junk G K={k,j}:=by rw [hJ,Finset.pair_comm]
     obtain ⟨hjv,hFilter⟩:=q2 s hbip hL.1 hL.2.1 hT hJ'
       (Ne.symm hne) hkj hjk hpure hnoflag u v huv hLost
     have hjval:=N26.q71 G K hL.1 hT j k hJ hjk hkj j (Or.inl rfl)
     refine ⟨huv,(hjval _).symm.trans hjv,?_⟩
     rcases hFilter with hu | hv
     · exact Or.inl ((N15.wmax_iff G K j _ _ hjval u).mp hu)
     · exact Or.inr ((N15.wmax_iff G K j _ _ hjval v).mp hv)
 obtain ⟨z,hz,zp,hzp,_,hP,hQ⟩:=hf
 exact ⟨z,hz,zp,hzp,hP,hQ⟩
lemma q36 {n:ℕ} (G:SimpleGraph (Fin n))
   [DecidableRel G.Adj] (K:Circuit) (s:Fin n→ Bool)
   (hbip:∀ u v,G.Adj u v→ s u≠ s v)
   (hL:IsLeastAO G K)
   (hOne:∀ E:Circuit,IsLeastAO G E→ (junk G E).card≠ 1)
   (hT:TopForm G K) {j k:ℕ} (hne:j≠ k) (hJ:junk G K={j,k})
   (hjk:¬ InCone n K j k) (hkj:¬ InCone n K k j) (h4:NoFourCycle G)
   (hP:2≤ (side (n:=n) K j 0).card) (hQ:2≤ (side (n:=n) K j 1).card)
   (hpure:∀ i∈ junk G K,∃ b:Fin 2,
     (∀ a∈ side (n:=n) K i b,s a=false)∧
     (∀ a∈ side (n:=n) K i (1-b),s a=true))
   (hjnot:¬ N19.CrossStar G (side (n:=n) K j 0) (side (n:=n) K j 1))
   (hknot:¬ N19.CrossStar G (side (n:=n) K k 0) (side (n:=n) K k 1)):False:=by
 exact hjnot (q12 G K s hbip hL hOne hT hne hJ hjk hkj h4
   hP hQ hpure hknot)
end N28
namespace N23
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
 PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
 PEqualNP.CleanedNonEdge PEqualNP.TopForm
lemma q41 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] {K:Circuit} (s:Fin n→ Bool)
   (hbip:∀ u v,G.Adj u v→ s u≠ s v) (h4:NoFourCycle G)
   (hAO:IsAO2 n K) (hTF:TopForm G K)
   (hcompute:circuitFun n K=graphFun G ∅)
   {g h p:ℕ} (c d:Fin 2) (hp:p < K.gates.length) (hgN:g < K.gates.length)
   (hJ:∀ k∈ junk G K,k=g∨ k=h)
   (hroot:opnd K g c=n+p)
   (hlive:∀ i < K.gates.length,
     K.output=n+i∨ ∃ j < K.gates.length,n+i∈ (gateAt K j).inputs)
   {A B C D:Finset (Fin n)} {u z t a:Fin n}
   (hAp:∀ x,gateVal n K p x=setOr A x)
   (hABg:∀ x,gateVal n K g x=setProduct A B x)
   (hCDh:∀ x,gateVal n K h x=setProduct C D x)
   (hBoperand:∀ x,N10.W n K x (opnd K g (1 - c))=setOr B x)
   (hCoperand:∀ x,N10.W n K x (opnd K h d)=setOr C x)
   (hDoperand:∀ x,N10.W n K x (opnd K h (1 - d))=setOr D x)
   (hu:u∈ A) (hzA:z∈ A) (ha:a∈ A) (huz:u≠ z)
   (htB:t∈ B) (hzC:z∈ C)
   (hC:2≤ C.card) (hD:2≤ D.card)
   (huB:∀ b∈ B,G.Adj u b)
   (hCt:∀ v∈ C,G.Adj v t) (hzD:∀ d∈ D,G.Adj z d)
   (hat:¬ G.Adj a t):readers n K p={g}:=by
 have hut:=huB t htB
 have hzt:=hCt z hzC
 have hA:=N21.q10 h4 hu hzA ha huz hut hzt hat
 apply N10.q27 hAO hTF hcompute c hp hgN hJ hroot hlive
 · intro v
   obtain ⟨x,hAx,hxv,hneg⟩:=q4 hA v
   exact ⟨x,by rw [hAp];exact hAx,hxv,hneg⟩
 · refine ⟨pairInput a t,?_,?_,?_⟩
   · rw [hAp]
     exact (setOr_pair A a t).mpr (Or.inl ha)
   · rw [hABg]
     simp only [setProduct,Z12,setOr_pair]
     exact ⟨Or.inl ha,Or.inr htB⟩
   · apply Z14.mpr
     intro hf
     exact hat ((q79 a t).mp hf)
 · obtain ⟨x,hAx,hCDx,hneg⟩:=
     N21.q23 s hbip h4 hu huz hut hzt hC hD hCt hzD
   exact ⟨x,by rw [hAp];exact hAx,by rw [hCDh];exact hCDx,hneg⟩
 · refine ⟨u,?_⟩
   intro x hBx hxu
   apply (q127 u).mpr (fun b hb=> (huB b hb).symm) x _ hxu
   rw [← hBoperand]
   exact hBx
 · intro b
   by_cases hb:b=d
   · subst b
     refine ⟨t,?_⟩
     intro x hCx hxt
     apply (q127 t).mpr hCt x _ hxt
     rw [← hCoperand]
     exact hCx
   · have he:b=1 - d:=by fin_cases b <;> fin_cases d <;> simp_all
     rw [he]
     refine ⟨z,?_⟩
     intro x hDx hxz
     apply (q127 z).mpr (fun d hd=> (hzD d hd).symm) x _ hxz
     rw [← hDoperand]
     exact hDx
end N23
namespace N14
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open N10 N27
lemma q48 {n:ℕ} {C:Circuit} {p:ℕ} {r:Gate}
   (hraw:∀ w∈ r.inputs,w < n) {i j:ℕ}:
   InCone n (patch C p r) i j→ InCone n C i j:=by
 induction j using Nat.strong_induction_on with
 | ind j ih=>
   intro hc
   obtain ⟨hj',k,hkj,hkin,hik⟩:=(inCone_iff n (patch C p r) i j).mp hc
   have hj:j < C.gates.length:=by simpa [q162] using hj'
   by_cases hjp:j=p
   · subst j
     rw [q95 hj] at hkin
     have:=hraw (n+k) hkin
     omega
   · rw [q96 C p j r (Ne.symm hjp)] at hkin
     apply (inCone_iff n C i j).mpr
     refine ⟨hj,k,hkj,hkin,?_⟩
     rcases hik with e | h
     · exact Or.inl e
     · exact Or.inr (ih k hkj h)
lemma q56 {n:ℕ} (C:Circuit) (p:ℕ) (u z:Fin n) {i j:ℕ}
   (h:InCone n (patch C p (rawOr u z)) i j):InCone n C i j:=by
 apply q48 _ h
 intro w hw
 simp only [rawOr,Z10,Z11,or_false] at hw
 rcases hw with rfl | rfl <;> omega
lemma q165 {n:ℕ} {C:Circuit} {p:ℕ} (u z:Fin n)
   (hpOR:(gateAt C p).op=GateOp.or) (k:ℕ) (hk:k < C.gates.length):
   (gateAt (patch C p (rawOr u z)) k).op=(gateAt C k).op:=by
 by_cases hkp:k=p
 · subst k
   rw [q95 hk]
   exact hpOR.symm
 · rw [q96 C p k (rawOr u z) (Ne.symm hkp)]
lemma q67 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
   {C D:Circuit} (hlen:D.gates.length=C.gates.length)
   (hop:∀ k,k < C.gates.length→ (gateAt D k).op=(gateAt C k).op)
   (hunder:∀ (x:Fin n→ Bool) w,W n D x w=true→ W n C x w=true):
   junk G D⊆ junk G C:=by
 intro k hk
 obtain ⟨hkr,hka,hkD,x,hx,hFx⟩:=Z0.mp hk
 have hkC:k < C.gates.length:=by omega
 refine Z0.mpr ⟨Z9.mpr hkC,?_,hkC,x,?_,hFx⟩
 · rw [← hop k hkC]
   exact hka
 · exact hunder x (n+k) hx
lemma q66 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
   {C D:Circuit} {g h:ℕ}
   (hsub:junk G D⊆ junk G C)
   (hjunk:∀ k,k∈ junk G C↔ k=g∨ k=h)
   (hgnew:IsDirtyAnd n G D g) (hhnew:IsDirtyAnd n G D h):
   junk G D=junk G C:=by
 apply Finset.Subset.antisymm hsub
 intro k hk
 rcases (hjunk k).mp hk with rfl | rfl
 · exact Z0.mpr ⟨Z9.mpr hgnew.2.1,hgnew⟩
 · exact Z0.mpr ⟨Z9.mpr hhnew.2.1,hhnew⟩
lemma q61 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
   {C D:Circuit} (hlen:D.gates.length=C.gates.length)
   (hop:∀ i,i < C.gates.length→ (gateAt D i).op=(gateAt C i).op)
   (hcone:∀ i j,InCone n D i j→ InCone n C i j)
   (hjunk:junk G C⊆ junk G D) (hT:TopForm G C):TopForm G D:=by
 intro i hi j hj hiand hib hjand hc
 have hiC:i < C.gates.length:=by omega
 have hjC:j < C.gates.length:=by omega
 have hiop:(gateAt C i).op=GateOp.and:=(hop i hiC).symm.trans hiand
 have hjop:(gateAt C j).op=GateOp.and:=(hop j hjC).symm.trans hjand
 have hibC:BelowF G C i:=by
   intro x hx
   by_contra hf
   have hm:i∈ junk G C:=by
     exact Z0.mpr ⟨Z9.mpr hiC,hiop,hiC,x,hx,
       Z14.mpr hf⟩
   obtain ⟨_,_,_,y,hy,hyF⟩:=Z0.mp (hjunk hm)
   have:=hib y hy
   rw [hyF] at this
   cases this
 exact hT i hiC j hjC hiop hibC hjop (hcone i j hc)
lemma q106 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
   {C:Circuit} (hL:IsLeastAO G C) (p:ℕ) (u z:Fin n)
   (hF:circuitFun n (patch C p (rawOr u z))=graphFun G ∅):
   IsLeastAO G (patch C p (rawOr u z)):=by
 refine ⟨q107 hL.1 p u z,hF,?_⟩
 intro D hD hDF
 rw [patch_size]
 exact hL.2.2 D hD hDF
lemma q43 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
   {C:Circuit} {p g h:ℕ} (u z:Fin n)
   (hL:IsLeastAO G C) (hT:TopForm G C)
   (hjunk:∀ k,k∈ junk G C↔ k=g∨ k=h)
   (hpOR:(gateAt C p).op=GateOp.or)
   (hF:circuitFun n (patch C p (rawOr u z))=graphFun G ∅)
   (hunder:∀ (x:Fin n→ Bool) w,
     W n (patch C p (rawOr u z)) x w=true→ W n C x w=true)
   (hgnew:IsDirtyAnd n G (patch C p (rawOr u z)) g)
   (hhnew:IsDirtyAnd n G (patch C p (rawOr u z)) h):
   IsLeastAO G (patch C p (rawOr u z))∧
     TopForm G (patch C p (rawOr u z))∧
     junk G (patch C p (rawOr u z))=junk G C:=by
 have hlen:=q162 C p (rawOr u z)
 have hop:=q165 u z hpOR
 have hsub:=q67 (G:=G) hlen hop hunder
 have heq:=q66 hsub hjunk hgnew hhnew
 refine ⟨q106 hL p u z hF,?_,heq⟩
 apply q61 hlen hop
   (fun i j hc=> q56 C p u z hc) _ hT
 rw [heq]
end N14
namespace N11
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
 PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
 PEqualNP.CleanedNonEdge PEqualNP.TopForm
open N10
lemma q74 {n:ℕ} (u z:Fin n) (x:Fin n→ Bool):
   setOr {u,z} x=(x u || x z):=by
 rw [Bool.eq_iff_iff]
 simp [setOr]
lemma q25 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] {K:Circuit} (s:Fin n→ Bool)
   (hbip:∀ u v,G.Adj u v→ s u≠ s v) (h4:NoFourCycle G)
   (hL:IsLeastAO G K) (hTF:TopForm G K)
   {g h p:ℕ} (c d:Fin 2) (hgh:g≠ h)
   (hJ:∀ k,k∈ junk G K↔ k=g∨ k=h)
   (hgnoth:¬ InCone n K g h) (hhnog:¬ InCone n K h g)
   (hroot:opnd K g c=n+p)
   (hlive:∀ i < K.gates.length,
     K.output=n+i∨ ∃ j < K.gates.length,n+i∈ (gateAt K j).inputs)
   {A B C D:Finset (Fin n)} {u z t a:Fin n}
   (hAp:∀ x,gateVal n K p x=setOr A x)
   (hABg:∀ x,gateVal n K g x=setProduct A B x)
   (hCDh:∀ x,gateVal n K h x=setProduct C D x)
   (hBoperand:∀ x,W n K x (opnd K g (1 - c))=setOr B x)
   (hCoperand:∀ x,W n K x (opnd K h d)=setOr C x)
   (hDoperand:∀ x,W n K x (opnd K h (1 - d))=setOr D x)
   (hu:u∈ A) (hzA:z∈ A) (ha:a∈ A) (huz:u≠ z)
   (htB:t∈ B) (hzC:z∈ C)
   (hB:2≤ B.card) (hC:2≤ C.card) (hD:2≤ D.card)
   (huB:∀ b∈ B,G.Adj u b)
   (hCt:∀ v∈ C,G.Adj v t) (hzD:∀ d∈ D,G.Adj z d)
   (hat:¬ G.Adj a t)
   (hAs:∀ v∈ A,s v=false) (hBs:∀ v∈ B,s v=true)
   (hCs:∀ v∈ C,s v=false) (hDs:∀ v∈ D,s v=true):
   let K':=N27.patch K p (N27.rawOr u z)
   IsAO2 n K'∧ circuitFun n K'=graphFun G ∅∧
   (∀ x,gateVal n K' g x=setProduct {u,z} B x)∧
   (∀ x,gateVal n K' h x=setProduct C D x)∧
   (∀ x w,W n K' x w=true→ W n K x w=true)∧
   (gateAt K p).op=GateOp.or:=by
 dsimp only
 have hgJ:=(hJ g).mpr (Or.inl rfl)
 have hhJ:=(hJ h).mpr (Or.inr rfl)
 obtain ⟨hgR,hgop,hgN,hgdirty⟩:=Z0.mp hgJ
 obtain ⟨hhR,hhop,hhN,hhdirty⟩:=Z0.mp hhJ
 have hAO:=hL.1
 have hrootmem:n+p∈ (gateAt K g).inputs:=by
   rw [← hroot,q116 hAO hgN]
   fin_cases c <;> simp
 have hpg:p < g:=by
   have:=hAO.2.1 g hgN (n+p) hrootmem
   omega
 have hpN:p < K.gates.length:=by omega
 have hpneh:p≠ h:=by
   intro heq
   apply hhnog
   apply (inCone_iff n K h g).mpr
   refine ⟨hgN,p,hpg,hrootmem,?_⟩
   exact Or.inl heq.symm
 have hut:=huB t htB
 have hzt:=hCt z hzC
 have hA:=N21.q10 h4 hu hzA ha huz hut hzt hat
 have hrootdirty:∃ x,gateVal n K p x=true∧ graphFun G ∅ x=false:=by
   refine ⟨pairInput u u,?_,?_⟩
   · rw [hAp]
     exact (setOr_pair A u u).mpr (Or.inl hu)
   · apply Z14.mpr
     intro hf
     exact G.loopless.irrefl u ((q79 u u).mp hf)
 have hpOR:(gateAt K p).op=GateOp.or:=by
   rcases hAO.1 _ (gateAt_mem' K p hpN) with hpAND | hpOR
   · have hpJ:p∈ junk G K:=
       Z0.mpr ⟨Z9.mpr hpN,hpAND,hpN,hrootdirty⟩
     rcases (hJ p).mp hpJ with heq | heq
     · omega
     · exact False.elim (hpneh heq)
   · exact hpOR
 have houtne:K.output≠ n+p:=by
   intro hout
   obtain ⟨x,hpx,hneg⟩:=hrootdirty
   have hv:circuitFun n K x=true:=by
     change W n K x K.output=true
     rw [hout]
     exact hpx
   rw [hL.2.1,hneg] at hv
   exact Bool.false_ne_true hv
 have hsole:=N23.q41 s hbip h4 hAO hTF hL.2.1
   c d hpN hgN (fun k hk=> (hJ k).mp hk) hroot hlive hAp hABg hCDh
   hBoperand hCoperand hDoperand hu hzA ha huz htB hzC hC hD huB hCt hzD hat
 have hread:=N27.q69 hsole
 have hAO':=N27.q107 hAO p u z
 have hotherne:opnd K g (1 - c)≠ n+p:=by
   intro heq
   apply q15 hA ⟨u,fun b hb=> (huB b hb).symm⟩
   intro x hAx
   have hBx:=hBoperand x
   rw [heq] at hBx
   have hpx:W n K x (n+p)=true:=by
     change gateVal n K p x=true
     rw [hAp]
     exact hAx
   exact hBx ▸ hpx
 have hins:(gateAt K g).inputs=[n+p,opnd K g (1 - c)]∨
     (gateAt K g).inputs=[opnd K g (1 - c),n+p]:=by
   have hlist:=q116 hAO hgN
   fin_cases c
   · left
     change (gateAt K g).inputs=[n+p,opnd K g 1]
     change opnd K g 0=n+p at hroot
     rw [← hroot]
     exact hlist
   · right
     change (gateAt K g).inputs=[opnd K g 0,n+p]
     change opnd K g 1=n+p at hroot
     rw [← hroot]
     exact hlist
 let U:=N27.restored n K p (N27.rawOr u z)
 have hUg:∀ x,U x (n+g)=setProduct {u,z} B x:=by
   intro x
   have hv:=N27.q76 hAO hpN hgN hread hgop hins hotherne u z x
   change U x (n+g)=_ at hv
   rw [hBoperand,← q74 u z x] at hv
   exact hv
 have hUh:∀ x,U x (n+h)=gateVal n K h x:=by
   intro x
   exact N27.q33 hAO hAO' hread x hhN hpneh.symm hgh.symm hgnoth
 have hrootUnder:∀ x,
     W n (N27.patch K p (N27.rawOr u z)) x (n+p)=true→
     W n K x (n+p)=true:=by
   intro x hx
   rw [N27.q83 hAO hpN,Z13] at hx
   change gateVal n K p x=true
   rw [hAp]
   simp only [setOr,Z1]
   rcases hx with hxu | hxz
   · exact ⟨u,hu,hxu⟩
   · exact ⟨z,hzA,hxz⟩
 have hUnder:∀ x w,
     W n (N27.patch K p (N27.rawOr u z)) x w=true→ W n K x w=true:=by
   intro x w hx
   exact N27.patch_under hAO hAO' x (hrootUnder x) w hx
 have hBD:∀ b∈ B,∀ d∈ D,¬ G.Adj b d:=by
   intro b hb d hd hadj
   exact hbip b d hadj ((hBs b hb).trans (hDs d hd).symm)
 have hUout:∀ x,U x K.output=graphFun G ∅ x:=by
   apply N7.q37 hAO hTF hL.2.1
     (fun k hk=> (hJ k).mp hk) hgop hgdirty U
   · intro x v
     exact N27.q129 K p (N27.rawOr u z) x v
   · intro x k hk hkg
     exact N27.q91 hAO hAO' hread x hk hkg
   · intro x hhx
     rw [hUh]
     exact hhx
   · intro v w _ q hfilter hgx hxq
     rw [hUg]
     apply N25.q5 s h4 hA hB huB hAs hBs
     · intro y hy hyq
       apply hfilter y
       · rw [hABg]
         exact hy
       · exact hyq
     · rw [← hABg]
       exact hgx
     · exact hxq
   · intro v w _ hclean hgx hhx
     rw [hUg]
     apply N25.q7 s h4 hB hD huB hzD hBD hAs hBs hCs hDs
     · intro y hgy hhy
       apply hclean y
       · rw [hABg]
         exact hgy
       · rw [hCDh]
         exact hhy
     · rw [← hABg]
       exact hgx
     · rw [← hCDh]
       exact hhx
   · intro x y hxy hx
     exact N27.q77 hAO hAO' x y hxy K.output hx
   · intro x hx
     have hv:=N27.q130 hAO hAO' x (hrootUnder x) K.output hx
     change circuitFun n K x=true at hv
     rw [hL.2.1] at hv
     exact hv
 refine ⟨hAO',?_,?_,?_,hUnder,hpOR⟩
 · funext x
   change W n (N27.patch K p (N27.rawOr u z)) x K.output=graphFun G ∅ x
   rw [← N27.q84 K p (N27.rawOr u z) x houtne]
   exact hUout x
 · intro x
   have hv:=hUg x
   dsimp only [U] at hv
   rw [N27.q84 K p (N27.rawOr u z) x (by omega)] at hv
   exact hv
 · intro x
   have hv:=hUh x
   dsimp only [U] at hv
   rw [N27.q84 K p (N27.rawOr u z) x (by omega),hCDh] at hv
   exact hv
def CrossStar {n:ℕ} (G:SimpleGraph (Fin n)) (K:Circuit) (k:ℕ):Prop:=
 ∃ (A B:Finset (Fin n)) (u v:Fin n),
   G.Adj u v∧ u∈ A∧ v∈ B∧
   (∀ a∈ A,G.Adj a v)∧ (∀ b∈ B,G.Adj b u)∧
   2≤ A.card∧ 2≤ B.card∧
   ∀ x,gateVal n K k x=setProduct A B x
lemma q55 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] {K:Circuit} (s:Fin n→ Bool)
   (hbip:∀ u v,G.Adj u v→ s u≠ s v) (h4:NoFourCycle G)
   (hL:IsLeastAO G K) (hTF:TopForm G K)
   {g h p:ℕ} (c d:Fin 2) (hgh:g≠ h)
   (hJ:∀ k,k∈ junk G K↔ k=g∨ k=h)
   (hgnoth:¬ InCone n K g h) (hhnog:¬ InCone n K h g)
   (hroot:opnd K g c=n+p)
   (hlive:∀ i < K.gates.length,
     K.output=n+i∨ ∃ j < K.gates.length,n+i∈ (gateAt K j).inputs)
   {A B C D:Finset (Fin n)} {u z t a:Fin n}
   (hAp:∀ x,gateVal n K p x=setOr A x)
   (hABg:∀ x,gateVal n K g x=setProduct A B x)
   (hCDh:∀ x,gateVal n K h x=setProduct C D x)
   (hBoperand:∀ x,W n K x (opnd K g (1 - c))=setOr B x)
   (hCoperand:∀ x,W n K x (opnd K h d)=setOr C x)
   (hDoperand:∀ x,W n K x (opnd K h (1 - d))=setOr D x)
   (hu:u∈ A) (hzA:z∈ A) (ha:a∈ A) (huz:u≠ z)
   (htB:t∈ B) (hzC:z∈ C) (htD:t∈ D)
   (hB:2≤ B.card) (hC:2≤ C.card) (hD:2≤ D.card)
   (huB:∀ b∈ B,G.Adj u b)
   (hCt:∀ v∈ C,G.Adj v t) (hzD:∀ d∈ D,G.Adj z d)
   (hat:¬ G.Adj a t)
   (hAs:∀ v∈ A,s v=false) (hBs:∀ v∈ B,s v=true)
   (hCs:∀ v∈ C,s v=false) (hDs:∀ v∈ D,s v=true):
   let K':=N27.patch K p (N27.rawOr u z)
   IsLeastAO G K'∧ TopForm G K'∧ K'.size=K.size∧
   (∀ k,k∈ junk G K'↔ k=g∨ k=h)∧ CrossStar G K' g∧ CrossStar G K' h:=by
 dsimp only
 obtain ⟨hAO',hF',hSemg,hSemh,hUnder,hpOR⟩:=
   q25 s hbip h4 hL hTF c d hgh hJ hgnoth hhnog hroot hlive
     hAp hABg hCDh hBoperand hCoperand hDoperand hu hzA ha huz htB hzC hB hC hD
     huB hCt hzD hat hAs hBs hCs hDs
 have hgJ:=(hJ g).mpr (Or.inl rfl)
 have hhJ:=(hJ h).mpr (Or.inr rfl)
 obtain ⟨hgR,hgop,hgN,hgdirty⟩:=Z0.mp hgJ
 obtain ⟨hhR,hhop,hhN,hhdirty⟩:=Z0.mp hhJ
 have hgnew:IsDirtyAnd n G (N27.patch K p (N27.rawOr u z)) g:=by
   refine ⟨(N14.q165 u z hpOR g hgN).trans hgop,?_,?_⟩
   · simpa only [N27.q162] using hgN
   · obtain ⟨x,hprod,hneg⟩:=
       N21.q28 h4 huz (huB t htB) (hCt z hzC) hB huB
     exact ⟨x,by rw [hSemg];exact hprod,hneg⟩
 have hhnew:IsDirtyAnd n G (N27.patch K p (N27.rawOr u z)) h:=by
   refine ⟨(N14.q165 u z hpOR h hhN).trans hhop,?_,?_⟩
   · simpa only [N27.q162] using hhN
   · obtain ⟨x,hhx,hneg⟩:=hhdirty
     refine ⟨x,?_,hneg⟩
     rw [hSemh,← hCDh]
     exact hhx
 obtain ⟨hL',hTF',hJ'⟩:=
   N14.q43 u z hL hTF hJ hpOR hF' hUnder hgnew hhnew
 refine ⟨hL',hTF',N27.patch_size K p (N27.rawOr u z),?_,?_,?_⟩
 · intro k
   rw [hJ']
   exact hJ k
 · refine ⟨{u,z},B,u,t,huB t htB,by simp,htB,?_,?_,?_,hB,hSemg⟩
   · intro v hv
     simp only [Z6,Z3] at hv
     rcases hv with rfl | rfl
     · exact huB t htB
     · exact hCt _ hzC
   · intro b hb
     exact (huB b hb).symm
   · simp [Finset.card_pair huz]
 · exact ⟨C,D,z,t,hCt z hzC,hzC,htD,hCt,
     fun d hd=> (hzD d hd).symm,hC,hD,hSemh⟩
end N11
namespace N13
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo
lemma q51 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
   {C:Circuit} (hAO:IsAO2 n C) (hF:circuitFun n C=graphFun G ∅)
   (hT:TopForm G C):IsLiftFixedPoint G C:=by
 apply @N17.q51
 all_goals assumption
end N13
namespace N12
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
 PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
 PEqualNP.CleanedNonEdge PEqualNP.TopForm
open N10
lemma q46 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] {K:Circuit} (s:Fin n→ Bool)
   (hbip:∀ u v,G.Adj u v→ s u≠ s v) (h4:NoFourCycle G)
   (hL:IsLeastAO G K) (hTF:TopForm G K)
   {g h p:ℕ} (c d:Fin 2) (hgh:g≠ h)
   (hJ:∀ k,k∈ junk G K↔ k=g∨ k=h)
   (hgnoth:¬ InCone n K g h) (hhnog:¬ InCone n K h g)
   (hroot:opnd K g c=n+p)
   {A B C D:Finset (Fin n)} {u z t a:Fin n}
   (hAp:∀ x,gateVal n K p x=setOr A x)
   (hABg:∀ x,gateVal n K g x=setProduct A B x)
   (hCDh:∀ x,gateVal n K h x=setProduct C D x)
   (hBoperand:∀ x,W n K x (opnd K g (1 - c))=setOr B x)
   (hCoperand:∀ x,W n K x (opnd K h d)=setOr C x)
   (hDoperand:∀ x,W n K x (opnd K h (1 - d))=setOr D x)
   (hu:u∈ A) (hzA:z∈ A) (ha:a∈ A) (huz:u≠ z)
   (htB:t∈ B) (hzC:z∈ C) (htD:t∈ D)
   (hB:2≤ B.card) (hC:2≤ C.card) (hD:2≤ D.card)
   (huB:∀ b∈ B,G.Adj u b)
   (hCt:∀ v∈ C,G.Adj v t) (hzD:∀ d∈ D,G.Adj z d)
   (hat:¬ G.Adj a t)
   (hAs:∀ v∈ A,s v=false) (hBs:∀ v∈ B,s v=true)
   (hCs:∀ v∈ C,s v=false) (hDs:∀ v∈ D,s v=true):False:=by
 have hlive:∀ i < K.gates.length,
     K.output=n+i∨ ∃ j < K.gates.length,n+i∈ (gateAt K j).inputs:=by
   intro i hi
   have hc:=N5.z088 hL ⟨u,t,huB t htB⟩ i hi
   rcases hc.2 with hout | ⟨_,hcone⟩
   · exact Or.inl hout
   · exact Or.inr (N5.z038 hcone)
 obtain ⟨hL',hTF',_,hJ',hFg,hFh⟩:=
   N11.q55 s hbip h4 hL hTF c d hgh hJ hgnoth hhnog hroot hlive
     hAp hABg hCDh hBoperand hCoperand hDoperand hu hzA ha huz htB hzC htD hB hC hD
     huB hCt hzD hat hAs hBs hCs hDs
 have hLift:=N13.q51 hL'.1 hL'.2.1 hTF'
 apply N5 n G (N27.patch K p (N27.rawOr u z))
   s hbip h4 hL' hLift
 refine ⟨g,h,hgh,hJ',?_,?_⟩
 · simpa only [N11.CrossStar,setProduct,setOr] using hFg
 · simpa only [N11.CrossStar,setProduct,setOr] using hFh
end N12
namespace N8
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
def Safe {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
   (A B:Finset (Fin n)) (w:Fin n):Prop:=
 ∀ x:Fin n→ Bool,setProduct A B x=true→ x w=true→ graphFun G ∅ x=true
lemma q19 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] (h4:NoFourCycle G) {A B C D:Finset (Fin n)}
   (hC:2≤ C.card) (hD:2≤ D.card) {z t:Fin n}
   (hzD:∀ d∈ D,G.Adj z d) (hCt:∀ c∈ C,G.Adj c t)
   (hAC:∀ a∈ A,∀ c∈ C,¬ G.Adj a c)
   (hBD:∀ b∈ B,∀ d∈ D,¬ G.Adj b d)
   (hclean:∀ x:Fin n→ Bool,
     setProduct A B x=true→ setProduct C D x=true→ graphFun G ∅ x=true)
   {u v:Fin n} (hu:u∈ A ∩ C) (hv:v∈ B ∩ D):
   Safe G A B u∨ Safe G A B v∨ (u=z∧ v=t):=by
 rcases q30 hBD hclean hu with huB | huD
 · exact Or.inl (N19.q134 huB)
 have hswap:∀ x:Fin n→ Bool,
     setProduct B A x=true→ setProduct D C x=true→ graphFun G ∅ x=true:=by
   intro x hx hy
   exact hclean x (by simpa only [q109 B A] using hx)
     (by simpa only [q109 D C] using hy)
 rcases q30 hAC hswap hv with hvA | hvC
 · exact Or.inr (Or.inl (N19.q112 (fun a ha=> (hvA a ha).symm)))
 · exact Or.inr (Or.inr ⟨N25.q44 h4 hD huD hzD,
     N25.q44 h4 hC hvC (fun c hc=> (hCt c hc).symm)⟩)
lemma q31 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] (s:Fin n→ Bool)
   (hbip:∀ u v,G.Adj u v→ s u≠ s v) (h4:NoFourCycle G)
   {A B C D:Finset (Fin n)}
   (hC:2≤ C.card) (hD:2≤ D.card) {z t:Fin n}
   (hzD:∀ d∈ D,G.Adj z d) (hCt:∀ c∈ C,G.Adj c t)
   (hAs:∀ a∈ A,s a=false) (hBs:∀ b∈ B,s b=true)
   (hCs:∀ c∈ C,s c=false) (hDs:∀ d∈ D,s d=true)
   (hclean:∀ x:Fin n→ Bool,
     setProduct A B x=true→ setProduct C D x=true→ graphFun G ∅ x=true)
   (u v:Fin n) (hg:setProduct A B (pairInput u v)=true)
   (hh:setProduct C D (pairInput u v)=true):
   Safe G A B u∨ Safe G A B v∨
     (pairInput u v z=true∧ pairInput u v t=true):=by
 have hAC:∀ a∈ A,∀ c∈ C,¬ G.Adj a c:=by
   intro a ha c hc
   exact q29 s hbip ((hAs a ha).trans (hCs c hc).symm)
 have hBD:∀ b∈ B,∀ d∈ D,¬ G.Adj b d:=by
   intro b hb d hd
   exact q29 s hbip ((hBs b hb).trans (hDs d hd).symm)
 rcases (q81 s hAs hBs hCs hDs u v).mp ⟨hg,hh⟩ with ⟨hu,hv⟩ | ⟨hv,hu⟩
 · rcases q19 h4 hC hD hzD hCt hAC hBD hclean hu hv with
     h | h | ⟨huz,hvt⟩
   · exact Or.inl h
   · exact Or.inr (Or.inl h)
   · exact Or.inr (Or.inr (by simp [pairInput,huz,hvt]))
 · rcases q19 h4 hC hD hzD hCt hAC hBD hclean hv hu with
     h | h | ⟨hvz,hut⟩
   · exact Or.inr (Or.inl h)
   · exact Or.inl h
   · exact Or.inr (Or.inr (by simp [pairInput,hvz,hut]))
end N8
namespace LargePureCase
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
 PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
 PEqualNP.CleanedNonEdge PEqualNP.TopForm
open N10
lemma q144 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
   {K:Circuit} (hAO:IsAO2 n K) (hT:TopForm G K) {g h:ℕ}
   (hJ:junk G K={g,h}) (hgh:¬ InCone n K g h) (hhg:¬ InCone n K h g)
   {j:ℕ} (hj:j=g∨ j=h) (c:Fin 2) (x:Fin n→ Bool):
   W n K x (opnd K j c)=setOr (side (n:=n) K j c) x:=by
 apply @N26.q70 (G:=G)
 all_goals assumption
lemma q148 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
   {K:Circuit} (hAO:IsAO2 n K) (hT:TopForm G K) {g h:ℕ}
   (hJ:junk G K={g,h}) (hgh:¬ InCone n K g h) (hhg:¬ InCone n K h g)
   {j:ℕ} (hj:j=g∨ j=h) (c:Fin 2) (x:Fin n→ Bool):
   gateVal n K j x=setProduct (side (n:=n) K j c) (side (n:=n) K j (1-c)) x:=by
 have hv:=N26.q71 G K hAO hT g h hJ hgh hhg j hj x
 fin_cases c
 · exact hv
 · change gateVal n K j x=setProduct (side K j 1) (side K j 0) x
   rw [q109]
   exact hv
lemma q39 {n:ℕ} {K:Circuit} {j:ℕ} (c:Fin 2)
   {A:Finset (Fin n)} (hA:2≤ A.card)
   (hval:∀ x,W n K x (opnd K j c)=setOr A x):
   ∃ p,opnd K j c=n+p∧ ∀ x,gateVal n K p x=setOr A x:=by
 have hn:n≤ opnd K j c:=by
   by_contra hh
   have hi:opnd K j c < n:=by omega
   let v:Fin n:=⟨opnd K j c,hi⟩
   have hsub:A⊆ {v}:=by
     intro a ha
     have haV:setOr A (pairInput a a)=true:=(setOr_pair A a a).mpr (Or.inl ha)
     rw [← hval,W_input n K (pairInput a a) v.val v.isLt] at haV
     simpa [pairInput,v,eq_comm] using haV
   have hc:=Finset.card_le_card hsub
   simp only [Finset.card_singleton] at hc
   omega
 refine ⟨opnd K j c-n,by omega,?_⟩
 intro x
 change W n K x (n+(opnd K j c-n))=_
 rw [Nat.add_sub_of_le hn]
 exact hval x
lemma q142 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
   {K:Circuit} (hL:IsLeastAO G K)
   (hOne:∀ E:Circuit,IsLeastAO G E→ (junk G E).card≠ 1)
   {g h:ℕ} (hne:g≠ h) (hJ:junk G K={g,h})
   (hgh:¬ InCone n K g h) (c:Fin 2) {A B:Finset (Fin n)} {u:Fin n}
   (hu:u∈ A) (huB:∀ b∈ B,G.Adj u b)
   (hBop:∀ x,W n K x (opnd K g (1-c))=setOr B x)
   (hCover:∀ a b,G.Adj a b→
     circuitFun n (N6.offPatch K g) (pairInput a b)=false→
     setProduct A B (pairInput a b)=true∧ pairInput a b u=true):False:=by
 have hgJ:g∈ junk G K:=by rw [hJ];simp
 have hg:=(N4.mem_junk.mp hgJ).1
 have hop:=N17.opnd_lt hL.1 hg (1-c)
 apply N4.q9 G K hL hOne hne hJ hgh
   ⟨GateOp.and,[u.val,opnd K g (1-c)]⟩ (Or.inl rfl) rfl
 · intro w hw
   simp only [Z10,Z11,or_false] at hw
   rcases hw with rfl | rfl
   · have:=u.isLt;omega
   · exact hop
 · intro x hf
   rw [N9.q151 K g (Nat.le_of_lt hg) u _ hop x]
   change (x u && W n K x (opnd K g (1-c)))=false
   rw [hBop]
   apply Z14.mpr
   intro ht
   have hc:=(N15.clean_left G A B u hu huB).2.1 x
   have hx:N15.product {u} B x=true:=by
     simpa [N15.product,setOr] using ht
   have hh:=hc hx
   rw [hf] at hh
   cases hh
 · intro a b hab hcut
   obtain ⟨hp,hpu⟩:=hCover a b hab hcut
   rw [N9.q151 K g (Nat.le_of_lt hg) u _ hop]
   change (pairInput a b u && W n K (pairInput a b) (opnd K g (1-c)))=true
   rw [hBop,hpu,Bool.true_and]
   have hh:setOr A (pairInput a b)=true∧ setOr B (pairInput a b)=true:=by
     simpa only [setProduct,Z12] using hp
   exact hh.2
lemma q141 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
   {K:Circuit} (hL:IsLeastAO G K)
   (hOne:∀ E:Circuit,IsLeastAO G E→ (junk G E).card≠ 1)
   {g h:ℕ} (hne:g≠ h) (hJ:junk G K={g,h})
   (hgh:¬ InCone n K g h) {z t:Fin n} (hzt:G.Adj z t)
   (hCover:∀ a b,G.Adj a b→
     circuitFun n (N6.offPatch K g) (pairInput a b)=false→
     pairInput a b z=true∧ pairInput a b t=true):False:=by
 apply N4.q9 G K hL hOne hne hJ hgh
   (N4.edgeGate z t) (Or.inl rfl) rfl
 · intro w hw
   simp only [N4.edgeGate,Z10,Z11,or_false] at hw
   rcases hw with rfl | rfl <;> omega
 · intro x hf
   rw [N4.edge_bit]
   apply Z14.mpr
   intro hh
   have hb:x z=true∧ x t=true:=by simpa only [Z12] using hh
   obtain ⟨hz,ht⟩:=hb
   have hv:=(q158 x).mpr ⟨z,t,hzt,hz,ht⟩
   rw [hf] at hv
   cases hv
 · intro a b hab hcut
   rw [N4.edge_bit]
   simpa only [Z12] using hCover a b hab hcut
lemma q35 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] {K:Circuit} (s:Fin n→ Bool)
   (hbip:∀ a b,G.Adj a b→ s a≠ s b) (h4:NoFourCycle G)
   (hAO:IsAO2 n K) (hF:circuitFun n K=graphFun G ∅) (hT:TopForm G K)
   {g h:ℕ} (hne:g≠ h) (hJ:junk G K={g,h}) (hgh:¬ InCone n K g h)
   {A B C D:Finset (Fin n)} {z t:Fin n}
   (hgval:∀ x,gateVal n K g x=setProduct A B x)
   (hhval:∀ x,gateVal n K h x=setProduct C D x)
   (hC:2≤ C.card) (hD:2≤ D.card)
   (hzD:∀ d∈ D,G.Adj z d) (hCt:∀ c∈ C,G.Adj c t)
   (hAs:∀ a∈ A,s a=false) (hBs:∀ b∈ B,s b=true)
   (hCs:∀ a∈ C,s a=false) (hDs:∀ b∈ D,s b=true)
   (a b:Fin n) (hab:G.Adj a b)
   (hcut:circuitFun n (N6.offPatch K g) (pairInput a b)=false):
   setProduct A B (pairInput a b)=true∧
   (N15.Useful G A B a b∨
     (pairInput a b z=true∧ pairInput a b t=true)):=by
 have hJ':junk G K={h,g}:=by rw [hJ,Finset.pair_comm]
 rcases N6.q17 hAO hF hT hJ' (Ne.symm hne) hgh
     a b hab hcut with ⟨hg,hu⟩ | ⟨hg,hh,hclean⟩
 · refine ⟨(hgval _).symm.trans hg,Or.inl ⟨hab,(hgval _).symm.trans hg,?_⟩⟩
   rcases hu with ha | hb
   · exact Or.inl ((N15.wmax_iff G K g A B hgval a).mp ha)
   · exact Or.inr ((N15.wmax_iff G K g A B hgval b).mp hb)
 · have hgp:=(hgval _).symm.trans hg
   have hhp:=(hhval _).symm.trans hh
   have hf:=N8.q31 s hbip h4 hC hD hzD hCt
     hAs hBs hCs hDs (by
       intro x hx hy
       exact hclean x ((hgval x).trans hx) ((hhval x).trans hy)) a b hgp hhp
   refine ⟨hgp,?_⟩
   rcases hf with ha | hb | hc
   · exact Or.inl ⟨hab,hgp,Or.inl ha⟩
   · exact Or.inl ⟨hab,hgp,Or.inr hb⟩
   · exact Or.inr hc
lemma q65 {n:ℕ} (s:Fin n→ Bool)
   {A B:Finset (Fin n)} {z t a b:Fin n}
   (hAs:∀ a∈ A,s a=false) (hBs:∀ b∈ B,s b=true)
   (hzs:s z=false) (hts:s t=true)
   (hg:setProduct A B (pairInput a b)=true)
   (hz:pairInput a b z=true) (ht:pairInput a b t=true):z∈ A∧ t∈ B:=by
 have hzt:z≠ t:=by intro he;rw [he,hts] at hzs;contradiction
 have hpair:pairInput a b=pairInput z t:=by
   simp only [pairInput,Z1] at hz ht
   rcases hz with rfl | rfl <;> rcases ht with rfl | rfl
   · exact (hzt rfl).elim
   · rfl
   · funext v;simp [pairInput,or_comm]
   · exact (hzt rfl).elim
 rw [hpair] at hg
 simp only [setProduct,Z12,setOr_pair] at hg
 rcases hg.1 with hzA | htA
 · rcases hg.2 with hzB | htB
   · have hh:=hBs z hzB;rw [hzs] at hh;contradiction
   · exact ⟨hzA,htB⟩
 · have hh:=hAs t htA;rw [hts] at hh;contradiction
lemma q14 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] {K:Circuit} (s:Fin n→ Bool)
   (hbip:∀ a b,G.Adj a b→ s a≠ s b) (h4:NoFourCycle G)
   (hL:IsLeastAO G K)
   (hOne:∀ E:Circuit,IsLeastAO G E→ (junk G E).card≠ 1)
   (hT:TopForm G K) {g h:ℕ} (hne:g≠ h) (hJ:junk G K={g,h})
   (hgh:¬ InCone n K g h) (hhg:¬ InCone n K h g) (c d:Fin 2)
   {A B C D:Finset (Fin n)} {u z t:Fin n}
   (hAop:∀ x,W n K x (opnd K g c)=setOr A x)
   (hBop:∀ x,W n K x (opnd K g (1-c))=setOr B x)
   (hCop:∀ x,W n K x (opnd K h d)=setOr C x)
   (hDop:∀ x,W n K x (opnd K h (1-d))=setOr D x)
   (hgval:∀ x,gateVal n K g x=setProduct A B x)
   (hhval:∀ x,gateVal n K h x=setProduct C D x)
   (hA:2≤ A.card) (hB:2≤ B.card) (hC:2≤ C.card) (hD:2≤ D.card)
   (hAs:∀ a∈ A,s a=false) (hBs:∀ b∈ B,s b=true)
   (hCs:∀ a∈ C,s a=false) (hDs:∀ b∈ D,s b=true)
   (hu:u∈ A) (huB:∀ b∈ B,G.Adj u b)
   (hz:z∈ C) (ht:t∈ D)
   (hzD:∀ d∈ D,G.Adj z d) (hCt:∀ c∈ C,G.Adj c t)
   (hnot:¬ N19.CrossStar G A B)
   (hUse:∀ a b,N15.Useful G A B a b→ pairInput a b u=true):False:=by
 by_cases hard:z∈ A∧ t∈ B∧ u≠ z
 · obtain ⟨p,hroot,hpval⟩:=q39 c hA hAop
   obtain ⟨a,ha,hat⟩:∃ a∈ A,¬ G.Adj a t:=by
     by_contra hh
     apply hnot
     exact ⟨u,hu,t,hard.2.1,by simpa using hh,huB⟩
   have hJiff:∀ k,k∈ junk G K↔ k=g∨ k=h:=by intro k;simp [hJ]
   exact N12.q46 s hbip h4 hL hT c d hne hJiff
     hgh hhg hroot hpval hgval hhval hBop hCop hDop hu hard.1 ha hard.2.2 hard.2.1
     hz ht hB hC hD huB hCt hzD hat hAs hBs hCs hDs
 · apply q142 hL hOne hne hJ hgh c hu huB hBop
   intro a b hab hcut
   obtain ⟨hg,hcase⟩:=q35 s hbip h4 hL.1 hL.2.1 hT hne hJ hgh
     hgval hhval hC hD hzD hCt hAs hBs hCs hDs a b hab hcut
   refine ⟨hg,?_⟩
   rcases hcase with hf | ⟨haz,hat⟩
   · exact hUse a b hf
   · have hmem:=q65 s hAs hBs (hCs z hz) (hDs t ht) hg haz hat
     have he:u=z:=by by_contra hn;exact hard ⟨hmem.1,hmem.2,hn⟩
     rwa [he]
lemma q113 {n:ℕ} {G:SimpleGraph (Fin n)} {A B:Finset (Fin n)}:
   N19.CrossStar G A B↔ N19.CrossStar G B A:=by
 constructor
 · rintro ⟨u,hu,v,hv,hA,hB⟩
   exact ⟨v,hv,u,hu,(fun b hb=> (hB b hb).symm),(fun a ha=> (hA a ha).symm)⟩
 · rintro ⟨u,hu,v,hv,hB,hA⟩
   exact ⟨v,hv,u,hu,(fun a ha=> (hA a ha).symm),(fun b hb=> (hB b hb).symm)⟩
lemma q73 {n:ℕ} {G:SimpleGraph (Fin n)}
   [DecidableRel G.Adj] {K:Circuit} (s:Fin n→ Bool)
   (hbip:∀ a b,G.Adj a b→ s a≠ s b) (h4:NoFourCycle G)
   (hL:IsLeastAO G K)
   (hOne:∀ E:Circuit,IsLeastAO G E→ (junk G E).card≠ 1)
   (hT:TopForm G K) {g h:ℕ} (hne:g≠ h) (hJ:junk G K={g,h})
   (hgh:¬ InCone n K g h) (hhg:¬ InCone n K h g) (c d:Fin 2)
   {A B C D:Finset (Fin n)}
   (hAop:∀ x,W n K x (opnd K g c)=setOr A x)
   (hBop:∀ x,W n K x (opnd K g (1-c))=setOr B x)
   (hCop:∀ x,W n K x (opnd K h d)=setOr C x)
   (hDop:∀ x,W n K x (opnd K h (1-d))=setOr D x)
   (hgval:∀ x,gateVal n K g x=setProduct A B x)
   (hhval:∀ x,gateVal n K h x=setProduct C D x)
   (hA:2≤ A.card) (hB:2≤ B.card) (hC:2≤ C.card) (hD:2≤ D.card)
   (hAs:∀ a∈ A,s a=false) (hBs:∀ b∈ B,s b=true)
   (hCs:∀ a∈ C,s a=false) (hDs:∀ b∈ D,s b=true)
   (hnot:¬ N19.CrossStar G A B) (hflag:N19.CrossStar G C D):False:=by
 obtain ⟨z,hz,t,ht,hCt,hzD⟩:=hflag
 have hdis:Disjoint A B:=by
   apply Finset.disjoint_left.mpr
   intro a ha hb
   have hh:=hBs a hb
   rw [hAs a ha] at hh
   contradiction
 rcases N15.q135 G A B h4 hdis hA hB with
     hf | ⟨u,hu,huB,hUse⟩ | ⟨u,hu,huA,hUse⟩ | hNone
 · obtain ⟨u,hu,v,hv,_,hAv,huB⟩:=hf
   exact hnot ⟨u,hu,v,hv,hAv,huB⟩
 · exact q14 s hbip h4 hL hOne hT hne hJ hgh hhg c d
     hAop hBop hCop hDop hgval hhval hA hB hC hD hAs hBs hCs hDs
     hu huB hz ht hzD hCt hnot hUse
 · have hcc:1-(1-c)=c:=by fin_cases c <;> rfl
   have hdd:1-(1-d)=d:=by fin_cases d <;> rfl
   apply q14 (fun v=> !(s v)) ?_ h4 hL hOne hT hne hJ hgh hhg
     (1-c) (1-d) hBop (by simpa only [hcc] using hAop)
     hDop (by simpa only [hdd] using hCop)
     (by intro x;rw [q109];exact hgval x)
     (by intro x;rw [q109];exact hhval x)
     hB hA hD hC
     (by intro v hv;simp [hBs v hv]) (by intro v hv;simp [hAs v hv])
     (by intro v hv;simp [hDs v hv]) (by intro v hv;simp [hCs v hv])
     hu (fun a ha=> (huA a ha).symm) ht hz
     (fun a ha=> (hCt a ha).symm) (fun b hb=> (hzD b hb).symm)
     (fun hf=> hnot (q113.mpr hf)) ?_
   · intro a b hab hh
     apply hbip a b hab
     simpa using congrArg Bool.not hh
   · intro a b hh
     apply hUse a b
     simpa only [N15.Useful,N15.Safe,
       N15.product,Bool.and_comm] using hh
 · apply q141 hL hOne hne hJ hgh (hzD t ht)
   intro a b hab hcut
   obtain ⟨_,hc⟩:=q35 s hbip h4 hL.1 hL.2.1 hT hne hJ hgh
     hgval hhval hC hD hzD hCt hAs hBs hCs hDs a b hab hcut
   exact hc.resolve_left (hNone a b)
lemma q49 {n:ℕ} (G:SimpleGraph (Fin n))
   [DecidableRel G.Adj] (K:Circuit) (s:Fin n→ Bool)
   (hbip:∀ a b,G.Adj a b→ s a≠ s b) (h4:NoFourCycle G)
   (hL:IsLeastAO G K)
   (hOne:∀ E:Circuit,IsLeastAO G E→ (junk G E).card≠ 1)
   (hT:TopForm G K) {g h:ℕ} (hne:g≠ h) (hJ:junk G K={g,h})
   (hgh:¬ InCone n K g h) (hhg:¬ InCone n K h g)
   (hpure:∀ j∈ junk G K,∃ b:Fin 2,
     (∀ a∈ side (n:=n) K j b,s a=false)∧
     (∀ a∈ side (n:=n) K j (1-b),s a=true))
   (hlarge:∀ j∈ junk G K,∀ b:Fin 2,2≤ (side (n:=n) K j b).card)
   (hnot:¬ N19.CrossStar G (side (n:=n) K g 0) (side (n:=n) K g 1))
   (hflag:N19.CrossStar G (side (n:=n) K h 0) (side (n:=n) K h 1)):False:=by
 have hgJ:g∈ junk G K:=by rw [hJ];simp
 have hhJ:h∈ junk G K:=by rw [hJ];simp
 obtain ⟨c,hAs,hBs⟩:=hpure g hgJ
 obtain ⟨d,hCs,hDs⟩:=hpure h hhJ
 have hn:¬ N19.CrossStar G (side (n:=n) K g c) (side (n:=n) K g (1-c)):=by
   intro hf
   apply hnot
   fin_cases c
   · exact hf
   · exact q113.mpr hf
 have hf:N19.CrossStar G (side (n:=n) K h d) (side (n:=n) K h (1-d)):=by
   fin_cases d
   · exact hflag
   · exact q113.mp hflag
 exact q73 s hbip h4 hL hOne hT hne hJ hgh hhg c d
   (q144 hL.1 hT hJ hgh hhg (Or.inl rfl) c)
   (q144 hL.1 hT hJ hgh hhg (Or.inl rfl) (1-c))
   (q144 hL.1 hT hJ hgh hhg (Or.inr rfl) d)
   (q144 hL.1 hT hJ hgh hhg (Or.inr rfl) (1-d))
   (q148 hL.1 hT hJ hgh hhg (Or.inl rfl) c)
   (q148 hL.1 hT hJ hgh hhg (Or.inr rfl) d)
   (hlarge g hgJ c) (hlarge g hgJ (1-c)) (hlarge h hhJ d) (hlarge h hhJ (1-d))
   hAs hBs hCs hDs hn hf
lemma no_large_pure_independent_pair {n:ℕ} (G:SimpleGraph (Fin n))
   [DecidableRel G.Adj] (K:Circuit) (s:Fin n→ Bool)
   (hbip:∀ a b,G.Adj a b→ s a≠ s b) (h4:NoFourCycle G)
   (hL:IsLeastAO G K)
   (hOne:∀ E:Circuit,IsLeastAO G E→ (junk G E).card≠ 1)
   (hT:TopForm G K) {g h:ℕ} (hne:g≠ h) (hJ:junk G K={g,h})
   (hgh:¬ InCone n K g h) (hhg:¬ InCone n K h g)
   (hpure:∀ j∈ junk G K,∃ b:Fin 2,
     (∀ a∈ side (n:=n) K j b,s a=false)∧
     (∀ a∈ side (n:=n) K j (1-b),s a=true))
   (hlarge:∀ j∈ junk G K,∀ b:Fin 2,2≤ (side (n:=n) K j b).card):False:=by
 have hgJ:g∈ junk G K:=by rw [hJ];simp
 have hhJ:h∈ junk G K:=by rw [hJ];simp
 by_cases hgF:N19.CrossStar G (side (n:=n) K g 0) (side (n:=n) K g 1)
 · by_cases hhF:N19.CrossStar G (side (n:=n) K h 0) (side (n:=n) K h 1)
   · have hLift:=N17.q51 hL.1 hL.2.1 hT
     apply N5 n G K s hbip h4 hL hLift
     refine ⟨g,h,hne,?_,?_,?_⟩
     · intro k;simp [hJ]
     · obtain ⟨u,hu,v,hv,hA,hB⟩:=hgF
       refine ⟨side (n:=n) K g 0,side (n:=n) K g 1,u,v,hB v hv,hu,hv,hA,
         (fun b hb=> (hB b hb).symm),hlarge g hgJ 0,hlarge g hgJ 1,?_⟩
       exact N26.q71 G K hL.1 hT g h hJ hgh hhg g (Or.inl rfl)
     · obtain ⟨u,hu,v,hv,hA,hB⟩:=hhF
       refine ⟨side (n:=n) K h 0,side (n:=n) K h 1,u,v,hB v hv,hu,hv,hA,
         (fun b hb=> (hB b hb).symm),hlarge h hhJ 0,hlarge h hhJ 1,?_⟩
       exact N26.q71 G K hL.1 hT g h hJ hgh hhg h (Or.inr rfl)
   · exact q49 G K s hbip h4 hL hOne hT (Ne.symm hne)
       (by rw [hJ,Finset.pair_comm]) hhg hgh hpure hlarge hhF hgF
 · by_cases hhF:N19.CrossStar G (side (n:=n) K h 0) (side (n:=n) K h 1)
   · exact q49 G K s hbip h4 hL hOne hT hne hJ hgh hhg hpure hlarge hgF hhF
   · exact N28.q36 G K s hbip hL hOne hT hne hJ hgh hhg h4
       (hlarge g hgJ 0) (hlarge g hgJ 1) hpure hgF hhF
end LargePureCase
end PEqualNP.Outside.L_meta_5012
