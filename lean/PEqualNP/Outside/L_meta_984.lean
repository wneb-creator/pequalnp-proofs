import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_984_aux
namespace AndPart
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev F (n : ℕ) := Finset (Fin n)
abbrev G (n : ℕ) := List (Fin n × Fin n)
lemma mem_uf {α} [Fintype α] {p : α → Prop} [DecidablePred p] {x} : x ∈ Finset.univ.filter p ↔ p x := by simp
def isAndG (g : Gate) : Bool := match g.op with | .and => true | _ => false
def isOrG (g : Gate) : Bool := match g.op with | .or => true | _ => false
def andCount (C : Circuit) : ℕ := (C.gates.filter isAndG).length
def orCount (C : Circuit) : ℕ := (C.gates.filter isOrG).length
lemma filt_add (gs : List Gate) (h : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp)) :
 (gs.filter isAndG).length + (gs.filter isOrG).length = gs.length := by
 induction gs with
 | nil => simp
 | cons g gs ih =>
  have hg : g.op = .and ∨ g.op = .or := h g (by simp)
  have hr := ih fun g' h' => h g' (by simp [h'])
  rcases hg with h | h <;> simp only [List.filter_cons,isAndG,isOrG,h,↓reduceIte,Bool.false_eq_true,List.length_cons] <;> omega
theorem andCount_add_orCount (C : Circuit) (hC : Monotone2 C) : andCount C + orCount C = C.size :=
 filt_add C.gates fun g hg => (hC g hg).1
def oV {n : ℕ} (S : F n) (x : Fin n → Bool) : Bool := decide (∃ v ∈ S,x v = true)
def oG (gs : Finset ℕ) (vals : List Bool) : Bool := decide (∃ j ∈ gs,vals.getD j false = true)
inductive WE (n : ℕ) where | tt | po (v : F n) (g : Finset ℕ)
structure AG (n : ℕ) where
 lv : F n
 lg : Finset ℕ
 rv : F n
 rg : Finset ℕ
def eAS {n : ℕ} (x : Fin n → Bool) (vs : List Bool) (g : AG n) : List Bool :=
 vs++[(oV g.lv x||oG g.lg vs)&&(oV g.rv x||oG g.rg vs)]
def eAG {n : ℕ} (ags : List (AG n)) (x : Fin n → Bool) : List Bool := ags.foldl (eAS x) []
def eE {n : ℕ} (ags : List (AG n)) (x : Fin n → Bool) : WE n → Bool
 | .tt => true | .po v g => oV v x||oG g (eAG ags x)
def AgWF {n : ℕ} (ags : List (AG n)) : Prop :=
 ∀ i (hi : i < ags.length),(∀ j ∈ ags[i].lg,j < i) ∧ (∀ j ∈ ags[i].rg,j < i)
def EWF {n : ℕ} (m : ℕ) : WE n → Prop | .tt => True | .po _ g => ∀ j ∈ g,j < m
lemma eAG_len_aux {n : ℕ} (ags : List (AG n)) (x : Fin n → Bool) (init : List Bool) :
 (ags.foldl (eAS x) init).length = init.length + ags.length := by
 induction ags generalizing init with
 | nil => simp
 | cons g gs ih => simp only [List.foldl_cons,eAS,List.length_cons];rw [ih];simp;omega
lemma eAG_len {n : ℕ} (ags : List (AG n)) (x : Fin n → Bool) : (eAG ags x).length = ags.length := by
 unfold eAG;simpa using eAG_len_aux ags x []
lemma getD_app_l {α : Type} (l1 l2 : List α) (d : α) (i : ℕ) (hi : i < l1.length) :
 (l1++l2).getD i d = l1.getD i d := by
 rw [List.getD_eq_getElem _ _ (by simp;omega),List.getD_eq_getElem _ _ hi,List.getElem_append_left hi]
lemma getD_app_self {α : Type} (l : List α) (a d : α) : (l++[a]).getD l.length d = a := by
 rw [List.getD_eq_getElem _ _ (by simp)];simp
lemma eAG_app {n : ℕ} (ags : List (AG n)) (g : AG n) (x : Fin n → Bool) :
 eAG (ags++[g]) x = eAG ags x++[(oV g.lv x||oG g.lg (eAG ags x))&&(oV g.rv x||oG g.rg (eAG ags x))] := by
 simp [eAG,List.foldl_append,eAS]
lemma eE_app {n : ℕ} (ags : List (AG n)) (g : AG n) (x : Fin n → Bool) (e : WE n) (he : EWF ags.length e) :
 eE (ags++[g]) x e = eE ags x e := by
 cases e with
 | tt => rfl
 | po v gs =>
  simp only [eE,eAG_app,oG];congr 1;apply decide_eq_decide.mpr
  constructor <;> rintro ⟨j,hj,hv⟩ <;> refine ⟨j,hj,?_⟩ <;>
   have hl : j < (eAG ags x).length := by rw [eAG_len];exact he j hj
  · rwa [getD_app_l _ _ _ _ hl] at hv
  · rwa [getD_app_l _ _ _ _ hl]
lemma agWF_app {n : ℕ} (ags : List (AG n)) (g : AG n) (h : AgWF ags)
 (hl : ∀ j ∈ g.lg,j < ags.length) (hr : ∀ j ∈ g.rg,j < ags.length) : AgWF (ags++[g]) := by
 intro i hi;simp only [List.length_append,List.length_singleton] at hi
 by_cases hlt : i < ags.length
 · simp only [List.getElem_append_left hlt];exact h i hlt
 · have : i = ags.length := by omega
   subst this;simp only [List.getElem_append_right (le_refl _),Nat.sub_self,List.getElem_singleton];exact ⟨hl,hr⟩
lemma ewf_mono {n : ℕ} {m1 m2 : ℕ} (hle : m1 ≤ m2) {e : WE n} (he : EWF m1 e) : EWF m2 e := by
 cases e with | tt => trivial | po _ g => exact fun j hj => lt_of_lt_of_le (he j hj) hle
lemma getD_map_eE {n : ℕ} (ags : List (AG n)) (x : Fin n → Bool) (w : List (WE n)) (i : ℕ) :
 (w.map (eE ags x)).getD i false = eE ags x (w.getD i (.po ∅ ∅)) := by
 by_cases hi : i < w.length
 · rw [List.getD_eq_getElem _ _ (by simp [hi]),List.getD_eq_getElem _ _ hi,List.getElem_map]
 · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by omega)];simp [eE,oV,oG]
def gSt (w : List Bool) (g : Gate) : List Bool := w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
lemma oV_emp {n : ℕ} (x : Fin n → Bool) : oV (∅ : F n) x = false := by simp [oV]
lemma oG_emp (vs : List Bool) : oG (∅ : Finset ℕ) vs = false := by simp [oG]
lemma oV_un {n : ℕ} (s1 s2 : F n) (x : Fin n → Bool) : oV (s1 ∪ s2) x = (oV s1 x||oV s2 x) := by
 rw [Bool.eq_iff_iff];simp only [oV,Bool.or_eq_true,decide_eq_true_eq,Finset.mem_union]
 exact ⟨fun ⟨v,h,hv⟩ => h.elim (fun h1 => Or.inl ⟨v,h1,hv⟩) (fun h2 => Or.inr ⟨v,h2,hv⟩),
     fun h => h.elim (fun ⟨v,h1,hv⟩ => ⟨v,Or.inl h1,hv⟩) (fun ⟨v,h2,hv⟩ => ⟨v,Or.inr h2,hv⟩)⟩
lemma oG_un (g1 g2 : Finset ℕ) (vs : List Bool) : oG (g1 ∪ g2) vs = (oG g1 vs||oG g2 vs) := by
 rw [Bool.eq_iff_iff];simp only [oG,Bool.or_eq_true,decide_eq_true_eq,Finset.mem_union]
 exact ⟨fun ⟨j,h,hj⟩ => h.elim (fun h1 => Or.inl ⟨j,h1,hj⟩) (fun h2 => Or.inr ⟨j,h2,hj⟩),
     fun h => h.elim (fun ⟨j,h1,hj⟩ => ⟨j,Or.inl h1,hj⟩) (fun ⟨j,h2,hj⟩ => ⟨j,Or.inr h2,hj⟩)⟩
lemma gSt_a2 {n : ℕ} (ags : List (AG n)) (x : Fin n → Bool) (w : List (WE n)) (i j : ℕ) :
 gSt (w.map (eE ags x)) ⟨.and,[i,j]⟩ = w.map (eE ags x)++[eE ags x (w.getD i (.po ∅ ∅))&&eE ags x (w.getD j (.po ∅ ∅))] := by
 simp only [gSt,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,Bool.and_true,getD_map_eE]
lemma gSt_o2 {n : ℕ} (ags : List (AG n)) (x : Fin n → Bool) (w : List (WE n)) (i j : ℕ) :
 gSt (w.map (eE ags x)) ⟨.or,[i,j]⟩ = w.map (eE ags x)++[eE ags x (w.getD i (.po ∅ ∅))||eE ags x (w.getD j (.po ∅ ∅))] := by
 simp only [gSt,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false,getD_map_eE]
lemma compileGates {n : ℕ} (gs : List Gate) (ags : List (AG n)) (w : List (WE n))
 (hm : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
 (hA : AgWF ags) (hW : ∀ e ∈ w,EWF ags.length e) :
 ∃ (ags' : List (AG n)) (w' : List (WE n)),AgWF ags' ∧
  ags'.length ≤ ags.length + (gs.filter isAndG).length ∧ (∀ e ∈ w',EWF ags'.length e) ∧
  ∀ x : Fin n → Bool,gs.foldl gSt (w.map (eE ags x)) = w'.map (eE ags' x) := by
 induction gs generalizing ags w with
 | nil => exact ⟨ags,w,hA,by simp,hW,fun _ => rfl⟩
 | cons g gs ih =>
  have ⟨hop,hlen⟩ := hm g (by simp)
  have hgs : ∀ g' ∈ gs,g'.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 := fun g' h' => hm g' (by simp [h'])
  have hgW : ∀ i,EWF ags.length (w.getD i (.po ∅ ∅)) := fun i => by
   by_cases hi : i < w.length
   · rw [List.getD_eq_getElem _ _ hi];exact hW _ (List.getElem_mem hi)
   · rw [List.getD_eq_default _ _ (by omega)];intro j hj;simp at hj
  have same : ∀ (eN : WE n),EWF ags.length eN → (∀ x,gSt (w.map (eE ags x)) g = (w++[eN]).map (eE ags x)) →
    ∃ (ags' : List (AG n)) (w' : List (WE n)),AgWF ags' ∧ ags'.length ≤ ags.length + ((g :: gs).filter isAndG).length ∧ (∀ e ∈ w',EWF ags'.length e) ∧ ∀ x,(g :: gs).foldl gSt (w.map (eE ags x)) = w'.map (eE ags' x) := fun eN heN hs => by
   have hw' : ∀ e ∈ w++[eN],EWF ags.length e := fun e he => (List.mem_append.mp he).elim (hW e) (fun h2 => by simpa [List.mem_singleton.mp h2] using heN)
   obtain ⟨ags',w',h1,h2,h3,h4⟩ := ih ags (w++[eN]) hgs hA hw'
   have hf : (gs.filter isAndG).length ≤ ((g :: gs).filter isAndG).length := by simp only [List.filter_cons];split <;> simp
   exact ⟨ags',w',h1,by omega,h3,fun x => by simp only [List.foldl_cons,hs x];exact h4 x⟩
  obtain ⟨op,ins⟩ := g;change op = .and ∨ op = .or at hop
  cases ins with
  | nil =>
   rcases hop with rfl | rfl
   · exact same .tt trivial fun x => by simp [gSt,GateOp.eval,eE]
   · exact same (.po ∅ ∅) (fun _ h => by simp at h) fun x => by simp [gSt,GateOp.eval,eE,oV_emp,oG_emp]
  | cons i ins1 =>
   cases ins1 with
   | nil =>
    rcases hop with rfl | rfl
    · exact same (w.getD i (.po ∅ ∅)) (hgW i) fun x => by simp only [gSt,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,Bool.and_true,List.map_append,getD_map_eE]
    · exact same (w.getD i (.po ∅ ∅)) (hgW i) fun x => by simp only [gSt,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false,List.map_append,getD_map_eE]
   | cons j ins2 =>
    cases ins2 with
    | cons => simp at hlen
    | nil =>
     rcases hop with rfl | rfl
     · cases hei : w.getD i (.po ∅ ∅) with
       | tt => exact same (w.getD j (.po ∅ ∅)) (hgW j) fun x => by rw [gSt_a2,hei];simp [eE]
       | po v1 g1 =>
        cases hej : w.getD j (.po ∅ ∅) with
        | tt => exact same (.po v1 g1) (by have h := hgW i;rw [hei] at h;exact h) fun x => by rw [gSt_a2,hei,hej];simp [eE]
        | po v2 g2 =>
         let agN : AG n := ⟨v1,g1,v2,g2⟩;let ags1 := ags++[agN];let eN : WE n := .po ∅ {ags.length}
         have hg1 : ∀ k ∈ g1,k < ags.length := by have h := hgW i;rw [hei] at h;exact h
         have hg2 : ∀ k ∈ g2,k < ags.length := by have h := hgW j;rw [hej] at h;exact h
         have hw1 : ∀ e ∈ w++[eN],EWF ags1.length e := fun e he => (List.mem_append.mp he).elim
          (fun h1 => ewf_mono (by simp [ags1]) (hW e h1))
          (fun h2 => by rw [List.mem_singleton.mp h2];intro k hk;simp only [Finset.mem_singleton] at hk;subst hk;simp [ags1])
         obtain ⟨ags',w',h1,h2,h3,h4⟩ := ih ags1 (w++[eN]) hgs (agWF_app ags agN hA hg1 hg2) hw1
         refine ⟨ags',w',h1,?_,h3,?_⟩
         · simp only [ags1,List.length_append,List.filter_cons,isAndG,↓reduceIte,List.length_cons,List.length_nil] at h2 ⊢;omega
         · intro x;simp only [List.foldl_cons]
           have hmp : w.map (eE ags x) = w.map (eE ags1 x) := List.map_congr_left fun e he => (eE_app ags agN x e (hW e he)).symm
           have hev : eE ags1 x eN = (eE ags x (.po v1 g1)&&eE ags x (.po v2 g2)) := by
            simp only [eN,eE,oV_emp,Bool.false_or,oG,Finset.mem_singleton,exists_eq_left,ags1,eAG_app,agN];rw [(eAG_len ags x).symm,getD_app_self];simp
           rw [gSt_a2,hei,hej,← hev,hmp];simpa only [List.map_append,List.map_singleton] using h4 x
     · cases hei : w.getD i (.po ∅ ∅) with
       | tt => exact same .tt trivial fun x => by rw [gSt_o2,hei];simp [eE]
       | po v1 g1 =>
        cases hej : w.getD j (.po ∅ ∅) with
        | tt => exact same .tt trivial fun x => by rw [gSt_o2,hei,hej];simp [eE]
        | po v2 g2 =>
         have hw12 : EWF ags.length (.po (v1 ∪ v2) (g1 ∪ g2)) := fun k hk =>
          (Finset.mem_union.mp hk).elim (fun h1 => by have h := hgW i;rw [hei] at h;exact h k h1) (fun h2 => by have h := hgW j;rw [hej] at h;exact h k h2)
         exact same (.po (v1 ∪ v2) (g1 ∪ g2)) hw12 fun x => by
          rw [gSt_o2,hei,hej];simp only [List.map_append,List.map_singleton,eE,oV_un,oG_un];congr 2
          cases oV v1 x <;> cases oV v2 x <;> cases oG g1 (eAG ags x) <;> cases oG g2 (eAG ags x) <;> rfl
def eW (w : Fin 512) (x : Fin 6 → Bool) : Bool :=
 let g0 := x 0&&x 1
 let g1 := (x 2||(w.val.testBit 0&&g0))&&(x 3||(w.val.testBit 1&&g0))
 let g2 := (x 4||(w.val.testBit 2&&g0)||(w.val.testBit 3&&g1)) &&
      (x 5||(w.val.testBit 4&&g0)||(w.val.testBit 5&&g1))
 (w.val.testBit 6&&g0)||(w.val.testBit 7&&g1)||(w.val.testBit 8&&g2)
def bbit (b : Bool) : Nat := match b with | true => 1 | false => 0
def mkW (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) : Fin 512 :=
 ⟨bbit b0 + 2 * (bbit b1 + 2 * (bbit b2 + 2 * (bbit b3 +
  2 * (bbit b4 + 2 * (bbit b5 + 2 * (bbit b6 + 2 * (bbit b7 + 2 * bbit b8))))))),by
  have h : ∀ b,bbit b ≤ 1 := fun b => by cases b <;> simp [bbit]
  have := h b0;have := h b1;have := h b2;have := h b3;have := h b4
  have := h b5;have := h b6;have := h b7;have := h b8;omega⟩
lemma tb_am2 (b : Bool) (r k : Nat) : (bbit b + 2 * r).testBit (k + 1) = r.testBit k := by
 cases b
 · simp [bbit,Nat.testBit_succ,Nat.mul_comm]
 · simp only [bbit,Nat.testBit_succ];have hdiv : (1 + 2 * r) / 2 = r := by omega
   rw [hdiv]
lemma tb_0am2 (b : Bool) (r : Nat) : (bbit b + 2 * r).testBit 0 = b := by
 cases b <;> simp [bbit,Nat.testBit_zero]
lemma tb_mkW (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) :
 let w := (mkW b0 b1 b2 b3 b4 b5 b6 b7 b8).val
 w.testBit 0 = b0 ∧ w.testBit 1 = b1 ∧ w.testBit 2 = b2 ∧ w.testBit 3 = b3 ∧
 w.testBit 4 = b4 ∧ w.testBit 5 = b5 ∧ w.testBit 6 = b6 ∧ w.testBit 7 = b7 ∧ w.testBit 8 = b8 := by
 simp only [mkW,tb_0am2,tb_am2];cases b8 <;> simp [bbit,Nat.testBit_zero]
lemma oG_lt0 (gs : Finset ℕ) (vs : List Bool) (h : ∀ j ∈ gs,j < 0) : oG gs vs = false := by
 simp only [oG,decide_eq_false_iff_not,not_exists];exact fun j hj => absurd (h j hj.1) (Nat.not_lt_zero j)
lemma oG_lt1 (gs : Finset ℕ) (vs : List Bool) (h : ∀ j ∈ gs,j < 1) :
 oG gs vs = (decide (0 ∈ gs)&&vs.getD 0 false) := by
 rw [Bool.eq_iff_iff];simp only [oG,decide_eq_true_eq,Bool.and_eq_true]
 exact ⟨fun ⟨j,hj,hv⟩ => by have : j = 0 := (by have := h j hj;omega);subst this;exact ⟨hj,hv⟩,fun ⟨h0,hv⟩ => ⟨0,h0,hv⟩⟩
lemma oG_lt2 (gs : Finset ℕ) (vs : List Bool) (h : ∀ j ∈ gs,j < 2) :
 oG gs vs = ((decide (0 ∈ gs)&&vs.getD 0 false)||(decide (1 ∈ gs)&&vs.getD 1 false)) := by
 rw [Bool.eq_iff_iff];simp only [oG,decide_eq_true_eq,Bool.or_eq_true,Bool.and_eq_true]
 exact ⟨fun ⟨j,hj,hv⟩ => by
  have : j = 0 ∨ j = 1 := by have := h j hj;omega
  rcases this with rfl | rfl;exact Or.inl ⟨hj,hv⟩;exact Or.inr ⟨hj,hv⟩,
  fun h => h.elim (fun ⟨h0,hv⟩ => ⟨0,h0,hv⟩) (fun ⟨h1,hv⟩ => ⟨1,h1,hv⟩)⟩
lemma oG_lt3 (gs : Finset ℕ) (vs : List Bool) (h : ∀ j ∈ gs,j < 3) :
 oG gs vs = ((decide (0 ∈ gs)&&vs.getD 0 false)||(decide (1 ∈ gs)&&vs.getD 1 false)||(decide (2 ∈ gs)&&vs.getD 2 false)) := by
 rw [Bool.eq_iff_iff];simp only [oG,decide_eq_true_eq,Bool.or_eq_true,Bool.and_eq_true]
 exact ⟨fun ⟨j,hj,hv⟩ => by
  have : j = 0 ∨ j = 1 ∨ j = 2 := by have := h j hj;omega
  rcases this with rfl | rfl | rfl
  · exact Or.inl (Or.inl ⟨hj,hv⟩)
  · exact Or.inl (Or.inr ⟨hj,hv⟩)
  · exact Or.inr ⟨hj,hv⟩,
  fun h => h.elim (fun h' => h'.elim (fun ⟨h0,hv⟩ => ⟨0,h0,hv⟩) (fun ⟨h1,hv⟩ => ⟨1,h1,hv⟩)) (fun ⟨h2,hv⟩ => ⟨2,h2,hv⟩)⟩
lemma pad_ag {n : ℕ} (ags : List (AG n)) (hA : AgWF ags) (e : WE n) (he : EWF ags.length e) :
 ∃ ags' : List (AG n),ags'.length = ags.length + 1 ∧ AgWF ags' ∧ EWF ags'.length e ∧ ∀ x,eE ags' x e = eE ags x e :=
 ⟨ags++[⟨∅,∅,∅,∅⟩],by simp,agWF_app ags _ hA (fun _ h => by simp at h) (fun _ h => by simp at h),
  ewf_mono (by simp) he,fun x => eE_app ags _ x e he⟩
theorem compile_le_three {n : ℕ} (C : Circuit) (hm : Monotone2 C)
 (h0 : C.eval (List.ofFn (fun _ : Fin n => false)) = false) (hand : andCount C ≤ 3) :
 ∃ (w : Fin 512) (S : Fin 6 → F n) (O : F n),
  (andCount C ≤ 2 → w.val.testBit 8 = false) ∧ ∀ x : Fin n → Bool,C.eval (List.ofFn x) = (oV O x||eW w (fun k => oV (S k) x)) := by
 let w0 : List (WE n) := List.ofFn fun i : Fin n => WE.po {i} ∅
 have hwf0 : ∀ e ∈ w0,EWF 0 e := fun e he => by obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he;intro j hj;simp at hj
 have hmap0 : ∀ x : Fin n → Bool,w0.map (eE [] x) = List.ofFn x := fun x => by
  apply List.ext_getElem (by simp [w0]);intro i hi1 _
  simp only [w0,List.getElem_map,List.getElem_ofFn,eE,oV,oG_emp,Finset.mem_singleton,exists_eq_left,Bool.or_false]
  cases x ⟨i,by simpa [w0] using hi1⟩ <;> rfl
 obtain ⟨ags,w',hA,hlen,hW',hfold⟩ := compileGates C.gates [] w0 hm (fun _ h => by simp at h) hwf0
 simp only [List.length_nil,Nat.zero_add] at hlen;change ags.length ≤ andCount C at hlen
 have hlen3 : ags.length ≤ 3 := le_trans hlen hand
 let oE := w'.getD C.output (.po ∅ ∅)
 have hoWF : EWF ags.length oE := by
  dsimp [oE];by_cases hi : C.output < w'.length
  · rw [List.getD_eq_getElem _ _ hi];exact hW' _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)];intro j hj;simp at hj
 have hev : ∀ x : Fin n → Bool,C.eval (List.ofFn x) = eE ags x oE := fun x => by
  simp only [Circuit.eval,Circuit.wires];have hf := hfold x;rw [hmap0 x] at hf
  change (C.gates.foldl gSt (List.ofFn x)).getD C.output false = _;rw [hf,getD_map_eE]
 cases hout : oE with
 | tt => have hc := hev (fun _ => false);rw [h0,hout] at hc;simp [eE] at hc
 | po O OG =>
  rw [hout] at hoWF
  have ho2 : andCount C ≤ 2 → decide (2 ∈ OG) = false := fun h2 => by simp only [decide_eq_false_iff_not];intro hm;have := hoWF 2 hm;omega
  have hpad : ∃ ags3 : List (AG n),ags3.length = 3 ∧ AgWF ags3 ∧ EWF 3 (.po O OG) ∧ ∀ x,eE ags3 x (.po O OG) = eE ags x (.po O OG) := by
   have step : ∀ k,∀ a : List (AG n),a.length + k = 3 → AgWF a → EWF a.length (.po O OG) →
     ∃ b : List (AG n),b.length = 3 ∧ AgWF b ∧ EWF 3 (.po O OG) ∧ ∀ x,eE b x (.po O OG) = eE a x (.po O OG) := by
    intro k;induction k with
    | zero => intro a hl hAa hEa;exact ⟨a,by omega,hAa,by rwa [show a.length = 3 by omega] at hEa,fun _ => rfl⟩
    | succ k ih =>
     intro a hl hAa hEa
     obtain ⟨a1,hl1,hA1,hE1,he1⟩ := pad_ag a hAa _ hEa
     obtain ⟨b,hlb,hAb,hEb,heb⟩ := ih a1 (by omega) hA1 hE1
     exact ⟨b,hlb,hAb,hEb,fun x => (heb x).trans (he1 x)⟩
   exact step (3 - ags.length) ags (by omega) hA hoWF
  obtain ⟨ags3,hl3,hA3,hOG3,he3⟩ := hpad
  rcases ags3 with _ | ⟨a0,_ | ⟨a1,_ | ⟨a2,_ | _⟩⟩⟩
  · simp at hl3
  · simp at hl3
  · simp at hl3
  · let u10 := decide (0 ∈ a1.lg);let v10 := decide (0 ∈ a1.rg)
    let u20 := decide (0 ∈ a2.lg);let u21 := decide (1 ∈ a2.lg);let v20 := decide (0 ∈ a2.rg);let v21 := decide (1 ∈ a2.rg)
    obtain ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8⟩ := tb_mkW u10 v10 u20 u21 v20 v21 (decide (0 ∈ OG)) (decide (1 ∈ OG)) (decide (2 ∈ OG))
    let S : Fin 6 → F n := fun k => match k.val with | 0 => a0.lv | 1 => a0.rv | 2 => a1.lv | 3 => a1.rv | 4 => a2.lv | _ => a2.rv
    have ha0 := hA3 0 (by simp);have ha1 := hA3 1 (by simp);have ha2 := hA3 2 (by simp)
    refine ⟨mkW u10 v10 u20 u21 v20 v21 (decide (0 ∈ OG)) (decide (1 ∈ OG)) (decide (2 ∈ OG)),S,O,fun h2 => by rw [t8];exact ho2 h2,fun x => ?_⟩
    rw [hev x,hout,← he3 x]
    have hS : S 0 = a0.lv ∧ S 1 = a0.rv ∧ S 2 = a1.lv ∧ S 3 = a1.rv ∧ S 4 = a2.lv ∧ S 5 = a2.rv := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
    simp only [eE,eW,t0,t1,t2,t3,t4,t5,t6,t7,t8,hS.1,hS.2.1,hS.2.2.1,hS.2.2.2.1,hS.2.2.2.2.1,hS.2.2.2.2.2,
     oG_lt3 OG _ hOG3,eAG,List.foldl_cons,List.foldl_nil,eAS,List.nil_append,List.cons_append,List.getD_cons_zero,List.getD_cons_succ,
     oG_lt0 a0.lg [] ha0.1,oG_lt0 a0.rg [] ha0.2,oG_lt1 a1.lg _ ha1.1,oG_lt1 a1.rg _ ha1.2,oG_lt2 a2.lg _ ha2.1,oG_lt2 a2.rg _ ha2.2,
     u10,v10,u20,u21,v20,v21,Bool.or_false,Bool.or_assoc]
  · simp only [List.length_cons] at hl3;omega
def ttV0 : Nat := 0xAAAAAAAAAAAAAAAA
def ttV1 : Nat := 0xCCCCCCCCCCCCCCCC
def ttV2 : Nat := 0xF0F0F0F0F0F0F0F0
def ttV3 : Nat := 0xFF00FF00FF00FF00
def ttV4 : Nat := 0xFFFF0000FFFF0000
def ttV5 : Nat := 0xFFFFFFFF00000000
def bitOn (x b : Nat) : Bool := match Nat.beq (Nat.land x b) 0 with | true => false | false => true
lemma tb_and (a b k : Nat) : (Nat.land a b).testBit k = (a.testBit k&&b.testBit k) := Nat.testBit_land a b k
lemma tb_or (a b k : Nat) : (Nat.lor a b).testBit k = (a.testBit k||b.testBit k) := Nat.testBit_lor a b k
lemma tb_xor (a b k : Nat) : (Nat.xor a b).testBit k = (a.testBit k != b.testBit k) := Nat.testBit_xor a b k
lemma bitOn_pow (x k : Nat) : bitOn x (2 ^ k) = x.testBit k := by
 unfold bitOn;cases h : x.testBit k
 · have hz : Nat.land x (2 ^ k) = 0 := Nat.eq_of_testBit_eq fun i => by
    rw [tb_and,Nat.testBit_two_pow,Nat.zero_testBit];by_cases hik : k = i
    · subst hik;simp [h]
    · simp [hik]
   rw [hz]
 · have hne : Nat.land x (2 ^ k) ≠ 0 := fun hz => by
    have := congrArg (fun n => n.testBit k) hz;rw [tb_and,Nat.testBit_two_pow_self,Nat.zero_testBit,h] at this;exact absurd this (by decide)
   have hb : Nat.beq (Nat.land x (2 ^ k)) 0 = false := by cases h1 : Nat.beq (Nat.land x (2 ^ k)) 0;rfl;exact absurd (Nat.eq_of_beq_eq_true h1) hne
   rw [hb]
def wTTN (w : Nat) : Nat :=
 let g0 := Nat.land ttV0 ttV1
 let l1 := match bitOn w 1 with | true => Nat.lor ttV2 g0 | false => ttV2
 let r1 := match bitOn w 2 with | true => Nat.lor ttV3 g0 | false => ttV3
 let g1 := Nat.land l1 r1
 let l2a := match bitOn w 4 with | true => Nat.lor ttV4 g0 | false => ttV4
 let l2 := match bitOn w 8 with | true => Nat.lor l2a g1 | false => l2a
 let r2a := match bitOn w 16 with | true => Nat.lor ttV5 g0 | false => ttV5
 let r2 := match bitOn w 32 with | true => Nat.lor r2a g1 | false => r2a
 let g2 := Nat.land l2 r2
 let o0 := match bitOn w 64 with | true => g0 | false => 0
 let o1 := match bitOn w 128 with | true => g1 | false => 0
 let o2 := match bitOn w 256 with | true => g2 | false => 0
 Nat.lor (Nat.lor o0 o1) o2
def wTT (w : Fin 512) : Nat := wTTN w.val
def f1TT : Nat := Nat.lor (Nat.lor (Nat.land ttV0 ttV1) (Nat.land ttV2 ttV3)) (Nat.land ttV4 ttV5)
def f2TT (s1 s2 : Bool) : Nat :=
 let t1 := match s1 with | true => ttV3 | false => ttV2
 let t2 := match s2 with | true => ttV5 | false => ttV4
 Nat.lor (Nat.lor (Nat.land ttV2 ttV3) (Nat.land ttV4 ttV5)) (Nat.land (Nat.land ttV0 ttV1) (Nat.lor t1 t2))
def m6 (m : Fin 64) (k : Fin 6) : Bool := m.val.testBit k.val
def b6M (f : Fin 6 → Bool) : Fin 64 :=
 ⟨(if f 0 then 1 else 0) + (if f 1 then 2 else 0) + (if f 2 then 4 else 0) +
  (if f 3 then 8 else 0) + (if f 4 then 16 else 0) + (if f 5 then 32 else 0),by
  have h : ∀ (b : Bool) (v : Nat),(if b then v else 0) ≤ v := fun b v => by cases b <;> simp
  have := h (f 0) 1;have := h (f 1) 2;have := h (f 2) 4;have := h (f 3) 8;have := h (f 4) 16;have := h (f 5) 32;omega⟩
lemma tb_V : ∀ m : Fin 64,ttV0.testBit m.val = m.val.testBit 0 ∧ ttV1.testBit m.val = m.val.testBit 1 ∧
 ttV2.testBit m.val = m.val.testBit 2 ∧ ttV3.testBit m.val = m.val.testBit 3 ∧
 ttV4.testBit m.val = m.val.testBit 4 ∧ ttV5.testBit m.val = m.val.testBit 5 := by decide +kernel
lemma m6_b6M_aux : ∀ b0 b1 b2 b3 b4 b5 : Bool,
 let f : Fin 6 → Bool := fun k => match k.val with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 | _ => b5
 ∀ k : Fin 6,m6 (b6M f) k = f k := by decide +kernel
lemma m6_b6M (f : Fin 6 → Bool) : m6 (b6M f) = f := by
 have h := m6_b6M_aux (f 0) (f 1) (f 2) (f 3) (f 4) (f 5)
 have hf : f = fun k : Fin 6 => match k.val with | 0 => f 0 | 1 => f 1 | 2 => f 2 | 3 => f 3 | 4 => f 4 | _ => f 5 := by
  funext k;fin_cases k <;> rfl
 funext k;rw [hf];exact h k
lemma tb_optOr (b : Bool) (x y m : Nat) : (match b with | true => Nat.lor x y | false => x).testBit m = (x.testBit m||(b&&y.testBit m)) := by cases b <;> simp
lemma tb_optVal (b : Bool) (x m : Nat) : (match b with | true => x | false => 0).testBit m = (b&&x.testBit m) := by cases b <;> simp
lemma m6_v (m : Fin 64) : m6 m 0 = m.val.testBit 0 ∧ m6 m 1 = m.val.testBit 1 ∧ m6 m 2 = m.val.testBit 2 ∧ m6 m 3 = m.val.testBit 3 ∧ m6 m 4 = m.val.testBit 4 ∧ m6 m 5 = m.val.testBit 5 := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
lemma tb_wTT (w : Fin 512) (m : Fin 64) : (wTT w).testBit m.val = eW w (m6 m) := by
 obtain ⟨v0,v1,v2,v3,v4,v5⟩ := tb_V m;obtain ⟨m0,m1,m2,m3,m4,m5⟩ := m6_v m
 have b0 : bitOn w.val 1 = w.val.testBit 0 := bitOn_pow _ 0;have b1 : bitOn w.val 2 = w.val.testBit 1 := bitOn_pow _ 1
 have b2 : bitOn w.val 4 = w.val.testBit 2 := bitOn_pow _ 2;have b3 : bitOn w.val 8 = w.val.testBit 3 := bitOn_pow _ 3
 have b4 : bitOn w.val 16 = w.val.testBit 4 := bitOn_pow _ 4;have b5 : bitOn w.val 32 = w.val.testBit 5 := bitOn_pow _ 5
 have b6 : bitOn w.val 64 = w.val.testBit 6 := bitOn_pow _ 6;have b7 : bitOn w.val 128 = w.val.testBit 7 := bitOn_pow _ 7
 have b8 : bitOn w.val 256 = w.val.testBit 8 := bitOn_pow _ 8
 simp only [wTT,wTTN,eW,m0,m1,m2,m3,m4,m5,b0,b1,b2,b3,b4,b5,b6,b7,b8,tb_and,tb_or,tb_optOr,tb_optVal,v0,v1,v2,v3,v4,v5]
def f1E (x : Fin 6 → Bool) : Bool := (x 0&&x 1)||(x 2&&x 3)||(x 4&&x 5)
def f2E (s1 s2 : Bool) (x : Fin 6 → Bool) : Bool :=
 (x 2&&x 3)||(x 4&&x 5)||(x 0&&x 1&&((if s1 then x 3 else x 2)||(if s2 then x 5 else x 4)))
lemma tb_f1TT (m : Fin 64) : f1TT.testBit m.val = f1E (m6 m) := by
 obtain ⟨v0,v1,v2,v3,v4,v5⟩ := tb_V m;obtain ⟨m0,m1,m2,m3,m4,m5⟩ := m6_v m
 simp only [f1TT,f1E,m0,m1,m2,m3,m4,m5,tb_and,tb_or,v0,v1,v2,v3,v4,v5]
lemma tb_f2TT (s1 s2 : Bool) (m : Fin 64) : (f2TT s1 s2).testBit m.val = f2E s1 s2 (m6 m) := by
 obtain ⟨v0,v1,v2,v3,v4,v5⟩ := tb_V m;obtain ⟨m0,m1,m2,m3,m4,m5⟩ := m6_v m
 cases s1 <;> cases s2 <;> simp only [f2TT,f2E,m0,m1,m2,m3,m4,m5,tb_and,tb_or,v0,v1,v2,v3,v4,v5,Bool.false_eq_true,↓reduceIte]
lemma band_m {a b c d : Bool} (h1 : a = true → c = true) (h2 : b = true → d = true) : (a&&b) = true → (c&&d) = true := by
 cases a <;> cases b <;> cases c <;> cases d <;> simp_all
lemma band_cm (b : Bool) {x y : Bool} (h : x = true → y = true) : (b&&x) = true → (b&&y) = true := band_m id h
lemma bor_m {a b c d : Bool} (h1 : a = true → c = true) (h2 : b = true → d = true) : (a||b) = true → (c||d) = true := by
 cases a <;> cases b <;> cases c <;> cases d <;> simp_all
lemma eW_mono (w : Fin 512) (x y : Fin 6 → Bool) (hxy : ∀ k : Fin 6,x k = true → y k = true) :
 eW w x = true → eW w y = true := by
 unfold eW
 have g0 := band_m (hxy 0) (hxy 1)
 have g1 := band_m (bor_m (hxy 2) (band_cm (w.val.testBit 0) g0)) (bor_m (hxy 3) (band_cm (w.val.testBit 1) g0))
 have g2 := band_m (bor_m (bor_m (hxy 4) (band_cm (w.val.testBit 2) g0)) (band_cm (w.val.testBit 3) g1)) (bor_m (bor_m (hxy 5) (band_cm (w.val.testBit 4) g0)) (band_cm (w.val.testBit 5) g1))
 exact bor_m (bor_m (band_cm (w.val.testBit 6) g0) (band_cm (w.val.testBit 7) g1)) (band_cm (w.val.testBit 8) g2)
def imz (tt m : Nat) : Bool :=
 match tt.testBit m with
 | true => false
 | false => (m.testBit 0||tt.testBit (Nat.lor m 1))&&(m.testBit 1||tt.testBit (Nat.lor m 2)) &&
  (m.testBit 2||tt.testBit (Nat.lor m 4))&&(m.testBit 3||tt.testBit (Nat.lor m 8)) &&
  (m.testBit 4||tt.testBit (Nat.lor m 16))&&(m.testBit 5||tt.testBit (Nat.lor m 32))
def imzF (tt m b : Nat) : Bool :=
 match Nat.beq (Nat.land tt b) 0 with
 | false => false
 | true => (bitOn m 1||bitOn tt (b * 2))&&(bitOn m 2||bitOn tt (b * 4)) &&
  (bitOn m 4||bitOn tt (b * 16))&&(bitOn m 8||bitOn tt (b * 256)) &&
  (bitOn m 16||bitOn tt (b * 65536))&&(bitOn m 32||bitOn tt (b * 4294967296))
lemma lor_pow_add : ∀ (m : Fin 64) (k : Fin 6),m.val.testBit k.val = false → Nat.lor m.val (2 ^ k.val) = m.val + 2 ^ k.val := by decide +kernel
lemma imzF_eq (tt m : Nat) (hm64 : m < 64) : imzF tt m (2 ^ m) = imz tt m := by
 have hm0 : Nat.beq (Nat.land tt (2 ^ m)) 0 = !tt.testBit m := by
  have h0 := bitOn_pow tt m;unfold bitOn at h0;cases h : Nat.beq (Nat.land tt (2 ^ m)) 0 <;> simp_all
 unfold imzF imz;rw [hm0];cases htt : tt.testBit m
 · simp only [Bool.not_false]
   have st : ∀ k : Fin 6,(bitOn m (2 ^ k.val)||bitOn tt (2 ^ m * 2 ^ (2 ^ k.val))) = (m.testBit k.val||tt.testBit (Nat.lor m (2 ^ k.val))) := fun k => by
    rw [bitOn_pow];cases hm : m.testBit k.val
    · rw [← Nat.pow_add,lor_pow_add ⟨m,hm64⟩ k hm,bitOn_pow]
    · simp
   have s0 : (bitOn m 1||bitOn tt (2 ^ m * 2)) = (m.testBit 0||tt.testBit (Nat.lor m 1)) := st ⟨0,by decide⟩
   have s1 : (bitOn m 2||bitOn tt (2 ^ m * 4)) = (m.testBit 1||tt.testBit (Nat.lor m 2)) := st ⟨1,by decide⟩
   have s2 : (bitOn m 4||bitOn tt (2 ^ m * 16)) = (m.testBit 2||tt.testBit (Nat.lor m 4)) := st ⟨2,by decide⟩
   have s3 : (bitOn m 8||bitOn tt (2 ^ m * 256)) = (m.testBit 3||tt.testBit (Nat.lor m 8)) := st ⟨3,by decide⟩
   have s4 : (bitOn m 16||bitOn tt (2 ^ m * 65536)) = (m.testBit 4||tt.testBit (Nat.lor m 16)) := st ⟨4,by decide⟩
   have s5 : (bitOn m 32||bitOn tt (2 ^ m * 4294967296)) = (m.testBit 5||tt.testBit (Nat.lor m 32)) := st ⟨5,by decide⟩
   rw [s0,s1,s2,s3,s4,s5]
 · simp
def cMZL (tt : Nat) : Nat → Nat → Nat → Nat → Nat
 | 0,_,_,acc => acc
 | r + 1,m,b,acc => match imzF tt m b with
  | true => cMZL tt r (m + 1) (b + b) (acc + 1)
  | false => cMZL tt r (m + 1) (b + b) acc
def cMZ (tt : Nat) : Nat := cMZL tt 64 0 1 0
def mzF (tt : Nat) : Finset (Fin 64) := Finset.univ.filter fun m : Fin 64 => imz tt m.val = true
lemma cMZL_eq (tt rem m acc : Nat) (hr : m + rem ≤ 64) :
 cMZL tt rem m (2 ^ m) acc = acc + (Finset.univ.filter fun z : Fin 64 => m ≤ z.val ∧ z.val < m + rem ∧ imz tt z.val = true).card := by
 induction rem generalizing m acc with
 | zero =>
  have he : (Finset.univ.filter fun z : Fin 64 => m ≤ z.val ∧ z.val < m + 0 ∧ imz tt z.val = true) = ∅ := by
   ext z;simp only [mem_uf,Finset.notMem_empty,iff_false];omega
  rw [he];simp [cMZL]
 | succ r ih =>
  have hlt : m < 64 := by omega
  have hpow : 2 ^ m + 2 ^ m = 2 ^ (m + 1) := by rw [Nat.pow_succ];omega
  have hp : (Finset.univ.filter fun z : Fin 64 => m ≤ z.val ∧ z.val < m + (r + 1) ∧ imz tt z.val = true) =
   (if imz tt m = true then {⟨m,hlt⟩} else ∅) ∪ (Finset.univ.filter fun z : Fin 64 => m + 1 ≤ z.val ∧ z.val < m + 1 + r ∧ imz tt z.val = true) := by
   ext z;by_cases hzm : z.val = m
   · subst hzm;cases hz : imz tt z.val <;> simp [hz]
   · cases hz : imz tt m <;> simp only [mem_uf,Finset.mem_union,Finset.mem_singleton,Finset.notMem_empty,↓reduceIte,Bool.false_eq_true]
     · exact ⟨fun ⟨h1,h2,h3⟩ => Or.inr ⟨by omega,by omega,h3⟩,fun h => h.elim False.elim fun ⟨h1,h2,h3⟩ => ⟨by omega,by omega,h3⟩⟩
     · exact ⟨fun ⟨h1,h2,h3⟩ => Or.inr ⟨by omega,by omega,h3⟩,fun h => h.elim (fun e => absurd (congrArg Fin.val e) hzm) fun ⟨h1,h2,h3⟩ => ⟨by omega,by omega,h3⟩⟩
  have hd : Disjoint (if imz tt m = true then ({⟨m,hlt⟩} : Finset (Fin 64)) else ∅)
   (Finset.univ.filter fun z : Fin 64 => m + 1 ≤ z.val ∧ z.val < m + 1 + r ∧ imz tt z.val = true) := by cases hz : imz tt m <;> simp [hz]
  rw [hp,Finset.card_union_of_disjoint hd];simp only [cMZL,imzF_eq tt m hlt,hpow]
  cases hz : imz tt m
  · simp only [Bool.false_eq_true,↓reduceIte,Finset.card_empty,Nat.zero_add];exact ih (m + 1) acc (by omega)
  · simp only [↓reduceIte,Finset.card_singleton];rw [ih (m + 1) (acc + 1) (by omega)];omega
lemma card_mzF (tt : Nat) : (mzF tt).card = cMZ tt := by
 have h := cMZL_eq tt 64 0 0 (by omega)
 simp only [cMZ,Nat.pow_zero,Nat.zero_add,Nat.zero_le,true_and] at h ⊢
 have he : mzF tt = Finset.univ.filter fun z : Fin 64 => z.val < 64 ∧ imz tt z.val = true := by ext z;simp [mzF]
 rw [h,he]
def chkBelow (p : Nat → Bool) : Nat → Bool
 | 0 => true
 | k + 1 => match p k with | true => chkBelow p k | false => false
lemma chkBelow_s (p : Nat → Bool) (n : Nat) (h : chkBelow p n = true) : ∀ k < n,p k = true := by
 induction n with
 | zero => intro k hk;omega
 | succ n ih =>
  intro k hk;simp only [chkBelow] at h;cases hp : p n
  · rw [hp] at h;simp at h
  · rw [hp] at h;by_cases e : k = n;subst e;exact hp;exact ih h k (by omega)
def chk1W (w : Nat) : Bool :=
 let tt := wTTN w;let o2 := bitOn w 256
 match Nat.beq tt f1TT with
 | true => o2
 | false => match Nat.beq tt (f2TT false false)||Nat.beq tt (f2TT false true) ||
   Nat.beq tt (f2TT true false)||Nat.beq tt (f2TT true true) with
  | true => o2
  | false => let c := cMZ tt;match o2 with | false => Nat.ble c 4 | true => Nat.ble c 6
theorem chk_w_all : chkBelow chk1W 512 = true := by decide +kernel
theorem cMZ_f1 : cMZ f1TT = 8 := by decide +kernel
theorem cMZ_f2 : cMZ (f2TT false false) = 7 ∧ cMZ (f2TT false true) = 7 ∧ cMZ (f2TT true false) = 7 ∧ cMZ (f2TT true true) = 7 := by decide +kernel
lemma w_cases (w : Fin 512) :
 (wTT w = f1TT ∧ w.val.testBit 8 = true) ∨
 ((wTT w = f2TT false false ∨ wTT w = f2TT false true ∨ wTT w = f2TT true false ∨ wTT w = f2TT true true) ∧ w.val.testBit 8 = true) ∨
 (cMZ (wTT w) ≤ 6 ∧ (w.val.testBit 8 = false → cMZ (wTT w) ≤ 4)) := by
 have h := chkBelow_s chk1W 512 chk_w_all w.val w.isLt
 have ho2 : bitOn w.val 256 = w.val.testBit 8 := bitOn_pow w.val 8
 unfold chk1W at h;dsimp only at h;rw [ho2] at h;unfold wTT
 cases h1 : Nat.beq (wTTN w.val) f1TT
 · rw [h1] at h
   cases h2 : (Nat.beq (wTTN w.val) (f2TT false false)||Nat.beq (wTTN w.val) (f2TT false true) ||
    Nat.beq (wTTN w.val) (f2TT true false)||Nat.beq (wTTN w.val) (f2TT true true))
   · rw [h2] at h;right;right;cases h8 : w.val.testBit 8
     · rw [h8] at h;have h4 := Nat.le_of_ble_eq_true h;exact ⟨by omega,fun _ => h4⟩
     · rw [h8] at h;exact ⟨Nat.le_of_ble_eq_true h,fun c => by simp at c⟩
   · rw [h2] at h;right;left;refine ⟨?_,h⟩;simp only [Bool.or_eq_true] at h2
     rcases h2 with ((ha | hb) | hc) | hd
     · exact Or.inl (Nat.eq_of_beq_eq_true ha)
     · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true hb))
     · exact Or.inr (Or.inr (Or.inl (Nat.eq_of_beq_eq_true hc)))
     · exact Or.inr (Or.inr (Or.inr (Nat.eq_of_beq_eq_true hd)))
 · rw [h1] at h;exact Or.inl ⟨Nat.eq_of_beq_eq_true h1,h⟩
lemma w_eq_f1 (w : Fin 512) (h : wTT w = f1TT) (x : Fin 6 → Bool) : eW w x = f1E x := by
 have hx := tb_wTT w (b6M x);rw [h,tb_f1TT,m6_b6M] at hx;exact hx.symm
lemma w_eq_f2 (w : Fin 512) (s1 s2 : Bool) (h : wTT w = f2TT s1 s2) (x : Fin 6 → Bool) : eW w x = f2E s1 s2 x := by
 have hx := tb_wTT w (b6M x);rw [h,tb_f2TT,m6_b6M] at hx;exact hx.symm
def eFn {n : ℕ} (E : G n) (x : Fin n → Bool) : Bool := E.any fun e => x e.1&&x e.2
def noLoop {n : ℕ} (E : G n) : Bool := E.all fun e => e.1 != e.2
def adj {n : ℕ} (E : G n) (u v : Fin n) : Bool := E.any fun e => (e.1 == u&&e.2 == v)||(e.1 == v&&e.2 == u)
def iF {n : ℕ} (I : F n) (v : Fin n) : Bool := decide (v ∈ I)
def m2f {n : ℕ} (m : Nat) : F n := Finset.univ.filter fun v : Fin n => m.testBit v.val = true
def isIM {n : ℕ} (E : G n) (m : Nat) : Bool := E.all fun e => !(m.testBit e.1.val&&m.testBit e.2.val)
def isMIM (n : ℕ) (E : G n) (m : Nat) : Bool :=
 isIM E m&&(List.finRange n).all fun v => m.testBit v.val||!isIM E (Nat.lor m (1 <<< v.val))
def mIMs (n : ℕ) (E : G n) : List Nat := (List.range (2 ^ n)).filter (isMIM n E)
lemma eFn_false {n : ℕ} (E : G n) : eFn E (fun _ => false) = false := by simp [eFn]
lemma eFn_sing {n : ℕ} (E : G n) (hl : noLoop E = true) (v : Fin n) :
 eFn E (fun w => decide (w = v)) = false := by
 unfold eFn;rw [List.any_eq_false];intro e he
 have hne : e.1 ≠ e.2 := by simpa [bne_iff_ne] using List.all_eq_true.mp hl e he
 by_cases h1 : e.1 = v
 · have h2 : e.2 ≠ v := fun h2 => hne (h1.trans h2.symm);simp [h1,h2]
 · simp [h1]
lemma outV_emp {n : ℕ} (E : G n) (hl : noLoop E = true) (w : Fin 512)
 (S : Fin 6 → F n) (O : F n)
 (hc : ∀ x,eFn E x = (oV O x||eW w (fun k => oV (S k) x))) :
 ∀ x,eFn E x = eW w (fun k => oV (S k) x) := by
 have hO : O = ∅ := by
  ext v;simp only [Finset.notMem_empty,iff_false];intro hv
  have h1 := hc (fun u => decide (u = v));rw [eFn_sing E hl v] at h1
  have hor : oV O (fun u => decide (u = v)) = true := by simp only [oV,decide_eq_true_eq];exact ⟨v,hv,by simp⟩
  rw [hor,Bool.true_or] at h1;exact absurd h1 (by decide)
 intro x;have hx := hc x;rwa [hO,oV_emp,Bool.false_or] at hx
lemma isIM_s {n : ℕ} (E : G n) (m : Nat) (hm : isIM E m = true) :
 eFn E (iF (m2f m)) = false := by
 unfold eFn;rw [List.any_eq_false];intro e he
 have h := List.all_eq_true.mp hm e he
 simp only [iF,m2f,mem_uf]
 cases h1 : m.testBit e.1.val <;> cases h2 : m.testBit e.2.val <;> simp_all
lemma isMIM_s {n : ℕ} (E : G n) (m : Nat) (hm : isMIM n E m = true) :
 ∀ J : F n,m2f m ⊆ J → eFn E (iF J) = false → J = m2f m := by
 simp only [isMIM,Bool.and_eq_true] at hm;intro J hsub hJ
 apply Finset.Subset.antisymm _ hsub;intro v hvJ;by_contra hvn
 have hvf : m.testBit v.val = false := by
  simp only [m2f,mem_uf] at hvn
  cases h : m.testBit v.val;rfl;exact absurd h hvn
 have hall := List.all_eq_true.mp hm.2 v (List.mem_finRange v)
 rw [hvf,Bool.false_or,Bool.not_eq_true'] at hall
 have hind : isIM E (Nat.lor m (1 <<< v.val)) = true := by
  unfold isIM;rw [List.all_eq_true];intro e he
  have hJe := List.any_eq_false.mp hJ e he
  have hml : ∀ u : Fin n,(Nat.lor m (1 <<< v.val)).testBit u.val = true → u ∈ J := fun u hu => by
   rw [tb_or,Bool.or_eq_true] at hu;rcases hu with h1 | h2
   · exact hsub (by simp [m2f,h1])
   · have hsh : (1 <<< v.val) = 2 ^ v.val := by simp [Nat.shiftLeft_eq]
     rw [hsh,Nat.testBit_two_pow] at h2;simp only [decide_eq_true_eq] at h2
     exact (Fin.ext h2.symm) ▸ hvJ
  cases h1 : (Nat.lor m (1 <<< v.val)).testBit e.1.val
  · simp
  · cases h2 : (Nat.lor m (1 <<< v.val)).testBit e.2.val
    · simp
    · exfalso;have u1 := hml e.1 h1;have u2 := hml e.2 h2;simp [iF,u1,u2] at hJe
 rw [hind] at hall;exact absurd hall (by decide)
lemma m2f_inj {n : ℕ} {m1 m2 : Nat} (h1 : m1 < 2 ^ n) (h2 : m2 < 2 ^ n)
 (heq : m2f (n := n) m1 = m2f (n := n) m2) : m1 = m2 := by
 apply Nat.eq_of_testBit_eq;intro k;by_cases hk : k < n
 · have hm := congrArg (fun S => (⟨k,hk⟩ : Fin n) ∈ S) heq
   simp only [m2f,mem_uf] at hm
   exact Bool.eq_iff_iff.mpr (by rw [hm])
 · have hk' : n ≤ k := Nat.le_of_not_lt hk
   rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) hk')),
     Nat.testBit_lt_two_pow (lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) hk'))]
lemma lor_lt64 : ∀ (m : Fin 64) (k : Fin 6),Nat.lor m.val (2 ^ k.val) < 64 := by decide +kernel
lemma ex_mz_above (tt : Nat) (u : Fin 64) (hu : tt.testBit u.val = false) :
 ∃ m : Fin 64,(∀ k : Fin 6,u.val.testBit k.val = true → m.val.testBit k.val = true) ∧ imz tt m.val = true := by
 let wt6 : Fin 64 → ℕ := fun z => (Finset.univ.filter fun k : Fin 6 => z.val.testBit k.val = true).card
 let cand : Finset (Fin 64) := Finset.univ.filter fun z => (∀ k : Fin 6,u.val.testBit k.val = true → z.val.testBit k.val = true) ∧ tt.testBit z.val = false
 have hum : u ∈ cand := by simp only [cand,mem_uf];exact ⟨fun _ h => h,hu⟩
 obtain ⟨m,hmm,hmax⟩ := Finset.exists_max_image cand wt6 ⟨u,hum⟩
 simp only [cand,mem_uf] at hmm
 refine ⟨m,hmm.1,?_⟩
 have hst : ∀ k : Fin 6,m.val.testBit k.val = false → tt.testBit (Nat.lor m.val (2 ^ k.val)) = true := fun k hk => by
  let m' : Fin 64 := ⟨Nat.lor m.val (2 ^ k.val),lor_lt64 m k⟩
  have hsub : (Finset.univ.filter fun j : Fin 6 => m.val.testBit j.val = true) ⊂ (Finset.univ.filter fun j : Fin 6 => m'.val.testBit j.val = true) := by
   rw [Finset.ssubset_iff_subset_ne];refine ⟨fun j hj => ?_,fun heq => ?_⟩
   · simp only [mem_uf,m',tb_or,Bool.or_eq_true] at hj ⊢;exact Or.inl hj
   · have hkm' : k ∈ Finset.univ.filter fun j : Fin 6 => m'.val.testBit j.val = true := by
      simp only [mem_uf,m',tb_or,Nat.testBit_two_pow_self,Bool.or_true]
     rw [← heq] at hkm';simp only [mem_uf,hk] at hkm';exact absurd hkm' (by decide)
  have hwt : wt6 m < wt6 m' := Finset.card_lt_card hsub
  cases htt' : tt.testBit m'.val
  · exfalso
    have hm' : m' ∈ cand := by simp only [cand,mem_uf];exact ⟨fun j hj => by simp only [m',tb_or,Bool.or_eq_true];exact Or.inl (hmm.1 j hj),htt'⟩
    have := hmax m' hm';omega
  · rfl
 unfold imz;rw [hmm.2]
 have bOk : ∀ k : Fin 6,(m.val.testBit k.val||tt.testBit (Nat.lor m.val (2 ^ k.val))) = true := fun k => by
  cases hk : m.val.testBit k.val;rw [Bool.false_or];exact hst k hk;simp
 have b0 : (m.val.testBit 0||tt.testBit (Nat.lor m.val 1)) = true := bOk ⟨0,by decide⟩
 have b1 : (m.val.testBit 1||tt.testBit (Nat.lor m.val 2)) = true := bOk ⟨1,by decide⟩
 have b2 : (m.val.testBit 2||tt.testBit (Nat.lor m.val 4)) = true := bOk ⟨2,by decide⟩
 have b3 : (m.val.testBit 3||tt.testBit (Nat.lor m.val 8)) = true := bOk ⟨3,by decide⟩
 have b4 : (m.val.testBit 4||tt.testBit (Nat.lor m.val 16)) = true := bOk ⟨4,by decide⟩
 have b5 : (m.val.testBit 5||tt.testBit (Nat.lor m.val 32)) = true := bOk ⟨5,by decide⟩
 simp only [b0,b1,b2,b3,b4,b5,Bool.and_self]
lemma oV_iF_un {n : ℕ} (S I J : F n) : oV S (iF (I ∪ J)) = (oV S (iF I)||oV S (iF J)) := by
 rw [Bool.eq_iff_iff];simp only [oV,iF,Bool.or_eq_true,decide_eq_true_eq,Finset.mem_union]
 exact ⟨fun ⟨v,hvS,h⟩ => h.elim (fun h1 => Or.inl ⟨v,hvS,h1⟩) (fun h2 => Or.inr ⟨v,hvS,h2⟩),
     fun h => h.elim (fun ⟨v,hvS,h1⟩ => ⟨v,hvS,Or.inl h1⟩) (fun ⟨v,hvS,h2⟩ => ⟨v,hvS,Or.inr h2⟩)⟩
lemma mIMs_le_cMZ {n : ℕ} (E : G n) (w : Fin 512) (S : Fin 6 → F n)
 (hc : ∀ x,eFn E x = eW w (fun k => oV (S k) x)) : (mIMs n E).length ≤ cMZ (wTT w) := by
 classical
 rw [← card_mzF];let ms := mIMs n E;let Mf : Finset Nat := ms.toFinset
 have hcard : Mf.card = ms.length := List.toFinset_card_of_nodup (List.Nodup.filter _ List.nodup_range)
 rw [← hcard]
 have hz : ∀ m ∈ Mf,(wTT w).testBit (b6M (fun k => oV (S k) (iF (m2f m)))).val = false := fun m hm => by
  have hmax := (List.mem_filter.mp (List.mem_toFinset.mp hm)).2
  rw [tb_wTT,m6_b6M,← hc];exact isIM_s E m (Bool.and_eq_true _ _ ▸ hmax).1
 let f : Nat → Fin 64 := fun m => if h : m ∈ Mf then Classical.choose (ex_mz_above (wTT w) (b6M fun k => oV (S k) (iF (m2f m))) (hz m h)) else ⟨0,by decide⟩
 apply Finset.card_le_card_of_injOn f
 · intro m hm;have hm' : m ∈ Mf := hm
   have hs := Classical.choose_spec (ex_mz_above (wTT w) (b6M fun k => oV (S k) (iF (m2f m))) (hz m hm'))
   simp only [Finset.mem_coe,mzF,mem_uf,f,dite_eq_left,hm'];exact hs.2
 · intro m1 hm1 m2 hm2 hfeq;have hm1' : m1 ∈ Mf := hm1;have hm2' : m2 ∈ Mf := hm2
   have hs1 := Classical.choose_spec (ex_mz_above (wTT w) (b6M fun k => oV (S k) (iF (m2f m1))) (hz m1 hm1'))
   have hs2 := Classical.choose_spec (ex_mz_above (wTT w) (b6M fun k => oV (S k) (iF (m2f m2))) (hz m2 hm2'))
   simp only [f,dite_eq_left,hm1',hm2'] at hfeq
   set z := Classical.choose (ex_mz_above (wTT w) (b6M fun k => oV (S k) (iF (m2f m1))) (hz m1 hm1'))
   rw [← hfeq] at hs2
   have hzf : (wTT w).testBit z.val = false := by
    have hmz := hs1.2;unfold imz at hmz;cases htt : (wTT w).testBit z.val;rfl;rw [htt] at hmz;simp at hmz
   have hleu : ∀ k : Fin 6,oV (S k) (iF (m2f m1 ∪ m2f m2)) = true → m6 z k = true := fun k hk => by
    rw [oV_iF_un,Bool.or_eq_true] at hk;rcases hk with hk1 | hk2
    · exact hs1.1 k (by have := congrFun (m6_b6M fun j => oV (S j) (iF (m2f m1))) k;simpa [m6,hk1] using this)
    · exact hs2.1 k (by have := congrFun (m6_b6M fun j => oV (S j) (iF (m2f m2))) k;simpa [m6,hk2] using this)
   have huf : eFn E (iF (m2f m1 ∪ m2f m2)) = false := by
    rw [hc];cases hv : eW w (fun k => oV (S k) (iF (m2f m1 ∪ m2f m2)))
    · rfl
    · exfalso;have hzt := eW_mono w _ (m6 z) hleu hv;rw [← tb_wTT,hzf] at hzt;exact absurd hzt (by decide)
   have hm1f := List.mem_filter.mp (List.mem_toFinset.mp hm1')
   have hm2f := List.mem_filter.mp (List.mem_toFinset.mp hm2')
   exact m2f_inj (List.mem_range.mp hm1f.1) (List.mem_range.mp hm2f.1)
    ((isMIM_s E m1 hm1f.2 _ Finset.subset_union_left huf).symm.trans (isMIM_s E m2 hm2f.2 _ Finset.subset_union_right huf))
def c4F {n : ℕ} (E : G n) : Bool :=
 (List.finRange n).all fun u => ((List.finRange n).filter (fun v => decide (u < v))).all fun v =>
  (List.finRange n).all fun w => ((List.finRange n).filter (fun z => decide (w < z))).all fun z =>
   !(adj E u w&&adj E u z&&adj E v w&&adj E v z)
def noV3 {n : ℕ} (E : G n) : Bool :=
 (List.finRange n).all fun a => ((List.finRange n).filter (fun b => decide (a ≤ b))).all fun b =>
  ((List.finRange n).filter (fun c => decide (b ≤ c))).all fun c =>
   E.any fun e => e.1 != a&&e.1 != b&&e.1 != c&&e.2 != a&&e.2 != b&&e.2 != c
lemma c4F_s {n : ℕ} (E : G n) (hc4 : c4F E = true) (u v w z : Fin n)
 (huv : u ≠ v) (hwz : w ≠ z) (h1 : adj E u w = true) (h2 : adj E u z = true) (h3 : adj E v w = true) (h4 : adj E v z = true) : False := by
 have ord : ∀ a b c d : Fin n,a < b → c < d → adj E a c = true → adj E a d = true → adj E b c = true → adj E b d = true → False :=
  fun a b c d hab hcd h1' h2' h3' h4' => by
   have ha := List.all_eq_true.mp hc4 a (List.mem_finRange a)
   have hb := List.all_eq_true.mp ha b (List.mem_filter.mpr ⟨List.mem_finRange b,by simp [hab]⟩)
   have hc := List.all_eq_true.mp hb c (List.mem_finRange c)
   have hd := List.all_eq_true.mp hc d (List.mem_filter.mpr ⟨List.mem_finRange d,by simp [hcd]⟩)
   simp [h1',h2',h3',h4'] at hd
 rcases lt_or_gt_of_ne huv with huv' | huv' <;> rcases lt_or_gt_of_ne hwz with hwz' | hwz'
 · exact ord u v w z huv' hwz' h1 h2 h3 h4
 · exact ord u v z w huv' hwz' h2 h1 h4 h3
 · exact ord v u w z huv' hwz' h3 h4 h1 h2
 · exact ord v u z w huv' hwz' h4 h3 h2 h1
lemma noV3_s {n : ℕ} (hn : 0 < n) (E : G n) (hvc : noV3 E = true) (VC : F n) (hcd : VC.card ≤ 3) :
 ∃ e ∈ E,e.1 ∉ VC ∧ e.2 ∉ VC := by
 have htr : ∃ a b c : Fin n,a ≤ b ∧ b ≤ c ∧ ∀ v ∈ VC,v = a ∨ v = b ∨ v = c := by
  let l := VC.sort (· ≤ ·);have hlen : l.length ≤ 3 := by simpa [l,Finset.length_sort] using hcd
  have hp : l.Pairwise (· ≤ ·) := VC.pairwise_sort (· ≤ ·);have hm : ∀ v,v ∈ l ↔ v ∈ VC := fun v => VC.mem_sort (· ≤ ·)
  cases hl : l with
  | nil => exact ⟨⟨0,hn⟩,⟨0,hn⟩,⟨0,hn⟩,le_refl _,le_refl _,fun v hv => by have := (hm v).mpr hv;rw [hl] at this;simp at this⟩
  | cons a l1 =>
   cases hl1 : l1 with
   | nil => exact ⟨a,a,a,le_refl _,le_refl _,fun v hv => by have := (hm v).mpr hv;rw [hl,hl1] at this;exact Or.inl (List.mem_singleton.mp this)⟩
   | cons b l2 =>
    cases hl2 : l2 with
    | nil =>
     rw [hl,hl1,hl2] at hp;exact ⟨a,b,b,(List.pairwise_cons.mp hp).1 b (by simp),le_refl _,fun v hv => by
      have := (hm v).mpr hv;rw [hl,hl1,hl2] at this;simp only [List.mem_cons,List.not_mem_nil,or_false] at this
      exact this.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
    | cons c l3 =>
     cases hl3 : l3 with
     | nil =>
      rw [hl,hl1,hl2,hl3] at hp;have h1 := List.pairwise_cons.mp hp
      exact ⟨a,b,c,h1.1 b (by simp),(List.pairwise_cons.mp h1.2).1 c (by simp),fun v hv => by
       have := (hm v).mpr hv;rw [hl,hl1,hl2,hl3] at this;simpa only [List.mem_cons,List.not_mem_nil,or_false] using this⟩
     | cons d l4 => rw [hl,hl1,hl2,hl3] at hlen;simp only [List.length_cons] at hlen;omega
 obtain ⟨a,b,c,hab,hbc,hcov⟩ := htr
 have ha := List.all_eq_true.mp hvc a (List.mem_finRange a)
 have hb := List.all_eq_true.mp ha b (List.mem_filter.mpr ⟨List.mem_finRange b,by simp [hab]⟩)
 have hc := List.all_eq_true.mp hb c (List.mem_filter.mpr ⟨List.mem_finRange c,by simp [hbc]⟩)
 obtain ⟨e,he,hok⟩ := List.any_eq_true.mp hc;simp only [Bool.and_eq_true,bne_iff_ne] at hok
 exact ⟨e,he,fun h1 => by rcases hcov e.1 h1 with rfl | rfl | rfl;exact hok.1.1.1.1.1 rfl;exact hok.1.1.1.1.2 rfl;exact hok.1.1.1.2 rfl,
        fun h2 => by rcases hcov e.2 h2 with rfl | rfl | rfl;exact hok.1.1.2 rfl;exact hok.1.2 rfl;exact hok.2 rfl⟩
lemma f1_star {n : ℕ} (E : G n) (hl : noLoop E = true) (hc4 : c4F E = true) (A B : F n)
 (hs : ∀ x,(oV A x&&oV B x) = true → eFn E x = true) :
 ∃ C : F n,C.card ≤ 1 ∧ ∀ e : Fin n × Fin n,(oV A (fun v => decide (v = e.1 ∨ v = e.2))&&oV B (fun v => decide (v = e.1 ∨ v = e.2))) = true → e.1 ∈ C ∨ e.2 ∈ C := by
 have hadj : ∀ a ∈ A,∀ b ∈ B,adj E a b = true := fun a ha b hb => by
  let x : Fin n → Bool := fun v => decide (v = a ∨ v = b)
  have hedge := hs x (by simp only [Bool.and_eq_true,oV,decide_eq_true_eq];exact ⟨⟨a,ha,by simp [x]⟩,⟨b,hb,by simp [x]⟩⟩)
  obtain ⟨e,he,hx⟩ := List.any_eq_true.mp hedge;simp only [Bool.and_eq_true,x,decide_eq_true_eq] at hx
  have hne : e.1 ≠ e.2 := by simpa [bne_iff_ne] using List.all_eq_true.mp hl e he
  unfold adj;rw [List.any_eq_true];refine ⟨e,he,?_⟩
  rcases hx.1 with h1 | h1 <;> rcases hx.2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · simp [h1,h2]
  · simp [h1,h2]
  · exact absurd (h1.trans h2.symm) hne
 by_cases hA : A.card ≤ 1
 · exact ⟨A,hA,fun e he => by simp only [Bool.and_eq_true,oV,decide_eq_true_eq] at he;obtain ⟨v,hv,h1 | h2⟩ := he.1;exact Or.inl (h1 ▸ hv);exact Or.inr (h2 ▸ hv)⟩
 · by_cases hB : B.card ≤ 1
   · exact ⟨B,hB,fun e he => by simp only [Bool.and_eq_true,oV,decide_eq_true_eq] at he;obtain ⟨v,hv,h1 | h2⟩ := he.2;exact Or.inl (h1 ▸ hv);exact Or.inr (h2 ▸ hv)⟩
   · exfalso;obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
     obtain ⟨w,hw,z,hz,hwz⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
     exact c4F_s E hc4 u v w z huv hwz (hadj u hu w hw) (hadj u hu z hz) (hadj v hv w hw) (hadj v hv z hz)
lemma f1_imp {n : ℕ} (hn : 0 < n) (E : G n) (hl : noLoop E = true) (hc4 : c4F E = true) (hvc : noV3 E = true)
 (S : Fin 6 → F n) (hc : ∀ x,eFn E x = f1E (fun k => oV (S k) x)) : False := by
 obtain ⟨C0,h0,c0⟩ := f1_star E hl hc4 (S 0) (S 1) fun x hx => by rw [hc x];simp [f1E,hx]
 obtain ⟨C1,h1,c1⟩ := f1_star E hl hc4 (S 2) (S 3) fun x hx => by rw [hc x];simp [f1E,hx]
 obtain ⟨C2,h2,c2⟩ := f1_star E hl hc4 (S 4) (S 5) fun x hx => by rw [hc x];simp [f1E,hx]
 have hcd : (C0 ∪ C1 ∪ C2).card ≤ 3 := by have := Finset.card_union_le (C0 ∪ C1) C2;have := Finset.card_union_le C0 C1;omega
 obtain ⟨e,he,he1,he2⟩ := noV3_s hn E hvc (C0 ∪ C1 ∪ C2) hcd
 have hedge : eFn E (fun v => decide (v = e.1 ∨ v = e.2)) = true := by unfold eFn;rw [List.any_eq_true];exact ⟨e,he,by simp⟩
 rw [hc] at hedge;simp only [f1E,Bool.or_eq_true] at hedge
 rcases hedge with (h | h) | h
 · rcases c0 e h with h' | h' <;> [exact he1 (Finset.mem_union_left _ (Finset.mem_union_left _ h'));exact he2 (Finset.mem_union_left _ (Finset.mem_union_left _ h'))]
 · rcases c1 e h with h' | h' <;> [exact he1 (Finset.mem_union_left _ (Finset.mem_union_right _ h'));exact he2 (Finset.mem_union_left _ (Finset.mem_union_right _ h'))]
 · rcases c2 e h with h' | h' <;> [exact he1 (Finset.mem_union_right _ h');exact he2 (Finset.mem_union_right _ h')]
def f2MZ : Fin 7 → Fin 64
 | 0 => ⟨43,by decide⟩ | 1 => ⟨38,by decide⟩ | 2 => ⟨37,by decide⟩
 | 3 => ⟨26,by decide⟩ | 4 => ⟨25,by decide⟩ | 5 => ⟨22,by decide⟩ | 6 => ⟨21,by decide⟩
theorem imz_f2_iff : ∀ m : Fin 64,imz (f2TT false false) m.val = true ↔ ∃ r : Fin 7,f2MZ r = m := by decide +kernel
theorem f2MZ_z : ∀ r : Fin 7,(f2TT false false).testBit (f2MZ r).val = false := by decide +kernel
lemma f2E_mono (x y : Fin 6 → Bool) (h : ∀ k,x k = true → y k = true) : f2E false false x = true → f2E false false y = true := by
 unfold f2E;simp only [Bool.false_eq_true,↓reduceIte]
 exact bor_m (bor_m (band_m (h 2) (h 3)) (band_m (h 4) (h 5))) (band_m (band_m (h 0) (h 1)) (bor_m (h 2) (h 4)))
def allP7 (f : Fin 7 → Fin 7 → Fin 7 → Fin 7 → Fin 7 → Fin 7 → Fin 7 → Bool) : Bool :=
 (List.finRange 7).all fun i0 =>
  let r1 := (List.finRange 7).filter (· != i0)
  r1.all fun a1 => (r1.filter fun x => decide (a1 < x)).all fun b1 =>
   let r2 := r1.filter fun x => x != a1&&x != b1
   (r2.filter fun x => decide (a1 < x)).all fun a2 => (r2.filter fun x => decide (a2 < x)).all fun b2 =>
    let r3 := r2.filter fun x => x != a2&&x != b2
    r3.all fun a3 => (r3.filter fun x => decide (a3 < x)).all fun b3 => f i0 a1 b1 a2 b2 a3 b3
lemma allP7_s (f : Fin 7 → Fin 7 → Fin 7 → Fin 7 → Fin 7 → Fin 7 → Fin 7 → Bool) (h : allP7 f = true)
 (i0 a1 b1 a2 b2 a3 b3 : Fin 7) (ha1 : a1 ≠ i0) (hb1 : b1 ≠ i0) (h1 : a1 < b1)
 (ha2 : a2 ≠ i0 ∧ a2 ≠ a1 ∧ a2 ≠ b1) (h12 : a1 < a2) (hb2 : b2 ≠ i0 ∧ b2 ≠ a1 ∧ b2 ≠ b1) (h2 : a2 < b2)
 (ha3 : a3 ≠ i0 ∧ a3 ≠ a1 ∧ a3 ≠ b1 ∧ a3 ≠ a2 ∧ a3 ≠ b2) (hb3 : b3 ≠ i0 ∧ b3 ≠ a1 ∧ b3 ≠ b1 ∧ b3 ≠ a2 ∧ b3 ≠ b2) (h3 : a3 < b3) :
 f i0 a1 b1 a2 b2 a3 b3 = true := by
 have hi0 := List.all_eq_true.mp h i0 (List.mem_finRange i0)
 have m1 : ∀ x,x ≠ i0 → x ∈ (List.finRange 7).filter (· != i0) := fun x hx => List.mem_filter.mpr ⟨List.mem_finRange x,by simp [hx]⟩
 have hfb1 := List.all_eq_true.mp (List.all_eq_true.mp hi0 a1 (m1 a1 ha1)) b1 (List.mem_filter.mpr ⟨m1 b1 hb1,by simp [h1]⟩)
 have m2 : ∀ x,x ≠ i0 ∧ x ≠ a1 ∧ x ≠ b1 → x ∈ ((List.finRange 7).filter (· != i0)).filter (fun y => y != a1&&y != b1) :=
  fun x hx => List.mem_filter.mpr ⟨m1 x hx.1,by simp [hx.2.1,hx.2.2]⟩
 have hfb2 := List.all_eq_true.mp (List.all_eq_true.mp hfb1 a2 (List.mem_filter.mpr ⟨m2 a2 ha2,by simp [h12]⟩)) b2 (List.mem_filter.mpr ⟨m2 b2 hb2,by simp [h2]⟩)
 have m3 : ∀ x,x ≠ i0 ∧ x ≠ a1 ∧ x ≠ b1 ∧ x ≠ a2 ∧ x ≠ b2 → x ∈ (((List.finRange 7).filter (· != i0)).filter (fun y => y != a1&&y != b1)).filter (fun y => y != a2&&y != b2) :=
  fun x hx => List.mem_filter.mpr ⟨m2 x ⟨hx.1,hx.2.1,hx.2.2.1⟩,by simp [hx.2.2.2.1,hx.2.2.2.2]⟩
 exact List.all_eq_true.mp (List.all_eq_true.mp hfb2 a3 (m3 a3 ha3)) b3 (List.mem_filter.mpr ⟨m3 b3 hb3,by simp [h3]⟩)
def eM7 (e : Fin 7 × Fin 7) : Nat := Nat.lor (1 <<< e.1.val) (1 <<< e.2.val)
def hitM (em mask : Nat) : Bool := match Nat.beq (Nat.land em mask) 0 with | true => false | false => true
def eNec2 (a1 b1 a2 b2 em : Nat) : Bool := (hitM em a1&&hitM em b1)||(hitM em a2&&hitM em b2)||hitM em (Nat.lor a1 a2)
def eCov2 (a0 b0 a1 b1 a2 b2 em : Nat) : Bool := (hitM em a1&&hitM em b1)||(hitM em a2&&hitM em b2)||(hitM em a0&&hitM em b0&&hitM em (Nat.lor a1 a2))
def chkS2 (ems : List Nat) (a1 b1 a2 b2 x1 x2 x3 y1 y2 y3 : Nat) : Bool :=
 !(ems.all (eCov2 (Nat.xor 127 (Nat.lor (Nat.lor x1 x2) x3)) (Nat.xor 127 (Nat.lor (Nat.lor y1 y2) y3)) a1 b1 a2 b2))
def chkP7 (ems ms : List Nat) (i0 a1 b1 a2 b2 a3 b3 : Fin 7) : Bool :=
 let m0 := ms.getD i0.val 0;let ma1 := ms.getD a1.val 0;let mb1 := ms.getD b1.val 0
 let ma2 := ms.getD a2.val 0;let mb2 := ms.getD b2.val 0;let ma3 := ms.getD a3.val 0;let mb3 := ms.getD b3.val 0
 let u1 := Nat.lor ma1 mb1;let u2 := Nat.lor ma2 mb2;let u3 := Nat.lor ma3 mb3
 let A1 := Nat.xor 127 (Nat.lor m0 u2);let B1 := Nat.xor 127 (Nat.lor u1 u3)
 let A2 := Nat.xor 127 (Nat.lor m0 u1);let B2 := Nat.xor 127 (Nat.lor u2 u3)
 match ems.all (eNec2 A1 B1 A2 B2) with
 | false => true
 | true =>
  chkS2 ems A1 B1 A2 B2 ma1 ma2 ma3 mb1 mb2 mb3&&chkS2 ems A1 B1 A2 B2 ma1 ma2 mb3 mb1 mb2 ma3 &&
  chkS2 ems A1 B1 A2 B2 ma1 mb2 ma3 mb1 ma2 mb3&&chkS2 ems A1 B1 A2 B2 ma1 mb2 mb3 mb1 ma2 ma3 &&
  chkS2 ems A1 B1 A2 B2 mb1 ma2 ma3 ma1 mb2 mb3&&chkS2 ems A1 B1 A2 B2 mb1 ma2 mb3 ma1 mb2 ma3 &&
  chkS2 ems A1 B1 A2 B2 mb1 mb2 ma3 ma1 ma2 mb3&&chkS2 ems A1 B1 A2 B2 mb1 mb2 mb3 ma1 ma2 ma3
def noF2 (E : G 7) (ms : List Nat) : Bool := allP7 (chkP7 (E.map eM7) ms)
lemma tb_127 : ∀ v : Fin 7,(127 : Nat).testBit v.val = true := by decide +kernel
lemma hitM_e (e : Fin 7 × Fin 7) (A : F 7) (mask : Nat)
 (hs : ∀ v ∈ A,mask.testBit v.val = true) (hv : oV A (fun u => decide (u = e.1 ∨ u = e.2)) = true) : hitM (eM7 e) mask = true := by
 simp only [oV,decide_eq_true_eq] at hv;obtain ⟨v,hvA,hv12⟩ := hv
 have hem : (eM7 e).testBit v.val = true := hv12.elim (fun h => by rw [h];simp [eM7,Nat.shiftLeft_eq]) (fun h => by rw [h];simp [eM7,Nat.shiftLeft_eq])
 unfold hitM;cases hb : Nat.beq (Nat.land (eM7 e) mask) 0;rfl
 have := congrArg (fun n => n.testBit v.val) (Nat.eq_of_beq_eq_true hb);rw [tb_and,hem,hs v hvA,Nat.zero_testBit] at this;exact absurd this (by decide)
lemma f2_imp_ff (E : G 7) (hl : (mIMs 7 E).length = 7) (hf2 : noF2 E (mIMs 7 E) = true)
 (S : Fin 6 → F 7) (hc : ∀ x,eFn E x = f2E false false (fun k => oV (S k) x)) : False := by
 classical
 let ms := mIMs 7 E;have hml : ms.length = 7 := hl;have hnd : ms.Nodup := List.Nodup.filter _ List.nodup_range
 let mAt : Fin 7 → Nat := fun t => ms.getD t.val 0
 have hme : ∀ t : Fin 7,mAt t = ms[t.val]'(by omega) := fun t => List.getD_eq_getElem ms 0 (by omega)
 have hmm : ∀ t : Fin 7,mAt t ∈ ms := fun t => by rw [hme t];exact List.getElem_mem (by omega)
 have hmlt : ∀ t : Fin 7,mAt t < 2 ^ 7 := fun t => List.mem_range.mp (List.mem_filter.mp (hmm t)).1
 have hmax : ∀ t : Fin 7,isMIM 7 E (mAt t) = true := fun t => (List.mem_filter.mp (hmm t)).2
 let I : Fin 7 → F 7 := fun t => m2f (mAt t)
 have hIi : Function.Injective I := fun t1 t2 he => by
  have := m2f_inj (hmlt t1) (hmlt t2) he;rw [hme t1,hme t2] at this;exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp this)
 have hz : ∀ t : Fin 7,(f2TT false false).testBit (b6M (fun k => oV (S k) (iF (I t)))).val = false := fun t => by
  rw [tb_f2TT,m6_b6M,← hc];exact isIM_s E (mAt t) (Bool.and_eq_true _ _ ▸ hmax t).1
 have hex : ∀ t : Fin 7,∃ r : Fin 7,∀ k : Fin 6,oV (S k) (iF (I t)) = true → (f2MZ r).val.testBit k.val = true := fun t => by
  obtain ⟨z,hle,hmz⟩ := ex_mz_above (f2TT false false) (b6M fun k => oV (S k) (iF (I t))) (hz t)
  obtain ⟨r,rfl⟩ := (imz_f2_iff z).mp hmz
  exact ⟨r,fun k hk => hle k (by have := congrFun (m6_b6M fun j => oV (S j) (iF (I t))) k;simpa [m6,hk] using this)⟩
 let f : Fin 7 → Fin 7 := fun t => Classical.choose (hex t)
 have hfs : ∀ t k,oV (S k) (iF (I t)) = true → (f2MZ (f t)).val.testBit k.val = true := fun t => Classical.choose_spec (hex t)
 have hfi : Function.Injective f := fun t1 t2 hfe => by
  set r := f t1;have h2 : ∀ k,oV (S k) (iF (I t2)) = true → (f2MZ r).val.testBit k.val = true := hfe ▸ hfs t2
  have hle : ∀ k,oV (S k) (iF (I t1 ∪ I t2)) = true → m6 (f2MZ r) k = true := fun k hk => by
   rw [oV_iF_un,Bool.or_eq_true] at hk;exact hk.elim (hfs t1 k) (h2 k)
  have huf : eFn E (iF (I t1 ∪ I t2)) = false := by
   rw [hc];cases hv : f2E false false (fun k => oV (S k) (iF (I t1 ∪ I t2)))
   · rfl
   · exfalso;have h1 := f2E_mono _ (m6 (f2MZ r)) hle hv;rw [← tb_f2TT,f2MZ_z r] at h1;exact absurd h1 (by decide)
  exact hIi ((isMIM_s E (mAt t1) (hmax t1) _ Finset.subset_union_left huf).symm.trans (isMIM_s E (mAt t2) (hmax t2) _ Finset.subset_union_right huf))
 have hfb : Function.Bijective f := Finite.injective_iff_bijective.mp hfi
 let p0 : Fin 7 ≃ Fin 7 := (Equiv.ofBijective f hfb).symm
 have hp0 : ∀ r k,oV (S k) (iF (I (p0 r))) = true → (f2MZ r).val.testBit k.val = true := fun r k hk => by
  have hfp : f (p0 r) = r := Equiv.apply_symm_apply (Equiv.ofBijective f hfb) r
  have := hfs (p0 r) k hk;rwa [hfp] at this
 have hmain : ∀ (p : Fin 7 ≃ Fin 7) (T : Fin 6 → F 7),
   (∀ x,eFn E x = f2E false false (fun k => oV (T k) x)) →
   (∀ r k,oV (T k) (iF (I (p r))) = true → (f2MZ r).val.testBit k.val = true) →
   min (p 1) (p 2) < min (p 3) (p 4) → False := fun p T hTc hTs hmlt => by
  let i0 := p 0;let a1 := min (p 1) (p 2);let b1 := max (p 1) (p 2)
  let a2 := min (p 3) (p 4);let b2 := max (p 3) (p 4);let a3 := min (p 5) (p 6);let b3 := max (p 5) (p 6)
  have hm1 : (a1 = p 1 ∧ b1 = p 2) ∨ (a1 = p 2 ∧ b1 = p 1) := (le_total (p 1) (p 2)).elim (fun h => Or.inl ⟨min_eq_left h,max_eq_right h⟩) (fun h => Or.inr ⟨min_eq_right h,max_eq_left h⟩)
  have hm2 : (a2 = p 3 ∧ b2 = p 4) ∨ (a2 = p 4 ∧ b2 = p 3) := (le_total (p 3) (p 4)).elim (fun h => Or.inl ⟨min_eq_left h,max_eq_right h⟩) (fun h => Or.inr ⟨min_eq_right h,max_eq_left h⟩)
  have hm3 : (a3 = p 5 ∧ b3 = p 6) ∨ (a3 = p 6 ∧ b3 = p 5) := (le_total (p 5) (p 6)).elim (fun h => Or.inl ⟨min_eq_left h,max_eq_right h⟩) (fun h => Or.inr ⟨min_eq_right h,max_eq_left h⟩)
  have hltP : ∀ i j : Fin 7,i ≠ j → min (p i) (p j) < max (p i) (p j) := fun i j hij => lt_of_le_of_ne min_le_max fun he => by
   rcases le_total (p i) (p j) with h | h
   · rw [min_eq_left h,max_eq_right h] at he;exact hij (p.injective he)
   · rw [min_eq_right h,max_eq_left h] at he;exact hij.symm (p.injective he)
  have hnp : ∀ {x y : Fin 7} {i j k l : Fin 7},(x = p i ∨ x = p j) → (y = p k ∨ y = p l) →
    (h : i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l := by decide) → x ≠ y := fun hx hy h => by
   rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [h.1,h.2.1,h.2.2.1,h.2.2.2]
  have ha1_m : a1 = p 1 ∨ a1 = p 2 := hm1.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hb1_m : b1 = p 1 ∨ b1 = p 2 := hm1.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)
  have ha2_m : a2 = p 3 ∨ a2 = p 4 := hm2.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hb2_m : b2 = p 3 ∨ b2 = p 4 := hm2.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)
  have ha3_m : a3 = p 5 ∨ a3 = p 6 := hm3.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hb3_m : b3 = p 5 ∨ b3 = p 6 := hm3.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)
  have hi0_m : i0 = p 0 ∨ i0 = p 0 := Or.inl rfl
  have hchk : chkP7 (E.map eM7) ms i0 a1 b1 a2 b2 a3 b3 = true := allP7_s _ hf2 i0 a1 b1 a2 b2 a3 b3
   (hnp ha1_m hi0_m) (hnp hb1_m hi0_m) (hltP 1 2 (by decide))
   ⟨hnp ha2_m hi0_m,hnp ha2_m ha1_m,hnp ha2_m hb1_m⟩ hmlt
   ⟨hnp hb2_m hi0_m,hnp hb2_m ha1_m,hnp hb2_m hb1_m⟩ (hltP 3 4 (by decide))
   ⟨hnp ha3_m hi0_m,hnp ha3_m ha1_m,hnp ha3_m hb1_m,hnp ha3_m ha2_m,hnp ha3_m hb2_m⟩
   ⟨hnp hb3_m hi0_m,hnp hb3_m ha1_m,hnp hb3_m hb1_m,hnp hb3_m ha2_m,hnp hb3_m hb2_m⟩ (hltP 5 6 (by decide))
  have hd : ∀ (r : Fin 7) (k : Fin 6) (v : Fin 7),v ∈ T k → (hfl : (f2MZ r).val.testBit k.val = false := by decide) → (mAt (p r)).testBit v.val = false := fun r k v hvT hfl => by
   cases hb : (mAt (p r)).testBit v.val;rfl;exfalso
   have hor : oV (T k) (iF (I (p r))) = true := by simp only [oV,iF,decide_eq_true_eq];exact ⟨v,hvT,by simp [I,m2f,hb]⟩
   have := hTs r k hor;rw [hfl] at this;exact absurd this (by decide)
  have hu1 : Nat.lor (mAt a1) (mAt b1) = Nat.lor (mAt (p 1)) (mAt (p 2)) := hm1.elim (fun ⟨h1,h2⟩ => by rw [h1,h2]) (fun ⟨h1,h2⟩ => by rw [h1,h2];exact Nat.lor_comm _ _)
  have hu2 : Nat.lor (mAt a2) (mAt b2) = Nat.lor (mAt (p 3)) (mAt (p 4)) := hm2.elim (fun ⟨h1,h2⟩ => by rw [h1,h2]) (fun ⟨h1,h2⟩ => by rw [h1,h2];exact Nat.lor_comm _ _)
  have hu3 : Nat.lor (mAt a3) (mAt b3) = Nat.lor (mAt (p 5)) (mAt (p 6)) := hm3.elim (fun ⟨h1,h2⟩ => by rw [h1,h2]) (fun ⟨h1,h2⟩ => by rw [h1,h2];exact Nat.lor_comm _ _)
  let A1m := Nat.xor 127 (Nat.lor (mAt i0) (Nat.lor (mAt a2) (mAt b2)))
  let B1m := Nat.xor 127 (Nat.lor (Nat.lor (mAt a1) (mAt b1)) (Nat.lor (mAt a3) (mAt b3)))
  let A2m := Nat.xor 127 (Nat.lor (mAt i0) (Nat.lor (mAt a1) (mAt b1)))
  let B2m := Nat.xor 127 (Nat.lor (Nat.lor (mAt a2) (mAt b2)) (Nat.lor (mAt a3) (mAt b3)))
  let A0m := Nat.xor 127 (Nat.lor (Nat.lor (mAt (p 1)) (mAt (p 3))) (mAt (p 5)))
  let B0m := Nat.xor 127 (Nat.lor (Nat.lor (mAt (p 2)) (mAt (p 4))) (mAt (p 6)))
  have hA1 : ∀ v ∈ T 2,A1m.testBit v.val = true := fun v hv => by simp only [A1m,i0,hu2,tb_xor,tb_127,tb_or,hd 0 2 v hv,hd 3 2 v hv,hd 4 2 v hv];rfl
  have hB1 : ∀ v ∈ T 3,B1m.testBit v.val = true := fun v hv => by simp only [B1m,hu1,hu3,tb_xor,tb_127,tb_or,hd 1 3 v hv,hd 2 3 v hv,hd 5 3 v hv,hd 6 3 v hv];rfl
  have hA2 : ∀ v ∈ T 4,A2m.testBit v.val = true := fun v hv => by simp only [A2m,i0,hu1,tb_xor,tb_127,tb_or,hd 0 4 v hv,hd 1 4 v hv,hd 2 4 v hv];rfl
  have hB2 : ∀ v ∈ T 5,B2m.testBit v.val = true := fun v hv => by simp only [B2m,hu2,hu3,tb_xor,tb_127,tb_or,hd 3 5 v hv,hd 4 5 v hv,hd 5 5 v hv,hd 6 5 v hv];rfl
  have hA0 : ∀ v ∈ T 0,A0m.testBit v.val = true := fun v hv => by simp only [A0m,tb_xor,tb_127,tb_or,hd 1 0 v hv,hd 3 0 v hv,hd 5 0 v hv];rfl
  have hB0 : ∀ v ∈ T 1,B0m.testBit v.val = true := fun v hv => by simp only [B0m,tb_xor,tb_127,tb_or,hd 2 1 v hv,hd 4 1 v hv,hd 6 1 v hv];rfl
  have hA12 : ∀ v ∈ T 2 ∪ T 4,(Nat.lor A1m A2m).testBit v.val = true := fun v hv => by rw [tb_or,Bool.or_eq_true];exact (Finset.mem_union.mp hv).elim (fun h => Or.inl (hA1 v h)) (fun h => Or.inr (hA2 v h))
  have hallCov : (E.map eM7).all (eCov2 A0m B0m A1m B1m A2m B2m) = true := by
   rw [List.all_eq_true];intro em hem;obtain ⟨e,he,rfl⟩ := List.mem_map.mp hem
   have hedge : eFn E (fun v => decide (v = e.1 ∨ v = e.2)) = true := by unfold eFn;rw [List.any_eq_true];exact ⟨e,he,by simp⟩
   rw [hTc] at hedge;simp only [f2E,Bool.false_eq_true,↓reduceIte,Bool.or_eq_true,Bool.and_eq_true] at hedge
   unfold eCov2;simp only [Bool.or_eq_true,Bool.and_eq_true]
   rcases hedge with (⟨h1,h2⟩ | ⟨h1,h2⟩) | ⟨⟨h0a,h0b⟩,h12⟩
   · exact Or.inl (Or.inl ⟨hitM_e e (T 2) A1m hA1 h1,hitM_e e (T 3) B1m hB1 h2⟩)
   · exact Or.inl (Or.inr ⟨hitM_e e (T 4) A2m hA2 h1,hitM_e e (T 5) B2m hB2 h2⟩)
   · exact Or.inr ⟨⟨hitM_e e (T 0) A0m hA0 h0a,hitM_e e (T 1) B0m hB0 h0b⟩,hitM_e e (T 2 ∪ T 4) (Nat.lor A1m A2m) hA12 (by rw [oV_un,Bool.or_eq_true];exact h12)⟩
  have hallNec : (E.map eM7).all (eNec2 A1m B1m A2m B2m) = true := by
   rw [List.all_eq_true];intro em hem;have h := List.all_eq_true.mp hallCov em hem
   unfold eCov2 at h;unfold eNec2;simp only [Bool.or_eq_true,Bool.and_eq_true] at h ⊢
   rcases h with (h1 | h2) | ⟨_,h3⟩;exact Or.inl (Or.inl h1);exact Or.inl (Or.inr h2);exact Or.inr h3
  unfold chkP7 at hchk
  change (match (E.map eM7).all (eNec2 A1m B1m A2m B2m) with | false => true | true => _) = true at hchk
  rw [hallNec] at hchk;simp only [Bool.and_eq_true] at hchk
  have hsp : chkS2 (E.map eM7) A1m B1m A2m B2m (mAt (p 1)) (mAt (p 3)) (mAt (p 5)) (mAt (p 2)) (mAt (p 4)) (mAt (p 6)) = true := by
   rcases hm1 with ⟨h1a,h1b⟩ | ⟨h1a,h1b⟩ <;> rcases hm2 with ⟨h2a,h2b⟩ | ⟨h2a,h2b⟩ <;> rcases hm3 with ⟨h3a,h3b⟩ | ⟨h3a,h3b⟩ <;>
    rw [← h1a,← h1b,← h2a,← h2b,← h3a,← h3b]
   · exact hchk.1.1.1.1.1.1.1
   · exact hchk.1.1.1.1.1.1.2
   · exact hchk.1.1.1.1.1.2
   · exact hchk.1.1.1.1.2
   · exact hchk.1.1.1.2
   · exact hchk.1.1.2
   · exact hchk.1.2
   · exact hchk.2
  unfold chkS2 at hsp;change !((E.map eM7).all (eCov2 A0m B0m A1m B1m A2m B2m)) = true at hsp
  rw [hallCov] at hsp;exact absurd hsp (by decide)
 have hne_m : min (p0 1) (p0 2) ≠ min (p0 3) (p0 4) := fun he => by
  rcases le_total (p0 1) (p0 2) with h1 | h1 <;> rcases le_total (p0 3) (p0 4) with h2 | h2
  · rw [min_eq_left h1,min_eq_left h2] at he;exact absurd (p0.injective he) (by decide)
  · rw [min_eq_left h1,min_eq_right h2] at he;exact absurd (p0.injective he) (by decide)
  · rw [min_eq_right h1,min_eq_left h2] at he;exact absurd (p0.injective he) (by decide)
  · rw [min_eq_right h1,min_eq_right h2] at he;exact absurd (p0.injective he) (by decide)
 rcases lt_or_gt_of_ne hne_m with hlt | hgt
 · exact hmain p0 S hc hp0 hlt
 · let swR : Fin 7 ≃ Fin 7 :=
    { toFun := fun r => match r.val with | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | _ => r
      invFun := fun r => match r.val with | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | _ => r
      left_inv := fun r => by fin_cases r <;> rfl
      right_inv := fun r => by fin_cases r <;> rfl }
   let S1 : Fin 6 → F 7 := fun k => match k.val with | 2 => S 4 | 3 => S 5 | 4 => S 2 | 5 => S 3 | _ => S k
   have hS1c : ∀ x,eFn E x = f2E false false (fun k => oV (S1 k) x) := fun x => by
    rw [hc x];have hS : S1 0 = S 0 ∧ S1 1 = S 1 ∧ S1 2 = S 4 ∧ S1 3 = S 5 ∧ S1 4 = S 2 ∧ S1 5 = S 3 := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
    simp only [f2E,Bool.false_eq_true,↓reduceIte,hS.1,hS.2.1,hS.2.2.1,hS.2.2.2.1,hS.2.2.2.2.1,hS.2.2.2.2.2]
    cases oV (S 0) x <;> cases oV (S 1) x <;> cases oV (S 2) x <;> cases oV (S 3) x <;> cases oV (S 4) x <;> cases oV (S 5) x <;> rfl
   have hS1s : ∀ r k,oV (S1 k) (iF (I ((swR.trans p0) r))) = true → (f2MZ r).val.testBit k.val = true := fun r k hk => by
    have hsb : ∀ (r : Fin 7) (k : Fin 6),(f2MZ (swR r)).val.testBit (match k.val with | 2 => 4 | 3 => 5 | 4 => 2 | 5 => 3 | _ => k : Fin 6).val = (f2MZ r).val.testBit k.val := by decide +kernel
    have hke : S1 k = S (match k.val with | 2 => 4 | 3 => 5 | 4 => 2 | 5 => 3 | _ => k) := by fin_cases k <;> rfl
    rw [hke] at hk;rw [← hsb r k];exact hp0 (swR r) _ hk
   exact hmain (swR.trans p0) S1 hS1c hS1s hgt
lemma f2_imp (E : G 7) (hl : (mIMs 7 E).length = 7) (hf2 : noF2 E (mIMs 7 E) = true)
 (s1 s2 : Bool) (S : Fin 6 → F 7) (hc : ∀ x,eFn E x = f2E s1 s2 (fun k => oV (S k) x)) : False := by
 let S' : Fin 6 → F 7 := fun k => match k.val with
  | 0 => S 0 | 1 => S 1 | 2 => if s1 then S 3 else S 2 | 3 => if s1 then S 2 else S 3 | 4 => if s2 then S 5 else S 4 | _ => if s2 then S 4 else S 5
 apply f2_imp_ff E hl hf2 S';intro x;rw [hc x]
 have hS : S' 0 = S 0 ∧ S' 1 = S 1 ∧ S' 2 = (if s1 then S 3 else S 2) ∧ S' 3 = (if s1 then S 2 else S 3) ∧
  S' 4 = (if s2 then S 5 else S 4) ∧ S' 5 = (if s2 then S 4 else S 5) := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
 simp only [f2E,hS.1,hS.2.1,hS.2.2.1,hS.2.2.2.1,hS.2.2.2.2.1,hS.2.2.2.2.2]
 cases s1 <;> cases s2 <;> simp [Bool.and_comm]
lemma setup3 {n : ℕ} (E : G n) (hl : noLoop E = true) (f : (Fin n → Bool) → Bool) (hf : ∀ x,f x = eFn E x)
 (C : Circuit) (hm : Monotone2 C) (he : ∀ x,C.eval (List.ofFn x) = f x) (h3 : andCount C ≤ 3) :
 ∃ (w : Fin 512) (S : Fin 6 → F n),(andCount C ≤ 2 → w.val.testBit 8 = false) ∧ ∀ x,eFn E x = eW w (fun k => oV (S k) x) := by
 have he' : ∀ x,C.eval (List.ofFn x) = eFn E x := fun x => (he x).trans (hf x)
 obtain ⟨w,S,O,ho2,hc⟩ := compile_le_three C hm (by rw [he'];exact eFn_false E) h3
 exact ⟨w,S,ho2,outV_emp E hl w S O fun x => by rw [← he' x,hc x]⟩
theorem mk3 {n : ℕ} (E : G n) {f : (Fin n → Bool) → Bool}
 (C : Circuit) (hm : Monotone2 C) (he : ∀ x,C.eval (List.ofFn x) = f x)
 (hf : ∀ x,f x = eFn E x := by intro x;simp [eFn,Bool.or_assoc])
 (h : noLoop E = true ∧ 5 ≤ (mIMs n E).length := by decide +kernel) : 3 ≤ andCount C := by
 by_contra hlt;obtain ⟨w,S,ho2,hc⟩ := setup3 E h.1 f hf C hm he (by omega)
 have hle := mIMs_le_cMZ E w S hc;have h8 := ho2 (by omega)
 rcases w_cases w with ⟨_,ht⟩ | ⟨_,ht⟩ | ⟨_,h4⟩ <;> [rw [h8] at ht;rw [h8] at ht;have := h4 h8] <;> simp_all;omega
theorem mk4_9 {n : ℕ} (E : G n) {f : (Fin n → Bool) → Bool}
 (C : Circuit) (hm : Monotone2 C) (he : ∀ x,C.eval (List.ofFn x) = f x)
 (hf : ∀ x,f x = eFn E x := by intro x;simp [eFn,Bool.or_assoc])
 (h : noLoop E = true ∧ 9 ≤ (mIMs n E).length := by decide +kernel) : 4 ≤ andCount C := by
 by_contra hlt;obtain ⟨w,S,_,hc⟩ := setup3 E h.1 f hf C hm he (by omega)
 have hle := mIMs_le_cMZ E w S hc
 rcases w_cases w with ⟨h1,_⟩ | ⟨h2,_⟩ | ⟨h6,_⟩
 · rw [h1,cMZ_f1] at hle;omega
 · rcases h2 with h' | h' | h' | h' <;> simp [h',cMZ_f2.1,cMZ_f2.2.1,cMZ_f2.2.2.1,cMZ_f2.2.2.2] at hle <;> omega
 · omega
theorem mk4_8 {n : ℕ} (E : G n) {f : (Fin n → Bool) → Bool}
 (C : Circuit) (hm : Monotone2 C) (he : ∀ x,C.eval (List.ofFn x) = f x)
 (hf : ∀ x,f x = eFn E x := by intro x;simp [eFn,Bool.or_assoc])
 (h : noLoop E = true ∧ 8 ≤ (mIMs n E).length ∧ c4F E = true ∧ noV3 E = true := by decide +kernel)
 (hn : 0 < n := by decide) : 4 ≤ andCount C := by
 by_contra hlt;obtain ⟨w,S,_,hc⟩ := setup3 E h.1 f hf C hm he (by omega)
 have hle := mIMs_le_cMZ E w S hc
 rcases w_cases w with ⟨h1,_⟩ | ⟨h2,_⟩ | ⟨h6,_⟩
 · exact f1_imp hn E h.1 h.2.2.1 h.2.2.2 S fun x => (hc x).trans (w_eq_f1 w h1 _)
 · rcases h2 with h' | h' | h' | h' <;> simp [h',cMZ_f2.1,cMZ_f2.2.1,cMZ_f2.2.2.1,cMZ_f2.2.2.2] at hle <;> omega
 · omega
theorem mk4_7 (E : G 7) {f : (Fin 7 → Bool) → Bool}
 (C : Circuit) (hm : Monotone2 C) (he : ∀ x,C.eval (List.ofFn x) = f x)
 (hf : ∀ x,f x = eFn E x := by intro x;simp [eFn,Bool.or_assoc])
 (h : noLoop E = true ∧ (mIMs 7 E).length = 7 ∧ c4F E = true ∧ noV3 E = true ∧ noF2 E (mIMs 7 E) = true := by decide +kernel) : 4 ≤ andCount C := by
 by_contra hlt;obtain ⟨w,S,_,hc⟩ := setup3 E h.1 f hf C hm he (by omega)
 have hle := mIMs_le_cMZ E w S hc
 rcases w_cases w with ⟨h1,_⟩ | ⟨h2,_⟩ | ⟨h6,_⟩
 · exact f1_imp (by decide) E h.1 h.2.2.1 h.2.2.2.1 S fun x => (hc x).trans (w_eq_f1 w h1 _)
 · rcases h2 with h' | h' | h' | h' <;> exact f2_imp E h.2.1 h.2.2.2.2 _ _ S fun x => (hc x).trans (w_eq_f2 w _ _ h' _)
 · omega
theorem and_bound_0 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 4 ≤ andCount C := fun C m e => mk4_8 [(0,1),(0,2),(0,3),(1,2),(3,4),(3,5),(4,5)] C m e
theorem and_bound_1 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 4 ≤ andCount C := fun C m e => mk4_9 [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4),(5,6)] C m e
theorem and_bound_2 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) x) → 4 ≤ andCount C := fun C m e => mk4_9 [(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(4,6)] C m e
theorem and_bound_3 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 4 ≤ andCount C := fun C m e => mk4_8 [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,6)] C m e
theorem and_bound_4 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 4 ≤ andCount C := fun C m e => mk4_8 [(0,1),(0,2),(0,3),(1,2),(3,4),(3,5),(4,6)] C m e
theorem and_bound_5 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x) → 4 ≤ andCount C := fun C m e => mk4_8 [(0,1),(0,2),(0,3),(1,2),(3,4),(4,5),(5,6)] C m e
theorem and_bound_6 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 4 ≤ andCount C := fun C m e => mk4_9 [(0,1),(0,2),(0,3),(1,2),(4,5),(4,6),(5,6)] C m e
theorem and_bound_7 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 4 ≤ andCount C := fun C m e => mk4_8 [(0,1),(0,2),(0,3),(1,4),(2,5),(3,6),(4,5)] C m e
theorem and_bound_8 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 4 ≤ andCount C := fun C m e => mk4_7 [(0,1),(0,2),(1,3),(2,4),(3,5),(4,6),(5,6)] C m e
theorem and_bound_9 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) x) → 3 ≤ andCount C := fun C m e => mk3 [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(3,4)] C m e
theorem and_bound_10 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) x) → 3 ≤ andCount C := fun C m e => mk3 [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,6),(3,4)] C m e
theorem and_bound_11 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 4 ≤ andCount C := fun C m e => mk4_9 [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(3,4),(5,6)] C m e
theorem and_bound_12 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) x) → 3 ≤ andCount C := fun C m e => mk3 [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(1,6),(3,4)] C m e
theorem and_bound_13 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) x) → 4 ≤ andCount C := fun C m e => mk4_7 [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(2,6),(3,4)] C m e
theorem and_bound_14 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) x) → 3 ≤ andCount C := fun C m e => mk3 [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(3,6)] C m e
theorem and_bound_15 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) x) → 4 ≤ andCount C := fun C m e => mk4_8 [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(5,6)] C m e
theorem and_bound_16 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 3 ≤ andCount C := fun C m e => mk3 [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,6),(5,6)] C m e
theorem and_bound_17 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 4 ≤ andCount C := fun C m e => mk4_8 [(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(3,6),(5,6)] C m e
theorem and_bound_18 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 4 ≤ andCount C := fun C m e => mk4_8 [(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(4,6),(5,6)] C m e
theorem and_bound_19 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) x) → 4 ≤ andCount C := fun C m e => mk4_7 [(0,1),(0,2),(0,3),(1,2),(1,4),(2,5),(3,6),(4,6)] C m e
theorem and_bound_20 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 4 ≤ andCount C := fun C m e => mk4_7 [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(3,6),(4,5)] C m e
theorem and_bound_21 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 4 ≤ andCount C := fun C m e => mk4_8 [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(3,6),(5,6)] C m e
theorem and_bound_22 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) x) → 3 ≤ andCount C := fun C m e => mk3 [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,5),(5,6)] C m e
theorem and_bound_23 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 4 ≤ andCount C := fun C m e => mk4_7 [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,6),(5,6)] C m e
theorem and_bound_24 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 4 ≤ andCount C := fun C m e => mk4_9 [(0,1),(0,2),(0,3),(1,2),(3,4),(4,5),(4,6),(5,6)] C m e
theorem and_bound_25 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) x) → 4 ≤ andCount C := fun C m e => mk4_7 [(0,1),(0,2),(0,3),(1,4),(2,5),(3,6),(4,5),(4,6)] C m e
theorem and_bound_26 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 4 ≤ andCount C := fun C m e => mk4_9 [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(3,4),(5,6)] C m e
theorem and_bound_27 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) x) → 4 ≤ andCount C := fun C m e => mk4_8 [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(1,6),(3,4),(5,6)] C m e
theorem and_bound_28 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) x) → 4 ≤ andCount C := fun C m e => mk4_7 [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(3,6),(5,6)] C m e
theorem and_bound_29 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) x) → 4 ≤ andCount C := fun C m e => mk4_7 [(0,1),(0,2),(0,3),(1,2),(1,4),(2,5),(3,6),(4,6),(5,6)] C m e
theorem and_bound_30 : ∀ C : Circuit, Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) x) → 4 ≤ andCount C := fun C m e => mk4_8 [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(3,6),(4,5),(5,6)] C m e
end AndPart

namespace OrYF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-!
# Soundness framework for `OrCostYF`

Abstract meet/run calculus, circuit compilation, bitmask (`Nat`) representation on `Y_F`,
lexicographically minimal runs, pruning soundness (`isOnEdges`, operand restriction,
`usesLast` commutation, stabilizer `Aut(H, F)`), 1-stage and 2-stage cut + probe soundness,
terminal `M_d` soundness, base cases (`|E| ≤ 2`, `C_4`-free max-degree-2 graphs), and
peel-and-embed reductions.
-/

/-! ## Section 1: Abstract Meet and Run calculus -/

inductive Meet {X : Type} (B : Set (Set X)) : Set X → Prop
  | atom {f} : f ∈ B → Meet B f
  | top : Meet B Set.univ
  | bot : Meet B ∅
  | inter {f g} : Meet B f → Meet B g → Meet B (f ∩ g)

inductive Run {X : Type} : Set (Set X) → ℕ → Set X → Prop
  | done {B f} : Meet B f → Run B 0 f
  | add {B a b k f} : Meet B a → Meet B b → Run (insert (a ∪ b) B) k f → Run B (k + 1) f

theorem mapMeet {X Y : Type} {B : Set (Set X)} {D : Set (Set Y)} (π : Y → X)
    (atoms : ∀ f ∈ B, Meet D (π ⁻¹' f)) {f} (h : Meet B f) : Meet D (π ⁻¹' f) := by
  induction h with
  | atom hf => exact atoms _ hf
  | top => exact Meet.top
  | bot => exact Meet.bot
  | inter _ _ hi hj => exact hi.inter hj

theorem weaken {X : Type} {B D : Set (Set X)} (hd : B ⊆ D) {f}
    (h : Meet B f) : Meet D f :=
  mapMeet id (fun _ hf => Meet.atom (hd hf)) h

theorem freeMap {X Y : Type} {B : Set (Set X)} {D : Set (Set Y)} (π : Y → X)
    (atoms : ∀ f ∈ B, Meet D (π ⁻¹' f)) {k f} (h : Run B k f) : Run D k (π ⁻¹' f) := by
  induction h generalizing D with
  | done hf => exact Run.done (mapMeet π atoms hf)
  | @add B a b k f ha hb _ ih =>
    apply Run.add (mapMeet π atoms ha) (mapMeet π atoms hb)
    apply ih
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · exact Meet.atom (Set.mem_insert _ _)
    · exact weaken (Set.subset_insert _ _) (atoms _ hg)

theorem run_weaken {X : Type} {B D : Set (Set X)} (hd : B ⊆ D) {k f}
    (h : Run B k f) : Run D k f :=
  freeMap id (fun _ hf => Meet.atom (hd hf)) h

theorem run_succ {X : Type} {B : Set (Set X)} {k f} (h : Run B k f) : Run B (k + 1) f :=
  Run.add Meet.bot Meet.bot (run_weaken (Set.subset_insert _ _) h)

def Good {X Y : Type} (π : Y → X) (p q : X) (f : Set X) : Prop :=
  (p ∈ f ↔ q ∈ f) ∨ π ⁻¹' f = ∅

theorem meetGood {X Y : Type} {B : Set (Set X)} {π : Y → X} {p q : X}
    (atoms : ∀ f ∈ B, Good π p q f) {f} (h : Meet B f) : Good π p q f := by
  induction h with
  | atom h => exact atoms _ h
  | top => exact Or.inl Iff.rfl
  | bot => exact Or.inr rfl
  | inter _ _ ih jh =>
    rcases ih with h | h
    · rcases jh with j | j
      · exact Or.inl (and_congr h j)
      · exact Or.inr (by rw [Set.preimage_inter, j, Set.inter_empty])
    · exact Or.inr (by rw [Set.preimage_inter, h, Set.empty_inter])

theorem paidMap {X Y : Type} {B : Set (Set X)} {D : Set (Set Y)}
    (π : Y → X) (p q : X) (atoms : ∀ f ∈ B, Meet D (π ⁻¹' f))
    (good : ∀ f ∈ B, Good π p q f) {k f} (h : Run B k f) (bad : ¬ Good π p q f) :
    ∃ j < k, Run D j (π ⁻¹' f) := by
  classical
  induction h generalizing D with
  | done hf => exact (bad (meetGood good hf)).elim
  | @add B a b k f ha hb tail ih =>
    have aa := mapMeet π atoms ha
    have ab := mapMeet π atoms hb
    by_cases gg : Good π p q (a ∪ b)
    · let D' := insert ((π ⁻¹' a) ∪ (π ⁻¹' b)) D
      have m : ∀ g ∈ insert (a ∪ b) B, Meet D' (π ⁻¹' g) := by
        intro g hg
        rcases Set.mem_insert_iff.mp hg with rfl | hg
        · exact Meet.atom (Set.mem_insert _ _)
        · exact weaken (Set.subset_insert _ _) (atoms _ hg)
      obtain ⟨j, hj, hr⟩ := ih m (fun g hg => (Set.mem_insert_iff.mp hg).elim
        (fun e => e ▸ gg) (good g)) bad
      exact ⟨j + 1, by omega, Run.add aa ab hr⟩
    · have bypass : Meet D (π ⁻¹' (a ∪ b)) := by
        rcases meetGood good ha with h | h
        · rcases meetGood good hb with z | z
          · exact (gg (Or.inl (or_congr h z))).elim
          · simpa [Set.preimage_union, z] using aa
        · simpa [Set.preimage_union, h] using ab
      exact ⟨k, by omega, freeMap π (fun g hg => (Set.mem_insert_iff.mp hg).elim
        (fun e => e ▸ bypass) (atoms g)) tail⟩

/-! ### Monotonicity and `OnEdges` downward-replacement -/

def UpClosed {X : Type} (le : X → X → Prop) (f : Set X) : Prop :=
  ∀ x y, le x y → x ∈ f → y ∈ f

theorem meet_upClosed {X : Type} {le : X → X → Prop} {B : Set (Set X)}
    (hB : ∀ x ∈ B, UpClosed le x) {f : Set X} (hf : Meet B f) : UpClosed le f := by
  induction hf with
  | atom hx => exact hB _ hx
  | top => intro _ _ _ _; trivial
  | bot => intro _ _ _ hx; exact hx.elim
  | inter _ _ ih1 ih2 => intro x y hxy ⟨h1, h2⟩; exact ⟨ih1 x y hxy h1, ih2 x y hxy h2⟩

theorem run_upClosed {X : Type} {le : X → X → Prop} {B : Set (Set X)}
    (hB : ∀ x ∈ B, UpClosed le x) {k : ℕ} {f : Set X} (hr : Run B k f) : UpClosed le f := by
  induction hr with
  | done hf => exact meet_upClosed hB hf
  | @add B a b k f ha hb _ ih =>
    apply ih
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · intro x y hxy hx
      rcases hx with h1 | h2
      · exact Or.inl (meet_upClosed hB ha x y hxy h1)
      · exact Or.inr (meet_upClosed hB hb x y hxy h2)
    · exact hB g hg

theorem meet_replaceBelow {X : Type} {B D : Set (Set X)} {S : Set X}
    (hmap : ∀ x ∈ B, ∃ x', Meet D x' ∧ x' ⊆ x ∧ x' ∩ S = x ∩ S)
    {f : Set X} (hf : Meet B f) :
    ∃ f', Meet D f' ∧ f' ⊆ f ∧ f' ∩ S = f ∩ S := by
  induction hf with
  | atom hx => exact hmap _ hx
  | top => exact ⟨Set.univ, Meet.top, Set.Subset.rfl, rfl⟩
  | bot => exact ⟨∅, Meet.bot, Set.Subset.rfl, rfl⟩
  | inter _ _ ih1 ih2 =>
    obtain ⟨f1', hm1, hs1, he1⟩ := ih1
    obtain ⟨f2', hm2, hs2, he2⟩ := ih2
    refine ⟨f1' ∩ f2', hm1.inter hm2, Set.inter_subset_inter hs1 hs2, ?_⟩
    ext x
    have h1 := Set.ext_iff.mp he1 x
    have h2 := Set.ext_iff.mp he2 x
    simp only [Set.mem_inter_iff] at h1 h2 ⊢
    tauto

theorem run_replaceBelow {X : Type} {B D : Set (Set X)} {S : Set X}
    (hmap : ∀ x ∈ B, ∃ x', Meet D x' ∧ x' ⊆ x ∧ x' ∩ S = x ∩ S)
    {k : ℕ} {f : Set X} (hr : Run B k f) :
    ∃ f', Run D k f' ∧ f' ⊆ f ∧ f' ∩ S = f ∩ S := by
  induction hr generalizing D with
  | done hf =>
    obtain ⟨f', hm, hs, he⟩ := meet_replaceBelow hmap hf
    exact ⟨f', Run.done hm, hs, he⟩
  | @add B a b k f ha hb _ ih =>
    obtain ⟨a', hma, hsa, hea⟩ := meet_replaceBelow hmap ha
    obtain ⟨b', hmb, hsb, heb⟩ := meet_replaceBelow hmap hb
    let D' := insert (a' ∪ b') D
    have hmap' : ∀ x ∈ insert (a ∪ b) B, ∃ x', Meet D' x' ∧ x' ⊆ x ∧ x' ∩ S = x ∩ S := by
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · refine ⟨a' ∪ b', Meet.atom (Set.mem_insert _ _), Set.union_subset_union hsa hsb, ?_⟩
        rw [Set.union_inter_distrib_right, Set.union_inter_distrib_right, hea, heb]
      · obtain ⟨x', hmx, hsx, hex⟩ := hmap x hx
        exact ⟨x', weaken (Set.subset_insert _ _) hmx, hsx, hex⟩
    obtain ⟨f', hrf', hsf', hef'⟩ := ih hmap'
    exact ⟨f', Run.add hma hmb hrf', hsf', hef'⟩

theorem run_replaceBelow_upClosed {X : Type} {le : X → X → Prop}
    {B D : Set (Set X)} {S target : Set X}
    (hSt : S ⊆ target)
    (hclose : ∀ f, UpClosed le f → S ⊆ f → target ⊆ f)
    (hD : ∀ x ∈ D, UpClosed le x)
    (hmap : ∀ x ∈ B, ∃ x', Meet D x' ∧ x' ⊆ x ∧ x' ∩ S = x ∩ S)
    {k : ℕ} (hr : Run B k target) :
    Run D k target := by
  obtain ⟨f', hrf', hsub, heq⟩ := run_replaceBelow hmap hr
  have hup : UpClosed le f' := run_upClosed hD hrf'
  have hSf' : S ⊆ f' := by
    intro x hx
    have : x ∈ target ∩ S := ⟨hSt hx, hx⟩
    rw [← heq] at this
    exact this.1
  have htf' : target ⊆ f' := hclose f' hup hSf'
  have : f' = target := Set.Subset.antisymm hsub htf'
  exact this ▸ hrf'

/-! ## Section 2: Bitmask (`Nat`) Encoding of States `(n, H, F)` -/

def mkBitmask : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | k + 1, p => if p k then mkBitmask k p ||| (1 <<< k) else mkBitmask k p

theorem testBit_one_shiftLeft (k s : ℕ) : (1 <<< k).testBit s = decide (k = s) := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]

theorem testBit_mkBitmask (N : ℕ) (p : ℕ → Bool) (s : ℕ) :
    (mkBitmask N p).testBit s = (decide (s < N) && p s) := by
  induction N with
  | zero => simp [mkBitmask]
  | succ k ih =>
    simp only [mkBitmask]
    split_ifs with hpk
    · rw [Nat.testBit_or, ih, testBit_one_shiftLeft]
      by_cases hlt : s < k
      · have hne : k ≠ s := by omega
        have hlt' : s < k + 1 := by omega
        simp [hlt, hlt', hne]
      · by_cases heq : k = s
        · subst heq; simp [hpk]
        · have hlt' : ¬ (s < k + 1) := by omega
          simp [hlt, hlt', heq]
    · rw [ih]
      by_cases hlt : s < k
      · have hlt' : s < k + 1 := by omega
        simp [hlt, hlt']
      · by_cases heq : k = s
        · subst heq; simp [hpk]
        · have hlt' : ¬ (s < k + 1) := by omega
          simp [hlt, hlt']

theorem mkBitmask_testBit_lt {N : ℕ} {p : ℕ → Bool} {s : ℕ}
    (h : (mkBitmask N p).testBit s = true) : s < N := by
  rw [testBit_mkBitmask, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

def hasEdge (E : List (ℕ × ℕ)) (s : ℕ) : Bool :=
  E.any (fun e => s.testBit e.1 && s.testBit e.2)

theorem hasEdge_eq_true (E : List (ℕ × ℕ)) (s : ℕ) :
    hasEdge E s = true ↔ ∃ e ∈ E, s.testBit e.1 = true ∧ s.testBit e.2 = true := by
  simp [hasEdge]

def univYF (n : ℕ) (F : List (ℕ × ℕ)) : ℕ :=
  mkBitmask (2 ^ n) (fun s => !hasEdge F s)

def ttVarYF (n v maskYF : ℕ) : ℕ :=
  mkBitmask (2 ^ n) (fun s => maskYF.testBit s && s.testBit v)

def rawYF (n : ℕ) (maskYF : ℕ) : List ℕ :=
  (List.range n).map (fun v => ttVarYF n v maskYF)

def edgeTTYF (n : ℕ) (H : List (ℕ × ℕ)) (maskYF : ℕ) : ℕ :=
  mkBitmask (2 ^ n) (fun s => maskYF.testBit s && hasEdge H s)

def edgePtsMaskYF (H : List (ℕ × ℕ)) : ℕ :=
  H.foldl (fun acc e => acc ||| (1 <<< ((1 <<< e.1) ||| (1 <<< e.2)))) 0

def ttNeedYF (n a maskYF : ℕ) : ℕ :=
  mkBitmask (2 ^ n) (fun s => maskYF.testBit s && ((s &&& a) == a))

def masksTTYF (n : ℕ) (H : List (ℕ × ℕ)) (maskYF : ℕ) : List ℕ :=
  (0 :: (List.range n).map (fun v => 1 <<< v) ++
    H.map (fun e => (1 <<< e.1) ||| (1 <<< e.2))).map (fun m => ttNeedYF n m maskYF)

def undirEq (e₁ e₂ : ℕ × ℕ) : Bool :=
  (e₁.1 == e₂.1 && e₁.2 == e₂.2) || (e₁.1 == e₂.2 && e₁.2 == e₂.1)

def ValidState (n : ℕ) (H F : List (ℕ × ℕ)) : Prop :=
  (∀ e ∈ H, e.1 < n ∧ e.2 < n ∧ e.1 ≠ e.2) ∧
  (∀ e ∈ F, e.1 < n ∧ e.2 < n ∧ e.1 ≠ e.2) ∧
  (∀ e ∈ H, ∀ f ∈ F, undirEq e f = false)

def NoDupEdges (H : List (ℕ × ℕ)) : Prop :=
  H.Pairwise (fun e₁ e₂ => undirEq e₁ e₂ = false)

instance (n : ℕ) (H F : List (ℕ × ℕ)) : Decidable (ValidState n H F) := by
  unfold ValidState; infer_instance

instance (H : List (ℕ × ℕ)) : Decidable (NoDupEdges H) := by
  unfold NoDupEdges; infer_instance

theorem testBit_univYF (n : ℕ) (F : List (ℕ × ℕ)) (s : ℕ) :
    (univYF n F).testBit s = (decide (s < 2 ^ n) && !hasEdge F s) :=
  testBit_mkBitmask (2 ^ n) _ s

theorem univYF_testBit_lt {n : ℕ} {F : List (ℕ × ℕ)} {s : ℕ}
    (h : (univYF n F).testBit s = true) : s < 2 ^ n :=
  mkBitmask_testBit_lt h

theorem testBit_ttVarYF {n v maskYF : ℕ} (hM : ∀ s, maskYF.testBit s = true → s < 2 ^ n) (s : ℕ) :
    (ttVarYF n v maskYF).testBit s = (maskYF.testBit s && s.testBit v) := by
  rw [ttVarYF, testBit_mkBitmask]
  by_cases hm : maskYF.testBit s = true
  · simp [hm, hM s hm]
  · simp [hm]

theorem testBit_edgeTTYF {n : ℕ} {H : List (ℕ × ℕ)} {maskYF : ℕ}
    (hM : ∀ s, maskYF.testBit s = true → s < 2 ^ n) (s : ℕ) :
    (edgeTTYF n H maskYF).testBit s = (maskYF.testBit s && hasEdge H s) := by
  rw [edgeTTYF, testBit_mkBitmask]
  by_cases hm : maskYF.testBit s = true
  · simp [hm, hM s hm]
  · simp [hm]

theorem testBit_ttNeedYF {n a maskYF : ℕ}
    (hM : ∀ s, maskYF.testBit s = true → s < 2 ^ n) (s : ℕ) :
    (ttNeedYF n a maskYF).testBit s = (maskYF.testBit s && ((s &&& a) == a)) := by
  rw [ttNeedYF, testBit_mkBitmask]
  by_cases hm : maskYF.testBit s = true
  · simp [hm, hM s hm]
  · simp [hm]

theorem testBit_edgePtsMaskYF_aux (H : List (ℕ × ℕ)) (acc s : ℕ) :
    (H.foldl (fun a e => a ||| (1 <<< ((1 <<< e.1) ||| (1 <<< e.2)))) acc).testBit s =
      (acc.testBit s || H.any (fun e => decide (((1 <<< e.1) ||| (1 <<< e.2)) = s))) := by
  induction H generalizing acc with
  | nil => simp
  | cons e rest ih =>
    simp only [List.foldl_cons, List.any_cons]
    rw [ih, Nat.testBit_or, testBit_one_shiftLeft, Bool.or_assoc]

theorem testBit_edgePtsMaskYF (H : List (ℕ × ℕ)) (s : ℕ) :
    (edgePtsMaskYF H).testBit s = H.any (fun e => decide (((1 <<< e.1) ||| (1 <<< e.2)) = s)) := by
  simpa [edgePtsMaskYF] using testBit_edgePtsMaskYF_aux H 0 s

theorem twoBit_lt_two_pow {n u v : ℕ} (hu : u < n) (hv : v < n) :
    ((1 <<< u) ||| (1 <<< v)) < 2 ^ n := by
  have h1 : (1 <<< u) < 2 ^ n := by
    rw [Nat.shiftLeft_eq, one_mul]; exact Nat.pow_lt_pow_right (by omega) hu
  have h2 : (1 <<< v) < 2 ^ n := by
    rw [Nat.shiftLeft_eq, one_mul]; exact Nat.pow_lt_pow_right (by omega) hv
  exact Nat.or_lt_two_pow h1 h2

theorem oneBit_lt_two_pow {n u : ℕ} (hu : u < n) : (1 <<< u) < 2 ^ n := by
  rw [Nat.shiftLeft_eq, one_mul]; exact Nat.pow_lt_pow_right (by omega) hu

theorem twoBit_testBit (u v w : ℕ) :
    (((1 <<< u) ||| (1 <<< v)).testBit w = true) ↔ w = u ∨ w = v := by
  rw [Nat.testBit_or, testBit_one_shiftLeft, testBit_one_shiftLeft, Bool.or_eq_true,
    decide_eq_true_eq, decide_eq_true_eq]
  tauto

theorem edgePt_mem_univYF {n : ℕ} {H F : List (ℕ × ℕ)} (hv : ValidState n H F)
    {e : ℕ × ℕ} (he : e ∈ H) :
    (univYF n F).testBit ((1 <<< e.1) ||| (1 <<< e.2)) = true := by
  rcases hv with ⟨hH, hF, hdisj⟩
  obtain ⟨hu, hv', hne⟩ := hH e he
  rw [testBit_univYF, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  refine ⟨twoBit_lt_two_pow hu hv', ?_⟩
  rw [Bool.eq_false_iff]
  intro hf
  rw [hasEdge_eq_true] at hf
  obtain ⟨f, hfmem, hf1, hf2⟩ := hf
  rw [twoBit_testBit] at hf1 hf2
  obtain ⟨_, _, hfne⟩ := hF f hfmem
  have hd := hdisj e he f hfmem
  simp only [undirEq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne] at hd
  rcases hf1 with h1 | h1 <;> rcases hf2 with h2 | h2
  · exact hfne (h1.trans h2.symm)
  · rcases hd.1 with h | h <;> exact h (by omega)
  · rcases hd.2 with h | h <;> exact h (by omega)
  · exact hfne (h1.trans h2.symm)

theorem edgePt_mem_edgeTTYF {n : ℕ} {H F : List (ℕ × ℕ)} (hv : ValidState n H F)
    {e : ℕ × ℕ} (he : e ∈ H) :
    (edgeTTYF n H (univYF n F)).testBit ((1 <<< e.1) ||| (1 <<< e.2)) = true := by
  rw [testBit_edgeTTYF (fun _ => univYF_testBit_lt), Bool.and_eq_true]
  refine ⟨edgePt_mem_univYF hv he, ?_⟩
  rw [hasEdge_eq_true]
  exact ⟨e, he, (twoBit_testBit _ _ _).mpr (Or.inl rfl), (twoBit_testBit _ _ _).mpr (Or.inr rfl)⟩

theorem edgePtsMask_and_univYF {n : ℕ} {H F : List (ℕ × ℕ)} (hv : ValidState n H F) :
    edgePtsMaskYF H &&& univYF n F = edgePtsMaskYF H := by
  apply Nat.eq_of_testBit_eq
  intro s
  rw [Nat.testBit_and]
  cases h : (edgePtsMaskYF H).testBit s
  · simp
  · rw [testBit_edgePtsMaskYF, List.any_eq_true] at h
    obtain ⟨e, heH, heq⟩ := h
    rw [decide_eq_true_eq] at heq
    rw [← heq, edgePt_mem_univYF hv heH, Bool.true_and]

theorem edgeTTYF_and_univYF (n : ℕ) (H F : List (ℕ × ℕ)) :
    edgeTTYF n H (univYF n F) &&& univYF n F = edgeTTYF n H (univYF n F) := by
  apply Nat.eq_of_testBit_eq
  intro s
  rw [Nat.testBit_and, testBit_edgeTTYF (fun _ => univYF_testBit_lt)]
  cases (univYF n F).testBit s <;> simp

theorem ttVarYF_and_mask {n v M : ℕ} (hM : ∀ s, M.testBit s = true → s < 2 ^ n) :
    ttVarYF n v M &&& M = ttVarYF n v M := by
  apply Nat.eq_of_testBit_eq
  intro s
  rw [Nat.testBit_and, testBit_ttVarYF hM]
  cases M.testBit s <;> simp

theorem ttNeedYF_and_mask {n a M : ℕ} (hM : ∀ s, M.testBit s = true → s < 2 ^ n) :
    ttNeedYF n a M &&& M = ttNeedYF n a M := by
  apply Nat.eq_of_testBit_eq
  intro s
  rw [Nat.testBit_and, testBit_ttNeedYF hM]
  cases M.testBit s <;> simp

/-! ## Section 3: Domain `Dom`, `decM`, `encM`, `HasRunYF`, `OrCostLB`, `ofCircuitYF` -/

abbrev Dom (maskYF : ℕ) := { s : ℕ // maskYF.testBit s = true }

def decM (maskYF : ℕ) (g : ℕ) : Set (Dom maskYF) :=
  { s | g.testBit s.1 = true }

@[simp] theorem mem_decM (maskYF g : ℕ) (s : Dom maskYF) :
    s ∈ decM maskYF g ↔ g.testBit s.1 = true := Iff.rfl

def rawSet (n : ℕ) (F : List (ℕ × ℕ)) : Set (Set (Dom (univYF n F))) :=
  Set.range (fun v : Fin n => decM (univYF n F) (ttVarYF n v.1 (univYF n F)))

def targetSet (n : ℕ) (H F : List (ℕ × ℕ)) : Set (Dom (univYF n F)) :=
  decM (univYF n F) (edgeTTYF n H (univYF n F))

def HasRunYF (n : ℕ) (H F : List (ℕ × ℕ)) (k : ℕ) : Prop :=
  Run (rawSet n F) k (targetSet n H F)

def OrCostLB (n : ℕ) (H F : List (ℕ × ℕ)) (lb : ℕ) : Prop :=
  ∀ k, HasRunYF n H F k → lb ≤ k

theorem decM_zero (M : ℕ) : decM M 0 = ∅ := by
  ext s; simp [decM]

theorem decM_self (M : ℕ) : decM M M = Set.univ := by
  ext ⟨s, hs⟩; simp [decM, hs]

theorem decM_and (M a b : ℕ) : decM M (a &&& b) = decM M a ∩ decM M b := by
  ext s; simp [decM, Nat.testBit_and]

theorem decM_or (M a b : ℕ) : decM M (a ||| b) = decM M a ∪ decM M b := by
  ext s; simp [decM, Nat.testBit_or]

theorem sub_mask_testBit {a M s : ℕ} (h : a &&& M = a) (ha : a.testBit s = true) :
    M.testBit s = true := by
  have := congrArg (fun x => x.testBit s) h
  rw [Nat.testBit_and, ha, Bool.true_and] at this
  exact this

theorem decM_subset_iff {M a b : ℕ} (ha : a &&& M = a) :
    decM M a ⊆ decM M b ↔ a &&& b = a := by
  constructor
  · intro hsub
    apply Nat.eq_of_testBit_eq
    intro s
    rw [Nat.testBit_and]
    cases h : a.testBit s
    · simp
    · have hm : M.testBit s = true := sub_mask_testBit ha h
      have hb : b.testBit s = true := hsub (a := ⟨s, hm⟩) h
      simp [hb]
  · intro heq ⟨s, _⟩ has
    have := congrArg (fun x => x.testBit s) heq
    rw [Nat.testBit_and, has, Bool.true_and] at this
    exact this

theorem decM_inj {M a b : ℕ} (ha : a &&& M = a) (hb : b &&& M = b) :
    decM M a = decM M b ↔ a = b := by
  constructor
  · intro heq
    apply Nat.eq_of_testBit_eq
    intro s
    cases h1 : a.testBit s
    · cases h2 : b.testBit s
      · rfl
      · have hm : M.testBit s = true := sub_mask_testBit hb h2
        have : (⟨s, hm⟩ : Dom M) ∈ decM M a := by rw [heq]; exact h2
        simp [decM, h1] at this
    · have hm : M.testBit s = true := sub_mask_testBit ha h1
      have : (⟨s, hm⟩ : Dom M) ∈ decM M b := by rw [← heq]; exact h1
      exact this.symm
  · intro h; rw [h]

noncomputable def encM (N M : ℕ) (S : Set (Dom M)) : ℕ := by
  classical
  exact mkBitmask N (fun s => if h : M.testBit s = true then decide (⟨s, h⟩ ∈ S) else false)

theorem encM_and_self {N M : ℕ} (S : Set (Dom M)) : encM N M S &&& M = encM N M S := by
  classical
  apply Nat.eq_of_testBit_eq
  intro s
  rw [Nat.testBit_and, encM, testBit_mkBitmask]
  by_cases hm : M.testBit s = true
  · simp [hm]
  · simp [hm]

theorem decM_encM {N M : ℕ} (hM : ∀ s, M.testBit s = true → s < N) (S : Set (Dom M)) :
    decM M (encM N M S) = S := by
  classical
  ext ⟨s, hs⟩
  simp only [decM, encM, testBit_mkBitmask, Set.mem_ofPred_eq]
  simp [hM s hs, hs]

theorem encM_decM {N M g : ℕ} (hM : ∀ s, M.testBit s = true → s < N) (hg : g &&& M = g) :
    encM N M (decM M g) = g :=
  (decM_inj (encM_and_self _) hg).mp (decM_encM hM _)

theorem rawSet_eq_image (n : ℕ) (F : List (ℕ × ℕ)) :
    rawSet n F = decM (univYF n F) '' { x | x ∈ rawYF n (univYF n F) } := by
  ext S
  simp only [rawSet, rawYF, Set.mem_range, Set.mem_image, Set.mem_ofPred_eq, List.mem_map,
    List.mem_range]
  constructor
  · rintro ⟨⟨v, hv⟩, rfl⟩
    exact ⟨ttVarYF n v (univYF n F), ⟨v, hv, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩

/-! ### Circuit compilation (`ofCircuitYF`) -/

def isOrGate (g : Gate) : Bool :=
  match g.op with
  | .or => true
  | _ => false

def countOrGates (gs : List Gate) : ℕ :=
  (gs.filter isOrGate).length

def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

noncomputable def bitOfSet {X : Type} (s : X) (f : Set X) : Bool := by
  classical exact decide (s ∈ f)

theorem bitOfSet_read {X : Type} (s : X) (ws : List (Set X)) (j : ℕ) :
    (ws.map (bitOfSet s)).getD j false = bitOfSet s (ws.getD j ∅) := by
  classical
  by_cases hj : j < ws.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (Nat.le_of_not_gt hj),
      bitOfSet]

theorem compileSig {X : Type} (gs : List Gate) (out : ℕ) (B : Set (Set X)) (w : List (Set X))
    (f : Set X)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hw : ∀ z ∈ w, Meet B z)
    (val : ∀ s : X, (gs.foldl gateStep (w.map (bitOfSet s))).getD out false = bitOfSet s f) :
    ∃ k ≤ countOrGates gs, Run B k f := by
  classical
  induction gs generalizing B w with
  | nil =>
    have h : w.getD out ∅ = f := by
      ext s
      have hh := val s
      rw [List.foldl_nil, bitOfSet_read] at hh
      simpa [bitOfSet] using (Bool.eq_iff_iff.mp hh)
    refine ⟨0, by simp [countOrGates], Run.done ?_⟩
    rw [← h]
    by_cases j : out < w.length
    · rw [List.getD_eq_getElem _ _ j]; exact hw _ (List.getElem_mem _)
    · rw [List.getD_eq_default _ _ (by omega)]; exact Meet.bot
  | cons g gs ih =>
    have ok := legal g (by simp)
    have ht : ∀ a ∈ gs, a.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ a.inputs.length ≤ 2 :=
      fun a h => legal _ (by simp [h])
    have rd (j : ℕ) : Meet B (w.getD j ∅) := by
      by_cases hj : j < w.length
      · rw [List.getD_eq_getElem _ _ hj]; exact hw _ (List.getElem_mem _)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Meet.bot
    have handle (z : Set X) (hz : Meet B z ∨ ∃ a b, Meet B a ∧ Meet B b ∧ z = a ∪ b ∧ g.op = .or)
        (step : ∀ s, gateStep (w.map (bitOfSet s)) g = (w ++ [z]).map (bitOfSet s)) :
        ∃ k ≤ countOrGates (g :: gs), Run B k f := by
      have val' s : (gs.foldl gateStep ((w ++ [z]).map (bitOfSet s))).getD out false = bitOfSet s f := by
        simpa only [List.foldl_cons, step] using val s
      rcases hz with free | ⟨a, b, ha, hb, rfl, hop⟩
      · obtain ⟨k, hk, h⟩ := ih B _ ht (fun u hu => by
          rcases List.mem_append.mp hu with hu | hu
          · exact hw _ hu
          · simpa [List.mem_singleton.mp hu] using free) val'
        exact ⟨k, hk.trans (by simp [countOrGates, List.filter_cons]; split <;> simp), h⟩
      · obtain ⟨k, hk, h⟩ := ih (insert (a ∪ b) B) _ ht (fun u hu => by
          rcases List.mem_append.mp hu with hu | hu
          · exact weaken (Set.subset_insert _ _) (hw _ hu)
          · exact Meet.atom (List.mem_singleton.mp hu ▸ Set.mem_insert _ _)) val'
        refine ⟨k + 1, ?_, Run.add ha hb h⟩
        have go : isOrGate g = true := by simp [isOrGate, hop]
        simpa [countOrGates, go] using Nat.succ_le_succ hk
    obtain ⟨op, l⟩ := g
    change (op = .and ∨ op = .or) ∧ l.length ≤ 2 at ok
    obtain ⟨opok, hlen⟩ := ok
    cases l with
    | nil =>
      rcases opok with rfl | rfl
      · apply handle Set.univ (Or.inl Meet.top); intro s; simp [gateStep, GateOp.eval, bitOfSet]
      · apply handle ∅ (Or.inl Meet.bot); intro s; simp [gateStep, GateOp.eval, bitOfSet]
    | cons i l =>
      cases l with
      | nil =>
        rcases opok with rfl | rfl <;> apply handle (w.getD i ∅) (Or.inl (rd i)) <;>
          intro s <;> simp [gateStep, GateOp.eval] <;> cases w[i]? <;> simp [bitOfSet]
      | cons j l =>
        cases l with
        | cons => simp at hlen
        | nil =>
          rcases opok with rfl | rfl
          · apply handle (w.getD i ∅ ∩ w.getD j ∅) (Or.inl ((rd i).inter (rd j)))
            intro s; simp [gateStep, GateOp.eval]; cases w[i]? <;> cases w[j]? <;> simp [bitOfSet]
          · apply handle (w.getD i ∅ ∪ w.getD j ∅) (Or.inr ⟨_, _, rd i, rd j, rfl, rfl⟩)
            intro s; simp [gateStep, GateOp.eval]; cases w[i]? <;> cases w[j]? <;> simp [bitOfSet]

theorem ofCircuitYF {n : ℕ} (H : List (ℕ × ℕ)) (C : Circuit) (hc : Monotone2 C)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ e ∈ H, ∃ (h1 : e.1 < n) (h2 : e.2 < n), x ⟨e.1, h1⟩ = true ∧ x ⟨e.2, h2⟩ = true)
    (hH : ∀ e ∈ H, e.1 < n ∧ e.2 < n) :
    ∃ k ≤ countOrGates C.gates, HasRunYF n H [] k := by
  classical
  let M := univYF n []
  let w : List (Set (Dom M)) := List.ofFn (fun v : Fin n => decM M (ttVarYF n v.1 M))
  have hw : ∀ z ∈ w, Meet (rawSet n []) z := by
    intro z hz
    obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hz
    exact Meet.atom ⟨v, rfl⟩
  have hval (s : Dom M) :
      (C.gates.foldl gateStep (w.map (bitOfSet s))).getD C.output false =
        bitOfSet s (targetSet n H []) := by
    let x : Fin n → Bool := fun v => s.1.testBit v.1
    have hin : w.map (bitOfSet s) = List.ofFn x := by
      rw [show w = List.ofFn (fun v : Fin n => decM M (ttVarYF n v.1 M)) from rfl, List.map_ofFn]
      apply congrArg List.ofFn
      funext v
      have htb : (ttVarYF n v.1 M).testBit s.1 = s.1.testBit v.1 := by
        rw [testBit_ttVarYF (fun _ => univYF_testBit_lt), s.2, Bool.true_and]
      simp only [Function.comp_apply, bitOfSet, decM, Set.mem_ofPred_eq, htb, x]
      cases s.1.testBit v.1 <;> rfl
    rw [hin]
    change C.eval (List.ofFn x) = _
    apply Bool.eq_iff_iff.mpr
    have het : (edgeTTYF n H M).testBit s.1 = hasEdge H s.1 := by
      rw [testBit_edgeTTYF (fun _ => univYF_testBit_lt), s.2, Bool.true_and]
    change C.eval (List.ofFn x) = true ↔ decide (s ∈ targetSet n H []) = true
    rw [decide_eq_true_eq, he x]
    have hmem : s ∈ targetSet n H [] ↔ ∃ e ∈ H, s.1.testBit e.1 = true ∧ s.1.testBit e.2 = true := by
      change (edgeTTYF n H M).testBit s.1 = true ↔ _
      rw [het, hasEdge_eq_true]
    rw [hmem]
    simp only [x]
    constructor
    · rintro ⟨e, heH, _, _, h1, h2⟩; exact ⟨e, heH, h1, h2⟩
    · rintro ⟨e, heH, h1, h2⟩
      obtain ⟨hu, hv⟩ := hH e heH
      exact ⟨e, heH, hu, hv, h1, h2⟩
  exact compileSig C.gates C.output (rawSet n []) w (targetSet n H []) hc hw hval

theorem countOr_add_countAnd_list (gs : List Gate)
    (hmem : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    (gs.filter (fun g => match g.op with | .and => true | _ => false)).length +
      countOrGates gs = gs.length := by
  induction gs with
  | nil => simp [countOrGates]
  | cons g gs ih =>
    have hg := hmem g (by simp)
    have ih' := ih (fun x hx => hmem x (by simp [hx]))
    rcases hg with h | h <;> simp [countOrGates, isOrGate, h] at ih' ⊢ <;> omega

theorem countOr_add_countAnd (C : Circuit) (hc : Monotone2 C) :
    (C.gates.filter (fun g => match g.op with | .and => true | _ => false)).length +
      countOrGates C.gates = C.size :=
  countOr_add_countAnd_list C.gates (fun g hg => (hc g hg).1)

/-! ## Section 4: `isMeet`, `isOnEdges`, `RunListFrom`, `lexMinRun` & Pruning Lemmas -/

theorem land_eq (a b : ℕ) : Nat.land a b = a &&& b := rfl
theorem lor_eq (a b : ℕ) : Nat.lor a b = a ||| b := rfl

def isMeetLoop (target : ℕ) : List ℕ → ℕ → ℕ
  | [], acc => acc
  | b :: bs, acc =>
    match Nat.beq (Nat.land target b) target with
    | true => isMeetLoop target bs (Nat.land acc b)
    | false => isMeetLoop target bs acc

def isMeet (univMask : ℕ) (basis : List ℕ) (target : ℕ) : Bool :=
  match Nat.beq target 0 with
  | true => true
  | false => Nat.beq (isMeetLoop target basis univMask) target

def isOnEdges (univMask edgePtsMask : ℕ) (basis : List ℕ) (g : ℕ) : Bool :=
  let eg := Nat.land g edgePtsMask
  let acc := isMeetLoop eg basis univMask
  Nat.beq (Nat.land acc g) acc

theorem isMeetLoop_and_sub {target : ℕ} (bs : List ℕ) (acc : ℕ) :
    isMeetLoop target bs acc &&& acc = isMeetLoop target bs acc := by
  induction bs generalizing acc with
  | nil => simp [isMeetLoop]
  | cons b bs ih =>
    simp only [isMeetLoop]
    cases Nat.beq (Nat.land target b) target
    · exact ih acc
    · have h1 := ih (Nat.land acc b)
      apply Nat.eq_of_testBit_eq; intro s
      have h2 := congrArg (fun x => x.testBit s) h1
      simp only [land_eq, Nat.testBit_and] at h2 ⊢
      revert h2
      cases (isMeetLoop target bs (acc &&& b)).testBit s <;>
        cases acc.testBit s <;> cases b.testBit s <;> decide

theorem isMeetLoop_and_mask {target M : ℕ} (bs : List ℕ) {acc : ℕ} (hacc : acc &&& M = acc) :
    isMeetLoop target bs acc &&& M = isMeetLoop target bs acc := by
  have hsub := isMeetLoop_and_sub (target := target) bs acc
  apply Nat.eq_of_testBit_eq; intro s
  have h1 := congrArg (fun x => x.testBit s) hsub
  have h2 := congrArg (fun x => x.testBit s) hacc
  simp only [Nat.testBit_and] at h1 h2 ⊢
  revert h1 h2
  cases (isMeetLoop target bs acc).testBit s <;>
    cases acc.testBit s <;> cases M.testBit s <;> decide

theorem isMeetLoop_target_sub {target : ℕ} (bs : List ℕ) {acc : ℕ}
    (hacc : target &&& acc = target) :
    target &&& isMeetLoop target bs acc = target := by
  induction bs generalizing acc with
  | nil => exact hacc
  | cons b bs ih =>
    simp only [isMeetLoop]
    cases hb : Nat.beq (Nat.land target b) target
    · exact ih hacc
    · apply ih
      have hb' : target &&& b = target := by simpa [land_eq] using Nat.eq_of_beq_eq_true hb
      rw [land_eq, ← Nat.and_assoc, hacc, hb']

theorem isMeetLoop_mem_meet {M target : ℕ} {B : Set (Set (Dom M))} (bs : List ℕ)
    (hbs : ∀ b ∈ bs, decM M b ∈ B) {acc : ℕ} (hacc : Meet B (decM M acc)) :
    Meet B (decM M (isMeetLoop target bs acc)) := by
  induction bs generalizing acc with
  | nil => exact hacc
  | cons b bs ih =>
    simp only [isMeetLoop]
    cases Nat.beq (Nat.land target b) target
    · exact ih (fun x hx => hbs x (by simp [hx])) hacc
    · apply ih (fun x hx => hbs x (by simp [hx]))
      rw [land_eq, decM_and]
      exact hacc.inter (Meet.atom (hbs b (by simp)))

theorem isMeetLoop_le_factor {M target : ℕ} (bs : List ℕ) {b : ℕ} (hb : b ∈ bs)
    (htb : target &&& b = target) (acc : ℕ) :
    decM M (isMeetLoop target bs acc) ⊆ decM M b := by
  induction bs generalizing acc with
  | nil => simp at hb
  | cons x bs ih =>
    simp only [isMeetLoop]
    rcases List.mem_cons.mp hb with rfl | hb'
    · have hbeq : Nat.beq (Nat.land target b) target = true := by
        simpa [land_eq] using htb
      rw [hbeq]
      have hsub := isMeetLoop_and_sub (target := target) bs (Nat.land acc b)
      intro s hs
      have h1 := congrArg (fun z => z.testBit s.1) hsub
      simp only [land_eq, Nat.testBit_and] at h1
      change (isMeetLoop target bs (acc &&& b)).testBit s.1 = true at hs
      rw [hs, Bool.true_and] at h1
      have h2 : acc.testBit s.1 = true ∧ b.testBit s.1 = true := by
        simpa [Bool.and_eq_true] using h1.symm
      exact h2.2
    · cases Nat.beq (Nat.land target x) target
      · exact ih hb' acc
      · exact ih hb' (Nat.land acc x)

theorem isMeet_iff {M : ℕ} {B : List ℕ} {t : ℕ} (ht : t &&& M = t) :
    isMeet M B t = true ↔ Meet (decM M '' { b | b ∈ B }) (decM M t) := by
  unfold isMeet
  cases h0 : Nat.beq t 0
  · have ht0 : t ≠ 0 := by intro h; subst h; simp at h0
    constructor
    · intro h
      have heq : isMeetLoop t B M = t := Nat.eq_of_beq_eq_true h
      rw [← heq]
      apply isMeetLoop_mem_meet (B := decM M '' { b | b ∈ B }) B (fun b hb => ⟨b, hb, rfl⟩)
      rw [decM_self]; exact Meet.top
    · intro hm
      have hsub_all : ∀ S, Meet (decM M '' { b | b ∈ B }) S → decM M t ⊆ S →
          decM M (isMeetLoop t B M) ⊆ S := by
        intro S hS
        induction hS with
        | atom hmem =>
          rcases hmem with ⟨b, hb, rfl⟩
          intro htb
          exact isMeetLoop_le_factor B hb ((decM_subset_iff ht).mp htb) M
        | top => intro _; exact Set.subset_univ _
        | bot =>
          intro hte
          have : decM M t = decM M 0 := by
            rw [decM_zero]; exact Set.subset_empty_iff.mp hte
          exact (ht0 ((decM_inj ht (by simp)).mp this)).elim
        | inter _ _ ih1 ih2 =>
          intro hsub
          exact Set.subset_inter (ih1 (hsub.trans Set.inter_subset_left))
            (ih2 (hsub.trans Set.inter_subset_right))
      have h1 : decM M (isMeetLoop t B M) ⊆ decM M t := hsub_all _ hm Set.Subset.rfl
      have h2 : decM M t ⊆ decM M (isMeetLoop t B M) :=
        (decM_subset_iff ht).mpr (isMeetLoop_target_sub B ht)
      have heq : isMeetLoop t B M = t :=
        (decM_inj (isMeetLoop_and_mask B (by simp)) ht).mp (Set.Subset.antisymm h1 h2)
      simp [heq]
  · have ht0 : t = 0 := Nat.eq_of_beq_eq_true h0
    subst ht0
    simp [decM_zero, Meet.bot]

theorem isOnEdges_sound {M edgePts g : ℕ} {B : List ℕ}
    (hg : g &&& M = g)
    (hon : isOnEdges M edgePts B g = true) :
    ∃ h : ℕ, h &&& M = h ∧ Meet (decM M '' { b | b ∈ B }) (decM M h) ∧
      decM M h ⊆ decM M g ∧ decM M h ∩ decM M edgePts = decM M g ∩ decM M edgePts := by
  unfold isOnEdges at hon
  set eg := Nat.land g edgePts
  set h := isMeetLoop eg B M
  have hhM : h &&& M = h := isMeetLoop_and_mask B (by simp)
  have hhg : h &&& g = h := by simpa [land_eq] using Nat.eq_of_beq_eq_true hon
  have hegM : eg &&& M = eg := by
    apply Nat.eq_of_testBit_eq; intro s
    have h1 := congrArg (fun x => x.testBit s) hg
    simp only [eg, land_eq, Nat.testBit_and] at h1 ⊢
    revert h1
    cases g.testBit s <;> cases edgePts.testBit s <;> cases M.testBit s <;> decide
  have hegh : eg &&& h = eg := isMeetLoop_target_sub B hegM
  refine ⟨h, hhM, ?_, (decM_subset_iff hhM).mpr hhg, ?_⟩
  · apply isMeetLoop_mem_meet (B := decM M '' { b | b ∈ B }) B (fun b hb => ⟨b, hb, rfl⟩)
    rw [decM_self]; exact Meet.top
  · have hsub1 : decM M h ⊆ decM M g := (decM_subset_iff hhM).mpr hhg
    have hsub2 : decM M g ∩ decM M edgePts ⊆ decM M h := by
      rw [← decM_and]
      exact (decM_subset_iff hegM).mpr hegh
    exact Set.Subset.antisymm (Set.inter_subset_inter_left _ hsub1)
      (Set.subset_inter hsub2 Set.inter_subset_right)

/-! ### `MeetNat` and `RunListFrom` -/

def MeetNat (M : ℕ) (B : List ℕ) (t : ℕ) : Prop :=
  t &&& M = t ∧ isMeet M B t = true

def ValidPrefix (M : ℕ) (B : List ℕ) : List ℕ → Prop
  | [] => True
  | g :: rest =>
    (∃ a b, MeetNat M B a ∧ MeetNat M B b ∧ g = a ||| b) ∧
    ValidPrefix M (B ++ [g]) rest

def RunListFrom (M : ℕ) (B : List ℕ) (target : ℕ) : List ℕ → Prop
  | [] => MeetNat M B target
  | g :: rest =>
    (∃ a b, MeetNat M B a ∧ MeetNat M B b ∧ g = a ||| b) ∧
    RunListFrom M (B ++ [g]) target rest

theorem meetNat_iff {M : ℕ} {B : List ℕ} {t : ℕ} :
    MeetNat M B t ↔ t &&& M = t ∧ Meet (decM M '' { b | b ∈ B }) (decM M t) := by
  constructor
  · rintro ⟨ht, hm⟩; exact ⟨ht, (isMeet_iff ht).mp hm⟩
  · rintro ⟨ht, hm⟩; exact ⟨ht, (isMeet_iff ht).mpr hm⟩

theorem meetNat_weaken {M : ℕ} {B₁ B₂ : List ℕ} (hsub : ∀ x ∈ B₁, x ∈ B₂) {t : ℕ}
    (ht : MeetNat M B₁ t) : MeetNat M B₂ t := by
  rw [meetNat_iff] at ht ⊢
  exact ⟨ht.1, weaken (Set.image_mono (fun x hx => hsub x hx)) ht.2⟩

theorem or_and_mask {a b M : ℕ} (ha : a &&& M = a) (hb : b &&& M = b) :
    (a ||| b) &&& M = a ||| b := by
  apply Nat.eq_of_testBit_eq; intro s
  have h1 := congrArg (fun x => x.testBit s) ha
  have h2 := congrArg (fun x => x.testBit s) hb
  simp only [Nat.testBit_and, Nat.testBit_or] at h1 h2 ⊢
  revert h1 h2
  cases a.testBit s <;> cases b.testBit s <;> cases M.testBit s <;> decide

theorem runListFrom_to_run {M target : ℕ} {B gs : List ℕ}
    (hr : RunListFrom M B target gs) :
    Run (decM M '' { x | x ∈ B }) gs.length (decM M target) := by
  induction gs generalizing B with
  | nil =>
    exact Run.done (meetNat_iff.mp hr).2
  | cons g rest ih =>
    rcases hr with ⟨⟨a, b, ha, hb, rfl⟩, hrest⟩
    have ih' := ih hrest
    have hset : decM M '' { x | x ∈ B ++ [a ||| b] } =
        insert (decM M a ∪ decM M b) (decM M '' { x | x ∈ B }) := by
      ext S
      simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_append, List.mem_singleton,
        Set.mem_insert_iff]
      constructor
      · rintro ⟨x, hx | rfl, rfl⟩
        · exact Or.inr ⟨x, hx, rfl⟩
        · exact Or.inl (decM_or M a b)
      · rintro (rfl | ⟨x, hx, rfl⟩)
        · exact ⟨a ||| b, Or.inr rfl, decM_or M a b⟩
        · exact ⟨x, Or.inl hx, rfl⟩
    rw [hset] at ih'
    exact Run.add (meetNat_iff.mp ha).2 (meetNat_iff.mp hb).2 ih'

theorem run_to_runListFrom {N M target : ℕ} (hM : ∀ s, M.testBit s = true → s < N)
    (ht : target &&& M = target) {B : List ℕ} {k : ℕ}
    (hr : Run (decM M '' { x | x ∈ B }) k (decM M target)) :
    ∃ gs : List ℕ, gs.length = k ∧ RunListFrom M B target gs := by
  induction k generalizing B with
  | zero =>
    cases hr with
    | done hm => exact ⟨[], rfl, meetNat_iff.mpr ⟨ht, hm⟩⟩
  | succ k ih =>
    cases hr with
    | @add _ a b _ _ ha hb tail =>
      let ea := encM N M a
      let eb := encM N M b
      have hea : ea &&& M = ea := encM_and_self a
      have heb : eb &&& M = eb := encM_and_self b
      have hda : decM M ea = a := decM_encM hM a
      have hdb : decM M eb = b := decM_encM hM b
      have hset : decM M '' { x | x ∈ B ++ [ea ||| eb] } =
          insert (a ∪ b) (decM M '' { x | x ∈ B }) := by
        ext S
        simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_append, List.mem_singleton,
          Set.mem_insert_iff]
        constructor
        · rintro ⟨x, hx | rfl, rfl⟩
          · exact Or.inr ⟨x, hx, rfl⟩
          · exact Or.inl (by rw [decM_or, hda, hdb])
        · rintro (rfl | ⟨x, hx, rfl⟩)
          · exact ⟨ea ||| eb, Or.inr rfl, by rw [decM_or, hda, hdb]⟩
          · exact ⟨x, Or.inl hx, rfl⟩
      rw [← hset] at tail
      obtain ⟨rest, hlen, hrun⟩ := ih tail
      refine ⟨(ea ||| eb) :: rest, by simp [hlen], ?_, hrun⟩
      exact ⟨ea, eb, meetNat_iff.mpr ⟨hea, hda.symm ▸ ha⟩,
        meetNat_iff.mpr ⟨heb, hdb.symm ▸ hb⟩, rfl⟩

theorem runListFrom_append {M target : ℕ} {B pre suf : List ℕ} :
    RunListFrom M B target (pre ++ suf) ↔
      ValidPrefix M B pre ∧ RunListFrom M (B ++ pre) target suf := by
  induction pre generalizing B with
  | nil => simp [ValidPrefix]
  | cons g rest ih =>
    simp only [List.cons_append, RunListFrom, ValidPrefix]
    rw [ih, List.append_assoc, List.singleton_append]
    tauto

theorem runListFrom_equiv_basis {M target : ℕ} {B₁ B₂ gs : List ℕ}
    (heq : ∀ x, x ∈ B₁ ↔ x ∈ B₂) :
    RunListFrom M B₁ target gs → RunListFrom M B₂ target gs := by
  induction gs generalizing B₁ B₂ with
  | nil => exact meetNat_weaken (fun x hx => (heq x).mp hx)
  | cons g rest ih =>
    rintro ⟨⟨a, b, ha, hb, rfl⟩, hrest⟩
    refine ⟨⟨a, b, meetNat_weaken (fun x hx => (heq x).mp hx) ha,
      meetNat_weaken (fun x hx => (heq x).mp hx) hb, rfl⟩, ?_⟩
    exact ih (fun x => by simp [heq x]) hrest

theorem validPrefix_mem_sub_mask {M : ℕ} {B pre : List ℕ} (hp : ValidPrefix M B pre) :
    ∀ g ∈ pre, g &&& M = g := by
  induction pre generalizing B with
  | nil => intro g hg; simp at hg
  | cons g rest ih =>
    rcases hp with ⟨⟨a, b, ha, hb, rfl⟩, hrest⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact or_and_mask ha.1 hb.1
    · exact ih hrest x hx

theorem validPrefix_to_run {M target : ℕ} {B pre : List ℕ} (hp : ValidPrefix M B pre)
    {k : ℕ} (hr : Run (decM M '' { x | x ∈ B ++ pre }) k (decM M target)) :
    Run (decM M '' { x | x ∈ B }) (pre.length + k) (decM M target) := by
  induction pre generalizing B with
  | nil => simpa using hr
  | cons g rest ih =>
    rcases hp with ⟨⟨a, b, ha, hb, rfl⟩, hrest⟩
    have hr' : Run (decM M '' { x | x ∈ (B ++ [a ||| b]) ++ rest }) k (decM M target) := by
      simpa only [List.append_assoc, List.singleton_append] using hr
    have hr1 := ih hrest hr'
    have hset : decM M '' { x | x ∈ B ++ [a ||| b] } =
        insert (decM M a ∪ decM M b) (decM M '' { x | x ∈ B }) := by
      ext S
      simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_append, List.mem_singleton,
        Set.mem_insert_iff]
      constructor
      · rintro ⟨x, hx | rfl, rfl⟩
        · exact Or.inr ⟨x, hx, rfl⟩
        · exact Or.inl (decM_or M a b)
      · rintro (rfl | ⟨x, hx, rfl⟩)
        · exact ⟨a ||| b, Or.inr rfl, decM_or M a b⟩
        · exact ⟨x, Or.inl hx, rfl⟩
    rw [hset] at hr1
    rw [List.length_cons, Nat.succ_add]
    exact Run.add (meetNat_iff.mp ha).2 (meetNat_iff.mp hb).2 hr1

/-! ### Existence of global minimal-length, lexicographically minimal run -/

theorem exists_lexMin_of_length {P : List ℕ → Prop} :
    ∀ k, (∃ gs, gs.length = k ∧ P gs) →
      ∃ gs, gs.length = k ∧ P gs ∧
        ∀ gs', gs'.length = k → P gs' → ¬ List.Lex (· < ·) gs' gs := by
  classical
  intro k
  induction k generalizing P with
  | zero =>
    rintro ⟨gs, hlen, hp⟩
    cases gs with
    | nil =>
      refine ⟨[], rfl, hp, fun gs' hlen' _ hlex => ?_⟩
      cases gs' with
      | nil => cases hlex
      | cons => simp at hlen'
    | cons => simp at hlen
  | succ k ih =>
    intro hex
    have hQ : ∃ x : ℕ, ∃ tail : List ℕ, tail.length = k ∧ P (x :: tail) := by
      rcases hex with ⟨gs, hlen, hp⟩
      cases gs with
      | nil => simp at hlen
      | cons x tail => exact ⟨x, tail, by simpa using hlen, hp⟩
    let x₀ := Nat.find hQ
    have hx₀ : ∃ tail : List ℕ, tail.length = k ∧ P (x₀ :: tail) := Nat.find_spec hQ
    obtain ⟨tail₀, hlen₀, hp₀, hmin₀⟩ := ih (P := fun t => P (x₀ :: t)) hx₀
    refine ⟨x₀ :: tail₀, by simp [hlen₀], hp₀, fun gs' hlen' hp' hlex => ?_⟩
    cases gs' with
    | nil => simp at hlen'
    | cons x' tail' =>
      cases hlex with
      | rel hlt =>
        exact Nat.find_min hQ hlt ⟨tail', by simpa using hlen', hp'⟩
      | cons hlex' =>
        exact hmin₀ tail' (by simpa using hlen') hp' hlex'

theorem exists_lexMinRun {n bound : ℕ} {H F : List (ℕ × ℕ)}
    (hex : ∃ k ≤ bound, HasRunYF n H F k) :
    ∃ (k : ℕ) (gs : List ℕ), k ≤ bound ∧ gs.length = k ∧
      RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) gs ∧
      (∀ k' < k, ¬ HasRunYF n H F k') ∧
      (∀ gs', gs'.length = k →
        RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) gs' →
        ¬ List.Lex (· < ·) gs' gs) := by
  classical
  have hEx : ∃ k, HasRunYF n H F k := by rcases hex with ⟨k, _, h⟩; exact ⟨k, h⟩
  let k := Nat.find hEx
  have hk_le : k ≤ bound := by
    rcases hex with ⟨k', hk', hr'⟩
    exact (Nat.find_min' hEx hr').trans hk'
  have hk_run : HasRunYF n H F k := Nat.find_spec hEx
  have hk_min : ∀ k' < k, ¬ HasRunYF n H F k' := fun k' hk' => Nat.find_min hEx hk'
  have hr_list : ∃ gs : List ℕ, gs.length = k ∧
      RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) gs := by
    apply run_to_runListFrom (N := 2 ^ n) (fun _ => univYF_testBit_lt) (edgeTTYF_and_univYF n H F)
    simpa only [HasRunYF, rawSet_eq_image, targetSet] using hk_run
  obtain ⟨gs, hlen, hrun, hlex⟩ := exists_lexMin_of_length k hr_list
  exact ⟨k, gs, hk_le, hlen, hrun, hk_min, hlex⟩

/-! ### Pruning Lemmas 1–4 on a minimal-length, lex-minimal run -/

def bitLe {M : ℕ} (x y : Dom M) : Prop := x.1 &&& y.1 = x.1

theorem raw_upClosed {n : ℕ} {F : List (ℕ × ℕ)} {r : ℕ}
    (hr : r ∈ rawYF n (univYF n F)) :
    UpClosed (bitLe (M := univYF n F)) (decM (univYF n F) r) := by
  simp only [rawYF, List.mem_map, List.mem_range] at hr
  rcases hr with ⟨v, _, rfl⟩
  intro x y hxy hx
  simp only [decM, Set.mem_ofPred_eq, testBit_ttVarYF (fun _ => univYF_testBit_lt),
    x.2, y.2, Bool.true_and] at hx ⊢
  have := congrArg (fun z => z.testBit v) hxy
  rw [Nat.testBit_and, hx, Bool.true_and] at this
  exact this

theorem validPrefix_upClosed {M : ℕ} {B pre : List ℕ}
    (hB : ∀ r ∈ B, UpClosed (bitLe (M := M)) (decM M r))
    (hp : ValidPrefix M B pre) :
    ∀ x ∈ B ++ pre, UpClosed (bitLe (M := M)) (decM M x) := by
  induction pre generalizing B with
  | nil => simpa using hB
  | cons g rest ih =>
    rcases hp with ⟨⟨a, b, ha, hb, rfl⟩, hrest⟩
    have hB' : ∀ r ∈ B ++ [a ||| b], UpClosed (bitLe (M := M)) (decM M r) := by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hB r hr
      · rw [List.mem_singleton.mp hr, decM_or]
        have ha' : UpClosed (bitLe (M := M)) (decM M a) :=
          meet_upClosed (B := decM M '' { x | x ∈ B })
            (fun S hS => by rcases hS with ⟨x, hx, rfl⟩; exact hB x hx) (meetNat_iff.mp ha).2
        have hb' : UpClosed (bitLe (M := M)) (decM M b) :=
          meet_upClosed (B := decM M '' { x | x ∈ B })
            (fun S hS => by rcases hS with ⟨x, hx, rfl⟩; exact hB x hx) (meetNat_iff.mp hb).2
        intro x y hxy hmem
        rcases hmem with h1 | h2
        · exact Or.inl (ha' x y hxy h1)
        · exact Or.inr (hb' x y hxy h2)
    simpa [List.append_assoc] using ih hB' hrest

theorem edgePts_upClose_target {n : ℕ} {H F : List (ℕ × ℕ)} (hv : ValidState n H F) :
    (decM (univYF n F) (edgePtsMaskYF H) ⊆ targetSet n H F) ∧
    (∀ f : Set (Dom (univYF n F)), UpClosed (bitLe (M := univYF n F)) f →
      decM (univYF n F) (edgePtsMaskYF H) ⊆ f → targetSet n H F ⊆ f) := by
  constructor
  · intro s hs
    simp only [decM, Set.mem_ofPred_eq, testBit_edgePtsMaskYF, List.any_eq_true] at hs
    rcases hs with ⟨e, heH, heq⟩
    rw [decide_eq_true_eq] at heq
    change (edgeTTYF n H (univYF n F)).testBit s.1 = true
    rw [← heq]; exact edgePt_mem_edgeTTYF hv heH
  · intro f hf hsub s hs
    simp only [targetSet, decM, Set.mem_ofPred_eq,
      testBit_edgeTTYF (fun _ => univYF_testBit_lt), s.2, Bool.true_and, hasEdge_eq_true] at hs
    rcases hs with ⟨e, heH, h1, h2⟩
    let ep : ℕ := (1 <<< e.1) ||| (1 <<< e.2)
    have hepM : (univYF n F).testBit ep = true := edgePt_mem_univYF hv heH
    have hepPts : (⟨ep, hepM⟩ : Dom (univYF n F)) ∈ decM (univYF n F) (edgePtsMaskYF H) := by
      simp only [decM, Set.mem_ofPred_eq, testBit_edgePtsMaskYF, List.any_eq_true]
      exact ⟨e, heH, decide_eq_true rfl⟩
    have hle : bitLe (⟨ep, hepM⟩ : Dom (univYF n F)) s := by
      apply Nat.eq_of_testBit_eq; intro w
      rw [Nat.testBit_and]
      by_cases hw : ep.testBit w = true
      · rw [hw, Bool.true_and]
        rcases (twoBit_testBit e.1 e.2 w).mp hw with rfl | rfl
        · exact h1
        · exact h2
      · have hwf : ep.testBit w = false := Bool.eq_false_iff.mpr hw
        simp [hwf]
    exact hf ⟨ep, hepM⟩ s hle (hsub hepPts)

theorem lexMin_not_finished {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf : List ℕ}
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre ++ suf))
    (hmin : ∀ k' < (pre ++ suf).length, ¬ HasRunYF n H F k')
    (hsuf : suf ≠ []) :
    isMeet (univYF n F) (rawYF n (univYF n F) ++ pre) (edgeTTYF n H (univYF n F)) = false := by
  rw [Bool.eq_false_iff]
  intro hm
  have hp : ValidPrefix (univYF n F) (rawYF n (univYF n F)) pre := (runListFrom_append.mp hrun).1
  have hr : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) pre := by
    have h := runListFrom_append (M := univYF n F) (target := edgeTTYF n H (univYF n F))
      (B := rawYF n (univYF n F)) (pre := pre) (suf := [])
    rw [List.append_nil] at h
    exact h.mpr ⟨hp, edgeTTYF_and_univYF n H F, hm⟩
  have hr' := runListFrom_to_run hr
  rw [← rawSet_eq_image] at hr'
  have hlt : pre.length < (pre ++ suf).length := by
    cases suf with
    | nil => exact (hsuf rfl).elim
    | cons _ _ => simp
  exact hmin pre.length hlt hr'

theorem lexMin_eliminate_step {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf : List ℕ} {g h : ℕ}
    (hv : ValidState n H F)
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre ++ g :: suf))
    (hmin : ∀ k' < (pre ++ g :: suf).length, ¬ HasRunYF n H F k')
    (hmh : Meet (decM (univYF n F) '' { x | x ∈ rawYF n (univYF n F) ++ pre }) (decM (univYF n F) h))
    (hsub : decM (univYF n F) h ⊆ decM (univYF n F) g)
    (heq : decM (univYF n F) h ∩ decM (univYF n F) (edgePtsMaskYF H) =
      decM (univYF n F) g ∩ decM (univYF n F) (edgePtsMaskYF H)) : False := by
  set M := univYF n F
  set raw := rawYF n M
  set target := edgeTTYF n H M
  obtain ⟨hp, hstep⟩ := runListFrom_append.mp hrun
  rcases hstep with ⟨_, hsuf⟩
  have hrun_suf : Run (decM M '' { x | x ∈ (raw ++ pre) ++ [g] }) suf.length (targetSet n H F) :=
    runListFrom_to_run hsuf
  have hD_up : ∀ S ∈ decM M '' { x | x ∈ raw ++ pre }, UpClosed (bitLe (M := M)) S := by
    rintro S ⟨x, hx, rfl⟩
    exact validPrefix_upClosed (fun r hr => raw_upClosed hr) hp x hx
  have hmap : ∀ S ∈ decM M '' { x | x ∈ (raw ++ pre) ++ [g] },
      ∃ S', Meet (decM M '' { x | x ∈ raw ++ pre }) S' ∧ S' ⊆ S ∧
        S' ∩ decM M (edgePtsMaskYF H) = S ∩ decM M (edgePtsMaskYF H) := by
    rintro S ⟨x, hx, rfl⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact ⟨decM M x, Meet.atom ⟨x, hx, rfl⟩, Set.Subset.rfl, rfl⟩
    · rw [List.mem_singleton.mp hx]
      exact ⟨decM M h, hmh, hsub, heq⟩
  obtain ⟨hSt, hclose⟩ := edgePts_upClose_target hv
  have hrun_short : Run (decM M '' { x | x ∈ raw ++ pre }) suf.length (targetSet n H F) :=
    run_replaceBelow_upClosed hSt hclose hD_up hmap hrun_suf
  have hrun_full : HasRunYF n H F (pre.length + suf.length) := by
    have := validPrefix_to_run hp hrun_short
    rw [← rawSet_eq_image] at this
    exact this
  have hlt : pre.length + suf.length < (pre ++ g :: suf).length := by simp
  exact hmin _ hlt hrun_full

theorem lexMin_not_onEdges {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf : List ℕ} {g : ℕ}
    (hv : ValidState n H F)
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre ++ g :: suf))
    (hmin : ∀ k' < (pre ++ g :: suf).length, ¬ HasRunYF n H F k') :
    isOnEdges (univYF n F) (edgePtsMaskYF H) (rawYF n (univYF n F) ++ pre) g = false := by
  rw [Bool.eq_false_iff]
  intro hon
  have hgM : g &&& univYF n F = g := by
    obtain ⟨_, ⟨a, b, ha, hb, rfl⟩, _⟩ := runListFrom_append.mp hrun
    exact or_and_mask ha.1 hb.1
  obtain ⟨h, _, hmh, hsub, heq⟩ := isOnEdges_sound hgM hon
  exact lexMin_eliminate_step hv hrun hmin hmh hsub heq

/-! ### Operand decomposition and `genOps` completeness/soundness -/

theorem ttNeedYF_zero {n M : ℕ} (hM : ∀ s, M.testBit s = true → s < 2 ^ n) :
    ttNeedYF n 0 M = M := by
  apply Nat.eq_of_testBit_eq; intro s
  rw [testBit_ttNeedYF hM]; simp

theorem ttNeedYF_oneBit {n v M : ℕ} (hM : ∀ s, M.testBit s = true → s < 2 ^ n) :
    ttNeedYF n (1 <<< v) M = ttVarYF n v M := by
  apply Nat.eq_of_testBit_eq; intro s
  rw [testBit_ttNeedYF hM, testBit_ttVarYF hM]
  have hbit : ((s &&& (1 <<< v)) == (1 <<< v)) = s.testBit v := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq]
    constructor
    · intro heq
      have := congrArg (fun z => z.testBit v) heq
      rw [Nat.testBit_and, testBit_one_shiftLeft] at this
      simpa using this
    · intro hs
      apply Nat.eq_of_testBit_eq; intro w
      rw [Nat.testBit_and, testBit_one_shiftLeft]
      by_cases hw : v = w
      · subst hw; simp [hs]
      · simp [hw]
  rw [hbit]

theorem ttNeedYF_or {n a b M : ℕ} (hM : ∀ s, M.testBit s = true → s < 2 ^ n) :
    ttNeedYF n a M &&& ttNeedYF n b M = ttNeedYF n (a ||| b) M := by
  apply Nat.eq_of_testBit_eq; intro s
  rw [Nat.testBit_and, testBit_ttNeedYF hM, testBit_ttNeedYF hM, testBit_ttNeedYF hM]
  cases hm : M.testBit s
  · simp
  · simp only [Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨ha, hb⟩
      apply Nat.eq_of_testBit_eq; intro w
      have h1 := congrArg (fun z => z.testBit w) ha
      have h2 := congrArg (fun z => z.testBit w) hb
      simp only [Nat.testBit_and, Nat.testBit_or] at h1 h2 ⊢
      revert h1 h2
      cases s.testBit w <;> cases a.testBit w <;> cases b.testBit w <;> decide
    · intro hab
      constructor <;> apply Nat.eq_of_testBit_eq <;> intro w <;>
        (have h := congrArg (fun z => z.testBit w) hab
         simp only [Nat.testBit_and, Nat.testBit_or] at h ⊢
         revert h
         cases s.testBit w <;> cases a.testBit w <;> cases b.testBit w <;> decide)

theorem foldl_land_assoc (xs : List ℕ) (a b : ℕ) :
    xs.foldl Nat.land (a &&& b) = a &&& xs.foldl Nat.land b := by
  induction xs generalizing a b with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.foldl_cons, land_eq]
    rw [Nat.and_assoc, ih a (b &&& x)]

theorem foldl_land_append (xs ys : List ℕ) (M : ℕ) :
    (xs ++ ys).foldl Nat.land M = xs.foldl Nat.land M &&& ys.foldl Nat.land M := by
  rw [List.foldl_append]
  have h1 : xs.foldl Nat.land M = xs.foldl Nat.land M &&& M := by
    induction xs generalizing M with
    | nil => simp
    | cons x rest ih =>
      simp only [List.foldl_cons, land_eq]
      rw [foldl_land_assoc]
      apply Nat.eq_of_testBit_eq; intro s
      simp only [Nat.testBit_and]
      cases M.testBit s <;> cases (rest.foldl Nat.land x).testBit s <;> simp
  conv_lhs => rw [h1]
  exact foldl_land_assoc ys (xs.foldl Nat.land M) M

theorem foldl_land_mem_eq {xs ys : List ℕ} {M : ℕ}
    (heq : ∀ x, x ∈ xs ↔ x ∈ ys) :
    xs.foldl Nat.land M = ys.foldl Nat.land M := by
  have hbit : ∀ (zs : List ℕ) (acc s : ℕ),
      (zs.foldl Nat.land acc).testBit s = true ↔
        acc.testBit s = true ∧ ∀ z ∈ zs, z.testBit s = true := by
    intro zs
    induction zs with
    | nil => intro acc s; simp
    | cons z rest ih =>
      intro acc s
      simp only [List.foldl_cons, land_eq, ih, Nat.testBit_and, Bool.and_eq_true, List.mem_cons]
      constructor
      · rintro ⟨⟨ha, hz⟩, hrest⟩
        exact ⟨ha, fun w hw => hw.elim (fun e => e ▸ hz) (hrest w)⟩
      · rintro ⟨ha, hall⟩
        exact ⟨⟨ha, hall z (Or.inl rfl)⟩, fun w hw => hall w (Or.inr hw)⟩
  apply Nat.eq_of_testBit_eq; intro s
  apply Bool.eq_iff_iff.mpr
  rw [hbit xs M s, hbit ys M s]
  constructor
  · rintro ⟨hM, h⟩; exact ⟨hM, fun z hz => h z ((heq z).mpr hz)⟩
  · rintro ⟨hM, h⟩; exact ⟨hM, fun z hz => h z ((heq z).mp hz)⟩

theorem meet_decompose_nat {n : ℕ} {F : List (ℕ × ℕ)} {pre : List ℕ}
    {S : Set (Dom (univYF n F))}
    (hm : Meet (decM (univYF n F) '' { x | x ∈ rawYF n (univYF n F) ++ pre }) S) :
    S = ∅ ∨ ∃ (rMask : ℕ) (P : List ℕ), (∀ p ∈ P, p ∈ pre) ∧
      S = decM (univYF n F) (ttNeedYF n rMask (univYF n F) &&& P.foldl Nat.land (univYF n F)) := by
  have hM : ∀ s, (univYF n F).testBit s = true → s < 2 ^ n := fun _ => univYF_testBit_lt
  induction hm with
  | atom hx =>
    rcases hx with ⟨y, hy, rfl⟩
    rcases List.mem_append.mp hy with hy | hy
    · simp only [rawYF, List.mem_map, List.mem_range] at hy
      rcases hy with ⟨v, _, rfl⟩
      refine Or.inr ⟨1 <<< v, [], fun _ h => by simp at h, ?_⟩
      simp only [List.foldl_nil, ttNeedYF_oneBit hM, ttVarYF_and_mask hM]
    · refine Or.inr ⟨0, [y], fun p hp => (List.mem_singleton.mp hp) ▸ hy, ?_⟩
      simp only [List.foldl_cons, List.foldl_nil, land_eq, ttNeedYF_zero hM]
      rw [decM_and, decM_and, decM_self, Set.univ_inter, Set.univ_inter]
  | top =>
    refine Or.inr ⟨0, [], fun _ h => by simp at h, ?_⟩
    simp only [List.foldl_nil, ttNeedYF_zero hM, Nat.and_self, decM_self]
  | bot => exact Or.inl rfl
  | inter _ _ ih1 ih2 =>
    rcases ih1 with rfl | ⟨r1, P1, hP1, rfl⟩
    · exact Or.inl (Set.empty_inter _)
    rcases ih2 with rfl | ⟨r2, P2, hP2, rfl⟩
    · exact Or.inl (Set.inter_empty _)
    refine Or.inr ⟨r1 ||| r2, P1 ++ P2, fun p hp => (List.mem_append.mp hp).elim (hP1 p) (hP2 p), ?_⟩
    rw [← decM_and, ← ttNeedYF_or hM, foldl_land_append]
    congr 1
    apply Nat.eq_of_testBit_eq; intro s
    simp only [Nat.testBit_and]
    cases (ttNeedYF n r1 (univYF n F)).testBit s <;> cases (ttNeedYF n r2 (univYF n F)).testBit s <;>
      cases (P1.foldl Nat.land (univYF n F)).testBit s <;>
      cases (P2.foldl Nat.land (univYF n F)).testBit s <;> simp

theorem meetNat_decompose_on_edges {n : ℕ} {H F : List (ℕ × ℕ)} {pre : List ℕ} {x : ℕ}
    (hv : ValidState n H F)
    (hx : MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre) x)
    (hne : x &&& edgePtsMaskYF H ≠ 0) :
    ∃ mt ∈ masksTTYF n H (univYF n F), ∃ P : List ℕ, List.Sublist P pre ∧
      x = mt &&& P.foldl Nat.land (univYF n F) := by
  set M := univYF n F
  have hM : ∀ s, M.testBit s = true → s < 2 ^ n := fun _ => univYF_testBit_lt
  rcases meet_decompose_nat (meetNat_iff.mp hx).2 with hemp | ⟨rMask, P, hP, hS⟩
  · exfalso
    have hx0 : x = 0 := (decM_inj hx.1 (by simp)).mp (by rw [hemp, decM_zero])
    simp [hx0] at hne
  have hxEq : x = ttNeedYF n rMask M &&& P.foldl Nat.land M := by
    apply (decM_inj hx.1 ?_).mp hS
    apply Nat.eq_of_testBit_eq; intro s
    have ht := congrArg (fun z => z.testBit s) (ttNeedYF_and_mask (n := n) (a := rMask) hM)
    simp only [Nat.testBit_and] at ht ⊢
    revert ht
    cases (ttNeedYF n rMask M).testBit s <;> cases (P.foldl Nat.land M).testBit s <;>
      cases M.testBit s <;> decide
  have hexBit : ∃ s, (x &&& edgePtsMaskYF H).testBit s = true := by
    by_contra hall
    push Not at hall
    apply hne
    apply Nat.eq_of_testBit_eq; intro s
    simp only [Nat.zero_testBit]
    exact Bool.eq_false_iff.mpr (hall s)
  obtain ⟨s, hs⟩ := hexBit
  rw [Nat.testBit_and, Bool.and_eq_true, testBit_edgePtsMaskYF, List.any_eq_true] at hs
  obtain ⟨hxs, e, heH, hes⟩ := hs
  rw [decide_eq_true_eq] at hes
  have hneed : (ttNeedYF n rMask M).testBit s = true := by
    rw [hxEq, Nat.testBit_and, Bool.and_eq_true] at hxs; exact hxs.1
  rw [testBit_ttNeedYF hM, Bool.and_eq_true, beq_iff_eq] at hneed
  have hrSub : ∀ w, rMask.testBit w = true → w = e.1 ∨ w = e.2 := by
    intro w hw
    have := congrArg (fun z => z.testBit w) hneed.2
    rw [Nat.testBit_and, hw, Bool.and_true] at this
    rw [← hes] at this
    exact (twoBit_testBit e.1 e.2 w).mp this
  obtain ⟨he1, he2, _⟩ := hv.1 e heH
  have hrMem : ttNeedYF n rMask M ∈ masksTTYF n H M := by
    unfold masksTTYF
    apply List.mem_map.mpr
    refine ⟨rMask, ?_, rfl⟩
    cases hb1 : rMask.testBit e.1 <;> cases hb2 : rMask.testBit e.2
    · have hr0 : rMask = 0 := by
        apply Nat.eq_of_testBit_eq; intro w
        cases hw : rMask.testBit w
        · simp
        · rcases hrSub w hw with rfl | rfl <;> simp_all
      subst hr0; simp
    · have hr2 : rMask = 1 <<< e.2 := by
        apply Nat.eq_of_testBit_eq; intro w
        rw [testBit_one_shiftLeft]
        by_cases hw : e.2 = w
        · subst hw; simp [hb2]
        · simp only [hw, decide_false]
          cases hrw : rMask.testBit w
          · rfl
          · rcases hrSub w hrw with rfl | rfl <;> simp_all
      subst hr2
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr (Or.inl ⟨e.2, he2, rfl⟩)
    · have hr1 : rMask = 1 <<< e.1 := by
        apply Nat.eq_of_testBit_eq; intro w
        rw [testBit_one_shiftLeft]
        by_cases hw : e.1 = w
        · subst hw; simp [hb1]
        · simp only [hw, decide_false]
          cases hrw : rMask.testBit w
          · rfl
          · rcases hrSub w hrw with rfl | rfl <;> simp_all
      subst hr1
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr (Or.inl ⟨e.1, he1, rfl⟩)
    · have hr12 : rMask = (1 <<< e.1) ||| (1 <<< e.2) := by
        apply Nat.eq_of_testBit_eq; intro w
        rw [Nat.testBit_or, testBit_one_shiftLeft, testBit_one_shiftLeft]
        by_cases hw1 : e.1 = w
        · subst hw1; simp [hb1]
        · by_cases hw2 : e.2 = w
          · subst hw2; simp [hb2]
          · simp only [hw1, hw2, decide_false, Bool.or_false]
            cases hrw : rMask.testBit w
            · rfl
            · rcases hrSub w hrw with rfl | rfl <;> simp_all
      subst hr12
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map]
      exact Or.inr (Or.inr ⟨e, heH, rfl⟩)
  let P' := pre.filter (fun y => P.contains y)
  have hsub : List.Sublist P' pre := List.filter_sublist
  have hPeq : ∀ y, y ∈ P ↔ y ∈ P' := by
    intro y
    simp only [P', List.mem_filter, List.contains_eq_mem, decide_eq_true_eq]
    exact ⟨fun hy => ⟨hP y hy, hy⟩, fun h => h.2⟩
  refine ⟨ttNeedYF n rMask M, hrMem, P', hsub, ?_⟩
  rw [hxEq, foldl_land_mem_eq hPeq]

theorem lexMin_operands {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf : List ℕ} {g : ℕ}
    (hv : ValidState n H F)
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre ++ g :: suf))
    (hmin : ∀ k' < (pre ++ g :: suf).length, ¬ HasRunYF n H F k') :
    ∃ a b : ℕ, g = a ||| b ∧ a ≠ b ∧
      MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre) a ∧
      MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre) b ∧
      a ≠ 0 ∧ a ≠ univYF n F ∧ a &&& edgePtsMaskYF H ≠ 0 ∧
      b ≠ 0 ∧ b ≠ univYF n F ∧ b &&& edgePtsMaskYF H ≠ 0 := by
  set M := univYF n F
  set raw := rawYF n M
  set ep := edgePtsMaskYF H
  obtain ⟨_, ⟨a, b, ha, hb, hgab⟩, _⟩ := runListFrom_append.mp hrun
  have ha_ep : a &&& ep ≠ 0 := by
    intro h0
    have hsub : decM M b ⊆ decM M g := by
      rw [hgab, decM_or]; exact Set.subset_union_right
    have heq : decM M b ∩ decM M ep = decM M g ∩ decM M ep := by
      rw [hgab, decM_or, Set.union_inter_distrib_right]
      have ha0' : decM M a ∩ decM M ep = ∅ := by rw [← decM_and, h0, decM_zero]
      rw [ha0', Set.empty_union]
    exact lexMin_eliminate_step hv hrun hmin (meetNat_iff.mp hb).2 hsub heq
  have hb_ep : b &&& ep ≠ 0 := by
    intro h0
    have hsub : decM M a ⊆ decM M g := by
      rw [hgab, decM_or]; exact Set.subset_union_left
    have heq : decM M a ∩ decM M ep = decM M g ∩ decM M ep := by
      rw [hgab, decM_or, Set.union_inter_distrib_right]
      have hb0' : decM M b ∩ decM M ep = ∅ := by rw [← decM_and, h0, decM_zero]
      rw [hb0', Set.union_empty]
    exact lexMin_eliminate_step hv hrun hmin (meetNat_iff.mp ha).2 hsub heq
  have ha0 : a ≠ 0 := fun h => ha_ep (by simp [h])
  have hb0 : b ≠ 0 := fun h => hb_ep (by simp [h])
  have haM : a ≠ M := by
    intro h
    have hgm : g = M := by
      rw [hgab, h]
      apply Nat.eq_of_testBit_eq; intro s
      have h1 := congrArg (fun z => z.testBit s) hb.1
      simp only [Nat.testBit_or, Nat.testBit_and] at h1 ⊢
      revert h1
      cases M.testBit s <;> cases b.testBit s <;> decide
    exact lexMin_eliminate_step hv hrun hmin (hgm ▸ decM_self M ▸ Meet.top) Set.Subset.rfl rfl
  have hbM : b ≠ M := by
    intro h
    have hgm : g = M := by
      rw [hgab, h]
      apply Nat.eq_of_testBit_eq; intro s
      have h1 := congrArg (fun z => z.testBit s) ha.1
      simp only [Nat.testBit_or, Nat.testBit_and] at h1 ⊢
      revert h1
      cases M.testBit s <;> cases a.testBit s <;> decide
    exact lexMin_eliminate_step hv hrun hmin (hgm ▸ decM_self M ▸ Meet.top) Set.Subset.rfl rfl
  have hab : a ≠ b := by
    intro h
    have hga : g = a := by rw [hgab, h, Nat.or_self]
    exact lexMin_eliminate_step hv hrun hmin (hga ▸ (meetNat_iff.mp ha).2) Set.Subset.rfl rfl
  exact ⟨a, b, hgab, hab, ha, hb, ha0, haM, ha_ep, hb0, hbM, hb_ep⟩

/-! ### Pruning Lemma 3: `usesLast` commutation swap -/

theorem lex_append_left {α : Type} {r : α → α → Prop} :
    ∀ (pre l₁ l₂ : List α), List.Lex r l₁ l₂ → List.Lex r (pre ++ l₁) (pre ++ l₂)
  | [], _, _, h => h
  | _ :: rest, l₁, l₂, h => List.Lex.cons (lex_append_left rest l₁ l₂ h)

theorem lexMin_commSwap {n : ℕ} {H F : List (ℕ × ℕ)} {pre0 suf : List ℕ} {lastG g a b : ℕ}
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F))
      (pre0 ++ lastG :: g :: suf))
    (hlex : ∀ gs', gs'.length = (pre0 ++ lastG :: g :: suf).length →
      RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) gs' →
      ¬ List.Lex (· < ·) gs' (pre0 ++ lastG :: g :: suf))
    (ha : MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre0) a)
    (hb : MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre0) b)
    (hg : g = a ||| b) :
    ¬ (g < lastG) := by
  intro hlt
  set M := univYF n F
  set raw := rawYF n M
  set target := edgeTTYF n H M
  obtain ⟨hp0, ⟨a0, b0, ha0, hb0, hlg⟩, _, hsuf⟩ := runListFrom_append.mp hrun
  let gs' := pre0 ++ g :: lastG :: suf
  have hlen : gs'.length = (pre0 ++ lastG :: g :: suf).length := by simp [gs']
  have hrun' : RunListFrom M raw target gs' := by
    apply runListFrom_append.mpr
    refine ⟨hp0, ⟨a, b, ha, hb, hg⟩, ?_, ?_⟩
    · refine ⟨a0, b0, meetNat_weaken (fun x hx => List.mem_append_left _ hx) ha0,
        meetNat_weaken (fun x hx => List.mem_append_left _ hx) hb0, hlg⟩
    · apply runListFrom_equiv_basis (B₁ := (raw ++ pre0) ++ [lastG] ++ [g]) _ hsuf
      intro x; simp; tauto
  have hl : List.Lex (· < ·) gs' (pre0 ++ lastG :: g :: suf) :=
    lex_append_left pre0 (g :: lastG :: suf) (lastG :: g :: suf) (List.Lex.rel hlt)
  exact hlex gs' hlen hrun' hl

/-! ### Pruning Lemma 4: Stabilizer `Aut(H, F)` lex-minimality -/

def applyPermLoop (tbl : List ℕ) (f : ℕ) (s : ℕ) (acc : ℕ) : ℕ :=
  match tbl with
  | [] => acc
  | s2 :: rest =>
    let acc' := match f.testBit s with
      | true => Nat.lor acc (1 <<< s2)
      | false => acc
    applyPermLoop rest f (s + 1) acc'

def applyPerm (tbl : List ℕ) (f : ℕ) : ℕ :=
  applyPermLoop tbl f 0 0

theorem applyPermLoop_testBit (tbl : List ℕ) (f s acc y : ℕ) :
    (applyPermLoop tbl f s acc).testBit y = true ↔
      acc.testBit y = true ∨
      ∃ (i : ℕ) (hi : i < tbl.length), tbl[i] = y ∧ f.testBit (s + i) = true := by
  induction tbl generalizing s acc with
  | nil => simp [applyPermLoop]
  | cons s2 rest ih =>
    simp only [applyPermLoop]
    rw [ih]
    have hacc' : (match f.testBit s with
        | true => Nat.lor acc (1 <<< s2)
        | false => acc).testBit y = true ↔
        acc.testBit y = true ∨ (f.testBit s = true ∧ s2 = y) := by
      cases hfs : f.testBit s
      · simp
      · simp only [lor_eq, Nat.testBit_or, testBit_one_shiftLeft, Bool.or_eq_true,
          decide_eq_true_eq, true_and]
    rw [hacc']
    constructor
    · rintro ((ha | ⟨hfs, rfl⟩) | ⟨i, hi, hget, hfi⟩)
      · exact Or.inl ha
      · exact Or.inr ⟨0, by simp, rfl, by simpa using hfs⟩
      · exact Or.inr ⟨i + 1, by simp [hi], by simpa using hget,
          by rwa [show s + (i + 1) = s + 1 + i by omega]⟩
    · rintro (ha | ⟨i, hi, hget, hfi⟩)
      · exact Or.inl (Or.inl ha)
      · cases i with
        | zero => exact Or.inl (Or.inr ⟨by simpa using hfi, by simpa using hget⟩)
        | succ j =>
          exact Or.inr ⟨j, by simpa using hi, by simpa using hget,
            by rwa [show s + 1 + j = s + (j + 1) by omega]⟩

theorem applyPerm_testBit (tbl : List ℕ) (f y : ℕ) :
    (applyPerm tbl f).testBit y = true ↔
      ∃ (i : ℕ) (hi : i < tbl.length), tbl[i] = y ∧ f.testBit i = true := by
  simpa [applyPerm] using applyPermLoop_testBit tbl f 0 0 y

theorem applyPerm_zero (tbl : List ℕ) : applyPerm tbl 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro y
  apply Bool.eq_iff_iff.mpr
  simp [applyPerm_testBit]

theorem applyPerm_or (tbl : List ℕ) (a b : ℕ) :
    applyPerm tbl (a ||| b) = applyPerm tbl a ||| applyPerm tbl b := by
  apply Nat.eq_of_testBit_eq; intro y
  apply Bool.eq_iff_iff.mpr
  simp only [applyPerm_testBit, Nat.testBit_or, Bool.or_eq_true]
  constructor
  · rintro ⟨i, hi, hget, ha | hb⟩
    · exact Or.inl ⟨i, hi, hget, ha⟩
    · exact Or.inr ⟨i, hi, hget, hb⟩
  · rintro (⟨i, hi, hget, ha⟩ | ⟨i, hi, hget, hb⟩)
    · exact ⟨i, hi, hget, Or.inl ha⟩
    · exact ⟨i, hi, hget, Or.inr hb⟩

theorem applyPerm_and {tbl : List ℕ} (hnd : tbl.Nodup) (a b : ℕ) :
    applyPerm tbl (a &&& b) = applyPerm tbl a &&& applyPerm tbl b := by
  apply Nat.eq_of_testBit_eq; intro y
  apply Bool.eq_iff_iff.mpr
  simp only [applyPerm_testBit, Nat.testBit_and, Bool.and_eq_true]
  constructor
  · rintro ⟨i, hi, hget, ha, hb⟩
    exact ⟨⟨i, hi, hget, ha⟩, ⟨i, hi, hget, hb⟩⟩
  · rintro ⟨⟨i, hi, hgeti, ha⟩, ⟨j, hj, hgetj, hb⟩⟩
    have hij : i = j := (List.Nodup.getElem_inj_iff hnd).mp (hgeti.trans hgetj.symm)
    subst hij
    exact ⟨i, hi, hgeti, ha, hb⟩

def ValidAutTbl (M edgeTT : ℕ) (raw tbl : List ℕ) : Prop :=
  tbl.Nodup ∧ applyPerm tbl M = M ∧ applyPerm tbl edgeTT = edgeTT ∧
    ∀ r ∈ raw, applyPerm tbl r ∈ raw

instance (M edgeTT : ℕ) (raw tbl : List ℕ) : Decidable (ValidAutTbl M edgeTT raw tbl) := by
  unfold ValidAutTbl; infer_instance

theorem applyPerm_isMeetLoop {tbl : List ℕ} (hnd : tbl.Nodup) (M : ℕ)
    {B B' : List ℕ} (hB : ∀ b ∈ B, applyPerm tbl b ∈ B') {t acc : ℕ}
    (hacc : Meet (decM M '' { x | x ∈ B' }) (decM M (applyPerm tbl acc))) :
    Meet (decM M '' { x | x ∈ B' }) (decM M (applyPerm tbl (isMeetLoop t B acc))) := by
  induction B generalizing acc with
  | nil => exact hacc
  | cons b bs ih =>
    simp only [isMeetLoop]
    cases Nat.beq (Nat.land t b) t
    · exact ih (fun x hx => hB x (by simp [hx])) hacc
    · apply ih (fun x hx => hB x (by simp [hx]))
      rw [land_eq, applyPerm_and hnd, decM_and]
      exact hacc.inter (Meet.atom ⟨applyPerm tbl b, hB b (by simp), rfl⟩)

theorem applyPerm_meetNat {tbl : List ℕ} (hnd : tbl.Nodup) {M : ℕ} (hM : applyPerm tbl M = M)
    {B B' : List ℕ} (hB : ∀ b ∈ B, applyPerm tbl b ∈ B') {t : ℕ}
    (ht : MeetNat M B t) : MeetNat M B' (applyPerm tbl t) := by
  have htM : applyPerm tbl t &&& M = applyPerm tbl t := by
    rw [← hM, ← applyPerm_and hnd, ht.1]
  refine ⟨htM, (isMeet_iff htM).mpr ?_⟩
  rcases ht with ⟨_, hmt⟩
  unfold isMeet at hmt
  cases h0 : Nat.beq t 0
  · rw [h0] at hmt
    have heq : isMeetLoop t B M = t := Nat.eq_of_beq_eq_true hmt
    rw [← heq]
    apply applyPerm_isMeetLoop hnd M hB
    rw [hM, decM_self]; exact Meet.top
  · have ht0 : t = 0 := Nat.eq_of_beq_eq_true h0
    subst ht0
    rw [applyPerm_zero, decM_zero]; exact Meet.bot

theorem applyPerm_runListFrom {tbl : List ℕ} (hnd : tbl.Nodup) {M edgeTT : ℕ}
    (hM : applyPerm tbl M = M) (hE : applyPerm tbl edgeTT = edgeTT)
    {B B' gs : List ℕ} (hB : ∀ b ∈ B, applyPerm tbl b ∈ B')
    (hr : RunListFrom M B edgeTT gs) :
    RunListFrom M B' edgeTT (gs.map (applyPerm tbl)) := by
  induction gs generalizing B B' with
  | nil =>
    rw [← hE]
    exact applyPerm_meetNat hnd hM hB hr
  | cons g rest ih =>
    rcases hr with ⟨⟨a, b, ha, hb, rfl⟩, hrest⟩
    refine ⟨⟨applyPerm tbl a, applyPerm tbl b,
      applyPerm_meetNat hnd hM hB ha, applyPerm_meetNat hnd hM hB hb,
      applyPerm_or tbl a b⟩, ?_⟩
    apply ih (B' := B' ++ [applyPerm tbl (a ||| b)]) _ hrest
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (hB x hx)
    · rw [List.mem_singleton.mp hx]; exact List.mem_append_right _ (by simp)

theorem list_map_eq_self {α : Type} {f : α → α} :
    ∀ (l : List α), (∀ x ∈ l, f x = x) → l.map f = l
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.map_cons, h x (by simp), list_map_eq_self xs (fun y hy => h y (by simp [hy]))]

theorem lexMin_autStab {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf tbl : List ℕ} {g : ℕ}
    (haut : ValidAutTbl (univYF n F) (edgeTTYF n H (univYF n F)) (rawYF n (univYF n F)) tbl)
    (hstab : ∀ h ∈ pre, applyPerm tbl h = h)
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F))
      (pre ++ g :: suf))
    (hlex : ∀ gs', gs'.length = (pre ++ g :: suf).length →
      RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) gs' →
      ¬ List.Lex (· < ·) gs' (pre ++ g :: suf)) :
    ¬ (applyPerm tbl g < g) := by
  intro hlt
  rcases haut with ⟨hnd, hM, hE, hraw⟩
  let gs' := (pre ++ g :: suf).map (applyPerm tbl)
  have hrun' := applyPerm_runListFrom hnd hM hE hraw hrun
  have hpre_eq : pre.map (applyPerm tbl) = pre := list_map_eq_self pre hstab
  have hgs' : gs' = pre ++ applyPerm tbl g :: suf.map (applyPerm tbl) := by
    simp [gs', hpre_eq]
  have hl : List.Lex (· < ·) gs' (pre ++ g :: suf) := by
    rw [hgs']
    exact lex_append_left pre _ _ (List.Lex.rel hlt)
  exact hlex gs' (by simp [gs']) hrun' hl

/-! ### Pruning Lemma 5 (`birth_lex`) & Lemma 6 (`eg`-subset) -/

theorem validPrefix_weaken_basis {M : ℕ} {B₁ B₂ pre : List ℕ}
    (hsub : ∀ x ∈ B₁, x ∈ B₂) (hp : ValidPrefix M B₁ pre) :
    ValidPrefix M B₂ pre := by
  induction pre generalizing B₁ B₂ with
  | nil => trivial
  | cons g rest ih =>
    rcases hp with ⟨⟨a, b, ha, hb, rfl⟩, hrest⟩
    refine ⟨⟨a, b, meetNat_weaken hsub ha, meetNat_weaken hsub hb, rfl⟩, ?_⟩
    exact ih (fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ (hsub x hx)
      · exact List.mem_append_right _ hx) hrest

theorem validPrefix_append {M : ℕ} {B p₁ p₂ : List ℕ} :
    ValidPrefix M B (p₁ ++ p₂) ↔ ValidPrefix M B p₁ ∧ ValidPrefix M (B ++ p₁) p₂ := by
  induction p₁ generalizing B with
  | nil => simp [ValidPrefix]
  | cons g rest ih =>
    simp only [List.cons_append, ValidPrefix]
    rw [ih, List.append_assoc, List.singleton_append]
    tauto

theorem lexMin_birth_lex {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf : List ℕ} {g a b mb t : ℕ}
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F))
      (pre ++ g :: suf))
    (hlex : ∀ gs', gs'.length = (pre ++ g :: suf).length →
      RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) gs' →
      ¬ List.Lex (· < ·) gs' (pre ++ g :: suf))
    (hmb : mb ≤ t) (ht : t < pre.length)
    (ha : MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre.take mb) a)
    (hb : MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre.take mb) b)
    (hg : g = a ||| b) :
    ¬ (g < pre[t]) := by
  intro hlt
  set M := univYF n F
  set raw := rawYF n M
  set target := edgeTTYF n H M
  let A := pre.take t
  let B := pre.drop t
  have hpreAB : pre = A ++ B := (List.take_append_drop t pre).symm
  have hBne : B ≠ [] := by
    intro hB
    have hlen := congrArg List.length hpreAB
    simp only [hB, List.append_nil, List.length_take, A] at hlen
    omega
  obtain ⟨bt, Btail, hBeq⟩ := List.exists_cons_of_ne_nil hBne
  have hbt : bt = pre[t] := by
    have h1 : B[0]'(by simp [hBeq]) = pre[t] := by
      simp [B]
    simpa [hBeq] using h1
  have hpre_sub : ∀ x ∈ raw ++ pre.take mb, x ∈ raw ++ A := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ hx
    · refine List.mem_append_right _ ?_
      have htake : pre.take mb = (pre.take t).take mb := by
        rw [List.take_take, Nat.min_eq_left hmb]
      rw [htake] at hx
      exact List.mem_of_mem_take hx
  have haA : MeetNat M (raw ++ A) a := meetNat_weaken hpre_sub ha
  have hbA : MeetNat M (raw ++ A) b := meetNat_weaken hpre_sub hb
  obtain ⟨hp_pre, _, hsuf⟩ := runListFrom_append.mp hrun
  rw [hpreAB] at hp_pre
  obtain ⟨hpA, hpB⟩ := validPrefix_append.mp hp_pre
  let gs' := A ++ g :: B ++ suf
  have hlen : gs'.length = (pre ++ g :: suf).length := by
    have := congrArg List.length hpreAB
    simp only [gs', List.length_append, List.length_cons] at this ⊢
    omega
  have hrun' : RunListFrom M raw target gs' := by
    have hgs'_eq : gs' = (A ++ [g] ++ B) ++ suf := by simp [gs', List.append_assoc]
    rw [hgs'_eq]
    apply runListFrom_append.mpr
    constructor
    · rw [validPrefix_append]
      refine ⟨validPrefix_append.mpr ⟨hpA, ⟨a, b, haA, hbA, hg⟩, trivial⟩, ?_⟩
      apply validPrefix_weaken_basis (B₁ := raw ++ A) _ hpB
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ (List.mem_append_left _ hx)
    · apply runListFrom_equiv_basis (B₁ := (raw ++ pre) ++ [g]) _ hsuf
      intro x
      rw [hpreAB]
      simp; tauto
  have hlex' : List.Lex (· < ·) gs' (pre ++ g :: suf) := by
    have h1 : gs' = A ++ (g :: B ++ suf) := by simp [gs']
    have h2 : pre ++ g :: suf = A ++ (bt :: (Btail ++ g :: suf)) := by
      rw [hpreAB, hBeq]; simp [List.append_assoc]
    rw [h1, h2]
    exact lex_append_left A _ _ (List.Lex.rel (hbt.symm ▸ hlt))
  exact hlex gs' hlen hrun' hlex'

theorem lexMin_not_eg_sub {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf : List ℕ} {g a b : ℕ}
    (hv : ValidState n H F)
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F))
      (pre ++ g :: suf))
    (hmin : ∀ k' < (pre ++ g :: suf).length, ¬ HasRunYF n H F k')
    (hb : MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre) b)
    (hg : g = a ||| b)
    (hsub : (a &&& edgePtsMaskYF H) &&& (b &&& edgePtsMaskYF H) = a &&& edgePtsMaskYF H) :
    False := by
  set M := univYF n F
  set ep := edgePtsMaskYF H
  have hbg : decM M b ⊆ decM M g := by rw [hg, decM_or]; exact Set.subset_union_right
  have heq : decM M b ∩ decM M ep = decM M g ∩ decM M ep := by
    rw [← decM_and, ← decM_and]
    congr 1
    rw [hg]
    apply Nat.eq_of_testBit_eq; intro s
    have h1 := congrArg (fun z => z.testBit s) hsub
    simp only [Nat.testBit_and, Nat.testBit_or] at h1 ⊢
    revert h1
    cases a.testBit s <;> cases b.testBit s <;> cases ep.testBit s <;> decide
  exact lexMin_eliminate_step hv hrun hmin (meetNat_iff.mp hb).2 hbg heq

/-! ## Section 5: Base Cases & Peel-and-Embed Reductions -/

theorem baseZeroOneEdgesYF {n : ℕ} {H F : List (ℕ × ℕ)} (h : H.length ≤ 1) :
    OrCostLB n H F (H.length - 1) := by
  intro k _; omega

theorem mkBitmask_lt_two_pow (n : ℕ) (p : ℕ → Bool) : mkBitmask n p < 2 ^ n := by
  induction n with
  | zero => simp [mkBitmask]
  | succ k ih =>
    simp only [mkBitmask]
    have hpow : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
    have h1 : mkBitmask k p < 2 ^ (k + 1) := lt_trans ih hpow
    split_ifs
    · exact Nat.or_lt_two_pow h1 (oneBit_lt_two_pow (by omega))
    · exact h1

theorem baseTwoEdgesYF {n : ℕ} {H F : List (ℕ × ℕ)}
    (hv : ValidState n H F) (hnd : NoDupEdges H) (hlen : H.length = 2) :
    OrCostLB n H F 1 := by
  intro k hr
  by_contra hlt
  have hk0 : k = 0 := by omega
  subst hk0
  cases hr with
  | done hm =>
    have hM : ∀ s, (univYF n F).testBit s = true → s < 2 ^ n := fun _ => univYF_testBit_lt
    have hm' : Meet (decM (univYF n F) '' { x | x ∈ rawYF n (univYF n F) ++ [] })
        (targetSet n H F) := by
      simpa only [List.append_nil, ← rawSet_eq_image] using hm
    match H, hlen, hv, hnd, hm' with
    | [e₁, e₂], _, hv, hnd, hm' =>
      have hne12 : undirEq e₁ e₂ = false := by
        simp only [NoDupEdges, List.pairwise_cons, List.mem_singleton, forall_eq] at hnd
        exact hnd.1
      let s₁ := (1 <<< e₁.1) ||| (1 <<< e₁.2)
      let s₂ := (1 <<< e₂.1) ||| (1 <<< e₂.2)
      have hs₁M : (univYF n F).testBit s₁ = true := edgePt_mem_univYF hv (by simp)
      have hs₂M : (univYF n F).testBit s₂ = true := edgePt_mem_univYF hv (by simp)
      have hs₁T : (⟨s₁, hs₁M⟩ : Dom (univYF n F)) ∈ targetSet n [e₁, e₂] F :=
        edgePt_mem_edgeTTYF hv (by simp)
      have hs₂T : (⟨s₂, hs₂M⟩ : Dom (univYF n F)) ∈ targetSet n [e₁, e₂] F :=
        edgePt_mem_edgeTTYF hv (by simp)
      rcases meet_decompose_nat hm' with hemp | ⟨rMask, P, hP, hS⟩
      · rw [hemp] at hs₁T; exact hs₁T
      · have hPnil : P = [] := by
          cases P with
          | nil => rfl
          | cons p _ => exfalso; exact List.not_mem_nil (hP p (by simp))
        subst hPnil
        simp only [List.foldl_nil, ttNeedYF_and_mask hM] at hS
        have hs₁R : s₁ &&& rMask = rMask := by
          rw [hS, mem_decM, testBit_ttNeedYF hM, hs₁M, Bool.true_and, beq_iff_eq] at hs₁T
          exact hs₁T
        have hs₂R : s₂ &&& rMask = rMask := by
          rw [hS, mem_decM, testBit_ttNeedYF hM, hs₂M, Bool.true_and, beq_iff_eq] at hs₂T
          exact hs₂T
        have hrSub1 : ∀ w, rMask.testBit w = true → w = e₁.1 ∨ w = e₁.2 := by
          intro w hw
          have := congrArg (fun z => z.testBit w) hs₁R
          rw [Nat.testBit_and, hw, Bool.and_true] at this
          exact (twoBit_testBit e₁.1 e₁.2 w).mp this
        have hrSub2 : ∀ w, rMask.testBit w = true → w = e₂.1 ∨ w = e₂.2 := by
          intro w hw
          have := congrArg (fun z => z.testBit w) hs₂R
          rw [Nat.testBit_and, hw, Bool.and_true] at this
          exact (twoBit_testBit e₂.1 e₂.2 w).mp this
        have hrAtMostOne : ∀ w₁ w₂, rMask.testBit w₁ = true → rMask.testBit w₂ = true → w₁ = w₂ := by
          intro w₁ w₂ hw₁ hw₂
          by_contra hne
          rcases hrSub1 w₁ hw₁ with rfl | rfl <;> rcases hrSub1 w₂ hw₂ with rfl | rfl
          · exact hne rfl
          · rcases hrSub2 _ hw₁ with h1 | h1 <;> rcases hrSub2 _ hw₂ with h2 | h2
            · exact hne (h1.trans h2.symm)
            · simp [undirEq, h1, h2] at hne12
            · simp [undirEq, h1, h2] at hne12
            · exact hne (h1.trans h2.symm)
          · rcases hrSub2 _ hw₁ with h1 | h1 <;> rcases hrSub2 _ hw₂ with h2 | h2
            · exact hne (h1.trans h2.symm)
            · simp [undirEq, h1, h2] at hne12
            · simp [undirEq, h1, h2] at hne12
            · exact hne (h1.trans h2.symm)
          · exact hne rfl
        have hrLt : rMask < 2 ^ n := by
          have hrEq : rMask = mkBitmask n (fun w => rMask.testBit w) := by
            apply Nat.eq_of_testBit_eq; intro w
            rw [testBit_mkBitmask]
            cases hw : rMask.testBit w
            · simp
            · obtain ⟨he1, he2, _⟩ := hv.1 e₁ (by simp)
              have hwn : w < n := by rcases hrSub1 w hw with rfl | rfl <;> assumption
              simp [hwn]
          rw [hrEq]; exact mkBitmask_lt_two_pow n _
        have hrDom : (univYF n F).testBit rMask = true := by
          rw [testBit_univYF, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
          refine ⟨hrLt, Bool.eq_false_iff.mpr fun hf => ?_⟩
          rw [hasEdge_eq_true] at hf
          obtain ⟨f, hfF, h1, h2⟩ := hf
          exact (hv.2.1 f hfF).2.2 (hrAtMostOne f.1 f.2 h1 h2)
        have hrInNeed : (⟨rMask, hrDom⟩ : Dom (univYF n F)) ∈ targetSet n [e₁, e₂] F := by
          rw [hS, mem_decM, testBit_ttNeedYF hM, hrDom, Bool.true_and, Nat.and_self,
            beq_self_eq_true]
        rw [targetSet, mem_decM, testBit_edgeTTYF hM, hrDom, Bool.true_and,
          hasEdge_eq_true] at hrInNeed
        obtain ⟨e, heH, h1, h2⟩ := hrInNeed
        exact (hv.1 e heH).2.2 (hrAtMostOne e.1 e.2 h1 h2)

/-! ### Vertex deletion & `paidLeafYF` -/

def delVertEdges (v : ℕ) (E : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  E.filter (fun e => decide (e.1 ≠ v ∧ e.2 ≠ v))

def degH (H : List (ℕ × ℕ)) (v : ℕ) : ℕ :=
  (H.filter (fun e => decide (e.1 = v ∨ e.2 = v))).length

def eraseBit (n v s : ℕ) : ℕ :=
  mkBitmask n (fun w => s.testBit w && decide (w ≠ v))

theorem testBit_eraseBit {n v s w : ℕ} (hs : s < 2 ^ n) :
    (eraseBit n v s).testBit w = (s.testBit w && decide (w ≠ v)) := by
  rw [eraseBit, testBit_mkBitmask]
  by_cases hlt : w < n
  · simp [hlt]
  · have hsf : s.testBit w = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hs (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hlt, hsf]

theorem validState_delVert {n v : ℕ} {H F : List (ℕ × ℕ)} (hv : ValidState n H F) :
    ValidState n (delVertEdges v H) (delVertEdges v F) := by
  rcases hv with ⟨hH, hF, hdisj⟩
  refine ⟨fun e he => hH e (List.mem_of_mem_filter he),
    fun f hf => hF f (List.mem_of_mem_filter hf),
    fun e he f hf => hdisj e (List.mem_of_mem_filter he) f (List.mem_of_mem_filter hf)⟩

theorem length_delVert_add_degH (H : List (ℕ × ℕ)) (v : ℕ) :
    (delVertEdges v H).length + degH H v = H.length := by
  unfold delVertEdges degH
  induction H with
  | nil => simp
  | cons e rest ih =>
    simp only [List.filter_cons, List.length_cons]
    by_cases h : e.1 = v ∨ e.2 = v
    · have h1 : decide (e.1 ≠ v ∧ e.2 ≠ v) = false := by
        rw [decide_eq_false_iff_not]; omega
      have h2 : decide (e.1 = v ∨ e.2 = v) = true := decide_eq_true h
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    · have h1 : decide (e.1 ≠ v ∧ e.2 ≠ v) = true := by
        rw [decide_eq_true_eq]; omega
      have h2 : decide (e.1 = v ∨ e.2 = v) = false := decide_eq_false h
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega

theorem paidVertexYF {n : ℕ} {H F : List (ℕ × ℕ)} {v : ℕ}
    (hv : ValidState n H F)
    (hinc : ∃ e ∈ H, e.1 = v ∨ e.2 = v)
    (hsurv : 1 ≤ (delVertEdges v H).length)
    {k : ℕ} (hr : HasRunYF n H F k) :
    ∃ j < k, HasRunYF n (delVertEdges v H) (delVertEdges v F) j := by
  set H' := delVertEdges v H
  set F' := delVertEdges v F
  have hM' : ∀ s, (univYF n F').testBit s = true → s < 2 ^ n := fun _ => univYF_testBit_lt
  have herase_dom : ∀ s : Dom (univYF n F'), (univYF n F).testBit (eraseBit n v s.1) = true := by
    intro s
    have hslt : s.1 < 2 ^ n := hM' s.1 s.2
    rw [testBit_univYF, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    refine ⟨mkBitmask_lt_two_pow n _, Bool.eq_false_iff.mpr fun hf => ?_⟩
    rw [hasEdge_eq_true] at hf
    obtain ⟨f, hfF, h1, h2⟩ := hf
    rw [testBit_eraseBit hslt, Bool.and_eq_true, decide_eq_true_eq] at h1 h2
    have hfF' : f ∈ F' := List.mem_filter.mpr ⟨hfF, decide_eq_true ⟨h1.2, h2.2⟩⟩
    have hs2 := s.2
    rw [testBit_univYF, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff] at hs2
    exact hs2.2 (hasEdge_eq_true F' s.1 |>.mpr ⟨f, hfF', h1.1, h2.1⟩)
  let π : Dom (univYF n F') → Dom (univYF n F) := fun s => ⟨eraseBit n v s.1, herase_dom s⟩
  obtain ⟨e₀, he₀H, he₀v⟩ := hinc
  obtain ⟨he₀1, he₀2, he₀ne⟩ := hv.1 e₀ he₀H
  let u : ℕ := if e₀.1 = v then e₀.2 else e₀.1
  have hu_lt : u < n := by simp only [u]; split_ifs <;> omega
  have hp_eq : (1 <<< u) ||| (1 <<< v) = (1 <<< e₀.1) ||| (1 <<< e₀.2) := by
    simp only [u]; split_ifs with h
    · rw [h, Nat.or_comm]
    · have : e₀.2 = v := he₀v.resolve_left h
      rw [this]
  let p_val : ℕ := (1 <<< e₀.1) ||| (1 <<< e₀.2)
  let q_val : ℕ := 1 <<< u
  have hpM : (univYF n F).testBit p_val = true := edgePt_mem_univYF hv he₀H
  have hqM : (univYF n F).testBit q_val = true := by
    rw [testBit_univYF, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    refine ⟨oneBit_lt_two_pow hu_lt, Bool.eq_false_iff.mpr fun hf => ?_⟩
    rw [hasEdge_eq_true] at hf
    obtain ⟨f, hfF, h1, h2⟩ := hf
    rw [testBit_one_shiftLeft, decide_eq_true_eq] at h1 h2
    exact (hv.2.1 f hfF).2.2 (h1.symm.trans h2)
  let p : Dom (univYF n F) := ⟨p_val, hpM⟩
  let q : Dom (univYF n F) := ⟨q_val, hqM⟩
  have hatoms : ∀ f ∈ rawSet n F, Meet (rawSet n F') (π ⁻¹' f) := by
    rintro f ⟨w, rfl⟩
    by_cases hw : w.1 = v
    · have hemp : π ⁻¹' decM (univYF n F) (ttVarYF n w.1 (univYF n F)) = ∅ := by
        ext s
        simp only [Set.mem_preimage, mem_decM, testBit_ttVarYF (fun _ => univYF_testBit_lt),
          (π s).2, Bool.true_and, Set.mem_empty_iff_false, iff_false]
        change ¬ (eraseBit n v s.1).testBit w.1 = true
        rw [testBit_eraseBit (hM' s.1 s.2), hw]
        simp
      rw [hemp]; exact Meet.bot
    · have heq : π ⁻¹' decM (univYF n F) (ttVarYF n w.1 (univYF n F)) =
          decM (univYF n F') (ttVarYF n w.1 (univYF n F')) := by
        ext s
        simp only [Set.mem_preimage, mem_decM, testBit_ttVarYF (fun _ => univYF_testBit_lt),
          (π s).2, s.2, Bool.true_and]
        change (eraseBit n v s.1).testBit w.1 = true ↔ s.1.testBit w.1 = true
        rw [testBit_eraseBit (hM' s.1 s.2), decide_eq_true hw, Bool.and_true]
      rw [heq]; exact Meet.atom ⟨w, rfl⟩
  have hgood : ∀ f ∈ rawSet n F, Good π p q f := by
    rintro f ⟨w, rfl⟩
    by_cases hw : w.1 = v
    · right
      ext s
      simp only [Set.mem_preimage, mem_decM, testBit_ttVarYF (fun _ => univYF_testBit_lt),
        (π s).2, Bool.true_and, Set.mem_empty_iff_false, iff_false]
      change ¬ (eraseBit n v s.1).testBit w.1 = true
      rw [testBit_eraseBit (hM' s.1 s.2), hw]
      simp
    · left
      simp only [mem_decM, testBit_ttVarYF (fun _ => univYF_testBit_lt), p.2, q.2, Bool.true_and]
      change p_val.testBit w.1 = true ↔ q_val.testBit w.1 = true
      dsimp only [p_val, q_val]
      rw [← hp_eq, twoBit_testBit, testBit_one_shiftLeft, decide_eq_true_eq]
      constructor
      · rintro (h | h)
        · exact h.symm
        · exact (hw h).elim
      · intro h; exact Or.inl h.symm
  have hpreTarget : π ⁻¹' targetSet n H F = targetSet n H' F' := by
    ext s
    simp only [Set.mem_preimage, targetSet, mem_decM,
      testBit_edgeTTYF (fun _ => univYF_testBit_lt), (π s).2, s.2, Bool.true_and, hasEdge_eq_true]
    constructor
    · rintro ⟨e, heH, h1, h2⟩
      change (eraseBit n v s.1).testBit e.1 = true at h1
      change (eraseBit n v s.1).testBit e.2 = true at h2
      rw [testBit_eraseBit (hM' s.1 s.2), Bool.and_eq_true, decide_eq_true_eq] at h1 h2
      exact ⟨e, List.mem_filter.mpr ⟨heH, decide_eq_true ⟨h1.2, h2.2⟩⟩, h1.1, h2.1⟩
    · rintro ⟨e, heH', h1, h2⟩
      obtain ⟨heH, hne⟩ := List.mem_filter.mp heH'
      rw [decide_eq_true_eq] at hne
      refine ⟨e, heH, ?_, ?_⟩
      · change (eraseBit n v s.1).testBit e.1 = true
        rw [testBit_eraseBit (hM' s.1 s.2), h1, decide_eq_true hne.1]; rfl
      · change (eraseBit n v s.1).testBit e.2 = true
        rw [testBit_eraseBit (hM' s.1 s.2), h2, decide_eq_true hne.2]; rfl
  have hbad : ¬ Good π p q (targetSet n H F) := by
    rintro (hiff | hemp)
    · have hpT : p ∈ targetSet n H F := edgePt_mem_edgeTTYF hv he₀H
      have hqT : q ∈ targetSet n H F := hiff.mp hpT
      rw [targetSet, mem_decM, testBit_edgeTTYF (fun _ => univYF_testBit_lt), q.2, Bool.true_and,
        hasEdge_eq_true] at hqT
      obtain ⟨e, heH, h1, h2⟩ := hqT
      change (1 <<< u).testBit e.1 = true at h1
      change (1 <<< u).testBit e.2 = true at h2
      rw [testBit_one_shiftLeft, decide_eq_true_eq] at h1 h2
      exact (hv.1 e heH).2.2 (h1.symm.trans h2)
    · rw [hpreTarget] at hemp
      have hH'ne : H' ≠ [] := by intro h; simp [h] at hsurv
      obtain ⟨e₁, _, he₁eq⟩ := List.exists_cons_of_ne_nil hH'ne
      have he₁mem : e₁ ∈ H' := by rw [he₁eq]; simp
      have hv' : ValidState n H' F' := validState_delVert hv
      have hs₁M' : (univYF n F').testBit ((1 <<< e₁.1) ||| (1 <<< e₁.2)) = true :=
        edgePt_mem_univYF hv' he₁mem
      have hs₁T' : (⟨(1 <<< e₁.1) ||| (1 <<< e₁.2), hs₁M'⟩ : Dom (univYF n F')) ∈
          targetSet n H' F' :=
        edgePt_mem_edgeTTYF hv' he₁mem
      rw [hemp] at hs₁T'
      exact hs₁T'
  obtain ⟨j, hj, hr'⟩ := paidMap π p q hatoms hgood hr hbad
  rw [hpreTarget] at hr'
  exact ⟨j, hj, hr'⟩

theorem paidLeafYF {n : ℕ} {H F : List (ℕ × ℕ)} {v : ℕ}
    (hv : ValidState n H F) (hdeg : degH H v = 1) (hlen : 2 ≤ H.length)
    (hlb : OrCostLB n (delVertEdges v H) (delVertEdges v F) ((delVertEdges v H).length - 1)) :
    OrCostLB n H F (H.length - 1) := by
  have hlen' : (delVertEdges v H).length + 1 = H.length := by
    have := length_delVert_add_degH H v; omega
  have hinc : ∃ e ∈ H, e.1 = v ∨ e.2 = v := by
    unfold degH at hdeg
    have hne : H.filter (fun e => decide (e.1 = v ∨ e.2 = v)) ≠ [] := by
      intro h; rw [h] at hdeg; simp at hdeg
    obtain ⟨e, _, heq⟩ := List.exists_cons_of_ne_nil hne
    have hmem : e ∈ H.filter (fun e => decide (e.1 = v ∨ e.2 = v)) := by rw [heq]; simp
    obtain ⟨heH, hv'⟩ := List.mem_filter.mp hmem
    exact ⟨e, heH, decide_eq_true_eq.mp hv'⟩
  intro k hr
  obtain ⟨j, hj, hr'⟩ := paidVertexYF hv hinc (by omega) hr
  have h1 := hlb j hr'
  omega

/-! ### Graph embedding (`dropIsoYF` + `permYF` + `addForbYF`) & `validPeelEmbed` -/

def mapSubLoop (f : List ℕ) (t i acc : ℕ) : ℕ :=
  match f with
  | [] => acc
  | u :: rest =>
    let acc' := match t.testBit i with
      | true => Nat.lor acc (1 <<< u)
      | false => acc
    mapSubLoop rest t (i + 1) acc'

def mapSub (f : List ℕ) (t : ℕ) : ℕ := mapSubLoop f t 0 0

theorem mapSub_testBit (f : List ℕ) (t w : ℕ) :
    (mapSub f t).testBit w = true ↔
      ∃ (i : ℕ) (hi : i < f.length), f[i] = w ∧ t.testBit i = true := by
  -- Identical to applyPerm_testBit!
  have heq : ∀ (l : List ℕ) (i acc : ℕ), mapSubLoop l t i acc = applyPermLoop l t i acc := by
    intro l
    induction l with
    | nil => intro _ _; rfl
    | cons u rest ih =>
      intro i acc
      simp only [mapSubLoop, applyPermLoop]
      exact ih (i + 1) _
  change (mapSubLoop f t 0 0).testBit w = true ↔ _
  rw [heq f 0 0]
  exact applyPerm_testBit f t w

def validEmbed (n : ℕ) (H F : List (ℕ × ℕ)) (n' : ℕ) (H' F' : List (ℕ × ℕ)) (f : List ℕ) : Bool :=
  decide (f.length = n') &&
  decide f.Nodup &&
  f.all (fun x => decide (x < n)) &&
  H.all (fun e => H'.any (fun e' => decide (e'.1 < n' ∧ e'.2 < n') &&
    undirEq e (f.getD e'.1 0, f.getD e'.2 0))) &&
  H'.all (fun e' => decide (e'.1 < n' ∧ e'.2 < n') &&
    H.any (fun e => undirEq e (f.getD e'.1 0, f.getD e'.2 0))) &&
  F.all (fun e => (List.range n').all (fun i => (List.range n').all (fun j =>
    !decide (f.getD i 0 = e.1 ∧ f.getD j 0 = e.2) ||
    F'.any (fun f' => undirEq f' (i, j)))))

theorem undirEq_true_iff (e₁ e₂ : ℕ × ℕ) :
    undirEq e₁ e₂ = true ↔ (e₁.1 = e₂.1 ∧ e₁.2 = e₂.2) ∨ (e₁.1 = e₂.2 ∧ e₁.2 = e₂.1) := by
  simp [undirEq]

theorem mapSub_lt_two_pow {n : ℕ} {f : List ℕ} (hf : ∀ x ∈ f, x < n) (t : ℕ) :
    mapSub f t < 2 ^ n := by
  have heq : mapSub f t = mkBitmask n (fun w => (mapSub f t).testBit w) := by
    apply Nat.eq_of_testBit_eq; intro w
    rw [testBit_mkBitmask]
    cases hw : (mapSub f t).testBit w
    · simp
    · obtain ⟨i, hi, hget, _⟩ := (mapSub_testBit f t w).mp hw
      have hwn : w < n := hget ▸ hf f[i] (List.getElem_mem hi)
      simp [hwn]
  rw [heq]; exact mkBitmask_lt_two_pow n _

theorem embedYF_sound {n n' : ℕ} {H F H' F' : List (ℕ × ℕ)} {f : List ℕ}
    (hemb : validEmbed n H F n' H' F' f = true) :
    ∀ k, HasRunYF n H F k → HasRunYF n' H' F' k := by
  unfold validEmbed at hemb
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.mem_range] at hemb
  obtain ⟨⟨⟨⟨⟨hlen, hnd⟩, hflt⟩, hHdir⟩, hH'dir⟩, hFdir⟩ := hemb
  have hdom : ∀ t : Dom (univYF n' F'), (univYF n F).testBit (mapSub f t.1) = true := by
    intro t
    rw [testBit_univYF, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    refine ⟨mapSub_lt_two_pow hflt t.1, Bool.eq_false_iff.mpr fun hf => ?_⟩
    rw [hasEdge_eq_true] at hf
    obtain ⟨e, heF, h1, h2⟩ := hf
    obtain ⟨i, hi, hfi, hti⟩ := (mapSub_testBit f t.1 e.1).mp h1
    obtain ⟨j, hj, hfj, htj⟩ := (mapSub_testBit f t.1 e.2).mp h2
    have hi' : i < n' := hlen ▸ hi
    have hj' : j < n' := hlen ▸ hj
    have hgi : f.getD i 0 = e.1 := by rw [List.getD_eq_getElem _ _ hi]; exact hfi
    have hgj : f.getD j 0 = e.2 := by rw [List.getD_eq_getElem _ _ hj]; exact hfj
    rcases hFdir e heF i hi' j hj' with hno | ⟨f', hf'F', hue⟩
    · exact hno ⟨hgi, hgj⟩
    · have ht2 := t.2
      rw [testBit_univYF, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff] at ht2
      rw [undirEq_true_iff] at hue
      apply ht2.2
      rw [hasEdge_eq_true]
      rcases hue with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · exact ⟨f', hf'F', h1'.symm ▸ hti, h2'.symm ▸ htj⟩
      · exact ⟨f', hf'F', h1'.symm ▸ htj, h2'.symm ▸ hti⟩
  let π : Dom (univYF n' F') → Dom (univYF n F) := fun t => ⟨mapSub f t.1, hdom t⟩
  have hatoms : ∀ S ∈ rawSet n F, Meet (rawSet n' F') (π ⁻¹' S) := by
    rintro S ⟨v, rfl⟩
    by_cases hv : ∃ (i : ℕ) (hi : i < f.length), f[i] = v.1
    · obtain ⟨i, hi, hfi⟩ := hv
      have hi' : i < n' := hlen ▸ hi
      have heq : π ⁻¹' decM (univYF n F) (ttVarYF n v.1 (univYF n F)) =
          decM (univYF n' F') (ttVarYF n' i (univYF n' F')) := by
        ext t
        simp only [Set.mem_preimage, mem_decM, testBit_ttVarYF (fun _ => univYF_testBit_lt),
          (π t).2, t.2, Bool.true_and]
        change (mapSub f t.1).testBit v.1 = true ↔ t.1.testBit i = true
        rw [mapSub_testBit]
        constructor
        · rintro ⟨j, hj, hfj, htj⟩
          have hij : j = i := (List.Nodup.getElem_inj_iff hnd).mp (hfj.trans hfi.symm)
          exact hij ▸ htj
        · intro hti; exact ⟨i, hi, hfi, hti⟩
      rw [heq]; exact Meet.atom ⟨⟨i, hi'⟩, rfl⟩
    · have hemp : π ⁻¹' decM (univYF n F) (ttVarYF n v.1 (univYF n F)) = ∅ := by
        ext t
        simp only [Set.mem_preimage, mem_decM, testBit_ttVarYF (fun _ => univYF_testBit_lt),
          (π t).2, Bool.true_and, Set.mem_empty_iff_false, iff_false]
        change ¬ (mapSub f t.1).testBit v.1 = true
        rw [mapSub_testBit]
        rintro ⟨i, hi, hfi, _⟩
        exact hv ⟨i, hi, hfi⟩
      rw [hemp]; exact Meet.bot
  have htarget : π ⁻¹' targetSet n H F = targetSet n' H' F' := by
    ext t
    simp only [Set.mem_preimage, targetSet, mem_decM,
      testBit_edgeTTYF (fun _ => univYF_testBit_lt), (π t).2, t.2, Bool.true_and, hasEdge_eq_true]
    constructor
    · rintro ⟨e, heH, h1, h2⟩
      change (mapSub f t.1).testBit e.1 = true at h1
      change (mapSub f t.1).testBit e.2 = true at h2
      obtain ⟨i, hi, hfi, hti⟩ := (mapSub_testBit f t.1 e.1).mp h1
      obtain ⟨j, hj, hfj, htj⟩ := (mapSub_testBit f t.1 e.2).mp h2
      obtain ⟨e', he'H', ⟨he'1, he'2⟩, hue⟩ := hHdir e heH
      have h1lt : e'.1 < f.length := hlen.symm ▸ he'1
      have h2lt : e'.2 < f.length := hlen.symm ▸ he'2
      rw [List.getD_eq_getElem _ _ h1lt, List.getD_eq_getElem _ _ h2lt, undirEq_true_iff] at hue
      rcases hue with ⟨hu1, hu2⟩ | ⟨hu1, hu2⟩
      · have hi1 : i = e'.1 := (List.Nodup.getElem_inj_iff hnd).mp (hfi.trans hu1)
        have hj2 : j = e'.2 := (List.Nodup.getElem_inj_iff hnd).mp (hfj.trans hu2)
        exact ⟨e', he'H', hi1 ▸ hti, hj2 ▸ htj⟩
      · have hi2 : i = e'.2 := (List.Nodup.getElem_inj_iff hnd).mp (hfi.trans hu1)
        have hj1 : j = e'.1 := (List.Nodup.getElem_inj_iff hnd).mp (hfj.trans hu2)
        exact ⟨e', he'H', hj1 ▸ htj, hi2 ▸ hti⟩
    · rintro ⟨e', he'H', h1, h2⟩
      obtain ⟨⟨he'1, he'2⟩, e, heH, hue⟩ := hH'dir e' he'H'
      have h1lt : e'.1 < f.length := hlen.symm ▸ he'1
      have h2lt : e'.2 < f.length := hlen.symm ▸ he'2
      rw [List.getD_eq_getElem _ _ h1lt, List.getD_eq_getElem _ _ h2lt, undirEq_true_iff] at hue
      refine ⟨e, heH, ?_, ?_⟩
      · change (mapSub f t.1).testBit e.1 = true
        rw [mapSub_testBit]
        rcases hue with ⟨hu1, _⟩ | ⟨hu1, _⟩
        · exact ⟨e'.1, h1lt, hu1.symm, h1⟩
        · exact ⟨e'.2, h2lt, hu1.symm, h2⟩
      · change (mapSub f t.1).testBit e.2 = true
        rw [mapSub_testBit]
        rcases hue with ⟨_, hu2⟩ | ⟨_, hu2⟩
        · exact ⟨e'.2, h2lt, hu2.symm, h2⟩
        · exact ⟨e'.1, h1lt, hu2.symm, h1⟩
  intro k hr
  have hr' := freeMap π hatoms hr
  rwa [htarget] at hr'

def validPeelEmbed (n : ℕ) (H F : List (ℕ × ℕ)) :
    List ℕ → ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → List ℕ → Bool
  | [], n', H', F', f => decide (H.length = H'.length) && validEmbed n H F n' H' F' f
  | v :: rest, n', H', F', f =>
    decide (degH H v = 1 ∧ 2 ≤ H.length) &&
    validPeelEmbed n (delVertEdges v H) (delVertEdges v F) rest n' H' F' f

theorem validPeelEmbed_sound {n : ℕ} {H F : List (ℕ × ℕ)} {peels : List ℕ}
    {n' : ℕ} {H' F' : List (ℕ × ℕ)} {f : List ℕ}
    (hv : ValidState n H F)
    (hok : validPeelEmbed n H F peels n' H' F' f = true)
    (hlb : OrCostLB n' H' F' (H'.length - 1)) :
    OrCostLB n H F (H.length - 1) := by
  induction peels generalizing H F with
  | nil =>
    simp only [validPeelEmbed, Bool.and_eq_true, decide_eq_true_eq] at hok
    rw [hok.1]
    intro k hr
    exact hlb k (embedYF_sound hok.2 k hr)
  | cons v rest ih =>
    simp only [validPeelEmbed, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact paidLeafYF hv hok.1.1 hok.1.2 (ih (validState_delVert hv) hok.2)

/-! ## Section 6: Chained Cut + Probe Soundness & Terminal `M_d` Soundness -/

def probeOkGate (mc pm h : ℕ) : Bool :=
  let x := Nat.land h pm
  match Nat.beq x 0 with
  | true => true
  | false =>
    match Nat.beq x pm with
    | true => true
    | false => Nat.beq (Nat.land h mc) 0

def evalCutStep (mc : ℕ) (rc : List ℕ) (act : List ℕ) : List ℕ × List ℕ × ℕ :=
  let rec go : List ℕ → List ℕ → List ℕ → ℕ → List ℕ × List ℕ × ℕ
    | [], sb, actRev, sv => (sb, actRev.reverse, sv)
    | g :: rest, sb, actRev, sv =>
      let rg := Nat.land g mc
      match isMeet mc sb rg with
      | true => go rest sb actRev (sv + 1)
      | false => go rest (rg :: sb) (rg :: actRev) sv
  go act rc [] 0

theorem evalCutStep_go_inv {M_prev mc : ℕ} (hmc : mc &&& M_prev = mc)
    {raw_prev rc : List ℕ}
    (hraw : ∀ r ∈ raw_prev, r &&& mc = 0 ∨ r &&& mc ∈ rc) :
    ∀ (rest sb actRev : List ℕ) (sv : ℕ) (done : List ℕ),
      (∀ x ∈ sb, x ∈ rc ++ actRev.reverse) →
      (∀ x ∈ rc ++ actRev.reverse, x ∈ sb) →
      ValidPrefix mc rc actRev.reverse →
      (∀ h ∈ done, MeetNat mc sb (h &&& mc)) →
      ValidPrefix M_prev (raw_prev ++ done) rest →
      let res := evalCutStep.go mc rest sb actRev sv
      res.2.1.length + res.2.2 = actRev.length + sv + rest.length ∧
      ValidPrefix mc rc res.2.1 ∧
      (∀ x ∈ res.1, x ∈ rc ++ res.2.1) ∧
      (∀ x ∈ rc ++ res.2.1, x ∈ res.1) ∧
      (∀ h ∈ done ++ rest, MeetNat mc res.1 (h &&& mc)) := by
  intro rest
  induction rest with
  | nil =>
    intro sb actRev sv done hsb1 hsb2 hvp hdone _
    simp only [evalCutStep.go, List.length_reverse, List.length_nil, add_zero, List.append_nil]
    exact ⟨trivial, hvp, hsb1, hsb2, hdone⟩
  | cons g tail ih =>
    intro sb actRev sv done hsb1 hsb2 hvp hdone hrest_vp
    rcases hrest_vp with ⟨⟨a, b, ha, hb, hgab⟩, htail_vp⟩
    have hrgM : (g &&& mc) &&& mc = g &&& mc := by
      apply Nat.eq_of_testBit_eq; intro s; simp [Nat.testBit_and]
    have hmap_prev : ∀ x ∈ raw_prev ++ done, MeetNat mc sb (x &&& mc) := by
      intro x hx
      have hxM : (x &&& mc) &&& mc = x &&& mc := by
        apply Nat.eq_of_testBit_eq; intro s; simp [Nat.testBit_and]
      rcases List.mem_append.mp hx with hx | hx
      · rcases hraw x hx with h0 | hmem
        · rw [h0]; exact ⟨by simp, by simp [isMeet]⟩
        · exact meetNat_iff.mpr ⟨hxM, Meet.atom ⟨x &&& mc, hsb2 _ (List.mem_append_left _ hmem), rfl⟩⟩
      · exact hdone x hx
    let ι : Dom mc → Dom M_prev := fun s => ⟨s.1, sub_mask_testBit hmc s.2⟩
    have hι_meet : ∀ {t : ℕ}, MeetNat M_prev (raw_prev ++ done) t → MeetNat mc sb (t &&& mc) := by
      intro t ht
      have htM : (t &&& mc) &&& mc = t &&& mc := by
        apply Nat.eq_of_testBit_eq; intro s; simp [Nat.testBit_and]
      refine meetNat_iff.mpr ⟨htM, ?_⟩
      have hpre : ι ⁻¹' decM M_prev t = decM mc (t &&& mc) := by
        ext s; simp [ι, decM, Nat.testBit_and, s.2]
      rw [← hpre]
      apply mapMeet ι _ (meetNat_iff.mp ht).2
      rintro S ⟨x, hx, rfl⟩
      have hpx : ι ⁻¹' decM M_prev x = decM mc (x &&& mc) := by
        ext s; simp [ι, decM, Nat.testBit_and, s.2]
      rw [hpx]
      exact (meetNat_iff.mp (hmap_prev x hx)).2
    have ha_c : MeetNat mc sb (a &&& mc) := hι_meet ha
    have hb_c : MeetNat mc sb (b &&& mc) := hι_meet hb
    have hgab_c : g &&& mc = (a &&& mc) ||| (b &&& mc) := by
      rw [hgab]
      apply Nat.eq_of_testBit_eq; intro s
      simp only [Nat.testBit_and, Nat.testBit_or]
      cases a.testBit s <;> cases b.testBit s <;> cases mc.testBit s <;> decide
    have htail_vp' : ValidPrefix M_prev (raw_prev ++ (done ++ [g])) tail := by
      simpa only [List.append_assoc] using htail_vp
    simp only [evalCutStep.go, land_eq]
    cases hm : isMeet mc sb (g &&& mc)
    · -- not a meet: push `rg = g &&& mc` to `sb` and `actRev`
      have hvp' : ValidPrefix mc rc ((g &&& mc) :: actRev).reverse := by
        rw [List.reverse_cons, validPrefix_append]
        refine ⟨hvp, ⟨a &&& mc, b &&& mc,
          meetNat_weaken hsb1 ha_c, meetNat_weaken hsb1 hb_c, hgab_c⟩, trivial⟩
      have h1 := ih ((g &&& mc) :: sb) ((g &&& mc) :: actRev) sv (done ++ [g])
        (fun x hx => by
          rw [List.reverse_cons]
          rcases List.mem_cons.mp hx with rfl | hx
          · simp
          · have := hsb1 x hx; simp only [List.mem_append] at this ⊢; tauto)
        (fun x hx => by
          rw [List.reverse_cons] at hx
          rcases List.mem_append.mp hx with hx | hx
          · exact List.mem_cons_of_mem _ (hsb2 x (List.mem_append_left _ hx))
          · rcases List.mem_append.mp hx with hx | hx
            · exact List.mem_cons_of_mem _ (hsb2 x (List.mem_append_right _ hx))
            · rw [List.mem_singleton.mp hx]; exact List.mem_cons_self)
        hvp'
        (fun h hh => by
          rcases List.mem_append.mp hh with hh | hh
          · exact meetNat_weaken (fun x hx => List.mem_cons_of_mem _ hx) (hdone h hh)
          · rw [List.mem_singleton.mp hh]
            exact meetNat_iff.mpr ⟨hrgM, Meet.atom ⟨g &&& mc, List.mem_cons_self, rfl⟩⟩)
        htail_vp'
      simpa only [List.length_cons, List.append_assoc, List.singleton_append, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using h1
    · -- is a meet: increment `sv`
      have h1 := ih sb actRev (sv + 1) (done ++ [g]) hsb1 hsb2 hvp
        (fun h hh => by
          rcases List.mem_append.mp hh with hh | hh
          · exact hdone h hh
          · rw [List.mem_singleton.mp hh]; exact ⟨hrgM, hm⟩)
        htail_vp'
      simpa only [List.length_cons, List.append_assoc, List.singleton_append, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using h1

theorem probeOkGate_sound {M_prev mc pm p q : ℕ}
    (hmc : mc &&& M_prev = mc)
    (hpM : M_prev.testBit p = true) (hqM : M_prev.testBit q = true)
    (hp_pm : pm.testBit p = true) (hq_pm : pm.testBit q = true)
    {h : ℕ} (hok : probeOkGate mc pm h = true) :
    Good (fun s : Dom mc => (⟨s.1, sub_mask_testBit hmc s.2⟩ : Dom M_prev))
      ⟨p, hpM⟩ ⟨q, hqM⟩ (decM M_prev h) := by
  unfold probeOkGate at hok
  dsimp only at hok
  cases h0 : Nat.beq (Nat.land h pm) 0
  · rw [h0] at hok
    cases h1 : Nat.beq (Nat.land h pm) pm
    · rw [h1] at hok
      have hmc0 : h &&& mc = 0 := by simpa [land_eq] using Nat.eq_of_beq_eq_true hok
      right
      ext s
      simp only [Set.mem_preimage, decM, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hs
      have := congrArg (fun z => z.testBit s.1) hmc0
      rw [Nat.testBit_and, hs, s.2] at this
      simp at this
    · have hpm : h &&& pm = pm := by simpa [land_eq] using Nat.eq_of_beq_eq_true h1
      left
      have hp : h.testBit p = true := by
        have := congrArg (fun z => z.testBit p) hpm
        rw [Nat.testBit_and, hp_pm, Bool.and_true] at this; exact this
      have hq : h.testBit q = true := by
        have := congrArg (fun z => z.testBit q) hpm
        rw [Nat.testBit_and, hq_pm, Bool.and_true] at this; exact this
      simp [decM, hp, hq]
  · have hpm0 : h &&& pm = 0 := by simpa [land_eq] using Nat.eq_of_beq_eq_true h0
    left
    have hp : h.testBit p = false := by
      have := congrArg (fun z => z.testBit p) hpm0
      rw [Nat.testBit_and, hp_pm, Bool.and_true, Nat.zero_testBit] at this; exact this
    have hq : h.testBit q = false := by
      have := congrArg (fun z => z.testBit q) hpm0
      rw [Nat.testBit_and, hq_pm, Bool.and_true, Nat.zero_testBit] at this; exact this
    simp [decM, hp, hq]

theorem probeMask_exists_pq {M_prev edgeTT pm : ℕ}
    (hpmM : pm &&& M_prev = pm)
    (hne0 : pm &&& edgeTT ≠ 0)
    (hneP : pm &&& edgeTT ≠ pm) :
    ∃ p q : ℕ, M_prev.testBit p = true ∧ M_prev.testBit q = true ∧
      pm.testBit p = true ∧ pm.testBit q = true ∧
      edgeTT.testBit p = true ∧ edgeTT.testBit q = false := by
  have hexP : ∃ p, (pm &&& edgeTT).testBit p = true := by
    by_contra hall; push Not at hall
    apply hne0; apply Nat.eq_of_testBit_eq; intro s
    simp only [Nat.zero_testBit]; exact Bool.eq_false_iff.mpr (hall s)
  have hexQ : ∃ q, (pm &&& edgeTT).testBit q ≠ pm.testBit q := by
    by_contra hall; push Not at hall
    exact hneP (Nat.eq_of_testBit_eq hall)
  obtain ⟨p, hp⟩ := hexP
  rw [Nat.testBit_and, Bool.and_eq_true] at hp
  obtain ⟨q, hq⟩ := hexQ
  rw [Nat.testBit_and] at hq
  have hqp : pm.testBit q = true := by
    cases h : pm.testBit q
    · simp [h] at hq
    · rfl
  have hqe : edgeTT.testBit q = false := by
    cases h : edgeTT.testBit q
    · rfl
    · simp [hqp, h] at hq
  exact ⟨p, q, sub_mask_testBit hpmM hp.1, sub_mask_testBit hpmM hqp, hp.1, hqp, hp.2, hqe⟩

/-- One step of a chained vertex/edge cut: transforms a `Run` on `M_prev` into a `Run` on `mc ⊆ M_prev`,
saving `sv` gates via `isMeet`, plus `+1` extra saving via `paidMap` whenever a valid probe mask passes. -/
theorem cutStep_sound {M_prev mc edgeTT : ℕ} {raw_prev rc act_prev pv : List ℕ} {sufLen : ℕ}
    (hmc : mc &&& M_prev = mc)
    (hraw : ∀ r ∈ raw_prev, r &&& mc = 0 ∨ r &&& mc ∈ rc)
    (hvp_prev : ValidPrefix M_prev raw_prev act_prev)
    (hrun_prev : Run (decM M_prev '' { x | x ∈ raw_prev ++ act_prev }) sufLen (decM M_prev edgeTT))
    (hpv_valid : ∀ pm ∈ pv, pm &&& M_prev = pm ∧ pm &&& edgeTT ≠ 0 ∧ pm &&& edgeTT ≠ pm ∧
      edgeTT &&& mc ≠ 0 ∧ ∀ r ∈ raw_prev, probeOkGate mc pm r = true) :
    let res := evalCutStep mc rc act_prev
    let bonus := if pv.any (fun pm => act_prev.all (fun h => probeOkGate mc pm h)) then 1 else 0
    ValidPrefix mc rc res.2.1 ∧
    ∃ sufLen' : ℕ,
      res.2.1.length + sufLen' + res.2.2 + bonus ≤ act_prev.length + sufLen ∧
      Run (decM mc '' { x | x ∈ rc ++ res.2.1 }) sufLen' (decM mc edgeTT) := by
  have hinv := evalCutStep_go_inv hmc hraw act_prev rc [] 0 []
    (fun x hx => by simpa using hx)
    (fun x hx => by simpa using hx)
    trivial
    (fun _ h => by simp at h)
    (by simpa using hvp_prev)
  simp only [List.length_nil, zero_add, List.nil_append] at hinv
  obtain ⟨hlen, hvp_next, hsb1, hsb2, hall_meet⟩ := hinv
  change (evalCutStep mc rc act_prev).2.1.length + (evalCutStep mc rc act_prev).2.2 =
    act_prev.length at hlen
  let ι : Dom mc → Dom M_prev := fun s => ⟨s.1, sub_mask_testBit hmc s.2⟩
  have htarget : ι ⁻¹' decM M_prev edgeTT = decM mc edgeTT := by
    ext s; simp [ι, decM]
  have hatoms : ∀ S ∈ decM M_prev '' { x | x ∈ raw_prev ++ act_prev },
      Meet (decM mc '' { x | x ∈ rc ++ (evalCutStep mc rc act_prev).2.1 }) (ι ⁻¹' S) := by
    rintro S ⟨x, hx, rfl⟩
    have hpre : ι ⁻¹' decM M_prev x = decM mc (x &&& mc) := by
      ext s; simp [ι, decM, Nat.testBit_and, s.2]
    rw [hpre]
    rcases List.mem_append.mp hx with hx | hx
    · rcases hraw x hx with h0 | hmem
      · rw [h0, decM_zero]; exact Meet.bot
      · exact Meet.atom ⟨x &&& mc, List.mem_append_left _ hmem, rfl⟩
    · exact weaken (Set.image_mono (fun y hy => hsb1 y hy)) (meetNat_iff.mp (hall_meet x hx)).2
  dsimp only
  refine ⟨hvp_next, ?_⟩
  split_ifs with hprobe
  · rw [List.any_eq_true] at hprobe
    obtain ⟨pm, hpm_mem, hact_ok⟩ := hprobe
    rw [List.all_eq_true] at hact_ok
    obtain ⟨hpmM, hne0, hneP, hedgemc, hraw_ok⟩ := hpv_valid pm hpm_mem
    obtain ⟨p, q, hpM, hqM, hppm, hqpm, hpe, hqe⟩ := probeMask_exists_pq hpmM hne0 hneP
    have hgood : ∀ S ∈ decM M_prev '' { x | x ∈ raw_prev ++ act_prev },
        Good ι ⟨p, hpM⟩ ⟨q, hqM⟩ S := by
      rintro S ⟨x, hx, rfl⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact probeOkGate_sound hmc hpM hqM hppm hqpm (hraw_ok x hx)
      · exact probeOkGate_sound hmc hpM hqM hppm hqpm (hact_ok x hx)
    have hbad : ¬ Good ι ⟨p, hpM⟩ ⟨q, hqM⟩ (decM M_prev edgeTT) := by
      rintro (hiff | hemp)
      · have : edgeTT.testBit q = true := hiff.mp hpe
        simp [hqe] at this
      · rw [htarget] at hemp
        have hex : ∃ s, (edgeTT &&& mc).testBit s = true := by
          by_contra hall; push Not at hall
          apply hedgemc; apply Nat.eq_of_testBit_eq; intro s
          simp only [Nat.zero_testBit]; exact Bool.eq_false_iff.mpr (hall s)
        obtain ⟨s, hs⟩ := hex
        rw [Nat.testBit_and, Bool.and_eq_true] at hs
        have : (⟨s, hs.2⟩ : Dom mc) ∈ decM mc edgeTT := hs.1
        rw [hemp] at this; exact this
    obtain ⟨j, hj, hr'⟩ := paidMap ι ⟨p, hpM⟩ ⟨q, hqM⟩ hatoms hgood hrun_prev hbad
    rw [htarget] at hr'
    exact ⟨j, by omega, hr'⟩
  · have hr' := freeMap ι hatoms hrun_prev
    rw [htarget] at hr'
    exact ⟨sufLen, by omega, hr'⟩

theorem nat_beq_eq_true_iff (a b : ℕ) : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem nat_blt_eq_true {a b : ℕ} (h : Nat.blt a b = true) : a < b :=
  Nat.le_of_ble_eq_true h

theorem nat_sub_eq (a b : ℕ) : Nat.sub a b = a - b := rfl
theorem nat_div_eq (a b : ℕ) : Nat.div a b = a / b := rfl

theorem nat_beq_eq_false_iff (a b : ℕ) : Nat.beq a b = false ↔ a ≠ b := by
  cases h : Nat.beq a b
  · exact ⟨fun _ heq => by subst heq; simp at h, fun _ => rfl⟩
  · exact ⟨fun hc => (Bool.false_ne_true hc.symm).elim, fun hne => (hne (Nat.eq_of_beq_eq_true h)).elim⟩

/-! ### Chained Cut Steps & Bridge to `HasRunYF` -/

structure CutStepData where
  mc : ℕ
  rc : List ℕ
  pv : List ℕ

def ValidCutStep (M_prev edgeTT : ℕ) (raw_prev : List ℕ) (st : CutStepData) : Prop :=
  st.mc &&& M_prev = st.mc ∧
  (∀ r ∈ raw_prev, r &&& st.mc = 0 ∨ r &&& st.mc ∈ st.rc) ∧
  (∀ pm ∈ st.pv, pm &&& M_prev = pm ∧ pm &&& edgeTT ≠ 0 ∧ pm &&& edgeTT ≠ pm ∧
    edgeTT &&& st.mc ≠ 0 ∧ ∀ r ∈ raw_prev, probeOkGate st.mc pm r = true)

def evalCutChain (steps : List CutStepData) (act : List ℕ) : ℕ :=
  match steps with
  | [] => 0
  | st :: rest =>
    let res := evalCutStep st.mc st.rc act
    let bonus := if st.pv.any (fun pm => act.all (fun h => probeOkGate st.mc pm h)) then 1 else 0
    res.2.2 + bonus + evalCutChain rest res.2.1

def ValidCutChain (M edgeTT : ℕ) (raw : List ℕ) : List CutStepData → ℕ → List ℕ → Prop
  | [], M_end, raw_end => M = M_end ∧ raw = raw_end
  | st :: rest, M_end, raw_end =>
    ValidCutStep M edgeTT raw st ∧ ValidCutChain st.mc edgeTT st.rc rest M_end raw_end

theorem cutChain_sound {M edgeTT M_end : ℕ} {raw raw_end : List ℕ}
    (steps : List CutStepData)
    (hvalid : ValidCutChain M edgeTT raw steps M_end raw_end)
    {act : List ℕ} {sufLen : ℕ}
    (hvp : ValidPrefix M raw act)
    (hrun : Run (decM M '' { x | x ∈ raw ++ act }) sufLen (decM M edgeTT)) :
    ∃ k_end : ℕ, k_end + evalCutChain steps act ≤ act.length + sufLen ∧
      Run (decM M_end '' { x | x ∈ raw_end }) k_end (decM M_end edgeTT) := by
  induction steps generalizing M raw act sufLen with
  | nil =>
    rcases hvalid with ⟨rfl, rfl⟩
    refine ⟨act.length + sufLen, by simp [evalCutChain], validPrefix_to_run hvp hrun⟩
  | cons st rest ih =>
    rcases hvalid with ⟨⟨hmc, hraw, hpv⟩, hrest⟩
    have hstep := cutStep_sound hmc hraw hvp hrun hpv
    dsimp only at hstep
    obtain ⟨hvp', sufLen', hbudget, hrun'⟩ := hstep
    obtain ⟨k_end, hle, hrun_end⟩ := ih hrest hvp' hrun'
    refine ⟨k_end, ?_, hrun_end⟩
    simp only [evalCutChain]
    omega

def eraseMask (n vm s : ℕ) : ℕ :=
  mkBitmask n (fun w => s.testBit w && !vm.testBit w)

theorem testBit_eraseMask {n vm s w : ℕ} (hs : s < 2 ^ n) :
    (eraseMask n vm s).testBit w = (s.testBit w && !vm.testBit w) := by
  rw [eraseMask, testBit_mkBitmask]
  by_cases hlt : w < n
  · simp [hlt]
  · have hsf : s.testBit w = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hs (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hlt, hsf]

theorem cutEnd_to_hasRunYF {n : ℕ} {H F forbAdded : List (ℕ × ℕ)} {delVMask mc_end : ℕ}
    {rc_end : List ℕ} {k_end : ℕ}
    (hmc_spec : ∀ s, mc_end.testBit s = true ↔
      (univYF n (F ++ forbAdded)).testBit s = true ∧ s &&& delVMask = 0)
    (hrc_spec : ∀ r ∈ rc_end, r = 0 ∨ ∃ w < n, r = ttVarYF n w (univYF n F) &&& mc_end)
    (hrun : Run (decM mc_end '' { x | x ∈ rc_end }) k_end (decM mc_end (edgeTTYF n H (univYF n F)))) :
    let H_end := H.filter (fun e => !forbAdded.any (undirEq e) && !delVMask.testBit e.1 && !delVMask.testBit e.2)
    let F_end := (F ++ forbAdded).filter (fun e => !delVMask.testBit e.1 && !delVMask.testBit e.2)
    HasRunYF n H_end F_end k_end := by
  dsimp only
  set H_end := H.filter (fun e => !forbAdded.any (undirEq e) && !delVMask.testBit e.1 && !delVMask.testBit e.2)
  set F_end := (F ++ forbAdded).filter (fun e => !delVMask.testBit e.1 && !delVMask.testBit e.2)
  have hM : ∀ s, (univYF n F).testBit s = true → s < 2 ^ n := fun _ => univYF_testBit_lt
  have hM_end : ∀ s, (univYF n F_end).testBit s = true → s < 2 ^ n := fun _ => univYF_testBit_lt
  have hdom : ∀ s : Dom (univYF n F_end), mc_end.testBit (eraseMask n delVMask s.1) = true := by
    intro s
    have hslt : s.1 < 2 ^ n := hM_end s.1 s.2
    rw [hmc_spec]
    constructor
    · rw [testBit_univYF, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
      refine ⟨mkBitmask_lt_two_pow n _, Bool.eq_false_iff.mpr fun hf => ?_⟩
      rw [hasEdge_eq_true] at hf
      obtain ⟨f, hfmem, h1, h2⟩ := hf
      rw [testBit_eraseMask hslt, Bool.and_eq_true] at h1 h2
      have hfF_end : f ∈ F_end := List.mem_filter.mpr ⟨hfmem, by simp [h1.2, h2.2]⟩
      have hs2 := s.2
      rw [testBit_univYF, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff] at hs2
      exact hs2.2 (hasEdge_eq_true F_end s.1 |>.mpr ⟨f, hfF_end, h1.1, h2.1⟩)
    · apply Nat.eq_of_testBit_eq; intro w
      rw [Nat.testBit_and, testBit_eraseMask hslt, Nat.zero_testBit]
      cases s.1.testBit w <;> cases delVMask.testBit w <;> decide
  have hmc_sub_M : ∀ s, mc_end.testBit s = true → (univYF n F).testBit s = true := by
    intro s hs
    have h1 := (hmc_spec s).mp hs |>.1
    rw [testBit_univYF, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.eq_false_iff] at h1
    rw [testBit_univYF, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.eq_false_iff]
    refine ⟨h1.1, fun hf => h1.2 ?_⟩
    rw [hasEdge_eq_true] at hf ⊢
    obtain ⟨f, hfF, h2, h3⟩ := hf
    exact ⟨f, List.mem_append_left _ hfF, h2, h3⟩
  let π : Dom (univYF n F_end) → Dom mc_end := fun s => ⟨eraseMask n delVMask s.1, hdom s⟩
  have hatoms : ∀ S ∈ decM mc_end '' { x | x ∈ rc_end }, Meet (rawSet n F_end) (π ⁻¹' S) := by
    rintro S ⟨r, hr, rfl⟩
    rcases hrc_spec r hr with rfl | ⟨w, hw, rfl⟩
    · rw [decM_zero, Set.preimage_empty]; exact Meet.bot
    · by_cases hdel : delVMask.testBit w = true
      · have hemp : π ⁻¹' decM mc_end (ttVarYF n w (univYF n F) &&& mc_end) = ∅ := by
          ext s
          simp only [Set.mem_preimage, mem_decM, Nat.testBit_and, (π s).2, Bool.and_true,
            testBit_ttVarYF hM, hmc_sub_M _ (π s).2, Bool.true_and, Set.mem_empty_iff_false, iff_false]
          change ¬ (eraseMask n delVMask s.1).testBit w = true
          rw [testBit_eraseMask (hM_end s.1 s.2), hdel]; simp
        rw [hemp]; exact Meet.bot
      · have hdel' : delVMask.testBit w = false := Bool.eq_false_iff.mpr hdel
        have heq : π ⁻¹' decM mc_end (ttVarYF n w (univYF n F) &&& mc_end) =
            decM (univYF n F_end) (ttVarYF n w (univYF n F_end)) := by
          ext s
          simp only [Set.mem_preimage, mem_decM, Nat.testBit_and, (π s).2, Bool.and_true,
            testBit_ttVarYF hM, testBit_ttVarYF hM_end, hmc_sub_M _ (π s).2, s.2, Bool.true_and]
          change (eraseMask n delVMask s.1).testBit w = true ↔ s.1.testBit w = true
          rw [testBit_eraseMask (hM_end s.1 s.2), hdel']; simp
        rw [heq]; exact Meet.atom ⟨⟨w, hw⟩, rfl⟩
  have htarget : π ⁻¹' decM mc_end (edgeTTYF n H (univYF n F)) = targetSet n H_end F_end := by
    ext s
    have hslt : s.1 < 2 ^ n := hM_end s.1 s.2
    simp only [Set.mem_preimage, targetSet, mem_decM, testBit_edgeTTYF hM,
      testBit_edgeTTYF hM_end, hmc_sub_M _ (π s).2, s.2, Bool.true_and,
      hasEdge_eq_true]
    constructor
    · rintro ⟨e, heH, h1, h2⟩
      change (eraseMask n delVMask s.1).testBit e.1 = true at h1
      change (eraseMask n delVMask s.1).testBit e.2 = true at h2
      rw [testBit_eraseMask hslt, Bool.and_eq_true] at h1 h2
      have hnotForb : forbAdded.any (undirEq e) = false := by
        rw [Bool.eq_false_iff]
        intro hany
        rw [List.any_eq_true] at hany
        obtain ⟨f, hfmem, hue⟩ := hany
        rw [undirEq_true_iff] at hue
        have hfF_end : f ∈ F_end := by
          refine List.mem_filter.mpr ⟨List.mem_append_right _ hfmem, ?_⟩
          rcases hue with ⟨hu1, hu2⟩ | ⟨hu1, hu2⟩ <;>
            simp [← hu1, ← hu2, h1.2, h2.2]
        have hs2 := s.2
        rw [testBit_univYF, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff] at hs2
        apply hs2.2
        rw [hasEdge_eq_true]
        rcases hue with ⟨hu1, hu2⟩ | ⟨hu1, hu2⟩
        · exact ⟨f, hfF_end, hu1 ▸ h1.1, hu2 ▸ h2.1⟩
        · exact ⟨f, hfF_end, hu2 ▸ h2.1, hu1 ▸ h1.1⟩
      exact ⟨e, List.mem_filter.mpr ⟨heH, by simp [hnotForb, h1.2, h2.2]⟩, h1.1, h2.1⟩
    · rintro ⟨e, heEnd, h1, h2⟩
      obtain ⟨heH, hfilt⟩ := List.mem_filter.mp heEnd
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfilt
      refine ⟨e, heH, ?_, ?_⟩
      · change (eraseMask n delVMask s.1).testBit e.1 = true
        rw [testBit_eraseMask hslt, h1, hfilt.1.2]; rfl
      · change (eraseMask n delVMask s.1).testBit e.2 = true
        rw [testBit_eraseMask hslt, h2, hfilt.2]; rfl
  have hr' := freeMap π hatoms hrun
  rwa [htarget] at hr'

/-! ### Terminal `M_d` Soundness -/

def noCovPairs (edgePtsMask : ℕ) : List ℕ → Bool
  | [] => true
  | a :: rest => rest.all (fun b => !Nat.beq (Nat.land (Nat.lor a b) edgePtsMask) edgePtsMask) &&
      noCovPairs edgePtsMask rest

theorem noCovPairs_sound {edgePtsMask : ℕ} {l : List ℕ}
    (hok : noCovPairs edgePtsMask l = true) :
    ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ((a ||| b) &&& edgePtsMask) ≠ edgePtsMask := by
  induction l with
  | nil => intro a ha; simp at ha
  | cons x rest ih =>
    simp only [noCovPairs, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
      nat_beq_eq_false_iff, land_eq, lor_eq] at hok
    obtain ⟨hhead, htail⟩ := hok
    intro a ha b hb hab
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · exact (hab rfl).elim
    · exact hhead b hb'
    · rw [Nat.or_comm]; exact hhead a ha'
    · exact ih htail a ha' b hb' hab

theorem termMd_sound {n : ℕ} {H F : List (ℕ × ℕ)} {pre : List ℕ} {g : ℕ}
    (hv : ValidState n H F) (hHne : H ≠ [])
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre ++ [g]))
    (hmin : ∀ k' < (pre ++ [g]).length, ¬ HasRunYF n H F k')
    {ops : List ℕ}
    (hops : ∀ x, MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre) x →
      x ≠ 0 → x ≠ univYF n F → x &&& edgePtsMaskYF H ≠ 0 → x ∈ ops) :
    let M := univYF n F
    let B := rawYF n M ++ pre
    let edgeTT := edgeTTYF n H M
    let md := isMeetLoop edgeTT B M
    md = edgeTT ∨
    ¬ (noCovPairs (edgePtsMaskYF H) (ops.filter (fun op => Nat.beq (Nat.land op (md ^^^ edgeTT)) 0)) = true) := by
  set M := univYF n F
  set B := rawYF n M ++ pre
  set edgeTT := edgeTTYF n H M
  set ep := edgePtsMaskYF H
  set md := isMeetLoop edgeTT B M
  by_cases hmd : md = edgeTT
  · exact Or.inl hmd
  right
  intro hnocov
  have hnotFin : isMeet M B edgeTT = false :=
    lexMin_not_finished hrun hmin (by simp)
  obtain ⟨a, b, hgab, hab, ha, hb, ha0, haM, haep, hb0, hbM, hbep⟩ :=
    lexMin_operands hv hrun hmin
  have ha_in : a ∈ ops := hops a ha ha0 haM haep
  have hb_in : b ∈ ops := hops b hb hb0 hbM hbep
  obtain ⟨_, _, hend⟩ := runListFrom_append.mp hrun
  have hEdgeNe0 : edgeTT ≠ 0 := by
    obtain ⟨e, _, heq⟩ := List.exists_cons_of_ne_nil hHne
    intro h0
    have hbit := edgePt_mem_edgeTTYF hv (show e ∈ H by rw [heq]; simp)
    rw [show edgeTTYF n H (univYF n F) = edgeTT from rfl, h0] at hbit
    simp at hbit
  have hloop_end : isMeetLoop edgeTT (B ++ [g]) M = edgeTT := by
    have hm := hend.2
    unfold isMeet at hm
    have hb0' : Nat.beq edgeTT 0 = false := (nat_beq_eq_false_iff _ _).mpr hEdgeNe0
    rw [hb0'] at hm
    exact Nat.eq_of_beq_eq_true hm
  have hloop_split : isMeetLoop edgeTT (B ++ [g]) M =
      match Nat.beq (Nat.land edgeTT g) edgeTT with
      | true => md &&& g
      | false => md := by
    have haux : ∀ (l₁ l₂ : List ℕ) (acc : ℕ),
        isMeetLoop edgeTT (l₁ ++ l₂) acc = isMeetLoop edgeTT l₂ (isMeetLoop edgeTT l₁ acc) := by
      intro l₁
      induction l₁ with
      | nil => intro _ _; rfl
      | cons x xs ih =>
        intro l₂ acc
        simp only [List.cons_append, isMeetLoop]
        cases Nat.beq (Nat.land edgeTT x) edgeTT <;> exact ih l₂ _
    rw [haux B [g] M]
    simp only [isMeetLoop, md, land_eq]
  rw [hloop_split] at hloop_end
  have hsub_eg : edgeTT &&& g = edgeTT := by
    cases hbg : Nat.beq (Nat.land edgeTT g) edgeTT
    · rw [hbg] at hloop_end; exact (hmd hloop_end).elim
    · simpa [land_eq] using Nat.eq_of_beq_eq_true hbg
  have hmd_g : md &&& g = edgeTT := by
    have hbg : Nat.beq (Nat.land edgeTT g) edgeTT = true := by simpa [land_eq] using hsub_eg
    rw [hbg] at hloop_end
    exact hloop_end
  have hsub_md : edgeTT &&& md = edgeTT :=
    isMeetLoop_target_sub B (edgeTTYF_and_univYF n H F)
  have hg_bad : g &&& (md ^^^ edgeTT) = 0 := by
    apply Nat.eq_of_testBit_eq; intro s
    have h1 := congrArg (fun z => z.testBit s) hmd_g
    have h2 := congrArg (fun z => z.testBit s) hsub_md
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at h1 h2 ⊢
    revert h1 h2
    cases md.testBit s <;> cases edgeTT.testBit s <;> cases g.testBit s <;> decide
  have ha_bad : a &&& (md ^^^ edgeTT) = 0 := by
    apply Nat.eq_of_testBit_eq; intro s
    have h1 := congrArg (fun z => z.testBit s) hg_bad
    simp only [hgab, Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h1 ⊢
    revert h1
    cases a.testBit s <;> cases b.testBit s <;> cases (md ^^^ edgeTT).testBit s <;> decide
  have hb_bad : b &&& (md ^^^ edgeTT) = 0 := by
    apply Nat.eq_of_testBit_eq; intro s
    have h1 := congrArg (fun z => z.testBit s) hg_bad
    simp only [hgab, Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h1 ⊢
    revert h1
    cases a.testBit s <;> cases b.testBit s <;> cases (md ^^^ edgeTT).testBit s <;> decide
  have ha_good : a ∈ ops.filter (fun op => Nat.beq (Nat.land op (md ^^^ edgeTT)) 0) :=
    List.mem_filter.mpr ⟨ha_in, by simp [ha_bad]⟩
  have hb_good : b ∈ ops.filter (fun op => Nat.beq (Nat.land op (md ^^^ edgeTT)) 0) :=
    List.mem_filter.mpr ⟨hb_in, by simp [hb_bad]⟩
  have hcov : (a ||| b) &&& ep = ep := by
    rw [← hgab]
    apply Nat.eq_of_testBit_eq; intro s
    rw [Nat.testBit_and]
    cases hep : ep.testBit s
    · simp
    · have hed : edgeTT.testBit s = true := by
        rw [testBit_edgePtsMaskYF, List.any_eq_true] at hep
        obtain ⟨e, heH, heq⟩ := hep
        rw [decide_eq_true_eq] at heq
        rw [← heq]; exact edgePt_mem_edgeTTYF hv heH
      have hgs : g.testBit s = true := by
        have := congrArg (fun z => z.testBit s) hsub_eg
        rw [Nat.testBit_and, hed, Bool.true_and] at this; exact this
      simp [hgs]
  exact noCovPairs_sound hnocov a ha_good b hb_good hab hcov

/-! ### Section 6b: Unified `CutDef` Validity Checker & Soundness -/

structure CutDefData where
  loss : ℕ
  steps : List CutStepData

def checkValidCutStep (M_prev edgeTT : ℕ) (raw_prev : List ℕ) (st : CutStepData) : Bool :=
  Nat.beq (Nat.land st.mc M_prev) st.mc &&
  raw_prev.all (fun r => let r' := Nat.land r st.mc; Nat.beq r' 0 || st.rc.contains r') &&
  st.rc.all (fun r' => raw_prev.any (fun r => Nat.beq r' (Nat.land r st.mc))) &&
  st.pv.all (fun pm =>
    Nat.beq (Nat.land pm M_prev) pm &&
    !Nat.beq (Nat.land pm edgeTT) 0 &&
    !Nat.beq (Nat.land pm edgeTT) pm &&
    !Nat.beq (Nat.land edgeTT st.mc) 0 &&
    raw_prev.all (fun r => probeOkGate st.mc pm r))

def checkValidCutChain (M edgeTT : ℕ) (raw : List ℕ) :
    List CutStepData → ℕ → List ℕ → Bool
  | [], M_end, raw_end => Nat.beq M M_end && decide (raw = raw_end)
  | st :: rest, M_end, raw_end =>
    checkValidCutStep M edgeTT raw st &&
    checkValidCutChain st.mc edgeTT st.rc rest M_end raw_end

def cutEndMask (n : ℕ) (F forbAdded : List (ℕ × ℕ)) (delVMask : ℕ) : ℕ :=
  mkBitmask (2 ^ n) (fun s => (univYF n (F ++ forbAdded)).testBit s && Nat.beq (Nat.land s delVMask) 0)

def cutEndEdges (H forbAdded : List (ℕ × ℕ)) (delVMask : ℕ) : List (ℕ × ℕ) :=
  H.filter (fun e => !forbAdded.any (undirEq e) && !delVMask.testBit e.1 && !delVMask.testBit e.2)

def cutEndForb (F forbAdded : List (ℕ × ℕ)) (delVMask : ℕ) : List (ℕ × ℕ) :=
  (F ++ forbAdded).filter (fun e => !delVMask.testBit e.1 && !delVMask.testBit e.2)

def checkCutValid (n : ℕ) (H F : List (ℕ × ℕ)) (cut : CutDefData)
    (delVMask : ℕ) (forbAdded : List (ℕ × ℕ)) (peels : List ℕ)
    (n_c : ℕ) (H_c F_c : List (ℕ × ℕ)) (f : List ℕ) : Bool :=
  let M := univYF n F
  let raw := rawYF n M
  let edgeTT := edgeTTYF n H M
  let M_end := cutEndMask n F forbAdded delVMask
  let rc_end := match cut.steps.getLast? with | none => raw | some st => st.rc
  let H_end := cutEndEdges H forbAdded delVMask
  let F_end := cutEndForb F forbAdded delVMask
  checkValidCutChain M edgeTT raw cut.steps M_end rc_end &&
  decide (ValidState n H_end F_end) &&
  decide (1 ≤ H_end.length) &&
  decide (H.length ≤ H_end.length + cut.loss) &&
  validPeelEmbed n H_end F_end peels n_c H_c F_c f

theorem checkValidCutStep_sound {M_prev edgeTT : ℕ} {raw_prev : List ℕ} {st : CutStepData}
    (hok : checkValidCutStep M_prev edgeTT raw_prev st = true) :
    ValidCutStep M_prev edgeTT raw_prev st ∧
    (∀ r' ∈ st.rc, ∃ r ∈ raw_prev, r' = r &&& st.mc) := by
  unfold checkValidCutStep at hok
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', nat_beq_eq_true_iff, nat_beq_eq_false_iff, land_eq,
    List.contains_eq_mem, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hmc, hraw⟩, hrc⟩, hpv⟩ := hok
  refine ⟨⟨hmc, hraw, fun pm hpm => ?_⟩, hrc⟩
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hpv pm hpm
  exact ⟨h1, h2, h3, h4, h5⟩

theorem checkValidCutChain_sound {n : ℕ} {F : List (ℕ × ℕ)} {M edgeTT M_end : ℕ}
    {raw raw_end : List ℕ} {steps : List CutStepData}
    (hraw_inv : ∀ r ∈ raw, r = 0 ∨ ∃ w < n, r = ttVarYF n w (univYF n F) &&& M)
    (hok : checkValidCutChain M edgeTT raw steps M_end raw_end = true) :
    ValidCutChain M edgeTT raw steps M_end raw_end ∧
    (∀ r ∈ raw_end, r = 0 ∨ ∃ w < n, r = ttVarYF n w (univYF n F) &&& M_end) := by
  induction steps generalizing M raw with
  | nil =>
    simp only [checkValidCutChain, Bool.and_eq_true, nat_beq_eq_true_iff, decide_eq_true_eq] at hok
    rcases hok with ⟨rfl, rfl⟩
    exact ⟨⟨rfl, rfl⟩, hraw_inv⟩
  | cons st rest ih =>
    simp only [checkValidCutChain, Bool.and_eq_true] at hok
    obtain ⟨hst, hrc_sub⟩ := checkValidCutStep_sound hok.1
    have hraw_next : ∀ r' ∈ st.rc, r' = 0 ∨ ∃ w < n, r' = ttVarYF n w (univYF n F) &&& st.mc := by
      intro r' hr'
      obtain ⟨r, hr, rfl⟩ := hrc_sub r' hr'
      rcases hraw_inv r hr with rfl | ⟨w, hw, rfl⟩
      · exact Or.inl (by simp)
      · refine Or.inr ⟨w, hw, ?_⟩
        rw [Nat.and_assoc, Nat.and_comm M st.mc, hst.1]
    obtain ⟨hchain, hend_inv⟩ := ih hraw_next hok.2
    exact ⟨⟨hst, hchain⟩, hend_inv⟩

theorem cutDef_kills_sound {n : ℕ} {H F : List (ℕ × ℕ)} {cut : CutDefData}
    {delVMask : ℕ} {forbAdded : List (ℕ × ℕ)} {peels : List ℕ}
    {n_c : ℕ} {H_c F_c : List (ℕ × ℕ)} {f : List ℕ}
    (hcut : checkCutValid n H F cut delVMask forbAdded peels n_c H_c F_c f = true)
    (hchild : OrCostLB n_c H_c F_c (H_c.length - 1))
    {pre suf : List ℕ}
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre ++ suf))
    (hlen : (pre ++ suf).length + 2 ≤ H.length)
    (hkilled : cut.loss ≤ evalCutChain cut.steps pre) :
    False := by
  unfold checkCutValid at hcut
  dsimp only at hcut
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcut
  obtain ⟨⟨⟨⟨hchain_ok, hv_end⟩, hne_end⟩, hloss_le⟩, hpeel_ok⟩ := hcut
  set M := univYF n F
  set raw := rawYF n M
  set edgeTT := edgeTTYF n H M
  set M_end := cutEndMask n F forbAdded delVMask
  set rc_end := match cut.steps.getLast? with | none => raw | some st => st.rc
  have hM : ∀ s, M.testBit s = true → s < 2 ^ n := fun _ => univYF_testBit_lt
  have hraw_inv : ∀ r ∈ raw, r = 0 ∨ ∃ w < n, r = ttVarYF n w M &&& M := by
    intro r hr
    simp only [raw, rawYF, List.mem_map, List.mem_range] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    exact Or.inr ⟨w, hw, (ttVarYF_and_mask hM).symm⟩
  obtain ⟨hchain, hrc_inv⟩ := checkValidCutChain_sound hraw_inv hchain_ok
  obtain ⟨hvp, hsuf⟩ := runListFrom_append.mp hrun
  have hrun_suf : Run (decM M '' { x | x ∈ raw ++ pre }) suf.length (decM M edgeTT) :=
    runListFrom_to_run hsuf
  obtain ⟨k_end, hk_budget, hrun_end⟩ := cutChain_sound cut.steps hchain hvp hrun_suf
  have hmc_spec : ∀ s, M_end.testBit s = true ↔
      (univYF n (F ++ forbAdded)).testBit s = true ∧ s &&& delVMask = 0 := by
    intro s
    simp only [M_end, cutEndMask, testBit_mkBitmask, Bool.and_eq_true, decide_eq_true_eq,
      nat_beq_eq_true_iff, land_eq]
    exact ⟨fun ⟨_, h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨univYF_testBit_lt h1, h1, h2⟩⟩
  have hhas_end : HasRunYF n (cutEndEdges H forbAdded delVMask) (cutEndForb F forbAdded delVMask) k_end :=
    cutEnd_to_hasRunYF hmc_spec hrc_inv hrun_end
  have hlb_end : (cutEndEdges H forbAdded delVMask).length - 1 ≤ k_end :=
    validPeelEmbed_sound hv_end hpeel_ok hchild k_end hhas_end
  simp only [List.length_append] at hlen
  omega

/-! ## Section 7: Circuit-to-Graph Bridge & All 31 Target Graphs from `L-meta-984.stmt` -/

def edgeFnList (n : ℕ) (H : List (ℕ × ℕ)) (x : Fin n → Bool) : Bool :=
  H.any (fun e => if h : e.1 < n ∧ e.2 < n then x ⟨e.1, h.1⟩ && x ⟨e.2, h.2⟩ else false)

theorem or_bound_of_eval_eq {n lb : ℕ} {H : List (ℕ × ℕ)} {f : (Fin n → Bool) → Bool}
    (hH : ∀ e ∈ H, e.1 < n ∧ e.2 < n)
    (hf : ∀ x : Fin n → Bool, f x = edgeFnList n H x)
    (hlb : OrCostLB n H [] lb)
    (C : Circuit) (hc : Monotone2 C)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    lb ≤ countOrGates C.gates := by
  have he' : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ e ∈ H, ∃ (h1 : e.1 < n) (h2 : e.2 < n), x ⟨e.1, h1⟩ = true ∧ x ⟨e.2, h2⟩ = true := by
    intro x
    rw [he x, hf x, edgeFnList, List.any_eq_true]
    constructor
    · rintro ⟨e, heH, hval⟩
      obtain ⟨h1, h2⟩ := hH e heH
      simp only [h1, h2, and_self, ↓reduceDIte, Bool.and_eq_true] at hval
      exact ⟨e, heH, h1, h2, hval.1, hval.2⟩
    · rintro ⟨e, heH, h1, h2, hx1, hx2⟩
      refine ⟨e, heH, ?_⟩
      simp only [h1, h2, and_self, ↓reduceDIte, Bool.and_eq_true]
      exact ⟨hx1, hx2⟩
  obtain ⟨k, hk, hrun⟩ := ofCircuitYF H C hc he' hH
  exact (hlb k hrun).trans hk

def g0_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 5)]
def g0_fn (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)
theorem g0_fn_eq : ∀ x : Fin 6 → Bool, g0_fn x = edgeFnList 6 g0_edges x := by
  intro x; simp [g0_fn, edgeFnList, g0_edges, Bool.or_assoc]

def g1_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4), (5, 6)]
def g1_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)
theorem g1_fn_eq : ∀ x : Fin 7 → Bool, g1_fn x = edgeFnList 7 g1_edges x := by
  intro x; simp [g1_fn, edgeFnList, g1_edges, Bool.or_assoc]

def g2_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (4, 6)]
def g2_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)
theorem g2_fn_eq : ∀ x : Fin 7 → Bool, g2_fn x = edgeFnList 7 g2_edges x := by
  intro x; simp [g2_fn, edgeFnList, g2_edges, Bool.or_assoc]

def g3_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 6)]
def g3_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)
theorem g3_fn_eq : ∀ x : Fin 7 → Bool, g3_fn x = edgeFnList 7 g3_edges x := by
  intro x; simp [g3_fn, edgeFnList, g3_edges, Bool.or_assoc]

def g4_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 6)]
def g4_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)
theorem g4_fn_eq : ∀ x : Fin 7 → Bool, g4_fn x = edgeFnList 7 g4_edges x := by
  intro x; simp [g4_fn, edgeFnList, g4_edges, Bool.or_assoc]

def g5_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5), (5, 6)]
def g5_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)
theorem g5_fn_eq : ∀ x : Fin 7 → Bool, g5_fn x = edgeFnList 7 g5_edges x := by
  intro x; simp [g5_fn, edgeFnList, g5_edges, Bool.or_assoc]

def g6_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (4, 5), (4, 6), (5, 6)]
def g6_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)
theorem g6_fn_eq : ∀ x : Fin 7 → Bool, g6_fn x = edgeFnList 7 g6_edges x := by
  intro x; simp [g6_fn, edgeFnList, g6_edges, Bool.or_assoc]

def g7_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6), (4, 5)]
def g7_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)
theorem g7_fn_eq : ∀ x : Fin 7 → Bool, g7_fn x = edgeFnList 7 g7_edges x := by
  intro x; simp [g7_fn, edgeFnList, g7_edges, Bool.or_assoc]

def g8_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (1, 3), (2, 4), (3, 5), (4, 6), (5, 6)]
def g8_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
theorem g8_fn_eq : ∀ x : Fin 7 → Bool, g8_fn x = edgeFnList 7 g8_edges x := by
  intro x; simp [g8_fn, edgeFnList, g8_edges, Bool.or_assoc]

def g9_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (3, 4)]
def g9_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)
theorem g9_fn_eq : ∀ x : Fin 7 → Bool, g9_fn x = edgeFnList 7 g9_edges x := by
  intro x; simp [g9_fn, edgeFnList, g9_edges, Bool.or_assoc]

def g10_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 6), (3, 4)]
def g10_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)
theorem g10_fn_eq : ∀ x : Fin 7 → Bool, g10_fn x = edgeFnList 7 g10_edges x := by
  intro x; simp [g10_fn, edgeFnList, g10_edges, Bool.or_assoc]

def g11_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4), (5, 6)]
def g11_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)
theorem g11_fn_eq : ∀ x : Fin 7 → Bool, g11_fn x = edgeFnList 7 g11_edges x := by
  intro x; simp [g11_fn, edgeFnList, g11_edges, Bool.or_assoc]

def g12_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (1, 6), (3, 4)]
def g12_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)
theorem g12_fn_eq : ∀ x : Fin 7 → Bool, g12_fn x = edgeFnList 7 g12_edges x := by
  intro x; simp [g12_fn, edgeFnList, g12_edges, Bool.or_assoc]

def g13_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (2, 6), (3, 4)]
def g13_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)
theorem g13_fn_eq : ∀ x : Fin 7 → Bool, g13_fn x = edgeFnList 7 g13_edges x := by
  intro x; simp [g13_fn, edgeFnList, g13_edges, Bool.or_assoc]

def g14_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (3, 6)]
def g14_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)
theorem g14_fn_eq : ∀ x : Fin 7 → Bool, g14_fn x = edgeFnList 7 g14_edges x := by
  intro x; simp [g14_fn, edgeFnList, g14_edges, Bool.or_assoc]

def g15_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (5, 6)]
def g15_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)
theorem g15_fn_eq : ∀ x : Fin 7 → Bool, g15_fn x = edgeFnList 7 g15_edges x := by
  intro x; simp [g15_fn, edgeFnList, g15_edges, Bool.or_assoc]

def g16_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 6), (5, 6)]
def g16_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)
theorem g16_fn_eq : ∀ x : Fin 7 → Bool, g16_fn x = edgeFnList 7 g16_edges x := by
  intro x; simp [g16_fn, edgeFnList, g16_edges, Bool.or_assoc]

def g17_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (3, 6), (5, 6)]
def g17_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)
theorem g17_fn_eq : ∀ x : Fin 7 → Bool, g17_fn x = edgeFnList 7 g17_edges x := by
  intro x; simp [g17_fn, edgeFnList, g17_edges, Bool.or_assoc]

def g18_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (4, 6), (5, 6)]
def g18_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
theorem g18_fn_eq : ∀ x : Fin 7 → Bool, g18_fn x = edgeFnList 7 g18_edges x := by
  intro x; simp [g18_fn, edgeFnList, g18_edges, Bool.or_assoc]

def g19_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5), (3, 6), (4, 6)]
def g19_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)
theorem g19_fn_eq : ∀ x : Fin 7 → Bool, g19_fn x = edgeFnList 7 g19_edges x := by
  intro x; simp [g19_fn, edgeFnList, g19_edges, Bool.or_assoc]

def g20_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6), (4, 5)]
def g20_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)
theorem g20_fn_eq : ∀ x : Fin 7 → Bool, g20_fn x = edgeFnList 7 g20_edges x := by
  intro x; simp [g20_fn, edgeFnList, g20_edges, Bool.or_assoc]

def g21_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6), (5, 6)]
def g21_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)
theorem g21_fn_eq : ∀ x : Fin 7 → Bool, g21_fn x = edgeFnList 7 g21_edges x := by
  intro x; simp [g21_fn, edgeFnList, g21_edges, Bool.or_assoc]

def g22_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5), (5, 6)]
def g22_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)
theorem g22_fn_eq : ∀ x : Fin 7 → Bool, g22_fn x = edgeFnList 7 g22_edges x := by
  intro x; simp [g22_fn, edgeFnList, g22_edges, Bool.or_assoc]

def g23_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 6), (5, 6)]
def g23_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
theorem g23_fn_eq : ∀ x : Fin 7 → Bool, g23_fn x = edgeFnList 7 g23_edges x := by
  intro x; simp [g23_fn, edgeFnList, g23_edges, Bool.or_assoc]

def g24_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5), (4, 6), (5, 6)]
def g24_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)
theorem g24_fn_eq : ∀ x : Fin 7 → Bool, g24_fn x = edgeFnList 7 g24_edges x := by
  intro x; simp [g24_fn, edgeFnList, g24_edges, Bool.or_assoc]

def g25_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6), (4, 5), (4, 6)]
def g25_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)
theorem g25_fn_eq : ∀ x : Fin 7 → Bool, g25_fn x = edgeFnList 7 g25_edges x := by
  intro x; simp [g25_fn, edgeFnList, g25_edges, Bool.or_assoc]

def g26_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (3, 4), (5, 6)]
def g26_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)
theorem g26_fn_eq : ∀ x : Fin 7 → Bool, g26_fn x = edgeFnList 7 g26_edges x := by
  intro x; simp [g26_fn, edgeFnList, g26_edges, Bool.or_assoc]

def g27_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (1, 6), (3, 4), (5, 6)]
def g27_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)
theorem g27_fn_eq : ∀ x : Fin 7 → Bool, g27_fn x = edgeFnList 7 g27_edges x := by
  intro x; simp [g27_fn, edgeFnList, g27_edges, Bool.or_assoc]

def g28_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (3, 6), (5, 6)]
def g28_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)
theorem g28_fn_eq : ∀ x : Fin 7 → Bool, g28_fn x = edgeFnList 7 g28_edges x := by
  intro x; simp [g28_fn, edgeFnList, g28_edges, Bool.or_assoc]

def g29_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5), (3, 6), (4, 6), (5, 6)]
def g29_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)
theorem g29_fn_eq : ∀ x : Fin 7 → Bool, g29_fn x = edgeFnList 7 g29_edges x := by
  intro x; simp [g29_fn, edgeFnList, g29_edges, Bool.or_assoc]

def g30_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6), (4, 5), (5, 6)]
def g30_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)
theorem g30_fn_eq : ∀ x : Fin 7 → Bool, g30_fn x = edgeFnList 7 g30_edges x := by
  intro x; simp [g30_fn, edgeFnList, g30_edges, Bool.or_assoc]

/-! ## Section 8: Fast Witness-Guided Checker Definitions & Complete Soundness -/

structure StateDesc where
  n     : Nat
  edges : List (Nat × Nat)
  forb  : List (Nat × Nat)

structure CutSpecData where
  delVMask  : Nat
  forbAdded : List (Nat × Nat)
  peels     : List Nat
  childId   : Nat
  embed     : List Nat

structure GraphCoreSpec where
  graphIdx : Nat
  n        : Nat
  edges    : List (Nat × Nat)
  bound    : Nat
  coreId   : Nat
  peels    : List Nat
  embed    : List Nat

structure ChkStepState where
  mc        : Nat
  sb        : List Nat
  validPv   : List Nat
  tailBonus : Nat

structure ChkCutState where
  need  : Nat
  steps : List ChkStepState

inductive ChkCutStepSpec where
  | v : Nat → List Nat → ChkCutStepSpec
  | e : List (Nat × Nat) → ChkCutStepSpec

mutual
  inductive CertNode where
    | term : CertNode
    | branch : List Nat → List (List Nat) → CertList → CertNode

  inductive CertList where
    | nil : CertList
    | cons : Nat → CertNode → CertList → CertList
end

def chkAll128 : Nat := 0xffffffffffffffffffffffffffffffff

def chkVarOne : Nat → Nat
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000
  | _ => 0

def chkVarZero (v : Nat) : Nat := Nat.xor chkAll128 (chkVarOne v)

def chkForbLoop (acc : Nat) : List (Nat × Nat) → Nat
  | [] => acc
  | (u, v) :: rest =>
    chkForbLoop (Nat.land acc (Nat.xor chkAll128 (Nat.land (chkVarOne u) (chkVarOne v)))) rest

def chkMkRawLoop (maskYF : Nat) : Nat → Nat → List Nat
  | _, 0 => []
  | v, k + 1 => Nat.land maskYF (chkVarOne v) :: chkMkRawLoop maskYF (v + 1) k

def chkMkRaw (n maskYF : Nat) : List Nat := chkMkRawLoop maskYF 0 n

def chkMkEdgeMasks (maskYF : Nat) : List (Nat × Nat) → List Nat
  | [] => []
  | (u, v) :: rest => Nat.land maskYF (Nat.land (chkVarOne u) (chkVarOne v)) :: chkMkEdgeMasks maskYF rest

def chkMkMasksTT (n : Nat) (edges : List (Nat × Nat)) (maskYF : Nat) : List Nat :=
  maskYF :: chkMkRaw n maskYF ++ chkMkEdgeMasks maskYF edges

def chkFilterRc (mc : Nat) : List Nat → List Nat
  | [] => []
  | r :: rest =>
    let r' := Nat.land r mc
    match Nat.beq r' 0 with
    | true => chkFilterRc mc rest
    | false => r' :: chkFilterRc mc rest

def chkMkPv (v : Nat) : List Nat → List Nat
  | [] => []
  | s :: rest =>
    Nat.lor (Nat.pow 2 s) (Nat.pow 2 (Nat.lor s (Nat.pow 2 v))) :: chkMkPv v rest

def chkBuildCutSteps (mPrev : Nat) (rPrev : List Nat) : List ChkCutStepSpec → List CutStepData
  | [] => []
  | .v v ps :: rest =>
    let mc := Nat.land mPrev (chkVarZero v)
    let rc := chkFilterRc mc rPrev
    { mc := mc, rc := rc, pv := chkMkPv v ps } :: chkBuildCutSteps mc rc rest
  | .e es :: rest =>
    let mc := chkForbLoop mPrev es
    let rc := chkFilterRc mc rPrev
    { mc := mc, rc := rc, pv := [] } :: chkBuildCutSteps mc rc rest

def chkMkCuts (maskYF : Nat) (raw : List Nat) : List (Nat × List ChkCutStepSpec) → List CutDefData
  | [] => []
  | (loss, specs) :: rest =>
    { loss := loss, steps := chkBuildCutSteps maskYF raw specs } :: chkMkCuts maskYF raw rest

def chkAppend : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, ys => x :: chkAppend xs ys

def chkFlatten : List (List Nat) → List Nat
  | [] => []
  | c :: rest => chkAppend c (chkFlatten rest)

def chkMemNat (x : Nat) : List Nat → Bool
  | [] => false
  | y :: rest =>
    match Nat.beq x y with
    | true => true
    | false => chkMemNat x rest

def chkIsMeetLoop (target acc : Nat) : List Nat → Bool
  | [] => Nat.beq acc target
  | b :: rest =>
    match Nat.beq (Nat.land target b) target with
    | true =>
      let acc' := Nat.land acc b
      match Nat.beq acc' target with
      | true => true
      | false => chkIsMeetLoop target acc' rest
    | false => chkIsMeetLoop target acc rest

def chkIsMeet (univMask : Nat) (basis : List Nat) (target : Nat) : Bool :=
  match Nat.beq target 0 with
  | true => true
  | false => chkIsMeetLoop target univMask basis

def chkIsOnEdgesLoop (eg g acc : Nat) : List Nat → Bool
  | [] => Nat.beq (Nat.land acc g) acc
  | b :: rest =>
    match Nat.beq (Nat.land eg b) eg with
    | true =>
      let acc' := Nat.land acc b
      match Nat.beq (Nat.land acc' g) acc' with
      | true => true
      | false => chkIsOnEdgesLoop eg g acc' rest
    | false => chkIsOnEdgesLoop eg g acc rest

def chkProbeOkGate (mc pm h : Nat) : Bool :=
  let x := Nat.land h pm
  match Nat.beq x 0 with
  | true => true
  | false =>
    match Nat.beq x pm with
    | true => true
    | false => Nat.beq (Nat.land h mc) 0

def chkAllProbeOk (mc pm : Nat) : List Nat → Bool
  | [] => true
  | h :: rest =>
    match chkProbeOkGate mc pm h with
    | true => chkAllProbeOk mc pm rest
    | false => false

def chkFilterPv (mc : Nat) (act : List Nat) : List Nat → List Nat
  | [] => []
  | pm :: rest =>
    match chkAllProbeOk mc pm act with
    | true => pm :: chkFilterPv mc act rest
    | false => chkFilterPv mc act rest

def chkAnyProbeOk (mc g : Nat) : List Nat → Bool
  | [] => false
  | pm :: rest =>
    match chkProbeOkGate mc pm g with
    | true => true
    | false => chkAnyProbeOk mc g rest

def chkStepFilterAct (mc : Nat) : List Nat → List Nat → Nat → List Nat → (List Nat × Nat × List Nat)
  | [], sb, sv, actRev => (sb, sv, actRev.reverse)
  | h :: rest, sb, sv, actRev =>
    let rh := Nat.land h mc
    match chkIsMeet mc sb rh with
    | true => chkStepFilterAct mc rest sb (sv + 1) actRev
    | false => chkStepFilterAct mc rest (rh :: sb) sv (rh :: actRev)

def chkPrepSteps : List CutStepData → List Nat → Nat → (Nat × Nat × List ChkStepState)
  | [], _, sv => (sv, 0, [])
  | st :: rest, act, sv =>
    let vp := chkFilterPv st.mc act st.pv
    let (sb, sv', act') := chkStepFilterAct st.mc act st.rc sv []
    let (totSv, tailB, restStates) := chkPrepSteps rest act' sv'
    let myB := match vp with | [] => 0 | _ :: _ => 1
    (totSv, myB + tailB, { mc := st.mc, sb := sb, validPv := vp, tailBonus := tailB } :: restStates)

def chkPrepCutState (cut : CutDefData) (gs : List Nat) : ChkCutState :=
  let (totSv, _, sts) := chkPrepSteps cut.steps gs 0
  { need := Nat.sub cut.loss totSv, steps := sts }

def chkCutKillsAtStep (g need : Nat) : Nat → List ChkStepState → Bool
  | _, [] => Nat.beq need 0
  | 0, st :: _ =>
    let rg := Nat.land g st.mc
    match chkIsMeet st.mc st.sb rg with
    | false => false
    | true =>
      match Nat.ble need (1 + st.tailBonus) with
      | true => true
      | false =>
        match Nat.ble need (2 + st.tailBonus) with
        | true => chkAnyProbeOk st.mc g st.validPv
        | false => false
  | s' + 1, st :: rest =>
    let need' := match st.validPv with
      | [] => need
      | _ :: _ =>
        match chkAnyProbeOk st.mc g st.validPv with
        | true => Nat.sub need 1
        | false => need
    match Nat.beq need' 0 with
    | true => true
    | false => chkCutKillsAtStep (Nat.land g st.mc) need' s' rest

def chkCutKillsWit (cs : ChkCutState) (stepIdx g : Nat) : Bool :=
  match Nat.beq cs.need 0 with
  | true => true
  | false => chkCutKillsAtStep g cs.need stepIdx cs.steps

def chkGetCutState (xs : List ChkCutState) : Nat → ChkCutState
  | 0 => match xs with | c :: _ => c | [] => { need := 1, steps := [] }
  | k + 1 => match xs with | _ :: rest => chkGetCutState rest k | [] => { need := 1, steps := [] }

def chkApplyPermLoop (f acc : Nat) : List Nat → Nat
  | [] => acc
  | m2 :: rest =>
    match Nat.beq f 0 with
    | true => acc
    | false =>
      let acc' := match Nat.beq (Nat.land f 1) 1 with | true => Nat.lor acc m2 | false => acc
      chkApplyPermLoop (Nat.div f 2) acc' rest

def chkApplyPerm (tbl : List Nat) (f : Nat) : Nat :=
  chkApplyPermLoop f 0 tbl

def chkApplyPermList (f : Nat) : List (List Nat) → List Nat
  | [] => []
  | tbl :: rest => chkApplyPerm tbl f :: chkApplyPermList f rest

def chkAnyPermLt (g : Nat) : List Nat → List Nat → Bool
  | p :: ps, q :: qs =>
    match Nat.blt (Nat.lor p q) g with
    | true => true
    | false => chkAnyPermLt g ps qs
  | _, _ => false

def chkFilterStab (g : Nat) : List (List Nat) → List (List Nat)
  | [] => []
  | tbl :: rest =>
    match Nat.beq (chkApplyPerm tbl g) g with
    | true => tbl :: chkFilterStab g rest
    | false => chkFilterStab g rest

def chkGetCut (cuts : List CutDefData) : Nat → CutDefData
  | 0 => match cuts with | c :: _ => c | [] => { loss := 1, steps := [] }
  | k + 1 => match cuts with | _ :: rest => chkGetCut rest k | [] => { loss := 1, steps := [] }

def chkPrepHints (cuts : List CutDefData) (gs : List Nat) : List Nat → List ChkCutState
  | [] => []
  | ci :: rest => chkPrepCutState (chkGetCut cuts ci) gs :: chkPrepHints cuts gs rest

def chkSubsetsStep (g : Nat) : List Nat → List Nat → List Nat
  | [], acc => acc
  | x :: rest, acc => chkSubsetsStep g rest (Nat.land x g :: acc)

def chkAddBirthOps (maskYF edgePtsMask gi birth : Nat) : List Nat → List Nat → List (Nat × Nat × Nat) → (List Nat × List (Nat × Nat × Nat))
  | [], seen, acc => (seen, acc)
  | mt :: rest, seen, acc =>
    let op := Nat.land mt gi
    match Nat.beq op 0 with
    | true => chkAddBirthOps maskYF edgePtsMask gi birth rest seen acc
    | false =>
      match Nat.beq op maskYF with
      | true => chkAddBirthOps maskYF edgePtsMask gi birth rest seen acc
      | false =>
        let eg := Nat.land op edgePtsMask
        match Nat.beq eg 0 with
        | true => chkAddBirthOps maskYF edgePtsMask gi birth rest seen acc
        | false =>
          match chkMemNat op seen with
          | true => chkAddBirthOps maskYF edgePtsMask gi birth rest seen acc
          | false => chkAddBirthOps maskYF edgePtsMask gi birth rest (op :: seen) ((op, eg, birth) :: acc)

def chkAddSubsOps (maskYF edgePtsMask birth : Nat) (masksTT : List Nat) : List Nat → List Nat → List (Nat × Nat × Nat) → (List Nat × List (Nat × Nat × Nat))
  | [], seen, acc => (seen, acc)
  | gi :: rest, seen, acc =>
    let (seen', acc') := chkAddBirthOps maskYF edgePtsMask gi birth masksTT seen acc
    chkAddSubsOps maskYF edgePtsMask birth masksTT rest seen' acc'

def chkGenBirthLoop (maskYF edgePtsMask : Nat) (masksTT : List Nat) (birth : Nat)
    (subs seen : List Nat) (acc : List (Nat × Nat × Nat)) : List Nat → List (Nat × Nat × Nat)
  | [] => acc
  | g :: rest =>
    let newSubs := chkSubsetsStep g subs []
    let (seen', acc') := chkAddSubsOps maskYF edgePtsMask birth masksTT newSubs seen acc
    chkGenBirthLoop maskYF edgePtsMask masksTT (birth + 1) (newSubs ++ subs) seen' acc' rest

def chkGenBirthOps (maskYF edgePtsMask : Nat) (masksTT gs : List Nat) : List (Nat × Nat × Nat) :=
  let (seen0, acc0) := chkAddBirthOps maskYF edgePtsMask maskYF 0 masksTT [] []
  chkGenBirthLoop maskYF edgePtsMask masksTT 1 [maskYF] seen0 acc0 gs

def chkNatMax (a b : Nat) : Nat :=
  match Nat.blt a b with | true => b | false => a

def chkBuildSuffixMax : List Nat → List Nat
  | [] => [0]
  | g :: rest =>
    match chkBuildSuffixMax rest with
    | [] => [g, 0]
    | m :: ms => chkNatMax g m :: m :: ms

def chkGetNat (xs : List Nat) : Nat → Nat
  | 0 => match xs with | x :: _ => x | [] => 0
  | k + 1 => match xs with | _ :: rest => chkGetNat rest k | [] => 0

def chkCheckWitNoStab (maskYF : Nat) (b : List Nat) (hStates : List ChkCutState) (surv : List Nat)
    (eg g w : Nat) : Bool :=
  match w with
  | 0 => chkMemNat g surv
  | 1 => chkIsOnEdgesLoop eg g maskYF b
  | 2 => false
  | w3 + 3 => chkCutKillsWit (chkGetCutState hStates (Nat.div w3 8)) (Nat.land w3 7) g

def chkPairsNoStabInner (maskYF : Nat) (b : List Nat) (hStates : List ChkCutState)
    (surv : List Nat) (oi egi lim : Nat) : List (Nat × Nat × Nat) → List Nat → Option (List Nat)
  | [], wits => some wits
  | (oj, egj, _) :: rest, wits =>
    let eij := Nat.land egi egj
    match Nat.beq eij egi with
    | true => chkPairsNoStabInner maskYF b hStates surv oi egi lim rest wits
    | false =>
      match Nat.beq eij egj with
      | true => chkPairsNoStabInner maskYF b hStates surv oi egi lim rest wits
      | false =>
        let g := Nat.lor oi oj
        let skipLex := match Nat.beq lim 0 with | true => false | false => Nat.blt g lim
        match skipLex with
        | true => chkPairsNoStabInner maskYF b hStates surv oi egi lim rest wits
        | false =>
          match wits with
          | [] => none
          | w :: ws =>
            match chkCheckWitNoStab maskYF b hStates surv (Nat.lor egi egj) g w with
            | true => chkPairsNoStabInner maskYF b hStates surv oi egi lim rest ws
            | false => none

def chkPairsNoStabOuter (maskYF : Nat) (b : List Nat) (hStates : List ChkCutState)
    (surv smax : List Nat) : List (Nat × Nat × Nat) → List Nat → Bool
  | [], _ => true
  | (oi, egi, bi) :: rest, wits =>
    let lim := chkGetNat smax bi
    match chkPairsNoStabInner maskYF b hStates surv oi egi lim rest wits with
    | some wits' => chkPairsNoStabOuter maskYF b hStates surv smax rest wits'
    | none => false

def chkAttachPerms (stab : List (List Nat)) : List (Nat × Nat × Nat) → List (Nat × Nat × Nat × List Nat)
  | [] => []
  | (op, eg, bi) :: rest => (op, eg, bi, chkApplyPermList op stab) :: chkAttachPerms stab rest

def chkCheckWitStab (maskYF : Nat) (b : List Nat) (hStates : List ChkCutState) (surv : List Nat)
    (eg g : Nat) (pi pj : List Nat) (w : Nat) : Bool :=
  match w with
  | 0 => chkMemNat g surv
  | 1 => chkIsOnEdgesLoop eg g maskYF b
  | 2 => chkAnyPermLt g pi pj
  | w3 + 3 => chkCutKillsWit (chkGetCutState hStates (Nat.div w3 8)) (Nat.land w3 7) g

def chkPairsStabInner (maskYF : Nat) (b : List Nat) (hStates : List ChkCutState)
    (surv : List Nat) (oi egi lim : Nat) (pi : List Nat) : List (Nat × Nat × Nat × List Nat) → List Nat → Option (List Nat)
  | [], wits => some wits
  | (oj, egj, _, pj) :: rest, wits =>
    let eij := Nat.land egi egj
    match Nat.beq eij egi with
    | true => chkPairsStabInner maskYF b hStates surv oi egi lim pi rest wits
    | false =>
      match Nat.beq eij egj with
      | true => chkPairsStabInner maskYF b hStates surv oi egi lim pi rest wits
      | false =>
        let g := Nat.lor oi oj
        let skipLex := match Nat.beq lim 0 with | true => false | false => Nat.blt g lim
        match skipLex with
        | true => chkPairsStabInner maskYF b hStates surv oi egi lim pi rest wits
        | false =>
          match wits with
          | [] => none
          | w :: ws =>
            match chkCheckWitStab maskYF b hStates surv (Nat.lor egi egj) g pi pj w with
            | true => chkPairsStabInner maskYF b hStates surv oi egi lim pi rest ws
            | false => none

def chkPairsStabOuter (maskYF : Nat) (b : List Nat) (hStates : List ChkCutState)
    (surv smax : List Nat) : List (Nat × Nat × Nat × List Nat) → List Nat → Bool
  | [], _ => true
  | (oi, egi, bi, pi) :: rest, wits =>
    let lim := chkGetNat smax bi
    match chkPairsStabInner maskYF b hStates surv oi egi lim pi rest wits with
    | some wits' => chkPairsStabOuter maskYF b hStates surv smax rest wits'
    | none => false

def chkCertListGates : CertList → List Nat
  | .nil => []
  | .cons g _ rest => g :: chkCertListGates rest

def chkComputeMd (edgeTT acc : Nat) : List Nat → Nat
  | [] => acc
  | x :: rest =>
    match Nat.beq (Nat.land edgeTT x) edgeTT with
    | true => chkComputeMd edgeTT (Nat.land acc x) rest
    | false => chkComputeMd edgeTT acc rest

def chkFilterGoodOps (bad : Nat) : List (Nat × Nat × Nat) → List Nat
  | [] => []
  | (op, _, _) :: rest =>
    match Nat.beq (Nat.land op bad) 0 with
    | true => op :: chkFilterGoodOps bad rest
    | false => chkFilterGoodOps bad rest

def chkNoCovInner (edgePtsMask a : Nat) : List Nat → Bool
  | [] => true
  | b :: rest =>
    match Nat.beq (Nat.land (Nat.lor a b) edgePtsMask) edgePtsMask with
    | true => false
    | false => chkNoCovInner edgePtsMask a rest

def chkNoCovOuter (edgePtsMask : Nat) : List Nat → Bool
  | [] => true
  | a :: rest =>
    match chkNoCovInner edgePtsMask a rest with
    | true => chkNoCovOuter edgePtsMask rest
    | false => false

def chkCheckTermMd (maskYF edgePtsMask edgeTT : Nat) (raw masksTT gs : List Nat) : Bool :=
  let b := raw ++ gs
  let md := chkComputeMd edgeTT maskYF b
  match Nat.beq md edgeTT with
  | true => false
  | false =>
    let bad := Nat.xor md edgeTT
    let ops := chkGenBirthOps maskYF edgePtsMask masksTT gs
    let good := chkFilterGoodOps bad ops
    chkNoCovOuter edgePtsMask good

def chkCheckLayer (maskYF edgePtsMask edgeTT : Nat) (raw masksTT : List Nat) (cuts : List CutDefData)
    (gs : List Nat) (stab : List (List Nat)) (hints wits surv : List Nat) : Bool :=
  let b := raw ++ gs
  match chkIsMeet maskYF b edgeTT with
  | true => false
  | false =>
    let hStates := chkPrepHints cuts gs hints
    let ops := chkGenBirthOps maskYF edgePtsMask masksTT gs
    let smax := chkBuildSuffixMax gs
    match stab with
    | [] => chkPairsNoStabOuter maskYF b hStates surv smax ops wits
    | _ :: _ =>
      let pops := chkAttachPerms stab ops
      chkPairsStabOuter maskYF b hStates surv smax pops wits

def chkMkAutIdxLoop (perm : List Nat) : Nat → List Nat
  | 0 => [0]
  | k + 1 =>
    let prev := chkMkAutIdxLoop perm k
    let bit := Nat.pow 2 (chkGetNat perm k)
    prev ++ prev.map (fun s => Nat.lor s bit)

def chkMkAutIdxTbls (n : Nat) (perms : List (List Nat)) : List (List Nat) :=
  perms.map (fun p => chkMkAutIdxLoop p n)

def chkMkAutMaskTbls (idxTbls : List (List Nat)) : List (List Nat) :=
  idxTbls.map (fun tbl => tbl.map (fun s => Nat.pow 2 s))

mutual
  def chkCheckNode (maskYF edgePtsMask edgeTT : Nat) (raw masksTT : List Nat) (cuts : List CutDefData)
      (gs : List Nat) (stab : List (List Nat)) : CertNode → Bool
    | .term => chkCheckTermMd maskYF edgePtsMask edgeTT raw masksTT gs
    | .branch hints witsChunks children =>
      match chkCheckLayer maskYF edgePtsMask edgeTT raw masksTT cuts gs stab hints (chkFlatten witsChunks) (chkCertListGates children) with
      | true => chkCheckChildren maskYF edgePtsMask edgeTT raw masksTT cuts gs stab children
      | false => false

  def chkCheckChildren (maskYF edgePtsMask edgeTT : Nat) (raw masksTT : List Nat) (cuts : List CutDefData)
      (gs : List Nat) (stab : List (List Nat)) : CertList → Bool
    | .nil => true
    | .cons g ch rest =>
      match chkCheckNode maskYF edgePtsMask edgeTT raw masksTT cuts (gs ++ [g]) (chkFilterStab g stab) ch with
      | true => chkCheckChildren maskYF edgePtsMask edgeTT raw masksTT cuts gs stab rest
      | false => false
end

mutual
  def certDepthOk (maxD d : ℕ) : CertNode → Bool
    | .term => Nat.ble maxD d
    | .branch _ _ ch => certListDepthOk maxD (d + 1) ch

  def certListDepthOk (maxD d : ℕ) : CertList → Bool
    | .nil => true
    | .cons _ ch rest => certDepthOk maxD d ch && certListDepthOk maxD d rest
end

/-! ### Checker Soundness Proofs -/

theorem chkMemNat_iff (x : ℕ) (l : List ℕ) : chkMemNat x l = true ↔ x ∈ l := by
  induction l with
  | nil => simp [chkMemNat]
  | cons y rest ih =>
    simp only [chkMemNat, List.mem_cons]
    cases h : Nat.beq x y
    · simp [ih, (nat_beq_eq_false_iff x y).mp h]
    · simp [Nat.eq_of_beq_eq_true h]

theorem chkIsMeetLoop_eq (target acc : ℕ) (bs : List ℕ) (hsub : target &&& acc = target) :
    chkIsMeetLoop target acc bs = Nat.beq (isMeetLoop target bs acc) target := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b rest ih =>
    simp only [chkIsMeetLoop, isMeetLoop]
    cases hb : Nat.beq (Nat.land target b) target
    · exact ih acc hsub
    · have hb' : target &&& b = target := by simpa [land_eq] using Nat.eq_of_beq_eq_true hb
      have hsub' : target &&& (acc &&& b) = target := by rw [← Nat.and_assoc, hsub, hb']
      dsimp only
      cases heq : Nat.beq (Nat.land acc b) target
      · exact ih (Nat.land acc b) hsub'
      · have hacc' : acc &&& b = target := by simpa [land_eq] using Nat.eq_of_beq_eq_true heq
        have h1 : isMeetLoop target rest (acc &&& b) &&& target = isMeetLoop target rest (acc &&& b) := by
          simpa [hacc'] using isMeetLoop_and_sub (target := target) rest (acc &&& b)
        have h2 : target &&& isMeetLoop target rest (acc &&& b) = target :=
          isMeetLoop_target_sub rest hsub'
        have h3 : isMeetLoop target rest (acc &&& b) = target := by
          rw [← h1, Nat.and_comm, h2]
        simp [h3]

theorem chkIsMeet_eq_isMeet {M t : ℕ} (B : List ℕ) (ht : t &&& M = t) :
    chkIsMeet M B t = isMeet M B t := by
  unfold chkIsMeet isMeet
  cases Nat.beq t 0
  · exact chkIsMeetLoop_eq t M B ht
  · rfl

theorem chkIsOnEdgesLoop_sound (eg g acc : ℕ) (bs : List ℕ)
    (hok : chkIsOnEdgesLoop eg g acc bs = true) :
    isMeetLoop eg bs acc &&& g = isMeetLoop eg bs acc := by
  induction bs generalizing acc with
  | nil =>
    simpa [chkIsOnEdgesLoop, isMeetLoop, land_eq] using Nat.eq_of_beq_eq_true hok
  | cons b rest ih =>
    simp only [chkIsOnEdgesLoop, isMeetLoop] at hok ⊢
    cases hb : Nat.beq (Nat.land eg b) eg
    · rw [hb] at hok; exact ih acc hok
    · rw [hb] at hok
      dsimp only at hok
      cases h1 : Nat.beq (Nat.land (Nat.land acc b) g) (Nat.land acc b)
      · rw [h1] at hok; exact ih (Nat.land acc b) hok
      · have hag : (acc &&& b) &&& g = acc &&& b := by
          simpa [land_eq] using Nat.eq_of_beq_eq_true h1
        have hsub := isMeetLoop_and_sub (target := eg) rest (acc &&& b)
        apply Nat.eq_of_testBit_eq; intro s
        have ha1 := congrArg (fun z => z.testBit s) hsub
        have ha2 := congrArg (fun z => z.testBit s) hag
        simp only [land_eq, Nat.testBit_and] at ha1 ha2 ⊢
        revert ha1 ha2
        cases (isMeetLoop eg rest (acc &&& b)).testBit s <;>
          cases acc.testBit s <;> cases b.testBit s <;> cases g.testBit s <;> decide

theorem chkProbeOkGate_eq (mc pm h : ℕ) : chkProbeOkGate mc pm h = probeOkGate mc pm h := rfl

theorem chkAllProbeOk_iff (mc pm : ℕ) (act : List ℕ) :
    chkAllProbeOk mc pm act = true ↔ act.all (probeOkGate mc pm) = true := by
  induction act with
  | nil => simp [chkAllProbeOk]
  | cons h rest ih =>
    simp only [chkAllProbeOk, List.all_cons, chkProbeOkGate_eq]
    cases probeOkGate mc pm h <;> simp [ih]

theorem chkFilterPv_mem (mc : ℕ) (act pv : List ℕ) (pm : ℕ) :
    pm ∈ chkFilterPv mc act pv ↔ pm ∈ pv ∧ act.all (probeOkGate mc pm) = true := by
  induction pv with
  | nil => simp [chkFilterPv]
  | cons p rest ih =>
    simp only [chkFilterPv, List.mem_cons]
    cases hp : chkAllProbeOk mc p act
    · have hp' : ¬ act.all (probeOkGate mc p) = true := by
        rw [← chkAllProbeOk_iff]; simp [hp]
      simp only [ih]
      constructor
      · rintro ⟨hmem, hall⟩; exact ⟨Or.inr hmem, hall⟩
      · rintro ⟨rfl | hmem, hall⟩
        · exact (hp' hall).elim
        · exact ⟨hmem, hall⟩
    · have hp' : act.all (probeOkGate mc p) = true := (chkAllProbeOk_iff mc p act).mp hp
      simp only [List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨hmem, hall⟩)
        · exact ⟨Or.inl rfl, hp'⟩
        · exact ⟨Or.inr hmem, hall⟩
      · rintro ⟨rfl | hmem, hall⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hmem, hall⟩

theorem chkAnyProbeOk_iff (mc g : ℕ) (vp : List ℕ) :
    chkAnyProbeOk mc g vp = true ↔ ∃ pm ∈ vp, probeOkGate mc pm g = true := by
  induction vp with
  | nil => simp [chkAnyProbeOk]
  | cons pm rest ih =>
    simp only [chkAnyProbeOk, chkProbeOkGate_eq, List.mem_cons]
    cases hp : probeOkGate mc pm g
    · simp only [ih]
      constructor
      · rintro ⟨p, hmem, hok⟩; exact ⟨p, Or.inr hmem, hok⟩
      · rintro ⟨p, rfl | hmem, hok⟩
        · simp [hp] at hok
        · exact ⟨p, hmem, hok⟩
    · simp only [true_iff]; exact ⟨pm, Or.inl rfl, hp⟩

theorem chkAnyProbeOk_filterPv_iff (mc g : ℕ) (act pv : List ℕ) :
    chkAnyProbeOk mc g (chkFilterPv mc act pv) = true ↔
      pv.any (fun pm => (act ++ [g]).all (probeOkGate mc pm)) = true := by
  rw [chkAnyProbeOk_iff, List.any_eq_true]
  constructor
  · rintro ⟨pm, hmem, hg⟩
    obtain ⟨hpv, hact⟩ := (chkFilterPv_mem mc act pv pm).mp hmem
    exact ⟨pm, hpv, by simp [hact, hg]⟩
  · rintro ⟨pm, hpv, hall⟩
    simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hall
    exact ⟨pm, (chkFilterPv_mem mc act pv pm).mpr ⟨hpv, hall.1⟩, hall.2⟩

theorem chkStepFilterAct_eq (mc : ℕ) (act sb : List ℕ) (sv : ℕ) (actRev : List ℕ) :
    chkStepFilterAct mc act sb sv actRev =
      let r := evalCutStep.go mc act sb actRev sv
      (r.1, r.2.2, r.2.1) := by
  induction act generalizing sb sv actRev with
  | nil => rfl
  | cons h rest ih =>
    simp only [chkStepFilterAct, evalCutStep.go]
    have hrh : (Nat.land h mc) &&& mc = Nat.land h mc := by
      apply Nat.eq_of_testBit_eq; intro s; simp [Nat.testBit_and]
    rw [chkIsMeet_eq_isMeet sb hrh]
    cases isMeet mc sb (Nat.land h mc)
    · exact ih (Nat.land h mc :: sb) sv (Nat.land h mc :: actRev)
    · exact ih sb (sv + 1) actRev

theorem evalCutStep_go_sv_add (mc : ℕ) (act sb actRev : List ℕ) (sv k : ℕ) :
    evalCutStep.go mc act sb actRev (sv + k) =
      let r := evalCutStep.go mc act sb actRev sv
      (r.1, r.2.1, r.2.2 + k) := by
  induction act generalizing sb actRev sv with
  | nil => rfl
  | cons h rest ih =>
    simp only [evalCutStep.go]
    cases isMeet mc sb (Nat.land h mc)
    · exact ih (Nat.land h mc :: sb) (Nat.land h mc :: actRev) sv
    · rw [show sv + k + 1 = (sv + 1) + k by omega]
      exact ih sb actRev (sv + 1)

theorem evalCutStep_go_append_singleton (mc : ℕ) (act sb actRev : List ℕ) (sv g : ℕ) :
    evalCutStep.go mc (act ++ [g]) sb actRev sv =
      let r := evalCutStep.go mc act sb actRev sv
      let rg := Nat.land g mc
      match isMeet mc r.1 rg with
      | true => (r.1, r.2.1, r.2.2 + 1)
      | false => (rg :: r.1, r.2.1 ++ [rg], r.2.2) := by
  induction act generalizing sb actRev sv with
  | nil =>
    simp only [List.nil_append, evalCutStep.go]
    cases isMeet mc sb (Nat.land g mc) <;> simp
  | cons h rest ih =>
    simp only [List.cons_append, evalCutStep.go]
    cases isMeet mc sb (Nat.land h mc)
    · exact ih (Nat.land h mc :: sb) (Nat.land h mc :: actRev) sv
    · exact ih sb actRev (sv + 1)

theorem chkPrepSteps_sv_add (steps : List CutStepData) (act : List ℕ) (sv k : ℕ) :
    chkPrepSteps steps act (sv + k) =
      let r := chkPrepSteps steps act sv
      (r.1 + k, r.2.1, r.2.2) := by
  induction steps generalizing act sv with
  | nil => rfl
  | cons st rest ih =>
    simp only [chkPrepSteps, chkStepFilterAct_eq]
    have h1 := evalCutStep_go_sv_add st.mc act st.rc [] sv k
    simp only [h1]
    rw [ih (evalCutStep.go st.mc act st.rc [] sv).2.1 (evalCutStep.go st.mc act st.rc [] sv).2.2]

theorem chkPrepSteps_eval_eq (steps : List CutStepData) (act : List ℕ) :
    evalCutChain steps act = (chkPrepSteps steps act 0).1 + (chkPrepSteps steps act 0).2.1 := by
  induction steps generalizing act with
  | nil => simp [evalCutChain, chkPrepSteps]
  | cons st rest ih =>
    simp only [evalCutChain, chkPrepSteps, chkStepFilterAct_eq]
    set r := evalCutStep.go st.mc act st.rc [] 0
    have hshift : (chkPrepSteps rest r.2.1 r.2.2).1 = (chkPrepSteps rest r.2.1 0).1 + r.2.2 ∧
        (chkPrepSteps rest r.2.1 r.2.2).2.1 = (chkPrepSteps rest r.2.1 0).2.1 := by
      have h := chkPrepSteps_sv_add rest r.2.1 0 r.2.2
      simp only [zero_add] at h
      rw [h]; exact ⟨rfl, rfl⟩
    have hmyB : (if st.pv.any (fun pm => act.all (probeOkGate st.mc pm)) then 1 else 0) =
        match chkFilterPv st.mc act st.pv with | [] => 0 | _ :: _ => 1 := by
      cases hfp : chkFilterPv st.mc act st.pv
      · simp only [ite_eq_right_iff, Nat.one_ne_zero]
        intro hany
        rw [List.any_eq_true] at hany
        obtain ⟨pm, hpm, hall⟩ := hany
        have hmem : pm ∈ chkFilterPv st.mc act st.pv := (chkFilterPv_mem st.mc act st.pv pm).mpr ⟨hpm, hall⟩
        rw [hfp] at hmem; simp at hmem
      · rename_i pm _
        have hmem : pm ∈ chkFilterPv st.mc act st.pv := by rw [hfp]; simp
        obtain ⟨hpv, hall⟩ := (chkFilterPv_mem st.mc act st.pv pm).mp hmem
        have hany : st.pv.any (fun pm => act.all (probeOkGate st.mc pm)) = true :=
          List.any_eq_true.mpr ⟨pm, hpv, hall⟩
        simp [hany]
    have ih' := ih r.2.1
    change r.2.2 + (if st.pv.any (fun pm => act.all (probeOkGate st.mc pm)) then 1 else 0) +
      evalCutChain rest r.2.1 = _
    rw [hmyB, ih', hshift.1, hshift.2]
    omega

theorem evalCutChain_append_ge_totSv (steps : List CutStepData) (act : List ℕ) (g : ℕ) :
    (chkPrepSteps steps act 0).1 ≤ evalCutChain steps (act ++ [g]) := by
  induction steps generalizing act g with
  | nil => simp [chkPrepSteps, evalCutChain]
  | cons st rest ih =>
    simp only [evalCutChain, chkPrepSteps, chkStepFilterAct_eq]
    have hshift : (chkPrepSteps rest (evalCutStep.go st.mc act st.rc [] 0).2.1
        (evalCutStep.go st.mc act st.rc [] 0).2.2).1 =
        (chkPrepSteps rest (evalCutStep.go st.mc act st.rc [] 0).2.1 0).1 +
        (evalCutStep.go st.mc act st.rc [] 0).2.2 := by
      have h := chkPrepSteps_sv_add rest (evalCutStep.go st.mc act st.rc [] 0).2.1 0
        (evalCutStep.go st.mc act st.rc [] 0).2.2
      simp only [zero_add] at h
      rw [h]
    have hstep := evalCutStep_go_append_singleton st.mc act st.rc [] 0 g
    change _ ≤ (evalCutStep.go st.mc (act ++ [g]) st.rc [] 0).2.2 +
      (if st.pv.any (fun pm => (act ++ [g]).all (probeOkGate st.mc pm)) then 1 else 0) +
      evalCutChain rest (evalCutStep.go st.mc (act ++ [g]) st.rc [] 0).2.1
    rw [hstep, hshift]
    dsimp only
    cases hm : isMeet st.mc (evalCutStep.go st.mc act st.rc [] 0).1 (Nat.land g st.mc)
    · dsimp only
      have hrec := ih (evalCutStep.go st.mc act st.rc [] 0).2.1 (Nat.land g st.mc)
      omega
    · dsimp only
      have heq := chkPrepSteps_eval_eq rest (evalCutStep.go st.mc act st.rc [] 0).2.1
      omega

theorem chkCutKillsAtStep_le_one_add_allB (steps : List CutStepData) (act : List ℕ)
    (g need stepIdx : ℕ)
    (hok : chkCutKillsAtStep g need stepIdx (chkPrepSteps steps act 0).2.2 = true) :
    need ≤ 1 + (chkPrepSteps steps act 0).2.1 := by
  induction steps generalizing act g need stepIdx with
  | nil =>
    simp only [chkPrepSteps, chkCutKillsAtStep] at hok ⊢
    have h0 : need = 0 := Nat.eq_of_beq_eq_true hok
    omega
  | cons st rest ih =>
    simp only [chkPrepSteps, chkStepFilterAct_eq] at hok ⊢
    set r := evalCutStep.go st.mc act st.rc [] 0
    have hshift : (chkPrepSteps rest r.2.1 r.2.2).2.1 = (chkPrepSteps rest r.2.1 0).2.1 ∧
        (chkPrepSteps rest r.2.1 r.2.2).2.2 = (chkPrepSteps rest r.2.1 0).2.2 := by
      have h := chkPrepSteps_sv_add rest r.2.1 0 r.2.2
      simp only [zero_add] at h
      rw [h]; exact ⟨rfl, rfl⟩
    rw [hshift.1] at hok ⊢
    rw [hshift.2] at hok
    cases stepIdx with
    | zero =>
      simp only [chkCutKillsAtStep] at hok
      cases hm : chkIsMeet st.mc r.1 (Nat.land g st.mc)
      · rw [hm] at hok; simp at hok
      · rw [hm] at hok
        cases h1 : Nat.ble need (1 + (chkPrepSteps rest r.2.1 0).2.1)
        · rw [h1] at hok
          cases h2 : Nat.ble need (2 + (chkPrepSteps rest r.2.1 0).2.1)
          · rw [h2] at hok; simp at hok
          · rw [h2] at hok
            have hle : need ≤ 2 + (chkPrepSteps rest r.2.1 0).2.1 := Nat.le_of_ble_eq_true h2
            cases hvp : chkFilterPv st.mc act st.pv
            · rw [hvp] at hok; simp [chkAnyProbeOk] at hok
            · dsimp only; omega
        · have hle : need ≤ 1 + (chkPrepSteps rest r.2.1 0).2.1 := Nat.le_of_ble_eq_true h1
          cases chkFilterPv st.mc act st.pv <;> dsimp only <;> omega
    | succ s' =>
      simp only [chkCutKillsAtStep] at hok
      cases hvp : chkFilterPv st.mc act st.pv
      · rw [hvp] at hok; dsimp only at hok ⊢
        cases h0 : Nat.beq need 0
        · rw [h0] at hok
          have := ih r.2.1 (Nat.land g st.mc) need s' hok
          omega
        · have := Nat.eq_of_beq_eq_true h0; omega
      · rw [hvp] at hok; dsimp only at hok ⊢
        cases hp : chkAnyProbeOk st.mc g (chkFilterPv st.mc act st.pv)
        · rw [hvp] at hp; rw [hp] at hok; dsimp only at hok
          cases h0 : Nat.beq need 0
          · rw [h0] at hok
            have := ih r.2.1 (Nat.land g st.mc) need s' hok
            omega
          · have := Nat.eq_of_beq_eq_true h0; omega
        · rw [hvp] at hp; rw [hp] at hok; dsimp only at hok
          cases h0 : Nat.beq (Nat.sub need 1) 0
          · rw [h0] at hok
            have := ih r.2.1 (Nat.land g st.mc) (Nat.sub need 1) s' hok
            rw [nat_sub_eq] at this; omega
          · have := Nat.eq_of_beq_eq_true h0; rw [nat_sub_eq] at this; omega

theorem chkCutKillsAtStep_sound (steps : List CutStepData) (act : List ℕ)
    (g need stepIdx : ℕ)
    (hok : chkCutKillsAtStep g need stepIdx (chkPrepSteps steps act 0).2.2 = true) :
    (chkPrepSteps steps act 0).1 + need ≤ evalCutChain steps (act ++ [g]) := by
  induction steps generalizing act g need stepIdx with
  | nil =>
    simp only [chkPrepSteps, chkCutKillsAtStep, evalCutChain] at hok ⊢
    have := Nat.eq_of_beq_eq_true hok; omega
  | cons st rest ih =>
    simp only [evalCutChain, chkPrepSteps, chkStepFilterAct_eq] at hok ⊢
    have hshift : (chkPrepSteps rest (evalCutStep.go st.mc act st.rc [] 0).2.1
          (evalCutStep.go st.mc act st.rc [] 0).2.2).1 =
        (chkPrepSteps rest (evalCutStep.go st.mc act st.rc [] 0).2.1 0).1 +
          (evalCutStep.go st.mc act st.rc [] 0).2.2 ∧
      (chkPrepSteps rest (evalCutStep.go st.mc act st.rc [] 0).2.1
          (evalCutStep.go st.mc act st.rc [] 0).2.2).2.1 =
        (chkPrepSteps rest (evalCutStep.go st.mc act st.rc [] 0).2.1 0).2.1 ∧
      (chkPrepSteps rest (evalCutStep.go st.mc act st.rc [] 0).2.1
          (evalCutStep.go st.mc act st.rc [] 0).2.2).2.2 =
        (chkPrepSteps rest (evalCutStep.go st.mc act st.rc [] 0).2.1 0).2.2 := by
      have h := chkPrepSteps_sv_add rest (evalCutStep.go st.mc act st.rc [] 0).2.1 0
        (evalCutStep.go st.mc act st.rc [] 0).2.2
      simp only [zero_add] at h
      rw [h]; exact ⟨rfl, rfl, rfl⟩
    rw [hshift.1]
    rw [hshift.2.1, hshift.2.2] at hok
    have hstep := evalCutStep_go_append_singleton st.mc act st.rc [] 0 g
    change _ ≤ (evalCutStep.go st.mc (act ++ [g]) st.rc [] 0).2.2 +
      (if st.pv.any (fun pm => (act ++ [g]).all (probeOkGate st.mc pm)) then 1 else 0) +
      evalCutChain rest (evalCutStep.go st.mc (act ++ [g]) st.rc [] 0).2.1
    rw [hstep]
    set r := evalCutStep.go st.mc act st.rc [] 0
    have hrgM : Nat.land g st.mc &&& st.mc = Nat.land g st.mc := by
      apply Nat.eq_of_testBit_eq; intro s; simp [Nat.testBit_and]
    have hmeet_eq : chkIsMeet st.mc r.1 (Nat.land g st.mc) = isMeet st.mc r.1 (Nat.land g st.mc) :=
      chkIsMeet_eq_isMeet r.1 hrgM
    have hprobe_eq : (st.pv.any (fun pm => (act ++ [g]).all (probeOkGate st.mc pm))) =
        chkAnyProbeOk st.mc g (chkFilterPv st.mc act st.pv) := by
      apply Bool.eq_iff_iff.mpr
      exact (chkAnyProbeOk_filterPv_iff st.mc g act st.pv).symm
    rw [hprobe_eq]
    dsimp only
    cases hm : isMeet st.mc r.1 (Nat.land g st.mc)
    · -- `g` survives step `st`
      dsimp only
      cases stepIdx with
      | zero =>
        simp only [chkCutKillsAtStep, hmeet_eq, hm] at hok
        simp at hok
      | succ s' =>
        simp only [chkCutKillsAtStep] at hok
        have hge := evalCutChain_append_ge_totSv rest r.2.1 (Nat.land g st.mc)
        cases hvp : chkFilterPv st.mc act st.pv
        · rw [hvp] at hok; simp only at hok
          cases h0 : Nat.beq need 0
          · rw [h0] at hok; simp only at hok
            have hrec := ih r.2.1 (Nat.land g st.mc) need s' hok
            omega
          · have := Nat.eq_of_beq_eq_true h0; omega
        · rw [hvp] at hok; simp only at hok
          cases hp : chkAnyProbeOk st.mc g (_ :: _)
          · rw [hp] at hok; simp only at hok
            cases h0 : Nat.beq need 0
            · rw [h0] at hok; simp only at hok
              have hrec := ih r.2.1 (Nat.land g st.mc) need s' hok
              omega
            · have := Nat.eq_of_beq_eq_true h0; omega
          · rw [hp] at hok; simp only at hok
            simp only [↓reduceIte]
            cases h0 : Nat.beq (Nat.sub need 1) 0
            · rw [h0] at hok; simp only at hok
              have hrec := ih r.2.1 (Nat.land g st.mc) (Nat.sub need 1) s' hok
              rw [nat_sub_eq] at hrec; omega
            · have := Nat.eq_of_beq_eq_true h0; rw [nat_sub_eq] at this; omega
    · -- `g` is dropped as `isMeet` at step `st`
      dsimp only
      have hrest_eq := chkPrepSteps_eval_eq rest r.2.1
      rw [hrest_eq]
      cases stepIdx with
      | zero =>
        simp only [chkCutKillsAtStep, hmeet_eq, hm] at hok
        cases h1 : Nat.ble need (1 + (chkPrepSteps rest r.2.1 0).2.1)
        · rw [h1] at hok
          cases h2 : Nat.ble need (2 + (chkPrepSteps rest r.2.1 0).2.1)
          · rw [h2] at hok; simp at hok
          · rw [h2] at hok; simp only at hok
            have hle := Nat.le_of_ble_eq_true h2
            rw [hok]; simp only [↓reduceIte]; omega
        · have hle := Nat.le_of_ble_eq_true h1
          split_ifs <;> omega
      | succ s' =>
        simp only [chkCutKillsAtStep] at hok
        cases hvp : chkFilterPv st.mc act st.pv
        · rw [hvp] at hok; simp only at hok
          cases h0 : Nat.beq need 0
          · rw [h0] at hok; simp only at hok
            have hle := chkCutKillsAtStep_le_one_add_allB rest r.2.1 (Nat.land g st.mc) need s' hok
            simp [chkAnyProbeOk]; omega
          · have := Nat.eq_of_beq_eq_true h0; omega
        · rw [hvp] at hok; simp only at hok
          cases hp : chkAnyProbeOk st.mc g (_ :: _)
          · rw [hp] at hok; simp only at hok
            cases h0 : Nat.beq need 0
            · rw [h0] at hok; simp only at hok
              have hle := chkCutKillsAtStep_le_one_add_allB rest r.2.1 (Nat.land g st.mc) need s' hok
              omega
            · have := Nat.eq_of_beq_eq_true h0; omega
          · rw [hp] at hok; simp only at hok
            simp only [↓reduceIte]
            cases h0 : Nat.beq (Nat.sub need 1) 0
            · rw [h0] at hok; simp only at hok
              have hle := chkCutKillsAtStep_le_one_add_allB rest r.2.1 (Nat.land g st.mc) (Nat.sub need 1) s' hok
              rw [nat_sub_eq] at hle; omega
            · have := Nat.eq_of_beq_eq_true h0; rw [nat_sub_eq] at this; omega

theorem chkCutKillsWit_sound (cut : CutDefData) (gs : List ℕ) (stepIdx g : ℕ)
    (hok : chkCutKillsWit (chkPrepCutState cut gs) stepIdx g = true) :
    cut.loss ≤ evalCutChain cut.steps (gs ++ [g]) := by
  unfold chkCutKillsWit chkPrepCutState at hok
  dsimp only at hok
  cases h0 : Nat.beq (Nat.sub cut.loss (chkPrepSteps cut.steps gs 0).1) 0
  · rw [h0] at hok
    have h1 := chkCutKillsAtStep_sound cut.steps gs g _ stepIdx hok
    rw [nat_sub_eq] at h1; omega
  · have hle : cut.loss ≤ (chkPrepSteps cut.steps gs 0).1 := by
      have := Nat.eq_of_beq_eq_true h0; rw [nat_sub_eq] at this; omega
    exact hle.trans (evalCutChain_append_ge_totSv cut.steps gs g)

theorem chkApplyPermLoop_eq (tbl : List ℕ) (f s acc : ℕ) :
    chkApplyPermLoop (f / 2 ^ s) acc (tbl.map (fun x => Nat.pow 2 x)) =
      applyPermLoop tbl f s acc := by
  induction tbl generalizing s acc with
  | nil => rfl
  | cons s2 rest ih =>
    simp only [List.map_cons, chkApplyPermLoop, applyPermLoop]
    cases h0 : Nat.beq (f / 2 ^ s) 0
    · have hbit : Nat.beq (Nat.land (f / 2 ^ s) 1) 1 = f.testBit s := by
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow, land_eq, Nat.and_comm 1 _, Nat.and_one_is_mod]
        have hlt : (f / 2 ^ s) % 2 < 2 := Nat.mod_lt _ (by omega)
        generalize (f / 2 ^ s) % 2 = m at hlt ⊢
        interval_cases m <;> rfl
      have hpow : Nat.pow 2 s2 = 1 <<< s2 := by rw [Nat.shiftLeft_eq, one_mul]; rfl
      have hdiv : Nat.div (f / 2 ^ s) 2 = f / 2 ^ (s + 1) := by
        rw [nat_div_eq, Nat.div_div_eq_div_mul, Nat.pow_succ]
      rw [hbit, hpow, hdiv]
      cases f.testBit s
      · exact ih (s + 1) acc
      · exact ih (s + 1) (Nat.lor acc (1 <<< s2))
    · have hf0 : f / 2 ^ s = 0 := Nat.eq_of_beq_eq_true h0
      have hzero : ∀ (l : List ℕ) (t a : ℕ), f / 2 ^ t = 0 → applyPermLoop l f t a = a := by
        intro l
        induction l with
        | nil => intro _ _ _; rfl
        | cons x xs ihx =>
          intro t a ht
          simp only [applyPermLoop]
          have htb : f.testBit t = false := by
            rw [Nat.testBit, Nat.shiftRight_eq_div_pow, ht]; rfl
          have ht' : f / 2 ^ (t + 1) = 0 := by
            rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ht]
          rw [htb]; exact ihx (t + 1) a ht'
      exact (hzero (s2 :: rest) s acc hf0).symm

theorem chkApplyPerm_eq_applyPerm (tbl : List ℕ) (f : ℕ) :
    chkApplyPerm (tbl.map (fun s => Nat.pow 2 s)) f = applyPerm tbl f := by
  simpa [chkApplyPerm, applyPerm] using chkApplyPermLoop_eq tbl f 0 0

theorem chkAnyPermLt_sound (idxTbls : List (List ℕ)) (oi oj : ℕ)
    (hok : chkAnyPermLt (oi ||| oj)
      (chkApplyPermList oi (chkMkAutMaskTbls idxTbls))
      (chkApplyPermList oj (chkMkAutMaskTbls idxTbls)) = true) :
    ∃ tbl ∈ idxTbls, applyPerm tbl (oi ||| oj) < oi ||| oj := by
  induction idxTbls with
  | nil => simp [chkMkAutMaskTbls, chkApplyPermList, chkAnyPermLt] at hok
  | cons tbl rest ih =>
    simp only [chkMkAutMaskTbls, List.map_cons, chkApplyPermList, chkAnyPermLt,
      chkApplyPerm_eq_applyPerm, lor_eq, ← applyPerm_or] at hok
    cases hlt : Nat.blt (applyPerm tbl (oi ||| oj)) (oi ||| oj)
    · rw [hlt] at hok
      obtain ⟨t, ht, h⟩ := ih hok
      exact ⟨t, List.mem_cons_of_mem _ ht, h⟩
    · exact ⟨tbl, List.mem_cons_self, nat_blt_eq_true hlt⟩

theorem chkFilterStab_map (g : ℕ) (idxTbls : List (List ℕ)) :
    chkFilterStab g (chkMkAutMaskTbls idxTbls) =
      chkMkAutMaskTbls (idxTbls.filter (fun tbl => Nat.beq (applyPerm tbl g) g)) := by
  induction idxTbls with
  | nil => rfl
  | cons tbl rest ih =>
    simp only [chkMkAutMaskTbls, List.map_cons, chkFilterStab, chkApplyPerm_eq_applyPerm,
      List.filter_cons]
    cases Nat.beq (applyPerm tbl g) g
    · exact ih
    · dsimp only [chkMkAutMaskTbls] at ih
      rw [ih]; rfl

/-! ### `chkGenBirthOps` & `chkBuildSuffixMax` Soundness -/

theorem masksTTYF_meetNat {n : ℕ} {H F : List (ℕ × ℕ)} (hv : ValidState n H F) :
    ∀ mt ∈ masksTTYF n H (univYF n F),
      MeetNat (univYF n F) (rawYF n (univYF n F)) mt := by
  set M := univYF n F
  have hM : ∀ s, M.testBit s = true → s < 2 ^ n := fun _ => univYF_testBit_lt
  intro mt hmt
  unfold masksTTYF at hmt
  simp only [List.cons_append, List.mem_map, List.mem_cons, List.mem_append, List.mem_range] at hmt
  obtain ⟨m, hm, rfl⟩ := hmt
  refine meetNat_iff.mpr ⟨ttNeedYF_and_mask hM, ?_⟩
  rcases hm with rfl | ⟨v, hvlt, rfl⟩ | ⟨e, heH, rfl⟩
  · rw [ttNeedYF_zero hM, decM_self]; exact Meet.top
  · rw [ttNeedYF_oneBit hM]
    exact Meet.atom ⟨ttVarYF n v M, List.mem_map.mpr ⟨v, List.mem_range.mpr hvlt, rfl⟩, rfl⟩
  · obtain ⟨h1, h2, _⟩ := hv.1 e heH
    rw [← ttNeedYF_or hM, ttNeedYF_oneBit hM, ttNeedYF_oneBit hM, decM_and]
    exact (Meet.atom (B := decM M '' { x | x ∈ rawYF n M })
        ⟨ttVarYF n e.1 M, List.mem_map.mpr ⟨e.1, List.mem_range.mpr h1, rfl⟩, rfl⟩).inter
      (Meet.atom (B := decM M '' { x | x ∈ rawYF n M })
        ⟨ttVarYF n e.2 M, List.mem_map.mpr ⟨e.2, List.mem_range.mpr h2, rfl⟩, rfl⟩)

theorem chkSubsetsStep_mem (g : ℕ) (subs acc : List ℕ) (y : ℕ) :
    y ∈ chkSubsetsStep g subs acc ↔ y ∈ acc ∨ ∃ x ∈ subs, y = x &&& g := by
  induction subs generalizing acc with
  | nil => simp [chkSubsetsStep]
  | cons x rest ih =>
    simp only [chkSubsetsStep, ih, List.mem_cons, land_eq]
    constructor
    · rintro ((rfl | hy) | ⟨z, hz, rfl⟩)
      · exact Or.inr ⟨x, Or.inl rfl, rfl⟩
      · exact Or.inl hy
      · exact Or.inr ⟨z, Or.inr hz, rfl⟩
    · rintro (hy | ⟨z, rfl | hz, rfl⟩)
      · exact Or.inl (Or.inr hy)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr ⟨z, hz, rfl⟩

theorem chkAddBirthOps_inv {M ep gi birth : ℕ} {raw done : List ℕ}
    (hdone_len : birth = done.length)
    (hgi : MeetNat M (raw ++ done) gi)
    (masksTT : List ℕ) (hmasks : ∀ mt ∈ masksTT, MeetNat M raw mt)
    (seen : List ℕ) (acc : List (ℕ × ℕ × ℕ))
    (hacc_inv : ∀ x ∈ acc, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ birth ∧ MeetNat M (raw ++ done.take x.2.2) x.1)
    (hacc_pw : acc.Pairwise (fun x y => y.2.2 ≤ x.2.2))
    (hseen_acc : ∀ op ∈ seen, ∃ b, (op, op &&& ep, b) ∈ acc) :
    let res := chkAddBirthOps M ep gi birth masksTT seen acc
    (∀ x ∈ res.2, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ birth ∧ MeetNat M (raw ++ done.take x.2.2) x.1) ∧
    res.2.Pairwise (fun x y => y.2.2 ≤ x.2.2) ∧
    (∀ op ∈ seen, op ∈ res.1) ∧
    (∀ op ∈ res.1, ∃ b, (op, op &&& ep, b) ∈ res.2) ∧
    (∀ mt ∈ masksTT, (mt &&& gi) ≠ 0 → (mt &&& gi) ≠ M → (mt &&& gi) &&& ep ≠ 0 → (mt &&& gi) ∈ res.1) := by
  induction masksTT generalizing seen acc with
  | nil =>
    simp only [chkAddBirthOps, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨hacc_inv, hacc_pw, fun _ h => h, hseen_acc⟩
  | cons mt rest ih =>
    simp only [chkAddBirthOps, land_eq]
    have hmt : MeetNat M raw mt := hmasks mt List.mem_cons_self
    have hrest_m : ∀ m ∈ rest, MeetNat M raw m := fun m hm => hmasks m (List.mem_cons_of_mem _ hm)
    set op := mt &&& gi
    cases h0 : Nat.beq op 0
    · cases hM : Nat.beq op M
      · cases hep : Nat.beq (op &&& ep) 0
        · cases hmem : chkMemNat op seen
          · have hop_meet : MeetNat M (raw ++ done.take birth) op := by
              rw [hdone_len, List.take_length]
              have h1 : MeetNat M (raw ++ done) mt :=
                meetNat_weaken (fun x hx => List.mem_append_left _ hx) hmt
              have hsub : op &&& M = op := by
                apply Nat.eq_of_testBit_eq; intro s
                have ha := congrArg (fun z => z.testBit s) hmt.1
                simp only [op, Nat.testBit_and] at ha ⊢
                revert ha; cases mt.testBit s <;> cases gi.testBit s <;> cases M.testBit s <;> decide
              exact meetNat_iff.mpr ⟨hsub, by rw [decM_and]; exact (meetNat_iff.mp h1).2.inter (meetNat_iff.mp hgi).2⟩
            have hacc_inv' : ∀ x ∈ (op, op &&& ep, birth) :: acc,
                x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ birth ∧ MeetNat M (raw ++ done.take x.2.2) x.1 := by
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact ⟨rfl, le_rfl, hop_meet⟩
              · exact hacc_inv x hx
            have hacc_pw' : ((op, op &&& ep, birth) :: acc).Pairwise (fun x y => y.2.2 ≤ x.2.2) :=
              List.pairwise_cons.mpr ⟨fun y hy => (hacc_inv y hy).2.1, hacc_pw⟩
            have hseen_acc' : ∀ o ∈ op :: seen, ∃ b, (o, o &&& ep, b) ∈ (op, op &&& ep, birth) :: acc := by
              intro o ho
              rcases List.mem_cons.mp ho with rfl | ho
              · exact ⟨birth, List.mem_cons_self⟩
              · obtain ⟨b, hb⟩ := hseen_acc o ho
                exact ⟨b, List.mem_cons_of_mem _ hb⟩
            obtain ⟨i1, i2, i3, i4, i5⟩ := ih hrest_m (op :: seen) ((op, op &&& ep, birth) :: acc)
              hacc_inv' hacc_pw' hseen_acc'
            refine ⟨i1, i2, fun o ho => i3 o (List.mem_cons_of_mem _ ho), i4, fun m hm => ?_⟩
            rcases List.mem_cons.mp hm with rfl | hm
            · intro _ _ _; exact i3 op List.mem_cons_self
            · exact i5 m hm
          · obtain ⟨i1, i2, i3, i4, i5⟩ := ih hrest_m seen acc hacc_inv hacc_pw hseen_acc
            refine ⟨i1, i2, i3, i4, fun m hm => ?_⟩
            rcases List.mem_cons.mp hm with rfl | hm
            · intro _ _ _; exact i3 op ((chkMemNat_iff op seen).mp hmem)
            · exact i5 m hm
        · obtain ⟨i1, i2, i3, i4, i5⟩ := ih hrest_m seen acc hacc_inv hacc_pw hseen_acc
          refine ⟨i1, i2, i3, i4, fun m hm => ?_⟩
          rcases List.mem_cons.mp hm with rfl | hm
          · intro _ _ hne; exact (hne (Nat.eq_of_beq_eq_true hep)).elim
          · exact i5 m hm
      · obtain ⟨i1, i2, i3, i4, i5⟩ := ih hrest_m seen acc hacc_inv hacc_pw hseen_acc
        refine ⟨i1, i2, i3, i4, fun m hm => ?_⟩
        rcases List.mem_cons.mp hm with rfl | hm
        · intro _ hne _; exact (hne (Nat.eq_of_beq_eq_true hM)).elim
        · exact i5 m hm
    · obtain ⟨i1, i2, i3, i4, i5⟩ := ih hrest_m seen acc hacc_inv hacc_pw hseen_acc
      refine ⟨i1, i2, i3, i4, fun m hm => ?_⟩
      rcases List.mem_cons.mp hm with rfl | hm
      · intro hne _ _; exact (hne (Nat.eq_of_beq_eq_true h0)).elim
      · exact i5 m hm

theorem chkAddSubsOps_inv {M ep birth : ℕ} {raw done masksTT : List ℕ}
    (hdone_len : birth = done.length)
    (hmasks : ∀ mt ∈ masksTT, MeetNat M raw mt)
    (newSubs seen : List ℕ) (acc : List (ℕ × ℕ × ℕ))
    (hsubs : ∀ gi ∈ newSubs, MeetNat M (raw ++ done) gi)
    (hacc_inv : ∀ x ∈ acc, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ birth ∧ MeetNat M (raw ++ done.take x.2.2) x.1)
    (hacc_pw : acc.Pairwise (fun x y => y.2.2 ≤ x.2.2))
    (hseen_acc : ∀ op ∈ seen, ∃ b, (op, op &&& ep, b) ∈ acc) :
    let res := chkAddSubsOps M ep birth masksTT newSubs seen acc
    (∀ x ∈ res.2, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ birth ∧ MeetNat M (raw ++ done.take x.2.2) x.1) ∧
    res.2.Pairwise (fun x y => y.2.2 ≤ x.2.2) ∧
    (∀ op ∈ seen, op ∈ res.1) ∧
    (∀ op ∈ res.1, ∃ b, (op, op &&& ep, b) ∈ res.2) ∧
    (∀ gi ∈ newSubs, ∀ mt ∈ masksTT, (mt &&& gi) ≠ 0 → (mt &&& gi) ≠ M → (mt &&& gi) &&& ep ≠ 0 → (mt &&& gi) ∈ res.1) := by
  induction newSubs generalizing seen acc with
  | nil =>
    simp only [chkAddSubsOps, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨hacc_inv, hacc_pw, fun _ h => h, hseen_acc⟩
  | cons gi rest ih =>
    simp only [chkAddSubsOps]
    have h1 := chkAddBirthOps_inv hdone_len (hsubs gi List.mem_cons_self) masksTT hmasks seen acc
      hacc_inv hacc_pw hseen_acc
    set r1 := chkAddBirthOps M ep gi birth masksTT seen acc
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih r1.1 r1.2
      (fun g hg => hsubs g (List.mem_cons_of_mem _ hg)) h1.1 h1.2.1 h1.2.2.2.1
    refine ⟨i1, i2, fun o ho => i3 o (h1.2.2.1 o ho), i4, fun g hg mt hmt h0 hM hep => ?_⟩
    rcases List.mem_cons.mp hg with rfl | hg
    · exact i3 (mt &&& g) (h1.2.2.2.2 mt hmt h0 hM hep)
    · exact i5 g hg mt hmt h0 hM hep

theorem sublist_append_singleton {α : Type} {P done : List α} {g : α}
    (h : List.Sublist P (done ++ [g])) :
    List.Sublist P done ∨ ∃ P', List.Sublist P' done ∧ P = P' ++ [g] := by
  induction done generalizing P with
  | nil =>
    simp only [List.nil_append] at h
    cases h with
    | cons _ h' => cases h'; exact Or.inl List.Sublist.slnil
    | cons_cons _ h' => cases h'; exact Or.inr ⟨[], List.Sublist.slnil, rfl⟩
  | cons x xs ih =>
    simp only [List.cons_append] at h
    cases h with
    | cons _ h' =>
      rcases ih h' with h1 | ⟨P', h1, rfl⟩
      · exact Or.inl (List.Sublist.cons x h1)
      · exact Or.inr ⟨P', List.Sublist.cons x h1, rfl⟩
    | cons_cons _ h' =>
      rcases ih h' with h1 | ⟨P', h1, rfl⟩
      · exact Or.inl (List.Sublist.cons_cons x h1)
      · exact Or.inr ⟨x :: P', List.Sublist.cons_cons x h1, rfl⟩

theorem chkGenBirthLoop_inv {M ep : ℕ} {raw masksTT : List ℕ}
    (hmasks : ∀ mt ∈ masksTT, MeetNat M raw mt) :
    ∀ (rest done subs seen : List ℕ) (acc : List (ℕ × ℕ × ℕ)),
      ValidPrefix M (raw ++ done) rest →
      (∀ gi ∈ subs, MeetNat M (raw ++ done) gi) →
      (∀ P : List ℕ, List.Sublist P done → P.foldl Nat.land M ∈ subs) →
      (∀ x ∈ acc, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ done.length ∧ MeetNat M (raw ++ done.take x.2.2) x.1) →
      acc.Pairwise (fun x y => y.2.2 ≤ x.2.2) →
      (∀ op ∈ seen, ∃ b, (op, op &&& ep, b) ∈ acc) →
      (∀ gi ∈ subs, ∀ mt ∈ masksTT, (mt &&& gi) ≠ 0 → (mt &&& gi) ≠ M → (mt &&& gi) &&& ep ≠ 0 → (mt &&& gi) ∈ seen) →
      let res := chkGenBirthLoop M ep masksTT (done.length + 1) subs seen acc rest
      (∀ x ∈ res, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ (done ++ rest).length ∧
        MeetNat M (raw ++ (done ++ rest).take x.2.2) x.1) ∧
      res.Pairwise (fun x y => y.2.2 ≤ x.2.2) ∧
      (∀ P : List ℕ, List.Sublist P (done ++ rest) → ∀ mt ∈ masksTT,
        (mt &&& P.foldl Nat.land M) ≠ 0 → (mt &&& P.foldl Nat.land M) ≠ M →
        (mt &&& P.foldl Nat.land M) &&& ep ≠ 0 →
        ∃ b, (mt &&& P.foldl Nat.land M, (mt &&& P.foldl Nat.land M) &&& ep, b) ∈ res) := by
  intro rest
  induction rest with
  | nil =>
    intro done subs seen acc _ _ hsub_P hacc_inv hacc_pw hseen_acc hseen_cov
    simp only [chkGenBirthLoop, List.append_nil]
    exact ⟨hacc_inv, hacc_pw, fun P hP mt hmt h0 hM hep =>
      hseen_acc _ (hseen_cov _ (hsub_P P hP) mt hmt h0 hM hep)⟩
  | cons g tail ih =>
    intro done subs seen acc hvp hsubs hsub_P hacc_inv hacc_pw hseen_acc hseen_cov
    rcases hvp with ⟨⟨a, b, ha, hb, hgab⟩, htail_vp⟩
    have hgM : g &&& M = g := hgab ▸ or_and_mask ha.1 hb.1
    set done' := done ++ [g]
    have hlen' : done'.length = done.length + 1 := by simp [done']
    have hraw_sub : ∀ z ∈ raw ++ done, z ∈ raw ++ done' := by
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact List.mem_append_left _ hz
      · exact List.mem_append_right _ (List.mem_append_left _ hz)
    set newSubs := chkSubsetsStep g subs []
    have hnewSubs_meet : ∀ gi ∈ newSubs, MeetNat M (raw ++ done') gi := by
      intro gi hgi
      rw [chkSubsetsStep_mem] at hgi
      rcases hgi with hnil | ⟨x, hx, rfl⟩
      · simp at hnil
      · have hx' := meetNat_weaken hraw_sub (hsubs x hx)
        have hsub : (x &&& g) &&& M = x &&& g := by
          apply Nat.eq_of_testBit_eq; intro s
          have h1 := congrArg (fun z => z.testBit s) hgM
          simp only [Nat.testBit_and] at h1 ⊢
          revert h1; cases x.testBit s <;> cases g.testBit s <;> cases M.testBit s <;> decide
        have hg_mem : g ∈ raw ++ done' := by simp [done']
        exact meetNat_iff.mpr ⟨hsub, by rw [decM_and]; exact (meetNat_iff.mp hx').2.inter (Meet.atom ⟨g, hg_mem, rfl⟩)⟩
    have hacc_inv' : ∀ x ∈ acc, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ done.length + 1 ∧
        MeetNat M (raw ++ done'.take x.2.2) x.1 := by
      intro x hx
      obtain ⟨h1, h2, h3⟩ := hacc_inv x hx
      refine ⟨h1, by omega, ?_⟩
      have htake : done'.take x.2.2 = done.take x.2.2 := by
        simp only [done', List.take_append_of_le_length h2]
      rwa [htake]
    have hadd := chkAddSubsOps_inv hlen'.symm hmasks newSubs seen acc hnewSubs_meet
      hacc_inv' hacc_pw hseen_acc
    set r1 := chkAddSubsOps M ep (done.length + 1) masksTT newSubs seen acc
    have hsubs' : ∀ gi ∈ newSubs ++ subs, MeetNat M (raw ++ done') gi := by
      intro gi hgi
      rcases List.mem_append.mp hgi with hgi | hgi
      · exact hnewSubs_meet gi hgi
      · exact meetNat_weaken hraw_sub (hsubs gi hgi)
    have hsub_P' : ∀ P : List ℕ, List.Sublist P done' → P.foldl Nat.land M ∈ newSubs ++ subs := by
      intro P hP
      rcases sublist_append_singleton hP with h1 | ⟨P', h1, rfl⟩
      · exact List.mem_append_right _ (hsub_P P h1)
      · refine List.mem_append_left _ ?_
        rw [chkSubsetsStep_mem]
        refine Or.inr ⟨P'.foldl Nat.land M, hsub_P P' h1, ?_⟩
        simp [List.foldl_append]
    have hseen_cov' : ∀ gi ∈ newSubs ++ subs, ∀ mt ∈ masksTT,
        (mt &&& gi) ≠ 0 → (mt &&& gi) ≠ M → (mt &&& gi) &&& ep ≠ 0 → (mt &&& gi) ∈ r1.1 := by
      intro gi hgi mt hmt h0 hM hep
      rcases List.mem_append.mp hgi with hgi | hgi
      · exact hadd.2.2.2.2 gi hgi mt hmt h0 hM hep
      · exact hadd.2.2.1 _ (hseen_cov gi hgi mt hmt h0 hM hep)
    have htail_vp' : ValidPrefix M (raw ++ done') tail := by
      simpa only [done', List.append_assoc] using htail_vp
    have hrec := ih done' (newSubs ++ subs) r1.1 r1.2 htail_vp' hsubs' hsub_P'
      (by simpa only [hlen'] using hadd.1) hadd.2.1 hadd.2.2.2.1 hseen_cov'
    simp only [chkGenBirthLoop]
    simpa only [done', hlen', List.append_assoc, List.singleton_append] using hrec

theorem chkGenBirthOps_spec {n : ℕ} {H F : List (ℕ × ℕ)} {gs : List ℕ}
    (hv : ValidState n H F)
    (hvp : ValidPrefix (univYF n F) (rawYF n (univYF n F)) gs) :
    let M := univYF n F
    let ep := edgePtsMaskYF H
    let raw := rawYF n M
    let ops := chkGenBirthOps M ep (masksTTYF n H M) gs
    (∀ x ∈ ops, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ gs.length ∧ MeetNat M (raw ++ gs.take x.2.2) x.1) ∧
    ops.Pairwise (fun x y => y.2.2 ≤ x.2.2) ∧
    (∀ x : ℕ, MeetNat M (raw ++ gs) x → x ≠ 0 → x ≠ M → x &&& ep ≠ 0 →
      ∃ b, (x, x &&& ep, b) ∈ ops) := by
  set M := univYF n F
  set ep := edgePtsMaskYF H
  set raw := rawYF n M
  set masksTT := masksTTYF n H M
  have hmasks : ∀ mt ∈ masksTT, MeetNat M raw mt := masksTTYF_meetNat hv
  have hM_meet : MeetNat M (raw ++ []) M := by
    refine meetNat_iff.mpr ⟨by simp, ?_⟩
    rw [decM_self]; exact Meet.top
  have h0 := chkAddBirthOps_inv (ep := ep) (done := []) rfl hM_meet masksTT hmasks [] []
    (fun _ h => by simp at h) List.Pairwise.nil (fun _ h => by simp at h)
  set r0 := chkAddBirthOps M ep M 0 masksTT [] []
  have hloop := chkGenBirthLoop_inv hmasks gs [] [M] r0.1 r0.2
    (by simpa using hvp)
    (fun gi hgi => by rw [List.mem_singleton.mp hgi]; exact hM_meet)
    (fun P hP => by cases hP; simp)
    h0.1 h0.2.1 h0.2.2.2.1
    (fun gi hgi mt hmt h0' hM' hep' => by
      obtain rfl := List.mem_singleton.mp hgi; exact h0.2.2.2.2 mt hmt h0' hM' hep')
  simp only [List.length_nil, zero_add, List.nil_append] at hloop
  refine ⟨hloop.1, hloop.2.1, fun x hx h0' hM' hep' => ?_⟩
  obtain ⟨mt, hmt, P, hPsub, rfl⟩ := meetNat_decompose_on_edges hv hx hep'
  exact hloop.2.2 P hPsub mt hmt h0' hM' hep'

theorem chkBuildSuffixMax_nonempty (gs : List ℕ) :
    ∃ m ms, chkBuildSuffixMax gs = m :: ms := by
  induction gs with
  | nil => exact ⟨0, [], rfl⟩
  | cons g rest ih =>
    obtain ⟨m, ms, heq⟩ := ih
    exact ⟨chkNatMax g m, m :: ms, by simp [chkBuildSuffixMax, heq]⟩

theorem chkBuildSuffixMax_spec (gs : List ℕ) (bi g : ℕ)
    (hlim_ne : chkGetNat (chkBuildSuffixMax gs) bi ≠ 0)
    (hlt : g < chkGetNat (chkBuildSuffixMax gs) bi) :
    ∃ t, bi ≤ t ∧ ∃ (ht : t < gs.length), g < gs[t] := by
  induction gs generalizing bi with
  | nil =>
    cases bi with
    | zero => simp [chkBuildSuffixMax, chkGetNat] at hlim_ne
    | succ k => cases k <;> simp [chkBuildSuffixMax, chkGetNat] at hlim_ne
  | cons x rest ih =>
    obtain ⟨m, ms, hsm⟩ := chkBuildSuffixMax_nonempty rest
    have hcons : chkBuildSuffixMax (x :: rest) = chkNatMax x m :: m :: ms := by
      simp [chkBuildSuffixMax, hsm]
    rw [hcons] at hlim_ne hlt
    cases bi with
    | zero =>
      simp only [chkGetNat] at hlim_ne hlt
      unfold chkNatMax at hlt
      cases hxm : Nat.blt x m
      · rw [hxm] at hlt; dsimp only at hlt
        exact ⟨0, le_rfl, by simp, hlt⟩
      · rw [hxm] at hlt; dsimp only at hlt
        have hm0 : m ≠ 0 := by omega
        have hm_eq : chkGetNat (chkBuildSuffixMax rest) 0 = m := by simp [hsm, chkGetNat]
        obtain ⟨t, _, ht, hgt⟩ := ih 0 (hm_eq.symm ▸ hm0) (hm_eq.symm ▸ hlt)
        exact ⟨t + 1, Nat.zero_le _, by simp [ht], by simpa using hgt⟩
    | succ bi' =>
      simp only [chkGetNat] at hlim_ne hlt
      have heq : chkGetNat (m :: ms) bi' = chkGetNat (chkBuildSuffixMax rest) bi' := by rw [hsm]
      rw [heq] at hlim_ne hlt
      obtain ⟨t, hle, ht, hgt⟩ := ih bi' hlim_ne hlt
      exact ⟨t + 1, by omega, by simp [ht], by simpa using hgt⟩

/-! ### `chkCheckTermMd`, `chkCheckLayer`, `chkCheckNode`, and `state_cert_sound` -/

theorem chkComputeMd_eq (edgeTT acc : ℕ) (b : List ℕ) :
    chkComputeMd edgeTT acc b = isMeetLoop edgeTT b acc := by
  induction b generalizing acc with
  | nil => rfl
  | cons x rest ih =>
    simp only [chkComputeMd, isMeetLoop]
    cases Nat.beq (Nat.land edgeTT x) edgeTT <;> exact ih _

theorem chkFilterGoodOps_eq (bad : ℕ) (ops : List (ℕ × ℕ × ℕ)) :
    chkFilterGoodOps bad ops =
      (ops.map Prod.fst).filter (fun op => Nat.beq (Nat.land op bad) 0) := by
  induction ops with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨op, eg, b⟩
    simp only [chkFilterGoodOps, List.map_cons, List.filter_cons]
    cases Nat.beq (Nat.land op bad) 0 <;> simp [ih]

theorem chkNoCovInner_eq (ep a : ℕ) (l : List ℕ) :
    chkNoCovInner ep a l = l.all (fun b => !Nat.beq (Nat.land (Nat.lor a b) ep) ep) := by
  induction l with
  | nil => rfl
  | cons b rest ih =>
    simp only [chkNoCovInner, List.all_cons]
    cases Nat.beq (Nat.land (Nat.lor a b) ep) ep <;> simp [ih]

theorem chkNoCovOuter_eq (ep : ℕ) (l : List ℕ) :
    chkNoCovOuter ep l = noCovPairs ep l := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [chkNoCovOuter, noCovPairs, chkNoCovInner_eq]
    cases rest.all (fun b => !Nat.beq (Nat.land (Nat.lor a b) ep) ep) <;> simp [ih]

theorem chkCheckTermMd_sound {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf : List ℕ}
    (hv : ValidState n H F) (hHne : H ≠ [])
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre ++ suf))
    (hmin : ∀ k' < (pre ++ suf).length, ¬ HasRunYF n H F k')
    (hsuf_le : suf.length ≤ 1)
    (hok : chkCheckTermMd (univYF n F) (edgePtsMaskYF H) (edgeTTYF n H (univYF n F))
      (rawYF n (univYF n F)) (masksTTYF n H (univYF n F)) pre = true) :
    False := by
  set M := univYF n F
  set ep := edgePtsMaskYF H
  set edgeTT := edgeTTYF n H M
  set raw := rawYF n M
  unfold chkCheckTermMd at hok
  dsimp only at hok
  rw [chkComputeMd_eq] at hok
  cases hmd : Nat.beq (isMeetLoop edgeTT (raw ++ pre) M) edgeTT
  · rw [hmd] at hok
    have hmd_ne : isMeetLoop edgeTT (raw ++ pre) M ≠ edgeTT := (nat_beq_eq_false_iff _ _).mp hmd
    cases suf with
    | nil =>
      obtain ⟨_, hend⟩ := runListFrom_append.mp hrun
      have hEdgeNe0 : edgeTT ≠ 0 := by
        obtain ⟨e, _, heq⟩ := List.exists_cons_of_ne_nil hHne
        intro h0
        have hbit := edgePt_mem_edgeTTYF hv (show e ∈ H by rw [heq]; simp)
        rw [show edgeTTYF n H (univYF n F) = edgeTT from rfl, h0] at hbit; simp at hbit
      have hm := hend.2
      unfold isMeet at hm
      rw [(nat_beq_eq_false_iff _ _).mpr hEdgeNe0] at hm
      exact hmd_ne (Nat.eq_of_beq_eq_true hm)
    | cons g rest =>
      cases rest with
      | cons => simp at hsuf_le
      | nil =>
        have hvp : ValidPrefix M raw pre := (runListFrom_append.mp hrun).1
        have hops_spec := chkGenBirthOps_spec hv hvp
        have hops_cov : ∀ x, MeetNat M (raw ++ pre) x → x ≠ 0 → x ≠ M → x &&& ep ≠ 0 →
            x ∈ (chkGenBirthOps M ep (masksTTYF n H M) pre).map Prod.fst := by
          intro x hx h0 hM hep
          obtain ⟨b, hb⟩ := hops_spec.2.2 x hx h0 hM hep
          exact List.mem_map.mpr ⟨(x, x &&& ep, b), hb, rfl⟩
        have htm := termMd_sound hv hHne hrun hmin hops_cov
        rcases htm with heq | hnocov
        · exact hmd_ne heq
        · apply hnocov
          rw [← chkNoCovOuter_eq, ← chkFilterGoodOps_eq]
          exact hok
  · rw [hmd] at hok; simp at hok

theorem chkGetCut_mem {cuts : List CutDefData} {ci : ℕ} {gs : List ℕ} {stepIdx g : ℕ}
    (hok : chkCutKillsWit (chkPrepCutState (chkGetCut cuts ci) gs) stepIdx g = true) :
    chkGetCut cuts ci ∈ cuts := by
  induction cuts generalizing ci with
  | nil =>
    cases ci <;> simp [chkGetCut, chkPrepCutState, chkPrepSteps, chkCutKillsWit, chkCutKillsAtStep] at hok
  | cons c rest ih =>
    cases ci with
    | zero => exact List.mem_cons_self
    | succ k => exact List.mem_cons_of_mem _ (ih hok)

theorem chkGetCutState_mem {cuts : List CutDefData} {gs hints : List ℕ} {hi stepIdx g : ℕ}
    (hok : chkCutKillsWit (chkGetCutState (chkPrepHints cuts gs hints) hi) stepIdx g = true) :
    ∃ cut ∈ cuts, chkCutKillsWit (chkPrepCutState cut gs) stepIdx g = true := by
  induction hints generalizing hi with
  | nil =>
    cases hi <;> simp [chkPrepHints, chkGetCutState, chkCutKillsWit, chkCutKillsAtStep] at hok
  | cons ci rest ih =>
    cases hi with
    | zero =>
      simp only [chkPrepHints, chkGetCutState] at hok
      exact ⟨chkGetCut cuts ci, chkGetCut_mem hok, hok⟩
    | succ k =>
      simp only [chkPrepHints, chkGetCutState] at hok
      exact ih hok

theorem chkPairsNoStabInner_sound {maskYF : ℕ} {b : List ℕ} {hStates : List ChkCutState}
    {surv : List ℕ} {oi egi lim : ℕ} {rest : List (ℕ × ℕ × ℕ)} {wits wits' : List ℕ}
    (hok : chkPairsNoStabInner maskYF b hStates surv oi egi lim rest wits = some wits') :
    ∀ x ∈ rest,
      (egi &&& x.2.1 = egi) ∨ (egi &&& x.2.1 = x.2.1) ∨
      (lim ≠ 0 ∧ oi ||| x.1 < lim) ∨
      ∃ w, chkCheckWitNoStab maskYF b hStates surv (egi ||| x.2.1) (oi ||| x.1) w = true := by
  induction rest generalizing wits with
  | nil => intro x hx; simp at hx
  | cons p tail ih =>
    rcases p with ⟨oj, egj, bj⟩
    simp only [chkPairsNoStabInner, land_eq, lor_eq] at hok
    intro x hx
    cases h1 : Nat.beq (egi &&& egj) egi
    · rw [h1] at hok; dsimp only at hok
      cases h2 : Nat.beq (egi &&& egj) egj
      · rw [h2] at hok; dsimp only at hok
        cases hlex : (match Nat.beq lim 0 with | true => false | false => Nat.blt (oi ||| oj) lim)
        · rw [hlex] at hok; dsimp only at hok
          cases wits with
          | nil => simp at hok
          | cons w ws =>
            dsimp only at hok
            cases hw : chkCheckWitNoStab maskYF b hStates surv (egi ||| egj) (oi ||| oj) w
            · rw [hw] at hok; simp at hok
            · rw [hw] at hok; dsimp only at hok
              rcases List.mem_cons.mp hx with rfl | hx
              · exact Or.inr (Or.inr (Or.inr ⟨w, hw⟩))
              · exact ih hok x hx
        · rw [hlex] at hok; dsimp only at hok
          rcases List.mem_cons.mp hx with rfl | hx
          · cases hl0 : Nat.beq lim 0
            · rw [hl0] at hlex; dsimp only at hlex
              exact Or.inr (Or.inr (Or.inl ⟨(nat_beq_eq_false_iff _ _).mp hl0, nat_blt_eq_true hlex⟩))
            · rw [hl0] at hlex; simp at hlex
          · exact ih hok x hx
      · rw [h2] at hok; dsimp only at hok
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h2))
        · exact ih hok x hx
    · rw [h1] at hok; dsimp only at hok
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl (Nat.eq_of_beq_eq_true h1)
      · exact ih hok x hx

theorem chkPairsNoStabOuter_sound {maskYF : ℕ} {b : List ℕ} {hStates : List ChkCutState}
    {surv smax : List ℕ} {ops : List (ℕ × ℕ × ℕ)} {wits : List ℕ}
    (hok : chkPairsNoStabOuter maskYF b hStates surv smax ops wits = true)
    (hpw : ops.Pairwise (fun x y => y.2.2 ≤ x.2.2))
    {x y : ℕ × ℕ × ℕ} (hx : x ∈ ops) (hy : y ∈ ops) (hne : x.1 ≠ y.1) :
    ∃ p q : ℕ × ℕ × ℕ, ((p = x ∧ q = y) ∨ (p = y ∧ q = x)) ∧ q.2.2 ≤ p.2.2 ∧
      let lim := chkGetNat smax p.2.2
      ((p.2.1 &&& q.2.1 = p.2.1) ∨ (p.2.1 &&& q.2.1 = q.2.1) ∨
       (lim ≠ 0 ∧ p.1 ||| q.1 < lim) ∨
       ∃ w, chkCheckWitNoStab maskYF b hStates surv (p.2.1 ||| q.2.1) (p.1 ||| q.1) w = true) := by
  induction ops generalizing wits with
  | nil => simp at hx
  | cons z rest ih =>
    rcases z with ⟨oi, egi, bi⟩
    simp only [chkPairsNoStabOuter] at hok
    cases hinner : chkPairsNoStabInner maskYF b hStates surv oi egi (chkGetNat smax bi) rest wits with
    | none => rw [hinner] at hok; simp at hok
    | some wits' =>
      rw [hinner] at hok
      obtain ⟨hhead_pw, htail_pw⟩ := List.pairwise_cons.mp hpw
      rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
      · exact (hne rfl).elim
      · exact ⟨(oi, egi, bi), y, Or.inl ⟨rfl, rfl⟩, hhead_pw y hy',
          chkPairsNoStabInner_sound hinner y hy'⟩
      · exact ⟨(oi, egi, bi), x, Or.inr ⟨rfl, rfl⟩, hhead_pw x hx',
          chkPairsNoStabInner_sound hinner x hx'⟩
      · exact ih hok htail_pw hx' hy'

theorem chkPairsStabInner_sound {maskYF : ℕ} {b : List ℕ} {hStates : List ChkCutState}
    {surv : List ℕ} {oi egi lim : ℕ} {pi : List ℕ}
    {rest : List (ℕ × ℕ × ℕ × List ℕ)} {wits wits' : List ℕ}
    (hok : chkPairsStabInner maskYF b hStates surv oi egi lim pi rest wits = some wits') :
    ∀ x ∈ rest,
      (egi &&& x.2.1 = egi) ∨ (egi &&& x.2.1 = x.2.1) ∨
      (lim ≠ 0 ∧ oi ||| x.1 < lim) ∨
      ∃ w, chkCheckWitStab maskYF b hStates surv (egi ||| x.2.1) (oi ||| x.1) pi x.2.2.2 w = true := by
  induction rest generalizing wits with
  | nil => intro x hx; simp at hx
  | cons p tail ih =>
    rcases p with ⟨oj, egj, bj, pj⟩
    simp only [chkPairsStabInner, land_eq, lor_eq] at hok
    intro x hx
    cases h1 : Nat.beq (egi &&& egj) egi
    · rw [h1] at hok; dsimp only at hok
      cases h2 : Nat.beq (egi &&& egj) egj
      · rw [h2] at hok; dsimp only at hok
        cases hlex : (match Nat.beq lim 0 with | true => false | false => Nat.blt (oi ||| oj) lim)
        · rw [hlex] at hok; dsimp only at hok
          cases wits with
          | nil => simp at hok
          | cons w ws =>
            dsimp only at hok
            cases hw : chkCheckWitStab maskYF b hStates surv (egi ||| egj) (oi ||| oj) pi pj w
            · rw [hw] at hok; simp at hok
            · rw [hw] at hok; dsimp only at hok
              rcases List.mem_cons.mp hx with rfl | hx
              · exact Or.inr (Or.inr (Or.inr ⟨w, hw⟩))
              · exact ih hok x hx
        · rw [hlex] at hok; dsimp only at hok
          rcases List.mem_cons.mp hx with rfl | hx
          · cases hl0 : Nat.beq lim 0
            · rw [hl0] at hlex; dsimp only at hlex
              exact Or.inr (Or.inr (Or.inl ⟨(nat_beq_eq_false_iff _ _).mp hl0, nat_blt_eq_true hlex⟩))
            · rw [hl0] at hlex; simp at hlex
          · exact ih hok x hx
      · rw [h2] at hok; dsimp only at hok
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h2))
        · exact ih hok x hx
    · rw [h1] at hok; dsimp only at hok
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl (Nat.eq_of_beq_eq_true h1)
      · exact ih hok x hx

theorem chkAttachPerms_eq_map (stab : List (List ℕ)) (ops : List (ℕ × ℕ × ℕ)) :
    chkAttachPerms stab ops = ops.map (fun x => (x.1, x.2.1, x.2.2, chkApplyPermList x.1 stab)) := by
  induction ops with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨op, eg, b⟩
    simp [chkAttachPerms, ih]

theorem chkPairsStabOuter_sound {maskYF : ℕ} {b : List ℕ} {hStates : List ChkCutState}
    {surv smax : List ℕ} {stab : List (List ℕ)} {ops : List (ℕ × ℕ × ℕ)} {wits : List ℕ}
    (hok : chkPairsStabOuter maskYF b hStates surv smax (chkAttachPerms stab ops) wits = true)
    (hpw : ops.Pairwise (fun x y => y.2.2 ≤ x.2.2))
    {x y : ℕ × ℕ × ℕ} (hx : x ∈ ops) (hy : y ∈ ops) (hne : x.1 ≠ y.1) :
    ∃ p q : ℕ × ℕ × ℕ, ((p = x ∧ q = y) ∨ (p = y ∧ q = x)) ∧ q.2.2 ≤ p.2.2 ∧
      let lim := chkGetNat smax p.2.2
      ((p.2.1 &&& q.2.1 = p.2.1) ∨ (p.2.1 &&& q.2.1 = q.2.1) ∨
       (lim ≠ 0 ∧ p.1 ||| q.1 < lim) ∨
       ∃ w, chkCheckWitStab maskYF b hStates surv (p.2.1 ||| q.2.1) (p.1 ||| q.1)
         (chkApplyPermList p.1 stab) (chkApplyPermList q.1 stab) w = true) := by
  induction ops generalizing wits with
  | nil => simp at hx
  | cons z rest ih =>
    rcases z with ⟨oi, egi, bi⟩
    simp only [chkAttachPerms, chkPairsStabOuter] at hok
    cases hinner : chkPairsStabInner maskYF b hStates surv oi egi (chkGetNat smax bi)
        (chkApplyPermList oi stab) (chkAttachPerms stab rest) wits with
    | none => rw [hinner] at hok; simp at hok
    | some wits' =>
      rw [hinner] at hok
      obtain ⟨hhead_pw, htail_pw⟩ := List.pairwise_cons.mp hpw
      have hmem_attach : ∀ u ∈ rest, (u.1, u.2.1, u.2.2, chkApplyPermList u.1 stab) ∈ chkAttachPerms stab rest := by
        intro u hu
        rw [chkAttachPerms_eq_map]
        exact List.mem_map.mpr ⟨u, hu, rfl⟩
      rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
      · exact (hne rfl).elim
      · exact ⟨(oi, egi, bi), y, Or.inl ⟨rfl, rfl⟩, hhead_pw y hy',
          chkPairsStabInner_sound hinner _ (hmem_attach y hy')⟩
      · exact ⟨(oi, egi, bi), x, Or.inr ⟨rfl, rfl⟩, hhead_pw x hx',
          chkPairsStabInner_sound hinner _ (hmem_attach x hx')⟩
      · exact ih hok htail_pw hx' hy'

theorem chkCheckLayer_sound {n : ℕ} {H F : List (ℕ × ℕ)} {cuts : List CutDefData}
    {pre suf hints wits surv : List ℕ} {g : ℕ} {stabIdx : List (List ℕ)}
    (hv : ValidState n H F)
    (hcuts : ∀ cut ∈ cuts, ∀ (pre' suf' : List ℕ),
      RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre' ++ suf') →
      (pre' ++ suf').length + 2 ≤ H.length →
      cut.loss ≤ evalCutChain cut.steps pre' → False)
    (hstab_valid : ∀ tbl ∈ stabIdx, ValidAutTbl (univYF n F) (edgeTTYF n H (univYF n F)) (rawYF n (univYF n F)) tbl)
    (hstab_fix : ∀ tbl ∈ stabIdx, ∀ h ∈ pre, applyPerm tbl h = h)
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre ++ g :: suf))
    (hlen : (pre ++ g :: suf).length + 2 ≤ H.length)
    (hmin : ∀ k' < (pre ++ g :: suf).length, ¬ HasRunYF n H F k')
    (hlex : ∀ gs', gs'.length = (pre ++ g :: suf).length →
      RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) gs' →
      ¬ List.Lex (· < ·) gs' (pre ++ g :: suf))
    (hok : chkCheckLayer (univYF n F) (edgePtsMaskYF H) (edgeTTYF n H (univYF n F))
      (rawYF n (univYF n F)) (masksTTYF n H (univYF n F)) cuts pre
      (chkMkAutMaskTbls stabIdx) hints wits surv = true) :
    g ∈ surv := by
  set M := univYF n F
  set ep := edgePtsMaskYF H
  set edgeTT := edgeTTYF n H M
  set raw := rawYF n M
  set masksTT := masksTTYF n H M
  have hvp : ValidPrefix M raw pre := (runListFrom_append.mp hrun).1
  obtain ⟨a, b, hgab, hab, ha, hb, ha0, haM, haep, hb0, hbM, hbep⟩ := lexMin_operands hv hrun hmin
  have hops := chkGenBirthOps_spec hv hvp
  obtain ⟨ba, hba⟩ := hops.2.2 a ha ha0 haM haep
  obtain ⟨bb, hbb⟩ := hops.2.2 b hb hb0 hbM hbep
  have hdisch : ∀ (p q : ℕ × ℕ × ℕ),
      p ∈ chkGenBirthOps M ep masksTT pre → q ∈ chkGenBirthOps M ep masksTT pre →
      p.1 ||| q.1 = g → q.2.2 ≤ p.2.2 →
      ((p.2.1 &&& q.2.1 = p.2.1) ∨ (p.2.1 &&& q.2.1 = q.2.1) ∨
       (chkGetNat (chkBuildSuffixMax pre) p.2.2 ≠ 0 ∧ p.1 ||| q.1 < chkGetNat (chkBuildSuffixMax pre) p.2.2) ∨
       (chkMemNat g surv = true ∨
        chkIsOnEdgesLoop (p.2.1 ||| q.2.1) g M (raw ++ pre) = true ∨
        (∃ tbl ∈ stabIdx, applyPerm tbl g < g) ∨
        ∃ cut ∈ cuts, cut.loss ≤ evalCutChain cut.steps (pre ++ [g]))) →
      g ∈ surv := by
    intro p q hp hq hpg hqp hcase
    obtain ⟨hpe, hpb, hpM⟩ := hops.1 p hp
    obtain ⟨hqe, hqb, hqM⟩ := hops.1 q hq
    have hq_sub : ∀ z ∈ raw ++ pre.take q.2.2, z ∈ raw ++ pre.take p.2.2 := by
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact List.mem_append_left _ hz
      · refine List.mem_append_right _ ?_
        have htake : pre.take q.2.2 = (pre.take p.2.2).take q.2.2 := by
          rw [List.take_take, Nat.min_eq_left hqp]
        rw [htake] at hz
        exact List.mem_of_mem_take hz
    have hqM_p : MeetNat M (raw ++ pre.take p.2.2) q.1 := meetNat_weaken hq_sub hqM
    have hqM_full : MeetNat M (raw ++ pre) q.1 :=
      meetNat_weaken (fun z hz => (List.mem_append.mp hz).elim
        (List.mem_append_left _) (fun h => List.mem_append_right _ (List.mem_of_mem_take h))) hqM
    have hpM_full : MeetNat M (raw ++ pre) p.1 :=
      meetNat_weaken (fun z hz => (List.mem_append.mp hz).elim
        (List.mem_append_left _) (fun h => List.mem_append_right _ (List.mem_of_mem_take h))) hpM
    rcases hcase with hsub1 | hsub2 | ⟨hlim0, hlt⟩ | hmem | hon | ⟨tbl, htbl, hltp⟩ | ⟨cut, hcut, hkill⟩
    · rw [hpe, hqe] at hsub1
      exact (lexMin_not_eg_sub hv hrun hmin hqM_full hpg.symm hsub1).elim
    · rw [hpe, hqe, Nat.and_comm] at hsub2
      exact (lexMin_not_eg_sub hv hrun hmin hpM_full (Nat.or_comm _ _ ▸ hpg.symm) hsub2).elim
    · rw [hpg] at hlt
      obtain ⟨t, hpt, htlt, hgt⟩ := chkBuildSuffixMax_spec pre p.2.2 g hlim0 hlt
      exact (lexMin_birth_lex hrun hlex hpt htlt hpM hqM_p hpg.symm hgt).elim
    · exact (chkMemNat_iff g surv).mp hmem
    · exfalso
      have heg_eq : p.2.1 ||| q.2.1 = g &&& ep := by
        rw [hpe, hqe, ← hpg]
        apply Nat.eq_of_testBit_eq; intro s
        simp only [Nat.testBit_and, Nat.testBit_or]
        cases p.1.testBit s <;> cases q.1.testBit s <;> cases ep.testBit s <;> decide
      rw [heg_eq] at hon
      have hon' : isOnEdges M ep (raw ++ pre) g = true := by
        unfold isOnEdges
        rw [nat_beq_eq_true_iff]
        exact chkIsOnEdgesLoop_sound (g &&& ep) g M (raw ++ pre) hon
      have hno : isOnEdges M ep (raw ++ pre) g = false := lexMin_not_onEdges hv hrun hmin
      exact Bool.noConfusion (hon'.symm.trans hno)
    · exact (lexMin_autStab (hstab_valid tbl htbl) (hstab_fix tbl htbl) hrun hlex hltp).elim
    · exfalso
      have hrun' : RunListFrom M raw edgeTT ((pre ++ [g]) ++ suf) := by simpa [List.append_assoc] using hrun
      have hlen' : ((pre ++ [g]) ++ suf).length + 2 ≤ H.length := by simpa [List.append_assoc] using hlen
      exact hcuts cut hcut (pre ++ [g]) suf hrun' hlen' hkill
  unfold chkCheckLayer at hok
  dsimp only at hok
  cases hfin : chkIsMeet M (raw ++ pre) edgeTT
  · rw [hfin] at hok; dsimp only at hok
    cases hst : chkMkAutMaskTbls stabIdx with
    | nil =>
      rw [hst] at hok; dsimp only at hok
      obtain ⟨p, q, hpq, hqp, hres⟩ := chkPairsNoStabOuter_sound hok hops.2.1 hba hbb hab
      have hpg : p.1 ||| q.1 = g := by
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hgab.symm
        · rw [Nat.or_comm]; exact hgab.symm
      have hp_mem : p ∈ chkGenBirthOps M ep masksTT pre := by
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      have hq_mem : q ∈ chkGenBirthOps M ep masksTT pre := by
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      apply hdisch p q hp_mem hq_mem hpg hqp
      rcases hres with h1 | h2 | h3 | ⟨w, hw⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl h3))
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [hpg] at hw
        match w, hw with
        | 0, hw => exact Or.inl hw
        | 1, hw => exact Or.inr (Or.inl hw)
        | 2, hw => simp [chkCheckWitNoStab] at hw
        | w3 + 3, hw =>
          simp only [chkCheckWitNoStab] at hw
          obtain ⟨cut, hcut, hkw⟩ := chkGetCutState_mem hw
          exact Or.inr (Or.inr (Or.inr ⟨cut, hcut, chkCutKillsWit_sound cut pre (Nat.land w3 7) g hkw⟩))
    | cons hd tl =>
      rw [hst] at hok; dsimp only at hok
      rw [← hst] at hok
      obtain ⟨p, q, hpq, hqp, hres⟩ := chkPairsStabOuter_sound hok hops.2.1 hba hbb hab
      have hpg : p.1 ||| q.1 = g := by
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hgab.symm
        · rw [Nat.or_comm]; exact hgab.symm
      have hp_mem : p ∈ chkGenBirthOps M ep masksTT pre := by
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      have hq_mem : q ∈ chkGenBirthOps M ep masksTT pre := by
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      apply hdisch p q hp_mem hq_mem hpg hqp
      rcases hres with h1 | h2 | h3 | ⟨w, hw⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl h3))
      · refine Or.inr (Or.inr (Or.inr ?_))
        match w, hw with
        | 0, hw => exact Or.inl (hpg ▸ hw)
        | 1, hw => exact Or.inr (Or.inl (hpg ▸ hw))
        | 2, hw =>
          simp only [chkCheckWitStab] at hw
          obtain ⟨tbl, htbl, hltp⟩ := chkAnyPermLt_sound stabIdx p.1 q.1 hw
          exact Or.inr (Or.inr (Or.inl ⟨tbl, htbl, hpg ▸ hltp⟩))
        | w3 + 3, hw =>
          simp only [chkCheckWitStab] at hw
          rw [hpg] at hw
          obtain ⟨cut, hcut, hkw⟩ := chkGetCutState_mem hw
          exact Or.inr (Or.inr (Or.inr ⟨cut, hcut, chkCutKillsWit_sound cut pre (Nat.land w3 7) g hkw⟩))
  · rw [hfin] at hok; simp at hok

theorem chkCheckNode_sound {n : ℕ} {H F : List (ℕ × ℕ)} {cuts : List CutDefData}
    (hv : ValidState n H F) (h3 : 3 ≤ H.length)
    (hcuts : ∀ cut ∈ cuts, ∀ (pre' suf' : List ℕ),
      RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre' ++ suf') →
      (pre' ++ suf').length + 2 ≤ H.length →
      cut.loss ≤ evalCutChain cut.steps pre' → False) :
    ∀ (node : CertNode) (pre suf : List ℕ) (stabIdx : List (List ℕ)),
      (∀ tbl ∈ stabIdx, ValidAutTbl (univYF n F) (edgeTTYF n H (univYF n F)) (rawYF n (univYF n F)) tbl) →
      (∀ tbl ∈ stabIdx, ∀ h ∈ pre, applyPerm tbl h = h) →
      RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre ++ suf) →
      (pre ++ suf).length + 2 ≤ H.length →
      (∀ k' < (pre ++ suf).length, ¬ HasRunYF n H F k') →
      (∀ gs', gs'.length = (pre ++ suf).length →
        RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) gs' →
        ¬ List.Lex (· < ·) gs' (pre ++ suf)) →
      certDepthOk (H.length - 3) pre.length node = true →
      chkCheckNode (univYF n F) (edgePtsMaskYF H) (edgeTTYF n H (univYF n F))
        (rawYF n (univYF n F)) (masksTTYF n H (univYF n F)) cuts pre
        (chkMkAutMaskTbls stabIdx) node = true →
      False := by
  have hHne : H ≠ [] := by intro h; simp [h] at h3
  intro node
  induction node using CertNode.rec
      (motive_2 := fun ch =>
        ∀ (pre suf : List ℕ) (g : ℕ) (stabIdx : List (List ℕ)),
          (∀ tbl ∈ stabIdx, ValidAutTbl (univYF n F) (edgeTTYF n H (univYF n F)) (rawYF n (univYF n F)) tbl) →
          (∀ tbl ∈ stabIdx, ∀ h ∈ pre, applyPerm tbl h = h) →
          RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre ++ g :: suf) →
          (pre ++ g :: suf).length + 2 ≤ H.length →
          (∀ k' < (pre ++ g :: suf).length, ¬ HasRunYF n H F k') →
          (∀ gs', gs'.length = (pre ++ g :: suf).length →
            RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) gs' →
            ¬ List.Lex (· < ·) gs' (pre ++ g :: suf)) →
          g ∈ chkCertListGates ch →
          certListDepthOk (H.length - 3) (pre.length + 1) ch = true →
          chkCheckChildren (univYF n F) (edgePtsMaskYF H) (edgeTTYF n H (univYF n F))
            (rawYF n (univYF n F)) (masksTTYF n H (univYF n F)) cuts pre
            (chkMkAutMaskTbls stabIdx) ch = true →
          False) with
  | term =>
    intro pre suf stabIdx _ _ hrun hlen hmin _ hdepth hcert
    simp only [certDepthOk] at hdepth
    simp only [chkCheckNode] at hcert
    have hd_ge : H.length - 3 ≤ pre.length := Nat.le_of_ble_eq_true hdepth
    simp only [List.length_append] at hlen
    have hsuf_le : suf.length ≤ 1 := by omega
    exact chkCheckTermMd_sound hv hHne hrun hmin hsuf_le hcert
  | branch hints witsChunks children ih_ch =>
    intro pre suf stabIdx hstab_v hstab_f hrun hlen hmin hlex hdepth hcert
    simp only [certDepthOk] at hdepth
    simp only [chkCheckNode] at hcert
    cases hlay : chkCheckLayer (univYF n F) (edgePtsMaskYF H) (edgeTTYF n H (univYF n F))
        (rawYF n (univYF n F)) (masksTTYF n H (univYF n F)) cuts pre
        (chkMkAutMaskTbls stabIdx) hints (chkFlatten witsChunks) (chkCertListGates children)
    · rw [hlay] at hcert; simp at hcert
    · rw [hlay] at hcert; dsimp only at hcert
      cases suf with
      | nil =>
        obtain ⟨_, hend⟩ := runListFrom_append.mp hrun
        have hm := hend.2
        rw [← chkIsMeet_eq_isMeet _ (edgeTTYF_and_univYF n H F)] at hm
        unfold chkCheckLayer at hlay
        dsimp only at hlay
        rw [hm] at hlay
        simp at hlay
      | cons g suf' =>
        have hg_mem := chkCheckLayer_sound hv hcuts hstab_v hstab_f hrun hlen hmin hlex hlay
        exact ih_ch pre suf' g stabIdx hstab_v hstab_f hrun hlen hmin hlex hg_mem hdepth hcert
  | nil =>
    rename_i pre suf g stabIdx hstab_v hstab_f hrun hlen hmin hlex hmem hdepth hcert
    simp [chkCertListGates] at hmem
  | cons g₀ ch rest ih_node ih_rest =>
    rename_i pre suf g stabIdx hstab_v hstab_f hrun hlen hmin hlex hmem hdepth hcert
    simp only [certListDepthOk, Bool.and_eq_true] at hdepth
    simp only [chkCheckChildren] at hcert
    cases hhead : chkCheckNode (univYF n F) (edgePtsMaskYF H) (edgeTTYF n H (univYF n F))
        (rawYF n (univYF n F)) (masksTTYF n H (univYF n F)) cuts (pre ++ [g₀])
        (chkFilterStab g₀ (chkMkAutMaskTbls stabIdx)) ch
    · rw [hhead] at hcert; simp at hcert
    · rw [hhead] at hcert; dsimp only at hcert
      simp only [chkCertListGates, List.mem_cons] at hmem
      rcases hmem with rfl | hmem'
      · rw [chkFilterStab_map] at hhead
        let stab' := stabIdx.filter (fun tbl => Nat.beq (applyPerm tbl g) g)
        have hstab'_v : ∀ tbl ∈ stab', ValidAutTbl (univYF n F) (edgeTTYF n H (univYF n F))
            (rawYF n (univYF n F)) tbl :=
          fun tbl htbl => hstab_v tbl (List.mem_of_mem_filter htbl)
        have hstab'_f : ∀ tbl ∈ stab', ∀ h ∈ pre ++ [g], applyPerm tbl h = h := by
          intro tbl htbl h hh
          obtain ⟨ht_mem, ht_eq⟩ := List.mem_filter.mp htbl
          rcases List.mem_append.mp hh with hh | hh
          · exact hstab_f tbl ht_mem h hh
          · rw [List.mem_singleton.mp hh]; exact Nat.eq_of_beq_eq_true ht_eq
        have hrun' : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F))
            ((pre ++ [g]) ++ suf) := by simpa [List.append_assoc] using hrun
        have hlen' : ((pre ++ [g]) ++ suf).length + 2 ≤ H.length := by
          simpa [List.append_assoc] using hlen
        have hmin' : ∀ k' < ((pre ++ [g]) ++ suf).length, ¬ HasRunYF n H F k' := by
          simpa [List.append_assoc] using hmin
        have hlex' : ∀ gs', gs'.length = ((pre ++ [g]) ++ suf).length →
            RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) gs' →
            ¬ List.Lex (· < ·) gs' ((pre ++ [g]) ++ suf) := by
          simpa [List.append_assoc] using hlex
        have hdepth' : certDepthOk (H.length - 3) (pre ++ [g]).length ch = true := by
          simpa using hdepth.1
        exact ih_node (pre ++ [g]) suf stab' hstab'_v hstab'_f hrun' hlen' hmin' hlex' hdepth' hhead
      · exact ih_rest pre suf g stabIdx hstab_v hstab_f hrun hlen hmin hlex hmem' hdepth.2 hcert

/-- Master state certification theorem: turns a verified `chkCheckNode` certificate + cut validity
+ child `OrCostLB` theorems into `OrCostLB desc.n desc.edges desc.forb (desc.edges.length - 1)`. -/
def checkAllCutsValid (n : ℕ) (H F : List (ℕ × ℕ)) (states : List StateDesc) :
    List CutDefData → List CutSpecData → Bool
  | [], [] => true
  | cut :: cuts, spec :: specs =>
    match states[spec.childId]? with
    | none => false
    | some ch =>
      checkCutValid n H F cut spec.delVMask spec.forbAdded spec.peels
        ch.n ch.edges ch.forb spec.embed &&
      checkAllCutsValid n H F states cuts specs
  | _, _ => false

theorem checkAllCutsValid_sound {n : ℕ} {H F : List (ℕ × ℕ)} {states : List StateDesc}
    {cuts : List CutDefData} {specs : List CutSpecData}
    (hok : checkAllCutsValid n H F states cuts specs = true)
    (hchildren : ∀ spec ∈ specs, ∀ ch, states[spec.childId]? = some ch →
      OrCostLB ch.n ch.edges ch.forb (ch.edges.length - 1)) :
    ∀ cut ∈ cuts, ∀ (pre' suf' : List ℕ),
      RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre' ++ suf') →
      (pre' ++ suf').length + 2 ≤ H.length →
      cut.loss ≤ evalCutChain cut.steps pre' → False := by
  induction cuts generalizing specs with
  | nil => intro _ hc; simp at hc
  | cons cut rest ih =>
    cases specs with
    | nil => simp [checkAllCutsValid] at hok
    | cons spec srest =>
      simp only [checkAllCutsValid] at hok
      cases hst : states[spec.childId]? with
      | none => rw [hst] at hok; simp at hok
      | some ch =>
        rw [hst] at hok
        simp only [Bool.and_eq_true] at hok
        intro c hc pre' suf' hrun hlen hkill
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact cutDef_kills_sound hok.1 (hchildren spec List.mem_cons_self ch hst) hrun hlen hkill
        · exact ih hok.2 (fun s hs => hchildren s (List.mem_cons_of_mem _ hs)) c hc' pre' suf' hrun hlen hkill

theorem state_cert_sound {desc : StateDesc} {maskYF edgePts edgeTT : ℕ}
    {raw masksTT : List ℕ} {autIdxTbls auts : List (List ℕ)}
    {cuts : List CutDefData} {specs : List CutSpecData} {states : List StateDesc}
    {cert : CertNode}
    (hv : ValidState desc.n desc.edges desc.forb)
    (h3 : 3 ≤ desc.edges.length)
    (hM : maskYF = univYF desc.n desc.forb)
    (hEp : edgePts = edgePtsMaskYF desc.edges)
    (hEt : edgeTT = edgeTTYF desc.n desc.edges maskYF)
    (hRaw : raw = rawYF desc.n maskYF)
    (hMtt : masksTT = masksTTYF desc.n desc.edges maskYF)
    (hAuts : auts = chkMkAutMaskTbls autIdxTbls)
    (hAutV : ∀ tbl ∈ autIdxTbls, ValidAutTbl maskYF edgeTT raw tbl)
    (hCutsOk : checkAllCutsValid desc.n desc.edges desc.forb states cuts specs = true)
    (hChildren : ∀ spec ∈ specs, ∀ ch, states[spec.childId]? = some ch →
      OrCostLB ch.n ch.edges ch.forb (ch.edges.length - 1))
    (hDepth : certDepthOk (desc.edges.length - 3) 0 cert = true)
    (hCert : chkCheckNode maskYF edgePts edgeTT raw masksTT cuts [] auts cert = true) :
    OrCostLB desc.n desc.edges desc.forb (desc.edges.length - 1) := by
  subst hM hEp hEt hRaw hMtt hAuts
  intro k hr
  by_contra hlt
  have hle : k ≤ desc.edges.length - 2 := by omega
  obtain ⟨k₀, gs, hk₀_le, hlen, hrun, hmin, hlex⟩ :=
    exists_lexMinRun (bound := desc.edges.length - 2) ⟨k, hle, hr⟩
  subst hlen
  have hcuts_kill := checkAllCutsValid_sound hCutsOk hChildren
  exact chkCheckNode_sound hv h3 hcuts_kill cert [] gs autIdxTbls
    hAutV (fun _ _ _ h => by simp at h)
    (by simpa using hrun) (by simp; omega)
    (by simpa using hmin) (by simpa using hlex) hDepth hCert

/-! ## Section 9: DAG Certification & 31-Graph Core-Reduction Bridge -/

structure StateCertEntry where
  desc       : StateDesc
  maskYF     : ℕ
  edgePts    : ℕ
  edgeTT     : ℕ
  raw        : List ℕ
  masksTT    : List ℕ
  autIdxTbls : List (List ℕ)
  auts       : List (List ℕ)
  cuts       : List CutDefData
  specs      : List CutSpecData
  cert       : CertNode

def checkAllCutsDAG (n : ℕ) (H F : List (ℕ × ℕ)) (states : List StateDesc) :
    List CutDefData → List CutSpecData → Bool
  | [], [] => true
  | cut :: cuts, spec :: specs =>
    match states[spec.childId]? with
    | none => false
    | some ch =>
      decide (ch.edges.length < H.length) &&
      checkCutValid n H F cut spec.delVMask spec.forbAdded spec.peels
        ch.n ch.edges ch.forb spec.embed &&
      checkAllCutsDAG n H F states cuts specs
  | _, _ => false

theorem checkAllCutsDAG_sound {n : ℕ} {H F : List (ℕ × ℕ)} {states : List StateDesc}
    {cuts : List CutDefData} {specs : List CutSpecData}
    (hok : checkAllCutsDAG n H F states cuts specs = true) :
    checkAllCutsValid n H F states cuts specs = true ∧
    ∀ spec ∈ specs, ∀ ch, states[spec.childId]? = some ch → ch.edges.length < H.length := by
  induction cuts generalizing specs with
  | nil =>
    cases specs with
    | nil => exact ⟨rfl, fun _ h => by simp at h⟩
    | cons _ _ => simp [checkAllCutsDAG] at hok
  | cons cut rest ih =>
    cases specs with
    | nil => simp [checkAllCutsDAG] at hok
    | cons spec srest =>
      simp only [checkAllCutsDAG] at hok
      cases hst : states[spec.childId]? with
      | none => rw [hst] at hok; simp at hok
      | some ch =>
        rw [hst] at hok
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨hval, hlt⟩ := ih hok.2
        refine ⟨?_, ?_⟩
        · simp [checkAllCutsValid, hst, hok.1.2, hval]
        · intro s hs ch' hget
          rcases List.mem_cons.mp hs with rfl | hs'
          · rw [hst] at hget; cases hget; exact hok.1.1
          · exact hlt s hs' ch' hget

def checkStateEntryDAG (states : List StateDesc) (e : StateCertEntry) : Bool :=
  if e.desc.edges.length ≤ 1 then true
  else
    decide (ValidState e.desc.n e.desc.edges e.desc.forb) &&
    decide (3 ≤ e.desc.edges.length) &&
    (e.maskYF == univYF e.desc.n e.desc.forb) &&
    (e.edgePts == edgePtsMaskYF e.desc.edges) &&
    (e.edgeTT == edgeTTYF e.desc.n e.desc.edges e.maskYF) &&
    (e.raw == rawYF e.desc.n e.maskYF) &&
    (e.masksTT == masksTTYF e.desc.n e.desc.edges e.maskYF) &&
    (e.auts == chkMkAutMaskTbls e.autIdxTbls) &&
    e.autIdxTbls.all (fun tbl => decide (ValidAutTbl e.maskYF e.edgeTT e.raw tbl)) &&
    checkAllCutsDAG e.desc.n e.desc.edges e.desc.forb states e.cuts e.specs &&
    certDepthOk (e.desc.edges.length - 3) 0 e.cert

theorem allStates_orCostLB (entries : List StateCertEntry)
    (hMeta : ∀ e ∈ entries, checkStateEntryDAG (entries.map StateCertEntry.desc) e = true)
    (hCerts : ∀ e ∈ entries, e.desc.edges.length ≤ 1 ∨
      chkCheckNode e.maskYF e.edgePts e.edgeTT e.raw e.masksTT e.cuts [] e.auts e.cert = true) :
    ∀ (i : ℕ) (ch : StateDesc), (entries.map StateCertEntry.desc)[i]? = some ch →
      OrCostLB ch.n ch.edges ch.forb (ch.edges.length - 1) := by
  have hstrong : ∀ m : ℕ, ∀ e ∈ entries, e.desc.edges.length = m →
      OrCostLB e.desc.n e.desc.edges e.desc.forb (e.desc.edges.length - 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro e he hm
      by_cases h1 : e.desc.edges.length ≤ 1
      · intro k _; omega
      · have hdag := hMeta e he
        simp only [checkStateEntryDAG, h1, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
          beq_iff_eq, List.all_eq_true] at hdag
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, h3⟩, hM⟩, hEp⟩, hEt⟩, hRaw⟩, hMtt⟩, hAuts⟩, hAutV⟩, hCuts⟩, hDepth⟩ := hdag
        obtain ⟨hCutsValid, hCutsLt⟩ := checkAllCutsDAG_sound hCuts
        have hCert := (hCerts e he).resolve_left h1
        have hChildren : ∀ spec ∈ e.specs, ∀ ch,
            (entries.map StateCertEntry.desc)[spec.childId]? = some ch →
            OrCostLB ch.n ch.edges ch.forb (ch.edges.length - 1) := by
          intro spec hspec ch hget
          have hmem : ch ∈ entries.map StateCertEntry.desc := List.mem_of_getElem? hget
          obtain ⟨e', he', rfl⟩ := List.mem_map.mp hmem
          exact ih e'.desc.edges.length (hm ▸ hCutsLt spec hspec e'.desc hget) e' he' rfl
        exact state_cert_sound hv h3 hM hEp hEt hRaw hMtt hAuts hAutV hCutsValid hChildren hDepth hCert
  intro i ch hget
  have hmem : ch ∈ entries.map StateCertEntry.desc := List.mem_of_getElem? hget
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmem
  exact hstrong e.desc.edges.length e he rfl

def checkGraphCore (states : List StateDesc) (gc : GraphCoreSpec) : Bool :=
  match states[gc.coreId]? with
  | none => false
  | some ch =>
    decide (ValidState gc.n gc.edges []) &&
    validPeelEmbed gc.n gc.edges [] gc.peels ch.n ch.edges ch.forb gc.embed

theorem graphCore_orCostLB {states : List StateDesc} {cores : List GraphCoreSpec}
    (hStates : ∀ (i : ℕ) (ch : StateDesc), states[i]? = some ch →
      OrCostLB ch.n ch.edges ch.forb (ch.edges.length - 1))
    (hCores : cores.all (checkGraphCore states) = true)
    {idx : ℕ} {gc : GraphCoreSpec} (hget : cores[idx]? = some gc) :
    ValidState gc.n gc.edges [] ∧ OrCostLB gc.n gc.edges [] (gc.edges.length - 1) := by
  have hok : checkGraphCore states gc = true :=
    (List.all_eq_true.mp hCores) gc (List.mem_of_getElem? hget)
  simp only [checkGraphCore] at hok
  cases hst : states[gc.coreId]? with
  | none => rw [hst] at hok; simp at hok
  | some ch =>
    rw [hst] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact ⟨hok.1, validPeelEmbed_sound hok.1 hok.2 (hStates gc.coreId ch hst)⟩

theorem graph_or_bound_of_entry {n : ℕ} {H : List (ℕ × ℕ)} {f : (Fin n → Bool) → Bool}
    {states : List StateDesc} {cores : List GraphCoreSpec}
    (hf : ∀ x : Fin n → Bool, f x = edgeFnList n H x)
    (hStates : ∀ (i : ℕ) (ch : StateDesc), states[i]? = some ch →
      OrCostLB ch.n ch.edges ch.forb (ch.edges.length - 1))
    (hCores : cores.all (checkGraphCore states) = true)
    (idx : ℕ) (gc : GraphCoreSpec) (hget : cores[idx]? = some gc)
    (hn : gc.n = n) (hH : gc.edges = H)
    (C : Circuit) (hc : Monotone2 C) (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    H.length - 1 ≤ countOrGates C.gates := by
  obtain ⟨hv, hlb⟩ := graphCore_orCostLB hStates hCores hget
  subst hn hH
  exact or_bound_of_eval_eq (fun e heH => ⟨(hv.1 e heH).1, (hv.1 e heH).2.1⟩) hf hlb C hc he


-- State #0: n=6 |E|=7 |F|=0 nodes=0 cands=64 wits=64 cuts=5
def s0_desc : StateDesc := ⟨6,[(0,1),(0,4),(1,4),(2,3),(2,5),(3,5),(4,5)],[]⟩
def s0_maskYF : Nat := 0xffffffffffffffff
def s0_edgePts : Nat := 0x1011000061008
def s0_edgeTT : Nat := 0xfffffff8feeef888
def s0_raw : List Nat := chkMkRaw 6 s0_maskYF
def s0_masksTT : List Nat := chkMkMasksTT 6 s0_desc.edges s0_maskYF
def s0_autIdxTbls : List (List Nat) := []
def s0_auts : List (List Nat) := []
def s0_cutSpecs : List CutSpecData := [⟨2,[],[0,4],2,[2,3,5]⟩,⟨8,[],[2,5],2,[0,1,4]⟩,⟨0,[(4,5)],[],16,[0,1,2,3,4,5]⟩,⟨12,[],[5],2,[0,1,4]⟩,⟨19,[],[],2,[2,3,5]⟩]
def s0_cuts : List CutDefData := chkMkCuts s0_maskYF s0_raw [(2,[.v 1 [9,16,33]]),(2,[.v 3 [20,32]]),(1,[.e [(4,5)]]),(3,[.v 2 [10,32,24],.v 3 [32]]),(4,[.v 0 [6,24,34],.v 1 [16],.v 4 [32]])]
def s0_cert : CertNode := .branch [4,3,2,0,1] [[19,11,11,19,3,3,19,19,19,19,11,11,27,3,3,35,35,35,35,11,11,3,3,11,11,11,11,11,3,3,11,11,11,11,3,3,27,27,27,27,3,3,3,3,3,3,3,3,3,5,35,11,27,3,35,11,27,3,11,27,3,11,3,3]] (.nil)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_0 : chkCheckNode s0_maskYF s0_edgePts s0_edgeTT s0_raw s0_masksTT s0_cuts [] s0_auts s0_cert = true := by decide +kernel

-- State #1: n=5 |E|=6 |F|=0 nodes=0 cands=43 wits=43 cuts=4
def s1_desc : StateDesc := ⟨5,[(0,1),(0,4),(1,4),(2,3),(2,4),(3,4)],[]⟩
def s1_maskYF : Nat := 0xffffffff
def s1_edgePts : Nat := 0x1161008
def s1_edgeTT : Nat := 0xfffef888
def s1_raw : List Nat := chkMkRaw 5 s1_maskYF
def s1_masksTT : List Nat := chkMkMasksTT 5 s1_desc.edges s1_maskYF
def s1_autIdxTbls : List (List Nat) := []
def s1_auts : List (List Nat) := []
def s1_cutSpecs : List CutSpecData := [⟨0,[(3,4)],[3,2],2,[0,1,4]⟩,⟨2,[],[0],2,[2,3,4]⟩,⟨3,[],[],2,[2,3,4]⟩,⟨12,[],[],2,[0,1,4]⟩]
def s1_cuts : List CutDefData := chkMkCuts s1_maskYF s1_raw [(1,[.e [(3,4)]]),(2,[.v 1 [9,16]]),(3,[.v 0 [6,16,10],.v 1 [16]]),(3,[.v 2 [10,16],.v 3 [16]])]
def s1_cert : CertNode := .branch [2,3,1,0] [[11,11,19,3,3,27,27,27,11,11,3,3,11,11,11,11,3,3,11,11,11,3,3,19,19,19,3,3,3,3,3,3,3,12,11,19,3,11,19,3,11,3,3]] (.nil)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_1 : chkCheckNode s1_maskYF s1_edgePts s1_edgeTT s1_raw s1_masksTT s1_cuts [] s1_auts s1_cert = true := by decide +kernel

-- State #2: n=3 |E|=3 |F|=0 nodes=0 cands=0 wits=0 cuts=0
def s2_desc : StateDesc := ⟨3,[(0,1),(0,2),(1,2)],[]⟩
def s2_maskYF : Nat := 0xff
def s2_edgePts : Nat := 0x68
def s2_edgeTT : Nat := 0xe8
def s2_raw : List Nat := chkMkRaw 3 s2_maskYF
def s2_masksTT : List Nat := chkMkMasksTT 3 s2_desc.edges s2_maskYF
def s2_autIdxTbls : List (List Nat) := []
def s2_auts : List (List Nat) := []
def s2_cutSpecs : List CutSpecData := []
def s2_cuts : List CutDefData := chkMkCuts s2_maskYF s2_raw []
def s2_cert : CertNode := .term
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_2 : chkCheckNode s2_maskYF s2_edgePts s2_edgeTT s2_raw s2_masksTT s2_cuts [] s2_auts s2_cert = true := by decide +kernel

-- State #3: n=6 |E|=6 |F|=0 nodes=0 cands=54 wits=54 cuts=4
def s3_desc : StateDesc := ⟨6,[(0,1),(0,2),(1,2),(3,4),(3,5),(4,5)],[]⟩
def s3_maskYF : Nat := 0xffffffffffffffff
def s3_edgePts : Nat := 0x1010001000068
def s3_edgeTT : Nat := 0xffffffe8ffe8e8e8
def s3_raw : List Nat := chkMkRaw 6 s3_maskYF
def s3_masksTT : List Nat := chkMkMasksTT 6 s3_desc.edges s3_maskYF
def s3_autIdxTbls : List (List Nat) := []
def s3_auts : List (List Nat) := []
def s3_cutSpecs : List CutSpecData := [⟨0,[(4,5)],[4,3],2,[0,1,2]⟩,⟨4,[],[0],2,[3,4,5]⟩,⟨3,[],[],2,[3,4,5]⟩,⟨24,[],[],2,[0,1,2]⟩]
def s3_cuts : List CutDefData := chkMkCuts s3_maskYF s3_raw [(1,[.e [(4,5)]]),(2,[.v 2 [17,34]]),(3,[.v 0 [10,20,34],.v 1 [20,36]]),(3,[.v 3 [18,36],.v 4 [32]])]
def s3_cert : CertNode := .branch [2,3,1,0] [[11,11,19,3,3,27,27,27,27,11,11,3,3,11,11,11,11,11,3,3,11,11,11,11,3,3,19,19,19,19,3,3,3,3,3,3,3,3,3,12,11,19,4,3,11,19,4,3,11,11,3,19,3,3]] (.nil)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_3 : chkCheckNode s3_maskYF s3_edgePts s3_edgeTT s3_raw s3_masksTT s3_cuts [] s3_auts s3_cert = true := by decide +kernel

-- State #4: n=5 |E|=5 |F|=0 nodes=0 cands=35 wits=35 cuts=3
def s4_desc : StateDesc := ⟨5,[(0,1),(0,2),(1,3),(2,4),(3,4)],[]⟩
def s4_maskYF : Nat := 0xffffffff
def s4_edgePts : Nat := 0x1100428
def s4_edgeTT : Nat := 0xfff8eca8
def s4_raw : List Nat := chkMkRaw 5 s4_maskYF
def s4_masksTT : List Nat := chkMkMasksTT 5 s4_desc.edges s4_maskYF
def s4_autIdxTbls : List (List Nat) := []
def s4_auts : List (List Nat) := []
def s4_cutSpecs : List CutSpecData := [⟨0,[(2,4)],[2,0,1],17,[3,4]⟩,⟨24,[],[1],17,[0,2]⟩,⟨7,[],[],17,[3,4]⟩]
def s4_cuts : List CutDefData := chkMkCuts s4_maskYF s4_raw [(1,[.e [(2,4)]]),(3,[.v 3 [6,16],.v 4 [6]]),(4,[.v 0 [12,18],.v 1 [12],.v 2 [16]])]
def s4_cert : CertNode := .branch [2,1,0] [[11,11,3,3,11,11,11,11,3,3,19,19,19,3,3,11,11,11,3,3,3,3,3,3,3,11,12,12,3,11,11,3,4,3,3]] (.nil)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_4 : chkCheckNode s4_maskYF s4_edgePts s4_edgeTT s4_raw s4_masksTT s4_cuts [] s4_auts s4_cert = true := by decide +kernel

-- State #5: n=7 |E|=7 |F|=0 nodes=0 cands=77 wits=77 cuts=4
def s5_desc : StateDesc := ⟨7,[(0,1),(0,2),(1,3),(2,4),(3,5),(4,6),(5,6)],[]⟩
def s5_maskYF : Nat := 0xffffffffffffffffffffffffffffffff
def s5_edgePts : Nat := 0x1000100000000010000100428
def s5_edgeTT : Nat := 0xffffffffffffeca8fff8ffa8fcf8eca8
def s5_raw : List Nat := chkMkRaw 7 s5_maskYF
def s5_masksTT : List Nat := chkMkMasksTT 7 s5_desc.edges s5_maskYF
def s5_autIdxTbls : List (List Nat) := []
def s5_auts : List (List Nat) := []
def s5_cutSpecs : List CutSpecData := [⟨0,[(1,3)],[1,0,2,3,4],17,[5,6]⟩,⟨20,[],[0,1,3],17,[5,6]⟩,⟨112,[],[2,0],17,[1,3]⟩,⟨31,[],[],17,[5,6]⟩]
def s5_cuts : List CutDefData := chkMkCuts s5_maskYF s5_raw [(1,[.e [(1,3)]]),(3,[.v 4 [38,72],.v 2 [73]]),(4,[.v 5 [70,24],.v 6 [24],.v 4 [4]]),(6,[.v 0 [50,76],.v 1 [76],.v 2 [16],.v 3 [32],.v 4 [64]])]
def s5_cert : CertNode := .branch [3,2,1,0] [[11,11,11,11,3,3,11,11,11,11,11,11,19,19,3,3,19,19,19,19,19,11,11,3,3,11,11,11,11,11,19,3,3,19,19,19,19,19,3,3,27,27,27,27,27,3,3,3,3,3,3,3,3,3,3,3,11,19,12,20,4,3,11,11],[11,11,3,19,19,19,3,20,4,3,4,3,3]] (.nil)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_5 : chkCheckNode s5_maskYF s5_edgePts s5_edgeTT s5_raw s5_masksTT s5_cuts [] s5_auts s5_cert = true := by decide +kernel

-- State #6: n=6 |E|=7 |F|=0 nodes=1 cands=102 wits=103 cuts=6
def s6_desc : StateDesc := ⟨6,[(0,1),(0,2),(1,4),(2,5),(3,4),(3,5),(4,5)],[]⟩
def s6_maskYF : Nat := 0xffffffffffffffff
def s6_edgePts : Nat := 0x1011001040028
def s6_edgeTT : Nat := 0xfffffff8ffeca8a8
def s6_raw : List Nat := chkMkRaw 6 s6_maskYF
def s6_masksTT : List Nat := chkMkMasksTT 6 s6_desc.edges s6_maskYF
def s6_autIdxTbls : List (List Nat) := []
def s6_auts : List (List Nat) := []
def s6_cutSpecs : List CutSpecData := [⟨8,[],[],4,[0,1,2,4,5]⟩,⟨0,[(4,5)],[],18,[0,1,2,3,4,5]⟩,⟨5,[],[1],2,[3,4,5]⟩,⟨44,[],[0],17,[1,4]⟩,⟨7,[],[],2,[3,4,5]⟩,⟨27,[],[],17,[2,5]⟩]
def s6_cuts : List CutDefData := chkMkCuts s6_maskYF s6_raw [(2,[.v 3 [17,32,20]]),(1,[.e [(4,5)]]),(3,[.v 2 [17,32],.v 0 [34]]),(5,[.v 2 [1,32],.v 3 [34],.v 5 [16]]),(4,[.v 1 [9,20,33],.v 0 [20],.v 2 [32]]),(6,[.v 1 [1,20],.v 3 [17,20,32],.v 0 [20],.v 4 [32]])]
def s6_cert : CertNode := .branch [4,0,2,1] [[11,11,19,3,19,3,27,27,27,27,11,11,3,11,3,11,11,11,11,11,3,11,3,11,11,11,11,3,19,3,19,19,19,19,3,3,3,3,3,3,3,19,19,19,19,3,3,3,3,0,11,19,3,20,11,19,3,4,11,3,11,3,19,3]] (.cons 0xffffffffffff0000 (.branch [5,3,1] [[11,3,19,11,3,11,3,4,4,4,12,4,3,11,11,11,3,11,3,11,11,3,11,3,3,3,3,3,3,3,3,3,3,11,3,11,3,5,1]] (.nil)) (.nil))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_6 : chkCheckNode s6_maskYF s6_edgePts s6_edgeTT s6_raw s6_masksTT s6_cuts [] s6_auts s6_cert = true := by decide +kernel

-- State #7: n=7 |E|=8 |F|=0 nodes=0 cands=89 wits=89 cuts=5
def s7_desc : StateDesc := ⟨7,[(0,1),(0,2),(1,3),(2,6),(3,6),(4,5),(4,6),(5,6)],[]⟩
def s7_maskYF : Nat := 0xffffffffffffffffffffffffffffffff
def s7_edgePts : Nat := 0x1000101100001000000000428
def s7_edgeTT : Nat := 0xfffffffffffffff8ffffeca8eca8eca8
def s7_raw : List Nat := chkMkRaw 7 s7_maskYF
def s7_masksTT : List Nat := chkMkMasksTT 7 s7_desc.edges s7_maskYF
def s7_autIdxTbls : List (List Nat) := []
def s7_auts : List (List Nat) := []
def s7_cutSpecs : List CutSpecData := [⟨0,[(0,1)],[0,1,2,3],2,[4,5,6]⟩,⟨0,[(5,6)],[5,4],4,[0,1,2,3,6]⟩,⟨10,[],[0,2],2,[4,5,6]⟩,⟨48,[],[],4,[0,1,2,3,6]⟩,⟨15,[],[],2,[4,5,6]⟩]
def s7_cuts : List CutDefData := chkMkCuts s7_maskYF s7_raw [(1,[.e [(0,1)]]),(1,[.e [(5,6)]]),(3,[.v 3 [38,65],.v 1 [65]]),(3,[.v 4 [41,66],.v 5 [66]]),(5,[.v 2 [25,66,33],.v 0 [34,66],.v 1 [8],.v 3 [64]])]
def s7_cert : CertNode := .branch [4,3,2,1,0] [[11,11,19,3,19,3,27,27,27,27,27,27,11,11,3,11,3,11,11,11,11,11,11,11,3,11,3,11,11,11,11,11,11,3,19,3,19,19,19,19,19,19,3,3,3,3,3,3,3,3,3,19,19,19,19,19,19,3,3,3,3,3,3,35],[35,35,35,35,12,11,19,3,20,4,11,19,3,12,4,11,3,11,11,3,19,19,3,3,4]] (.nil)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_7 : chkCheckNode s7_maskYF s7_edgePts s7_edgeTT s7_raw s7_masksTT s7_cuts [] s7_auts s7_cert = true := by decide +kernel

-- State #8: n=7 |E|=8 |F|=0 nodes=1 cands=135 wits=136 cuts=7
def s8_desc : StateDesc := ⟨7,[(0,1),(0,2),(1,3),(2,5),(3,6),(4,5),(4,6),(5,6)],[]⟩
def s8_maskYF : Nat := 0xffffffffffffffffffffffffffffffff
def s8_edgePts : Nat := 0x1000101000001001000000428
def s8_edgeTT : Nat := 0xffffffffffffffa8fffffcf8eca8eca8
def s8_raw : List Nat := chkMkRaw 7 s8_maskYF
def s8_masksTT : List Nat := chkMkMasksTT 7 s8_desc.edges s8_maskYF
def s8_autIdxTbls : List (List Nat) := []
def s8_auts : List (List Nat) := []
def s8_cutSpecs : List CutSpecData := [⟨0,[(0,1)],[0,1,2,3],2,[4,5,6]⟩,⟨16,[],[],19,[0,1,2,3,5,6]⟩,⟨0,[(5,6)],[],20,[0,1,2,3,4,5,6]⟩,⟨10,[],[0,2],2,[4,5,6]⟩,⟨88,[],[1,0],17,[2,5]⟩,⟨15,[],[],2,[4,5,6]⟩,⟨55,[],[],17,[3,6]⟩]
def s8_cuts : List CutDefData := chkMkCuts s8_maskYF s8_raw [(1,[.e [(0,1)]]),(2,[.v 4 [41,66]]),(1,[.e [(5,6)]]),(3,[.v 3 [22,65,34],.v 1 [33,65]]),(5,[.v 3 [2,64],.v 4 [68],.v 6 [32]]),(5,[.v 2 [25,34,65],.v 0 [34,66],.v 1 [8],.v 3 [64]]),(7,[.v 2 [1,40],.v 4 [41,66],.v 0 [34],.v 1 [40],.v 5 [64]])]
def s8_cert : CertNode := .branch [5,1,3,2,0] [[11,11,19,3,19,3,27,27,27,27,27,27,11,11,3,11,3,11,11,11,11,11,11,11,3,11,3,11,11,11,11,11,11,3,19,3,19,19,19,19,19,19,3,3,3,3,3,3,3,3,3,19,19,19,19,19,19,3,3,3,3,3,3,35],[35,35,35,35,0,11,19,3,20,4,11,19,3,20,4,11,3,11,11,3,19,19,3,3,4]] (.cons 0xffffffffffffffffffffffff00000000 (.branch [6,4,0,2] [[11,3,27,11,3,11,3,19,4,4,4,12,4,4,3,11,11,11,3,11,3,11,11,11,3,11,11,3,3,3,3,3,3,3,3,3,3,3,3,11,3,19,11,3,6,5,1]] (.nil)) (.nil))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_8 : chkCheckNode s8_maskYF s8_edgePts s8_edgeTT s8_raw s8_masksTT s8_cuts [] s8_auts s8_cert = true := by decide +kernel

-- State #9: n=7 |E|=8 |F|=0 nodes=1 cands=165 wits=166 cuts=7
def s9_desc : StateDesc := ⟨7,[(0,1),(0,5),(1,5),(2,3),(2,6),(3,6),(4,5),(4,6)],[]⟩
def s9_maskYF : Nat := 0xffffffffffffffffffffffffffffffff
def s9_edgePts : Nat := 0x101100001000600001008
def s9_edgeTT : Nat := 0xfffffffefffffff8fffffeeef888f888
def s9_raw : List Nat := chkMkRaw 7 s9_maskYF
def s9_masksTT : List Nat := chkMkMasksTT 7 s9_desc.edges s9_maskYF
def s9_autIdxTbls : List (List Nat) := []
def s9_auts : List (List Nat) := []
def s9_cutSpecs : List CutSpecData := [⟨0,[(1,5)],[1,0,5,4],2,[2,3,6]⟩,⟨0,[(3,6)],[3,2,6,4],2,[0,1,5]⟩,⟨16,[],[],3,[0,1,5,2,3,6]⟩,⟨76,[],[4],2,[0,1,5]⟩,⟨49,[],[],2,[2,3,6]⟩,⟨50,[],[],2,[2,3,6]⟩,⟨51,[],[],2,[2,3,6]⟩]
def s9_cuts : List CutDefData := chkMkCuts s9_maskYF s9_raw [(1,[.e [(1,5)]]),(1,[.e [(3,6)]]),(2,[.v 4 [40,66]]),(4,[.v 2 [26,66,40],.v 3 [96],.v 6 [16]]),(5,[.v 0 [2,36,40,66],.v 4 [40,66,36],.v 5 [66]]),(5,[.v 1 [1,40],.v 4 [65],.v 5 [65]]),(5,[.v 0 [22,40,66],.v 1 [40,96],.v 5 [16],.v 4 [64]])]
def s9_cert : CertNode := .branch [6,3,2,0,1] [[19,19,11,11,19,3,3,19,19,19,19,19,19,11,11,19,3,3,19,19,19,19,19,11,11,27,3,3,35,35,35,35,35,11,11,3,3,11,11,11,11,11,11,3,3,11,11,11,11,11,3,3,27,27,27,27,27,3,3,3,3,3,3,3],[3,3,3,3,0,19,12,11,4,3,19,12,11,4,3,19,11,19,3,11,4,3,11,3,3]] (.cons 0xffffffffffffffffffffffff00000000 (.branch [4,3,5,1] [[4,11,19,3,27,11,11,19,3,3,4,4,4,4,4,20,11,19,3,4,4,11,11,19,3,3,27,4,11,19,3,11,3,11,11,11,11,11,3,3,11,11,11,11,3,3,19,19,19,11,11,3,3,19,19,19,11,3,3,3,3,3,3,3],[3,3,3,3,3,3,11,3,12,11,19,3,1]] (.nil)) (.nil))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_9 : chkCheckNode s9_maskYF s9_edgePts s9_edgeTT s9_raw s9_masksTT s9_cuts [] s9_auts s9_cert = true := by decide +kernel

-- State #10: n=7 |E|=8 |F|=0 nodes=1 cands=165 wits=166 cuts=9
def s10_desc : StateDesc := ⟨7,[(0,1),(0,5),(1,6),(2,3),(2,5),(3,6),(4,5),(4,6)],[]⟩
def s10_maskYF : Nat := 0xffffffffffffffffffffffffffffffff
def s10_edgePts : Nat := 0x101040001001200001008
def s10_edgeTT : Nat := 0xfffffffeffffffccfffffafaf888f888
def s10_raw : List Nat := chkMkRaw 7 s10_maskYF
def s10_masksTT : List Nat := chkMkMasksTT 7 s10_desc.edges s10_maskYF
def s10_autIdxTbls : List (List Nat) := []
def s10_auts : List (List Nat) := []
def s10_cutSpecs : List CutSpecData := [⟨0,[(1,6)],[1,0],4,[2,3,5,6,4]⟩,⟨0,[(2,5)],[2,3],4,[0,1,5,6,4]⟩,⟨2,[],[0],4,[2,3,5,6,4]⟩,⟨4,[],[3],4,[0,1,5,6,4]⟩,⟨16,[],[],19,[0,1,5,6,2,3]⟩,⟨3,[],[],4,[2,3,5,6,4]⟩,⟨12,[],[],4,[0,1,5,6,4]⟩,⟨60,[],[0],17,[1,6]⟩,⟨115,[],[],17,[2,3]⟩]
def s10_cuts : List CutDefData := chkMkCuts s10_maskYF s10_raw [(1,[.e [(1,6)]]),(1,[.e [(2,5)]]),(2,[.v 1 [1,68]]),(2,[.v 2 [8,32]]),(2,[.v 4 [42,68]]),(3,[.v 0 [22,40,96],.v 1 [68,96]]),(3,[.v 3 [22,96],.v 2 [96]]),(6,[.v 3 [4,64,68],.v 2 [32],.v 4 [65],.v 5 [65]]),(7,[.v 0 [2,40,34],.v 4 [42,68],.v 1 [64],.v 5 [68],.v 6 [8]])]
def s10_cert : CertNode := .branch [5,6,4,0,1] [[19,11,19,11,19,3,3,19,19,19,19,19,11,19,11,19,3,3,19,19,19,19,19,11,11,11,3,3,11,11,11,11,11,11,27,3,3,35,35,35,35,35,11,3,3,11,11,11,11,11,3,3,27,27,27,27,27,3,3,3,3,3,3,3],[3,3,3,3,0,19,11,12,4,3,19,11,12,4,3,11,19,19,3,11,11,3,4,3,3]] (.cons 0xffffffffffffffffffffffff00000000 (.branch [8,7,2,3] [[11,27,19,3,11,27,11,19,3,3,4,4,4,4,4,13,11,11,3,11,11,11,11,11,3,3,11,11,11,11,3,19,3,27,27,11,11,19,3,3,27,27,11,19,27,3,19,19,11,19,11,3,3,19,19,19,19,3,3,3,3,3,3,3],[3,3,3,3,3,3,11,3,11,27,19,3,1]] (.nil)) (.nil))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_10 : chkCheckNode s10_maskYF s10_edgePts s10_edgeTT s10_raw s10_masksTT s10_cuts [] s10_auts s10_cert = true := by decide +kernel

-- State #11: n=7 |E|=9 |F|=0 nodes=0 cands=102 wits=102 cuts=6
def s11_desc : StateDesc := ⟨7,[(0,1),(0,6),(1,6),(2,3),(2,6),(3,6),(4,5),(4,6),(5,6)],[]⟩
def s11_maskYF : Nat := 0xffffffffffffffffffffffffffffffff
def s11_edgePts : Nat := 0x1000101160001000000001008
def s11_edgeTT : Nat := 0xfffffffffffffffefffff888f888f888
def s11_raw : List Nat := chkMkRaw 7 s11_maskYF
def s11_masksTT : List Nat := chkMkMasksTT 7 s11_desc.edges s11_maskYF
def s11_autIdxTbls : List (List Nat) := []
def s11_auts : List (List Nat) := []
def s11_cutSpecs : List CutSpecData := [⟨0,[(5,6)],[5,4],1,[0,1,2,3,6]⟩,⟨2,[],[0],1,[2,3,4,5,6]⟩,⟨8,[],[2],1,[0,1,4,5,6]⟩,⟨3,[],[],1,[2,3,4,5,6]⟩,⟨12,[],[],1,[0,1,4,5,6]⟩,⟨48,[],[],1,[0,1,2,3,6]⟩]
def s11_cuts : List CutDefData := chkMkCuts s11_maskYF s11_raw [(1,[.e [(5,6)]]),(2,[.v 1 [41,64]]),(2,[.v 3 [36,64]]),(3,[.v 0 [22,64,42],.v 1 [64]]),(3,[.v 2 [26,64,40],.v 3 [64]]),(3,[.v 4 [42,64],.v 5 [64]])]
def s11_cert : CertNode := .branch [3,4,5,1,2,0] [[19,19,35,11,11,27,3,3,43,43,43,43,43,19,19,11,11,19,3,3,19,19,19,19,19,19,11,11,19,3,3,19,19,19,19,19,11,11,27,3,3,35,35,35,35,35,11,11,3,3,11,11,11,11,11,11,3,3,11,11,11,11,11,3],[3,27,27,27,27,27,3,3,3,3,3,3,3,3,3,3,3,20,19,35,11,27,3,19,35,11,27,3,19,11,19,3,11,27,3,11,3,3]] (.nil)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_11 : chkCheckNode s11_maskYF s11_edgePts s11_edgeTT s11_raw s11_masksTT s11_cuts [] s11_auts s11_cert = true := by decide +kernel

-- State #12: n=7 |E|=9 |F|=0 nodes=1 cands=183 wits=184 cuts=8
def s12_desc : StateDesc := ⟨7,[(0,1),(0,5),(1,5),(2,3),(2,6),(3,6),(4,5),(4,6),(5,6)],[]⟩
def s12_maskYF : Nat := 0xffffffffffffffffffffffffffffffff
def s12_edgePts : Nat := 0x1000101100001000600001008
def s12_edgeTT : Nat := 0xfffffffffffffff8fffffeeef888f888
def s12_raw : List Nat := chkMkRaw 7 s12_maskYF
def s12_masksTT : List Nat := chkMkMasksTT 7 s12_desc.edges s12_maskYF
def s12_autIdxTbls : List (List Nat) := []
def s12_auts : List (List Nat) := []
def s12_cutSpecs : List CutSpecData := [⟨2,[],[0],1,[2,3,4,5,6]⟩,⟨8,[],[2],1,[0,1,4,6,5]⟩,⟨16,[],[],0,[0,1,2,3,5,6]⟩,⟨0,[(5,6)],[],21,[0,1,2,3,4,5,6]⟩,⟨3,[],[],1,[2,3,4,5,6]⟩,⟨12,[],[],1,[0,1,4,6,5]⟩,⟨51,[],[],2,[2,3,6]⟩,⟨92,[],[],2,[0,1,5]⟩]
def s12_cuts : List CutDefData := chkMkCuts s12_maskYF s12_raw [(2,[.v 1 [9,40,65]]),(2,[.v 3 [4,36,64]]),(2,[.v 4 [40,66]]),(1,[.e [(5,6)]]),(3,[.v 0 [22,40,66],.v 1 [32]]),(3,[.v 2 [26,64,40],.v 3 [64]]),(6,[.v 0 [2,36,40,66],.v 4 [36,66,40],.v 1 [32],.v 5 [64]]),(6,[.v 2 [8,66,40],.v 3 [64],.v 4 [65],.v 6 [32]])]
def s12_cert : CertNode := .branch [4,5,2,3,0,1] [[19,19,27,11,11,27,3,3,27,27,27,27,27,19,19,11,11,19,3,3,19,19,19,19,19,19,11,11,19,3,3,19,19,19,19,19,11,11,35,3,3,43,43,43,43,43,11,11,3,3,11,11,11,11,11,11,3,3,11,11,11,11,11,3],[3,35,35,35,35,35,3,3,3,3,3,3,3,3,3,3,3,0,19,43,11,35,3,19,43,11,35,3,19,11,19,3,11,35,3,11,3,3]] (.cons 0xffffffffffffffffffffffff00000000 (.branch [6,7,0,1,3] [[27,11,19,3,35,27,11,11,19,3,3,4,4,4,4,4,13,11,19,3,27,27,27,11,11,19,3,3,27,27,11,19,3,11,3,11,11,11,11,11,11,3,3,11,11,11,11,3,3,19,19,19,19,11,11,3,3,19,19,19,11,3,3,3],[3,3,3,3,3,3,3,3,3,3,3,11,3,27,11,19,3,1]] (.nil)) (.nil))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_12 : chkCheckNode s12_maskYF s12_edgePts s12_edgeTT s12_raw s12_masksTT s12_cuts [] s12_auts s12_cert = true := by decide +kernel

-- State #13: n=7 |E|=9 |F|=0 nodes=12 cands=1426 wits=1891 cuts=26
def s13_desc : StateDesc := ⟨7,[(0,1),(0,4),(1,5),(2,4),(2,6),(3,5),(3,6),(4,6),(5,6)],[]⟩
def s13_maskYF : Nat := 0xffffffffffffffffffffffffffffffff
def s13_edgePts : Nat := 0x1000101100000010400120008
def s13_edgeTT : Nat := 0xfffffffffffffff8fffeffccfafa8888
def s13_raw : List Nat := chkMkRaw 7 s13_maskYF
def s13_masksTT : List Nat := chkMkMasksTT 7 s13_desc.edges s13_maskYF
def s13_autIdxTbls : List (List Nat) := chkMkAutIdxTbls 7 [[1,0,3,2,5,4,6]]
def s13_auts : List (List Nat) := chkMkAutMaskTbls s13_autIdxTbls
def s13_cutSpecs : List CutSpecData := [⟨4,[],[],6,[0,1,4,3,5,6]⟩,⟨8,[],[],6,[1,0,5,2,4,6]⟩,⟨0,[(4,6)],[],22,[0,1,2,3,4,5,6]⟩,⟨0,[(5,6)],[],22,[1,0,3,2,5,4,6]⟩,⟨3,[],[],1,[2,4,3,5,6]⟩,⟨17,[(5,6)],[1,2,5],17,[3,6]⟩,⟨20,[(5,6)],[0,1,5],17,[3,6]⟩,⟨84,[],[0,1],17,[3,5]⟩,⟨35,[],[3],2,[2,4,6]⟩,⟨42,[],[0],2,[2,4,6]⟩,⟨21,[],[1],2,[3,5,6]⟩,⟨92,[],[0],17,[1,5]⟩,⟨108,[],[1],17,[0,4]⟩,⟨92,[],[0],17,[1,5]⟩,⟨51,[],[2],17,[3,6]⟩,⟨92,[],[0],17,[1,5]⟩,⟨23,[],[],2,[3,5,6]⟩,⟨23,[],[],2,[3,5,6]⟩,⟨55,[],[],17,[3,6]⟩,⟨55,[],[],17,[3,6]⟩,⟨107,[],[],17,[2,4]⟩,⟨55,[],[],17,[3,6]⟩,⟨110,[],[],17,[0,4]⟩,⟨59,[],[],17,[2,6]⟩,⟨93,[],[],17,[1,5]⟩,⟨124,[],[],17,[0,1]⟩]
def s13_cuts : List CutDefData := chkMkCuts s13_maskYF s13_raw [(2,[.v 2 [26,65]]),(2,[.v 3 [37,65,48]]),(1,[.e [(4,6)]]),(1,[.e [(5,6)]]),(3,[.v 0 [6,48,66],.v 1 [48,36]]),(5,[.e [(5,6)],.v 4 [33],.v 0 [2,66]]),(5,[.e [(5,6)],.v 4 [33],.v 2 [65]]),(6,[.v 2 [65,26,48],.v 4 [],.v 6 [33]]),(5,[.v 0 [66,16,18],.v 1 [48],.v 5 [24]]),(5,[.v 1 [65,48,36],.v 5 [24],.v 3 [64]]),(5,[.v 2 [65,26],.v 4 [33],.v 0 [2]]),(7,[.v 3 [37,66,48,65],.v 2 [65],.v 6 [48],.v 4 [33]]),(7,[.v 3 [36,48],.v 2 [18,65,48,66],.v 6 [48],.v 5 [18]]),(7,[.v 3 [37,48,65,66],.v 4 [64],.v 2 [64],.v 6 [33]]),(7,[.v 4 [33,36],.v 0 [6],.v 1 [32],.v 5 [8]]),(7,[.v 6 [9,37,6,16],.v 2 [26,48],.v 3 [32],.v 4 [33]]),(6,[.v 0 [2,24,48],.v 2 [48,26,64],.v 1 [32],.v 4 [64]]),(6,[.v 1 [48,1],.v 2 [65],.v 0 [16],.v 4 [64]]),(8,[.v 0 [2,24,48],.v 2 [48,66,24],.v 1 [32],.v 5 [24],.v 4 [64]]),(8,[.v 1 [1,36,33],.v 2 [65,48,24],.v 5 [65],.v 0 [24],.v 4 [64]]),(8,[.v 1 [32,65,33],.v 5 [24],.v 3 [64],.v 6 [4],.v 0 [16]]),(8,[.v 2 [],.v 0 [2,48],.v 1 [32],.v 5 [24],.v 4 [64]]),(8,[.v 2 [16,66,48],.v 1 [48,1],.v 3 [32],.v 5 [64],.v 6 [16]]),(8,[.v 4 [33,36],.v 0 [2],.v 1 [32],.v 3 [32],.v 5 [64]]),(8,[.v 4 [36,33],.v 2 [64],.v 6 [33],.v 3 [32],.v 0 [2]]),(8,[.v 6 [],.v 2 [26,48],.v 3 [32],.v 5 [18],.v 4 [1]])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
def s13_cert : CertNode := .branch [0,4,2,1,3] [[19,2,2,2,2,2,2,2,35,2,2,2,2,19,19,3,3,19,11,11,2,19,19,19,19,2,3,3,2,2,2,2,27,27,2,2,2,3,2,2,2,2,27,2,2,2,3,3,3,3,2,3,2,3,3,3,3,3,3,2,3,3,3,11],[2,2,12,2,12,2,11,11,2,2,11,11,11,2,11,2,11,2,0,2,3,2,11,0,2,2,2,2,27,3,12,11,3,2,2,3,3,11]] (.cons 0xffffffffffffffffffff0000ffff0000 (.branch [16,1,2,3,17] [[11,4,3,19,11,11,4,4,35,3,3,27,11,4,35,3,11,3,11,11,11,11,11,11,3,3,11,11,11,11,3,3,27,19,11,11,35,3,3,4,4,4,4,4,36,3,3,3,3,3,3,3,3,3,3,3,3,3,11,35,3,0,11,35],[3,0,1]] (.cons 0xffffffffffffffffffffffffffff0000 (.branch [19,13,2,3] [[11,3,11,11,4,11,11,27,19,4,4,3,6,3,11,11,11,11,11,11,3,4,4,11,4,27,19,11,11,3,12,3,4,4,4,11,3,4,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,5,11,4,27,19,11,11],[4,4,3,3,14,5,11,4,3,3,3,6,1]] (.nil)) (.cons 0xffffffffffffffffffffffff00000000 (.branch [22,11,4,2,3] [[3,11,3,11,11,11,11,11,11,1,3,3,11,11,11,11,11,11,11,11,3,3,3,3,3,3,3,3,3,3,1,3,3,3,3,3,3,3,3,11,4,3,19,11,3,4,19,19,1,1,11,3,4,19,11,3,4,27,11,3,19,27,11,11],[3,3,4,19,19,27,11,3,4,19,3,11,11,0,11,11,35,27,3,3,4,19,19,11,11,11,11,11,11,3,3,3,3,3,3,3,3,1,3,3,3,3,3,3,3,3,4,11,3,19,4,35,27,11,11,3,3,19,19,4,4,11,3,19],[3,19,6,3,19,19,6,3,4,19,6,1]] (.cons 0xfff0fff0fff0fff0fff0ff00f0f00000 (.branch [12,22,4,2,3] [[1,3,1,1,1,11,1,11,11,1,11,11,11,1,3,1,11,11,11,11,11,1,11,11,1,1,1,3,4,4,4,1,19,3,35,27,1,4,19,19,4,4,4,1,4,4,1,1,1,1,4,1,4,4,1,19,35,27,1,1,4,19,19,4],[4,1,1,4,4,1,3,1,1,3,1,3,3,1,3,3,3,1,1,3,3,3,3,3,3,1,3,3,1,1,11,4,1,4,11,4,19,35,27,1,12,19,19,4,4,4,1,4,4,1,1,3,3,4,3,4,4,3,19,35,27,3,3,4],[19,19,4,4,3,3,4,4,4,3,1,3,3,4,3,4,3,1,3,19,3,35,27,1,3,11,4,19,19,4,4,3,4,4,3,3,1,11,11,3,1,4,11,4,3,19,35,27,3,3,1,4,19,19,4,4,3,4,4,1,1,3,3,1],[3,3,1,3,3,3,3,3,3,3,3,3,3,3,3,1,3,3,1,11,11,1,11,11,11,1,11,11,11,3,3,11,11,11,11,11,11,1,11,11,4,4,4,11,4,19,3,35,27,12,19,19,4,4,4,4,4,3,3,3,3,3,3,11],[11,11,11,11,11,1,3,12,11,19,3,11,12,19,19,1,1,3,11,12,19,3,11,12,27,3,11,19,27,3,3,11,11,12,19,19,27,3,11,12,19,1,3,1,3,3,3,3,3,3,1,11,11,11,11,11,1,12,12,35,27,12,12,11],[19,6,11,19,19,6,11,12,19,6,1]] (.nil)) (.nil))) (.nil)))) (.cons 0xffffffffffff0000ffffffffffff0000 (.branch [10,8] [[2,3,2,11,2,2,3,3,2,11,11,2,13,2,0,2,0,3,2,2,2,4,2,3,3,2,2,2,2,13,3,2,2,3,3,2,3,2,2,3,3,3,3,3,2,2,3,3,11,2,4,2,2,3,3,11,2,2,12,2,3,11,2,11],[2,2,3,3,2,11,11,2,2,11,2,2,3,11,0,2,3,2,11,2,3,2,11,11,2,0,2,3,2,11,1]] (.cons 0xfffffffffffff0f0f0f0f0f0f0f0f0f0 (.branch [15,14,9,1,6] [[3,27,19,12,3,27,3,19,11,19,3,11,11,27,1,19,37,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,3,3,1,27,3,19,4,1,3,27,3,3,19,11,19,11,27,3,19,4,3,11,11,11,3,3,11,3,11,11,11],[11,11,11,3,11,11,27,19,12,4,3,27,19,11,19,3,4,11,27,19,12,3,3,1,27,3,19,3,3,3,3,27,4,27,11,19,11,19,3,0,3,3,3,3]] (.cons 0xffffffffffffffffffff0000ffff0000 (.branch [21,11,6,9,15] [[4,3,11,4,11,27,4,3,11,11,27,4,27,3,36,3,36,36,21,3,4,11,3,4,1,11,3,27,4,1,11,11,3,3,27,4,27,1,20,3,20,20,4,11,1,4,1,11,27,4,11,11,1,27,4,27,3,20,1,20,1,20,20,3],[3,3,3,1,3,1,3,3,3,3,1,3,3,1,3,3,3,3,3,3,3,3,4,11,3,4,35,4,4,4,35,11,3,27,19,35,11,11,3,3,27,27,35,4,4,3,4,11,3,3,3,11,27,11,11,3,27,27,1,1,11,3,27,4],[11,3,4,1,11,3,27,4,1,11,11,3,3,27,4,27,1,11,3,27,4,3,11,11,11,11,11,11,11,11,3,11,11,11,11,11,11,3,3,11,11,11,11,11,3,11,11,3,1,1,3,3,1,3,3,3,3,3,3,3,3,3,3,3],[3,3,3,3,3,3,4,35,4,4,4,35,11,3,27,19,35,11,11,3,3,27,27,35,4,11,3,27,11,27,35,11,27,27,35,11,27,4,35,35,1]] (.nil)) (.nil))) (.cons 0xffffffffffffaaaaaaaaaaaaaaaaaaaa (.branch [24,20,10,1,5] [[11,27,19,11,27,27,19,3,11,11,5,3,3,27,37,11,1,3,11,27,19,11,1,27,27,19,3,11,3,11,5,14,27,19,11,1,1,11,27,19,11,3,1,27,27,19,3,11,3,11,3,27,12,11,3,3,3,3,3,3,3,3,3,3],[3,3,3,3,3,3,3,3,3,11,11,11,11,11,11,11,3,11,11,11,3,11,3,11,11,11,11,11,27,19,11,21,27,27,19,3,11,5,21,3,27,19,11,27,19,36,36,36,1,27,19,11,5,27,19,5,27,19,11,21,27,3,11,3],[11,5,0,27,19,11,5]] (.cons 0xffffffffffffffffffff0000ffff0000 (.branch [7,5,9,1] [[3,27,3,19,27,3,19,27,27,3,3,19,19,4,5,1,27,3,19,1,3,11,27,12,11,1,19,27,3,19,11,1,27,27,3,3,19,11,19,1,12,12,12,11,3,27,12,19,27,3,19,27,27,3,3,19,19,4,4,1,12,12,12,1],[3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,3,3,3,3,3,3,3,3,4,27,12,1,11,19,1,27,3,19,11,1,27,27,3,3,19,19,4,4,12,12,12,27,3,19,4,27,19,27,27,3,19,19,1,1,27],[3,19,4,27,3,4,1,19,27,3,19,4,1,27,27,3,3,19,4,19,1,27,3,19,4,3,27,27,27,27,27,19,27,27,27,3,19,27,27,11,27,27,3,3,19,27,19,27,27,3,27,27,3,13,3,20,12,19,3,12,3,3,13,3],[11,12,27,27,19,12,19,3,3,3,3,3,3,1,20,19,1,27,3,19,11,1,27,27,3,3,19,19,4,5,27,3,19,19,5,27,19,20,27,19,19,20,27,19,5,20,5,1]] (.nil)) (.nil))) (.cons 0xffffffffffffffffffffffffffff0000 (.branch [23,12,4,15] [[11,2,2,2,2,2,2,2,2,3,2,3,2,2,2,2,2,11,11,2,2,12,19,27,11,12,19,27,2,3,11,2,20,3,19,27,2,3,2,12,12,19,2,2,12,2,2,3,2,2,27,3,3,2,2,20,2,12,19,19,2,19,19,2],[3,2,2,19,3,2,19,19,2,2,19,2,19,2,19,1]] (.nil)) (.cons 0xffffffffffffffffffff0000ffff0000 (.branch [18,11,9,2] [[3,4,11,3,4,11,19,3,4,27,11,11,1,19,3,3,4,4,4,4,12,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,11,4,11,19,11,11,4,19,3,1,1,11,4,19,3,11,4,3,11,4,19,3,1],[11,11,4,4,19,3,3,1,11,4,19,3,11,3,11,11,11,11,3,11,11,11,11,11,11,11,3,3,11,11,11,11,3,3,0,11,19,3,4,20,27,11,11,19,3,3,4,4,4,4,4,12,3,3,3,3,3,3,3,3,3,3,3,3],[3,3,3,3,3,11,19,20,11,19,3,20,11,19,3,20,13,1]] (.cons 0xfffffffffffff0f0f0f00000f0f00000 (.branch [25,5,9,1,6] [[1,12,27,1,12,27,19,12,3,27,1,19,12,19,3,4,1,4,1,4,12,1,1,3,3,3,1,3,3,1,3,3,3,3,3,1,3,3,3,3,3,3,1,3,3,1,3,4,27,3,4,27,3,19,4,1,3,27,3,3,19,4,19,1],[4,3,4,4,12,1,27,3,12,1,27,19,12,1,3,27,3,19,12,19,3,4,4,3,4,12,12,3,27,13,27,19,13,3,3,27,19,12,19,3,4,3,4,4,37,3,3,3,3,3,3,1,27,4,3,3,1,3,3,3,27,19,3,27],[19,19,3,27,19,13,3,3,1]] (.nil)) (.nil))) (.nil)))))) (.nil)))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_13 : chkCheckNode s13_maskYF s13_edgePts s13_edgeTT s13_raw s13_masksTT s13_cuts [] s13_auts s13_cert = true := by decide +kernel

-- State #14: n=7 |E|=9 |F|=0 nodes=36 cands=7986 wits=12192 cuts=59
def s14_desc : StateDesc := ⟨7,[(0,3),(0,4),(1,3),(1,5),(2,3),(2,6),(4,5),(4,6),(5,6)],[]⟩
def s14_maskYF : Nat := 0xffffffffffffffffffffffffffffffff
def s14_edgePts : Nat := 0x1000100100001000400021600
def s14_edgeTT : Nat := 0xfffffffffffffef0fffffeccfeaafe00
def s14_raw : List Nat := chkMkRaw 7 s14_maskYF
def s14_masksTT : List Nat := chkMkMasksTT 7 s14_desc.edges s14_maskYF
def s14_autIdxTbls : List (List Nat) := chkMkAutIdxTbls 7 [[0,2,1,3,4,6,5],[1,0,2,3,5,4,6],[1,2,0,3,5,6,4],[2,0,1,3,6,4,5],[2,1,0,3,6,5,4]]
def s14_auts : List (List Nat) := chkMkAutMaskTbls s14_autIdxTbls
def s14_cutSpecs : List CutSpecData := [⟨8,[],[0,1,2],2,[4,5,6]⟩,⟨32,[],[1],4,[0,3,4,2,6]⟩,⟨64,[],[2],4,[0,3,4,1,5]⟩,⟨1,[],[],6,[3,1,2,4,5,6]⟩,⟨2,[],[],6,[3,0,2,5,4,6]⟩,⟨4,[],[],6,[3,0,1,6,4,5]⟩,⟨0,[(4,5)],[],23,[0,1,2,4,5,3,6]⟩,⟨0,[(4,6)],[],23,[0,2,1,4,6,3,5]⟩,⟨0,[(5,6)],[],23,[1,2,0,5,6,3,4]⟩,⟨48,[],[0,1,3],17,[2,6]⟩,⟨48,[],[0,1,3],17,[2,6]⟩,⟨80,[],[0,2,3],17,[1,5]⟩,⟨24,[],[1,2],17,[5,6]⟩,⟨24,[],[1,2],17,[5,6]⟩,⟨40,[],[0,2],17,[4,6]⟩,⟨17,[],[],4,[1,3,5,2,6]⟩,⟨34,[],[],4,[0,3,4,2,6]⟩,⟨17,[],[],4,[1,3,5,2,6]⟩,⟨25,[],[1,2],17,[5,6]⟩,⟨81,[],[2,3],17,[1,5]⟩,⟨112,[],[0,1],17,[2,3]⟩,⟨112,[],[0,1],17,[2,3]⟩,⟨13,[],[1],2,[4,5,6]⟩,⟨14,[],[0],2,[4,5,6]⟩,⟨14,[],[0],2,[4,5,6]⟩,⟨51,[],[3],17,[2,6]⟩,⟨29,[],[1],17,[5,6]⟩,⟨102,[],[3],17,[0,4]⟩,⟨102,[],[3],17,[0,4]⟩,⟨43,[],[2],17,[4,6]⟩,⟨78,[],[0],17,[4,5]⟩,⟨116,[],[0],17,[1,3]⟩,⟨51,[],[3],17,[2,6]⟩,⟨106,[],[],17,[0,4]⟩,⟨92,[],[],17,[1,5]⟩,⟨92,[],[],17,[1,5]⟩,⟨92,[],[],17,[1,5]⟩,⟨89,[],[],17,[1,5]⟩,⟨15,[],[],2,[4,5,6]⟩,⟨15,[],[],2,[4,5,6]⟩,⟨59,[],[],17,[2,6]⟩,⟨93,[],[],17,[1,5]⟩,⟨93,[],[],17,[1,5]⟩,⟨93,[],[],17,[1,5]⟩,⟨93,[],[],17,[1,5]⟩,⟨59,[],[],17,[2,6]⟩,⟨115,[],[],17,[2,3]⟩,⟨59,[],[],17,[2,6]⟩,⟨110,[],[],17,[0,4]⟩,⟨110,[],[],17,[0,4]⟩,⟨110,[],[],17,[0,4]⟩,⟨93,[],[],17,[1,5]⟩,⟨79,[],[],17,[4,5]⟩,⟨93,[],[],17,[1,5]⟩,⟨59,[],[],17,[2,6]⟩,⟨115,[],[],17,[2,3]⟩,⟨93,[],[],17,[1,5]⟩,⟨93,[],[],17,[1,5]⟩,⟨93,[],[],17,[1,5]⟩]
def s14_cuts : List CutDefData := chkMkCuts s14_maskYF s14_raw [(3,[.v 3 [18,37,65]]),(3,[.v 5 [24,22,72]]),(3,[.v 6 [40,7,24,20,33]]),(2,[.v 0 [72,22]]),(2,[.v 1 [24,32,8]]),(2,[.v 2 [24,64]]),(1,[.e [(4,5)]]),(1,[.e [(4,6)]]),(1,[.e [(5,6)]]),(5,[.v 4 [40,72,32],.v 5 [2,72]]),(5,[.v 5 [16],.v 4 [65]]),(5,[.v 6 [20,16],.v 4 [40,33]]),(6,[.v 3 [20,18],.v 4 [37,3,32]]),(6,[.v 4 [40,72],.v 3 []]),(6,[.v 5 [24,72],.v 3 []]),(4,[.v 0 [72,18],.v 4 [32]]),(4,[.v 1 [72,32,24,40],.v 5 [72,16,64]]),(4,[.v 4 [40,37,72],.v 0 [8]]),(6,[.v 0 [8],.v 3 [18],.v 4 [36,66]]),(6,[.v 0 [8,16,40,72],.v 4 [],.v 6 [36]]),(6,[.v 4 [],.v 5 [67,72],.v 6 [6]]),(6,[.v 5 [24,72],.v 6 [24],.v 4 []]),(5,[.v 0 [40,18],.v 2 [40,64],.v 3 [18]]),(5,[.v 1 [37,8,24],.v 2 [65],.v 3 [65]]),(5,[.v 2 [64,24,72],.v 1 [33],.v 3 []]),(7,[.v 0 [40,16],.v 1 [40,32,8],.v 4 [40],.v 5 [72]]),(7,[.v 0 [],.v 2 [],.v 4 [40],.v 3 []]),(7,[.v 1 [37,72,24],.v 2 [64],.v 5 [24],.v 6 [24]]),(7,[.v 1 [32,8,24],.v 2 [64,24,40,72],.v 6 [24,40],.v 5 [24]]),(7,[.v 1 [72,37,24,40],.v 5 [72,16],.v 0 [20],.v 3 [20]]),(7,[.v 2 [67,24,40,72],.v 1 [32],.v 6 [24],.v 3 []]),(7,[.v 2 [],.v 6 [24],.v 4 [40],.v 5 []]),(7,[.v 4 [],.v 1 [33,72,40],.v 0 [40],.v 5 [72]]),(8,[.v 1 [32,8,24],.v 5 [24],.v 3 [65],.v 6 [16,5]]),(8,[.v 2 [8],.v 3 [18],.v 4 [3,33],.v 6 [32]]),(8,[.v 2 [65,40,72],.v 6 [32],.v 3 [18],.v 4 [1]]),(8,[.v 6 [4,32],.v 2 [40],.v 3 [18],.v 4 [3]]),(8,[.v 6 [],.v 3 [1,18],.v 0 [16],.v 4 [32]]),(6,[.v 0 [],.v 2 [64,24,72],.v 3 [],.v 1 [32]]),(6,[.v 1 [32,72,40],.v 0 [8],.v 3 [20],.v 2 [64]]),(8,[.v 0 [16,72,24,40],.v 1 [36,24,40,72],.v 5 [24,72],.v 3 [20],.v 4 [64]]),(8,[.v 0 [40,16],.v 2 [8],.v 3 [18],.v 4 [66],.v 6 [32]]),(8,[.v 0 [],.v 2 [],.v 4 [40],.v 3 [],.v 6 [32]]),(8,[.v 0 [22,72,8,24],.v 2 [66,24,72,8],.v 6 [40,24],.v 3 [18],.v 4 [32]]),(8,[.v 0 [20,72,24],.v 6 [4],.v 2 [24,8],.v 3 [18],.v 4 [32]]),(8,[.v 1 [8,36,40],.v 0 [16,40,24],.v 4 [40],.v 3 [36],.v 5 [64]]),(8,[.v 1 [8,72,32],.v 0 [8],.v 4 [72],.v 5 [72],.v 6 [4]]),(8,[.v 1 [],.v 0 [20,72,40,24],.v 5 [24],.v 3 [20],.v 4 [64]]),(8,[.v 1 [8,37,72],.v 2 [8,64,40],.v 3 [65,33],.v 6 [33],.v 5 [16]]),(8,[.v 1 [],.v 2 [],.v 5 [24],.v 3 [],.v 6 [16]]),(8,[.v 1 [33,24],.v 6 [24,4],.v 2 [8],.v 3 [33],.v 5 [16]]),(8,[.v 2 [64,8,72],.v 0 [18,72,40,24],.v 6 [24,40],.v 3 [18],.v 4 [32]]),(8,[.v 2 [],.v 1 [33,24,72,40],.v 6 [40],.v 3 [],.v 0 [16]]),(8,[.v 2 [],.v 6 [],.v 0 [40,16],.v 3 [18],.v 4 [32]]),(8,[.v 4 [72,40],.v 1 [33,8,40],.v 0 [40],.v 3 [36],.v 5 [64]]),(8,[.v 4 [],.v 1 [37,8,40],.v 0 [72,8,40],.v 5 [72],.v 6 [4]]),(8,[.v 4 [40,72],.v 6 [40,4],.v 0 [8,40],.v 2 [40],.v 3 [2]]),(8,[.v 6 [6,33],.v 0 [8,20,40],.v 2 [24,40],.v 3 [18],.v 4 [32]]),(8,[.v 6 [37,22,4],.v 2 [],.v 0 [40],.v 3 [2],.v 4 [32]])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
def s14_cert : CertNode := .branch [3,4,6,7,8] [[2,2,2,2,2,2,2,2,35,2,2,2,2,19,2,2,11,11,2,2,2,2,2,27,2,2,2,2,2,3,3,2,19,2,2,19,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,2,2,11,2,2,2,3],[3,2,2,11,2,11,3,2,2,3,2,3,2,2,3,2,2,2,2,2,2,2,2,0,2,2,2,2,0,2,11,3,2,2,3,2,2,3]] (.cons 0xffffffffffff0000ffffffffffff0000 (.branch [15,5,6,1] [[2,3,19,11,11,2,2,3,3,2,27,0,0,2,0,3,2,4,2,2,2,2,3,2,2,27,2,2,3,2,3,3,3,3,2,3,3,3,2,3,3,2,11,11,2,3,0,0,11,2,3,19,11,2,2,3,3,2,0,0,11,2,3,1]] (.cons 0xffffffffffffff00ff00ff00ff00ff00 (.branch [43,6,27] [[4,2,3,2,3,11,4,4,2,2,3,3,2,21,1,4,2,3,4,2,3,2,3,11,4,4,2,2,3,3,2,5,1,4,2,3,1,2,2,2,2,2,1,2,2,2,2,2,2,2,21,2,2,2,2,4,19,3,19,3,1,11,4,4],[19,19,3,3,2,5,4,19,3,2,3,4,2,3,4,2,4,11,4,2,2,3,3,4,2,4,2,20,3,2,2,2,2,2,19,2,2,2,2,3,2,2,2,19,2,19,3,3,3,3,2,3,3,3,3,2,3,3,3,2,3,3,2,2],[3,6,11,4,2,3,5,2,6,4,2,3,1,2,3,5,6,11,4,2,2,3,3,2,5,5,4,2,3]] (.nil)) (.cons 0xfffffffffffff0f0f0f0f0f0f0f0f0f0 (.branch [44,6,5,2] [[19,2,3,11,1,19,2,2,3,3,2,5,5,1,2,3,19,2,3,19,11,19,2,2,3,3,2,27,0,1,2,27,1,2,2,2,1,2,2,2,2,2,2,2,5,2,2,2,2,5,5,3,1,11,19,19,5,5,3,3,2,5,19,5],[3,19,2,3,19,2,27,11,19,2,2,3,3,19,2,5,2,0,2,3,19,11,2,2,3,3,2,5,5,2,3,27,1,2,3,19,27,6,19,11,19,2,2,3,3,2,27,0,1,2,3]] (.cons 0xfffffffffffffff0ff00ff00ff00ff00 (.branch [44,28,6,9] [[2,3,2,3,12,19,2,2,3,3,2,5,1,2,0,1,1,2,2,2,1,2,2,2,1,2,2,2,2,2,2,2,5,2,2,2,2,1,27,11,3,1,27,11,3,1,19,27,27,11,11,3,3,2,27,27,27,27,1,2,3,4,2,3],[19,1,4,2,2,3,3,2,5,4,1,2,28,1,2,3,12,2,3,19,1,12,2,2,3,3,2,27,4,1,2,3,1,2,3,1,2,3,4,19,1,2,2,3,3,2,4,1,1,2,3,1,2,2,2,1,2,2,2,1,2,2,2,2],[2,2,2,27,2,2,2,2,27,11,3,1,27,11,3,1,19,27,27,11,11,3,3,2,27,27,11,3,2,3,1,1,2,27,1,2,3,12,2,27,19,2,2,3,3,1,2,12,4,2,12,3,2,2,2,11,2,2,2,2,2,2,2,11],[2,2,2,2,3,2,2,2,11,2,11,3,3,2,3,3,3,3,3,3,3,2,3,3,3,3,2,3,3,3,2,3,3,2,2,3,6,19,2,3,2,27,2,3,1,1,1,2,3,4,19,1,2,2,3,3,2,4,1,1,2,3]] (.cons 0xfffffffffffffafafaaafaaafaaafaaa (.branch [53,27,6] [[4,4,1,1,1,11,3,1,11,4,4,19,1,11,11,4,3,4,4,1,1,4,3,5,5,11,11,5,5,19,11,11,5,5,5,1,5,1,1,1,5,4,3,1,1,3,11,4,1,4,11,4,1,19,3,3,11,11,5,4,5,4,3,5],[4,1,1,4,3,1,1,3,11,4,1,4,11,1,1,19,3,3,11,11,1,4,5,4,3,5,4,5,3,1,1,11,3,3,11,1,19,1,3,11,11,5,3,5,5,3,1,5,3,3,4,1,11,1,11,3,3,19,11,11,4,1,4,4],[1,11,1,1,4,4,3,1,1,3,11,4,1,4,11,4,1,19,3,3,11,11,4,4,4,4,3,11,4,1,4,3,1,1,3,11,4,1,4,11,1,1,19,3,3,11,11,1,4,4,4,3,4,4,4,3,1,1,11,3,3,11,1,19],[1,3,11,11,4,3,4,4,3,1,11,3,4,5,3,3,4,3,11,5,5,3,3,3,11,19,3,3,11,11,5,4,5,5,5,3,11,3,4,1,1,1,11,4,1,11,4,4,19,1,11,11,4,4,4,4,1,1,4,3,1,5,3,1],[1,3,11,5,1,4,11,4,1,19,3,3,11,11,4,5,5,5,3,11,4,5,3,4,4,4,5,4,5,3,11,5,5,4,4,4,4,4,4,11,4,19,3,3,11,11,5,4,5,5,3,5,4,3,1,4,4,3,5,1,5,5,3,11],[3,1,4,4,1,3,11,5,5,4,4,19,3,11,11,5,1,5,5,3,5,4,3,3,1,1,1,3,3,3,3,1,1,3,3,1,3,3,3,3,3,3,3,3,3,3,1,3,3,3,3,3,11,5,11,5,19,11,11,5,5,5,11,11],[11,1,4,1,3,3,1,11,4,1,11,4,4,19,1,11,11,4,4,4,4,1,1,11,4,1,11,11,11,4,11,5,6,19,11,5,13,6,11,5,1,1,1,11,4,4,19,1,11,11,4,4,4,4,1,1,11,4]] (.nil)) (.nil))) (.cons 0xffaaffaaffaafaaafaaafaaafaaafaaa (.branch [58,23,17,6,0] [[4,19,4,3,4,19,3,11,4,4,3,3,19,3,11,11,19,1,3,4,19,11,1,35,4,4,3,4,19,35,4,3,11,3,3,19,3,35,11,11,35,3,19,35,4,11,19,19,19,19,19,19,19,19,3,11,3,3,19,19,19,11,11,19],[19,19,19,19,19,35,35,35,19,35,3,11,35,35,3,3,27,35,11,11,19,35,35,35,35,35,1,4,3,4,19,3,11,4,4,3,3,19,3,11,11,19,35,3,4,19,11,3,4,3,4,19,4,3,11,5,3,3,19,3,11,11,3,5],[19,35,4,11,35,11,4,19,1,35,11,11,19,35,19,19,35,1,11,4,35,3,3,3,27,35,11,11,19,35,3,3,0,1,3,3,1,35,11,4,1,19,3,35,11,11,19,35,19,35,3,11,4,19,11,19,1,19,3,19,11,11,19,19],[19,19,3,19,19,3,11,35,3,3,27,35,11,35,35,35,35,1,11,4,4,19,11,11,19,35,4,19,35,11,4,3,1,3,3,3,3,35,4,27,35,11,11,19,35,3,3,35,1,3,3]] (.cons 0xfffffffffffffff0ff00ff00ff00ff00 (.branch [37,1,3] [[3,3,3,3,4,3,11,4,3,4,19,19,4,3,11,4,19,3,4,19,4,3,3,4,3,11,4,19,3,4,4,4,4,1,3,3,3,4,1,11,4,4,3,19,4,4,1,11,4,3,4,19,4,3,3,4,1,11,4,19,3,1,4,4],[4,3,3,3,3,4,1,11,4,4,1,19,19,4,1,11,4,3,4,19,4,3,3,4,1,11,4,19,1,1,4,4,4,1,4,3,19,19,3,3,4,19,4,4,11,4,19,3,4,4,1,4,3,1,1,3,11,11,3,3,11,3,3,3],[1,3,11,11,1,11,3,3,11,11,11,11,11,3,3,11,11,1,3,4,19,3,3,3,3,3,3,1,3,4,19,1,4,3,3,11,4,3,19,4,3,3,4,19,1,4,19,3,3,19,3,3,3,3,4,3,4,1,3,11,4,19,19,4],[11,3,1,4,19,1,4,19,4,19,19,4,4,4,4,4,19,11,1,4,11,4,19,19,11,11,3,1,4,19,1,3,3,1,3,3,3,1,3,1,3,3,3,3,1,3,3,3,3,3,3,1,1,3,3,1,11,11,11,11,11,11,11,11],[11,1,11,11,11,1,11,3,11,11,11,11,11,11,3,11,11,11,4,4,19,4,4,19,4,4,4,1,4,4,19,1,11,3,4,11,4,19,19,11,3,4,4,19,4,3,4,4,3,3,1,1,11,4,1,4,19,4,3,3,4,11,4,19],[3,1,4,4,3,4,3,19,4,4,4,4,4,4,4,3,11,4,4,4,3,4,19,4,3,3,4,3,4,11,19,19,3,4,4,4,19,1,19,19,19,19,3,11,19,1,19,3,19,19,19,3,3,19,3,3,11,19,19,3,19,19,19,19],[19,19,19,4,19,4,11,11,19,11,4,4,19,1,3,3,3,1,3,1,1,1,3,3,3,3,1,3,3,3,3,3,3,1,1,3,3]] (.nil)) (.nil))) (.cons 0xffffffffffffffffff00ff00ff00ff00 (.branch [44,33,6] [[2,3,2,3,5,19,2,2,3,3,2,5,4,2,14,1,1,2,2,2,1,2,2,2,1,2,2,2,2,2,2,2,12,2,2,2,2,1,4,11,3,1,4,11,3,1,19,4,4,11,11,3,3,2,4,4,5,14,1,2,3,4,2,3],[19,1,4,2,2,3,3,2,12,4,1,2,14,1,2,3,5,2,3,19,1,5,2,2,3,3,2,12,4,1,2,3,1,2,2,2,1,2,2,2,1,2,2,2,2,2,2,2,12,2,2,2,2,5,11,3,1,5,11,3,1,19,4,5],[11,11,3,3,2,4,5,11,3,2,3,1,1,2,5,1,2,3,5,2,4,19,2,2,3,3,1,2,5,4,2,14,3,2,2,2,11,2,2,2,2,2,2,2,11,2,2,2,2,3,2,2,2,11,2,11,3,3,2,3,3,3,3,3],[3,3,2,3,3,3,3,2,3,3,3,2,3,3,2,2,3,6,19,2,3,2,6,2,3,4,19,2,4,1]] (.nil)) (.nil))))) (.cons 0xffffffffffffaaaaaaaaaaaaaaaaaaaa (.branch [57,48,6,10] [[4,11,19,3,4,11,11,4,3,4,27,4,4,11,1,3,3,3,1,3,3,3,3,3,3,3,3,3,3,3,3,1,1,27,11,3,1,19,3,27,11,11,3,27,27,27,27,11,3,4,3,11,3,19,3,4,11,11,4,28,4,4,4,4],[3,3,11,4,4,3,3,19,3,4,11,11,4,13,4,4,4,4,11,4,19,3,12,11,11,3,4,4,4,4,11,3,3,3,3,3,3,1,11,3,3,12,11,3,13,12,11,4,19,12,11,11,28,13,3,28,13,3,3,3]] (.nil)) (.cons 0xffffffffffffffffffffffffffff0000 (.branch [43,4] [[2,3,4,2,3,4,2,4,4,4,2,2,3,3,2,4,4,2,3,3,2,2,2,11,2,2,2,2,3,2,2,11,2,2,3,3,3,2,3,3,3,3,2,3,3,3,2,3,3,2,4,2,3,6,4,2,3,1]] (.nil)) (.cons 0xffffffffffffff00ffffffffffffff00 (.branch [51,50,6,3] [[3,2,27,2,27,19,3,3,2,2,27,27,2,12,12,3,2,27,2,3,3,2,3,3,2,3,3,3,2,2,3,3,3,2,3,2,3,11,2,2,2,2,5,2,2,2,27,2,2,2,11,2,2,11,12,11,27,2,12,19,3,3,2,11],[27,2,27,27,27,2,3,12,3,2,27,12,1,19,3,2,2,27,27,2,12,12,3,2,27]] (.nil)) (.cons 0xffffffffffffffffffff0000ffff0000 (.branch [43,16,6,1,11] [[3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,35,11,35,4,11,11,3,1,1,36,4,11,3,27,3,19,11,3,19,35,4,11,11,3,3,19,1,27,27,27,36,3,35,11,3,35,27,35,19,4,11,11,3,3,27,35,4],[4,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,11,27,4,11,11,3,27,36,4,11,3,27,0,1]] (.cons 0xffffffffffffffffffffffff00000000 (.branch [48,20,19] [[4,3,4,11,3,19,4,4,19,4,3,19,4,4,11,11,4,3,3,11,19,4,11,4,13,4,3,1,3,11,1,11,3,19,11,4,3,3,11,19,1,1,5,4,3,19,3,4,3,11,4,19,3,19,4,4,3,3,11,19,1,1,1,12],[21,12,12,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,4,11,1,4,19,11,11,4,4,3,11,19,1,1,12,4,3,19,11,3,11,1,11,11,1,3,11,1,11,11,3,3,11,11,1,1,11,11],[11,11,3,19,4,4,19,4,3,19,4,4,11,11,4,3,3,11,19,4,11,4,3,4,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,11,11,11,11,11,11,4,3,11,19,11,5,4,3,19,11,11,11,1]] (.nil)) (.nil))) (.cons 0xffffffffffffffffff00ff00ff00ff00 (.branch [43,6,23,2] [[4,2,3,2,3,11,27,4,2,2,3,3,2,6,27,4,2,3,1,2,2,2,2,2,1,2,2,2,2,2,2,2,6,2,2,2,2,4,19,3,19,3,1,11,27,4,19,19,3,3,2,27,4,19,3,2,3,0,2,3,4,2,27,11],[2,2,3,3,4,2,4,27,2,20,3,2,2,2,2,2,19,2,2,2,2,3,2,2,2,19,2,19,3,3,3,3,2,3,3,3,3,2,3,3,3,2,3,3,2,2,3,6,11,2,3,2,6,2,3,27,11,2,27,1]] (.cons 0xfffffffffffff0f0f000f000f000f000 (.branch [57,33,6] [[3,1,2,4,2,4,19,1,3,2,2,4,4,2,12,3,1,2,14,1,1,2,3,2,3,3,3,1,2,2,3,3,2,3,3,1,2,3,1,2,1,2,2,2,2,2,1,2,2,2,2,2,2,2,12,2,2,2,2,3,1,3,11,4],[11,4,1,19,3,3,11,11,4,4,2,3,3,5,14,5,2,5,2,4,3,2,4,5,2,3,19,1,2,2,4,4,1,2,5,2,13,2,4,2,4,5,19,2,2,4,4,2,5,3,2,14,1,1,3,1,1,5,1,2,3,2,4,6],[19,2,4,2,6,2,4,3,3,2,3,1]] (.nil)) (.nil))) (.nil))))))))) (.cons 0xffffff00ffffff00ffffff00ffffff00 (.branch [39,8,22,17] [[0,2,2,2,2,2,2,2,3,2,2,2,0,2,2,3,2,20,3,19,11,27,2,20,3,3,19,19,2,27,2,3,19,3,2,2,2,2,2,3,2,2,2,2,20,2,20,2,3,3,3,3,2,3,3,3,3,2,3,3,2,3,11,2],[27,2,2,3,3,2,19,19,19,2,19,11,2,3,2,0,2,3,2,11,2,2,3,3,11,11,11,11,2,11,11,27,2,20,2,20,2,2,3,2,19,2,19,0,2,2,2,2,2,27,0,20,3,19,1]] (.cons 0xffffff00ffffff00ffffff0000000000 (.branch [25,57,18] [[2,4,0,11,2,2,4,4,3,3,2,11,5,2,21,0,2,4,3,11,2,2,4,4,3,3,2,11,5,2,4,3,1,2,2,11,11,2,11,2,11,2,4,2,2,4,3,2,2,13,11,2,4,11,2,3,11,2,4,2,21,2,4,2],[11,2,2,11,11,3,3,11,11,2,11,11,11,2,11,2,20,2,2,4,2,3,2,3,11,2,2,2,2,2,5,6,13,4,3,1]] (.cons 0xffffaa00ffffaa00ffffaa00aaaaaa00 (.branch [56,16,18] [[3,2,11,1,4,2,2,11,11,1,3,2,4,3,2,5,1,1,2,1,2,11,2,2,1,2,2,11,11,2,2,4,2,2,4,2,3,1,2,11,3,4,1,2,2,11,11,3,3,2,3,2,5,3,1,2,3,1,3,2,2,3,3,1],[2,3,3,2,3,1,3,19,2,12,2,11,4,2,3,2,2,11,11,1,2,20,1,2,20,2,11,4,2,2,11,11,2,5,3,2,21,2,3,1,3,2,2,3,3,2,3,3,2,3,1,2,11,1,4,2,2,11,11,1,19,2,4,3],[2,11,1,1,2,2,11,4,2,11,2,4,2,11,2,2,11,19,2,2,21,11,2,11,19,2,19,4,2,11,2,12,2,11,2,3,2,2,11,11,3,19,3,4,2,4,19,3,2,4,2,20,2,2,11,2,3,2,19,4,2,2,2,2],[2,3,12,6,11,19,1]] (.nil)) (.cons 0xffffaaaaffffaaaaffffaaaaaaaaaaaa (.branch [32,36] [[3,2,4,1,11,2,2,4,4,1,3,2,11,3,2,14,1,1,1,2,1,2,11,2,2,1,2,2,11,11,2,2,11,2,2,11,2,1,3,1,2,4,3,11,1,2,2,4,4,3,3,2,3,2,14,3,2,4,11,2,2,4,4,2],[5,3,2,14,1,2,1,2,11,2,2,1,2,2,11,11,2,2,11,2,2,11,2,5,1,2,4,5,11,1,2,2,4,4,3,5,2,5,2,4,3,1,2,3,1,3,2,2,3,3,1,2,3,3,2,3,1,3,5,2,5,2,4,11],[2,3,2,2,4,4,1,2,5,1,2,13,2,4,11,2,2,4,4,2,5,5,2,4,2,3,3,2,2,3,3,2,3,3,2,3,1,2,4,1,11,2,2,4,4,1,5,2,11,3,2,4,1,1,2,2,11,11,2,11,2,11,2,4],[2,2,4,5,2,2,12,11,2,4,11,2,5,11,2,4,2,6,2,4,2,3,2,2,11,11,3,11,3,11,2,11,11,3,2,11,2,12,2,2,4,2,3,2,5,11,2,2,2,2,2,3,6,12,4,5,1]] (.nil)) (.nil)))) (.cons 0xffffffffffffff00ffffffff00000000 (.branch [46,43,2,18] [[19,3,12,3,11,19,19,12,3,3,11,11,19,1,5,12,3,11,19,3,19,19,3,11,19,19,19,19,3,3,11,11,1,19,19,19,3,11,3,12,3,0,19,19,12,3,3,11,11,5,19,5,29,0,0,3,3,3,3,3,3,3,3,3],[3,3,3,3,3,3,3,3,3,3,12,3,11,29,19,12,3,11,11,19,5,6,12,3,11,1,19,12,3,11,19,29,5,12,3,3,11,11,19,5,19,19,3,11]] (.cons 0xffffaa00ffffaa00ffffaa00aaaaaa00 (.branch [55,12,2] [[3,19,4,12,4,1,19,19,11,4,11,1,3,12,11,3,12,12,1,1,3,19,1,19,19,3,11,1,19,11,19,11,3,3,11,3,19,19,3,3,19,4,1,12,4,3,19,1,19,11,4,11,3,3,12,3,12,12,3,1,3,3,3,3],[3,1,3,3,3,3,3,1,3,3,3,3,3,1,11,11,3,11,11,11,11,11,11,11,3,3,11,11,11,11,1,11,11,1,11,11,19,4,12,12,4,19,19,11,4,11,5,12,3,12,12,19,4,12,4,1,19,19,11,4,11,1,11,19],[1,3,12,4,1,3,19,19,19,19,19,19,3,19,11,19,11,3,11,1,3,19,19,19,19,3,3,3,1,3,3,3,3,3,3,3,3,3,3,1,19,4,4,19,3,3,4,3,12,4,12,12,19,11,11,3,11,19,3,6,7,4,5,1],[19,12,4,12,19,12,3,11,4,11,3,11,19,3,19,19,19,19]] (.nil)) (.cons 0xffffccccffffccccffffcccccccccccc (.branch [55,43,2] [[1,1,19,3,1,19,19,19,19,1,19,19,3,19,3,11,19,19,19,3,19,4,4,19,4,4,4,4,19,19,4,4,3,11,4,19,3,4,4,1,4,1,3,19,1,4,1,4,19,19,4,1,3,3,11,4,19,3,4,1,4,1,1,3],[3,1,19,3,19,19,1,19,19,3,3,3,11,19,3,19,3,19,1,3,19,1,1,4,3,4,19,1,19,4,1,3,3,11,4,3,4,3,4,4,19,4,4,4,11,19,19,4,4,3,11,4,4,3,3,4,1,11,1,19,19,1,19,19],[19,19,1,19,19,19,19,3,11,19,19,19,3,19,3,4,1,19,3,1,4,4,4,4,19,3,19,4,4,3,11,4,3,4,4,3,4,1,3,1,3,1,3,3,3,3,3,1,3,3,3,3,3,3,1,3,4,19,3,4,4,19,4,4],[4,19,3,3,19,4,4,3,11,4,4,3,4,4,19,4,12,11,4,19,19,12,3,11,19,4,3,4,4,11,19,1,12,1,11,19,19,12,1,4,3,11,19,1,3,12,1,11,3,19,19,19,19,11,19,3,19,19,19,19,3,11,1,3],[19,19,19,11,3,3,3,3,3,3,3,3,1,19,1,4,19,4,12,4,11,6,19,12,4,3,11,19,3,6,12,4,11,1,19,12,4,11,19,6,3,12,4,4,3,11,19,3,19,19,19,11]] (.nil)) (.cons 0xffffaaaaffffaaaaffffaaaaaaaaaaaa (.branch [55,35,12,2] [[1,1,19,27,1,11,27,27,19,1,11,11,27,19,3,19,19,27,27,27,3,19,27,4,11,4,1,27,11,11,4,19,1,19,27,19,5,5,4,1,3,27,4,11,4,1,27,11,11,4,19,1,3,20,19,3,20,20,1,1,1,3,27,1],[11,27,3,19,1,11,11,27,19,3,3,19,3,27,27,3,1,3,27,4,1,11,4,3,27,1,11,11,4,19,3,3,20,3,20,20,3,27,4,20,11,4,27,11,11,4,19,5,20,3,20,20,1,19,27,1,11,27,27,27,1,11,11,27],[19,3,19,27,27,11,27,3,19,27,4,1,11,4,20,27,1,11,11,4,19,3,19,27,5,5,4,3,1,3,3,3,3,3,1,3,3,3,3,3,1,3,3,3,3,3,1,19,19,3,19,19,19,19,11,19,19,3,3,11,11,19,19,1],[19,19,1,19,19,27,4,5,11,4,27,11,11,4,19,27,5,5,11,4,27,4,11,4,1,27,11,11,4,19,1,19,27,1,3,11,4,1,3,27,27,11,27,27,27,3,11,11,27,19,3,19,1,3,27,11,27,27,3,3,3,3,3,3],[3,3,3,3,3,3,3,1,27,4,4,27,3,3,4,3,11,4,20,20,11,11,19,3,19,27,3,6,11,4,5,1,27,11,4,5,27,20,3,11,4,19,3,19,27,3,27,11,27,27]] (.nil)) (.nil))))) (.cons 0xffffffffffffff00ffffffffffffff00 (.branch [51,29,9] [[3,11,4,12,3,11,4,12,19,3,3,11,11,19,4,12,19,20,3,11,4,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,11,11,11,3,4,11,5,19,19,3,3,19,4,11,11,11,11,11,11,4,4,3,11,12],[19,19,3,3,11,11,4,4,4,4,13,11,3,5,3,12,3,11,4,5,1,19,3,11,11,19,4,12,19,5,3,11,4]] (.nil)) (.cons 0xffffffffffffffffffffffff00000000 (.branch [45,41,8] [[2,3,2,3,11,19,2,2,3,3,11,11,2,6,5,2,3,11,2,3,2,3,0,19,2,2,3,3,11,11,2,5,5,2,14,0,3,2,2,2,2,2,2,2,2,2,2,3,2,2,2,12,2,2,3,2,3,3,3,3,3,3,3,3],[3,2,3,3,3,3,2,3,3,2,3,2,3,11,6,2,3,11,11,5,6,2,3,11,1]] (.cons 0xffffaa00ffffaa00ffffaa00aaaaaa00 (.branch [54,41,8] [[3,2,4,2,4,1,19,2,2,4,4,1,3,2,5,3,2,14,1,1,2,2,4,1,2,4,2,2,1,2,2,4,4,2,2,5,2,2,14,2,3,2,4,1,2,4,3,19,1,2,2,4,4,3,3,2,3,2,14,3,1,2,3,3],[2,3,1,3,2,2,3,3,1,2,3,3,2,3,1,11,3,2,4,11,2,5,2,4,19,2,3,2,2,4,4,1,2,5,1,2,13,2,4,11,2,4,19,2,2,4,4,2,5,3,2,14,2,4,2,4,1,19,2,2,4,4,1,11],[2,6,3,2,4,1,2,3,2,3,1,3,2,2,3,3,2,3,3,2,3,1,2,2,2,2,2,2,12,2,4,4,4,19,3,3,2,3,2,4,11,6,2,4,3,11,3,6,2,4,11,1]] (.nil)) (.cons 0xffffaaaaffffaaaaffffaaaaaaaaaaaa (.branch [54,34,8] [[12,2,4,2,4,1,19,2,2,4,4,1,12,2,5,5,2,4,1,3,2,4,2,4,1,19,2,2,4,4,1,3,2,5,3,2,13,1,1,1,2,2,4,1,2,4,2,2,1,2,2,4,4,2,2,5,2,2,13,2,1,3,2,4],[1,2,4,3,19,1,2,2,4,4,3,3,2,3,2,13,3,2,4,5,2,4,19,2,2,4,4,2,5,3,2,13,1,2,2,4,1,2,4,2,2,1,2,2,4,4,2,2,5,2,2,14,2,12,2,4,1,2,4,5,19,1,2,2],[4,4,3,12,2,5,2,4,3,1,2,3,3,2,3,1,3,2,2,3,3,1,2,3,3,2,3,1,12,3,2,4,12,2,12,2,4,19,2,3,2,2,4,4,1,2,12,1,2,12,2,4,5,2,4,19,2,2,4,4,2,5,5,2],[4,2,4,2,4,1,19,2,2,4,4,1,12,2,13,3,2,4,1,2,3,2,3,3,2,2,3,3,2,3,3,2,3,1,2,2,2,2,2,2,11,2,4,4,4,19,3,3,2,3,2,4,5,13,2,4,3,12,3,6,2,4,5,1]] (.nil)) (.nil)))) (.cons 0xffffffffff00ff00ffffffffff00ff00 (.branch [40,24,54,1] [[11,3,11,11,11,3,11,11,11,11,11,11,11,11,11,11,3,3,11,11,11,11,11,3,4,4,11,3,4,4,11,12,27,19,19,11,11,1,3,3,4,4,4,4,12,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,3,3,3],[3,3,27,27,19,3,27,19,11,27,3,0,1,1,11,4,3,19,11,4,3,19,27,11,4,3,27,19,19,11,11,27,4,3,3,19,27,11,4,3,11,4,3,19,11,4,3,27,19,11,11,27,4,3,3,19,1,11,4,3,11,3,11,11],[11,11,11,11,11,11,11,11,3,3,11,11,11,11,11,3,4,4,11,0,27,27,19,19,11,11,3,3,4,4,4,27,4,12,3,3,3,3,3,3,3,3,3,3,3,1,3,3,3,3,3,19,3,19,19,11,3,23,19,11,3,19,27,27],[11,4,3,27,7,19,19,27,19,19,11,27,4,3,3,27,19,13,11,4,3,19,1]] (.cons 0xffffffffffffffffffffff00ff00ff00 (.branch [40,30,2] [[11,3,11,3,11,11,11,3,11,3,11,11,11,3,11,11,11,11,11,11,11,1,11,11,3,3,11,11,11,11,11,3,11,3,4,4,4,3,11,3,4,4,11,3,4,4,11,12,19,19,4,11,11,1,3,3,4,4,4,4,12,3,3,3],[3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,3,3,3,3,3,19,19,11,4,19,3,19,19,11,4,3,1,1,19,11,4,3,11,3,11,11,11,3,11,3,11,11,11,3,11,11,11,11,11,11,11,1,11],[11,3,3,11,11,11,11,11,3,4,4,4,3,11,3,4,4,11,3,4,4,11,12,19,19,4,11,11,1,3,3,4,4,4,4,12,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,3,3,3,3,3,19],[11,19,4,19,3,19,11,4,3,1,19,1,11,4,3,5,11,4,3,11,4,3,1,11,4,3,19,11,4,3,19,19,11,11,4,4,3,3,19,5,1,11,4,3,11,4,3,11,4,3,1,19,11,4,3,19,11,4,3,19,11,11,4,4],[3,3,19,5,1,11,4,3,11,3,4,3,11,11,11,0,3,11,11,11,4,0,11,19,19,5,4,4,3,3,11,11,11,11,11,11,3,11,3,4,4,11,3,4,4,11,12,19,19,4,11,11,1,3,3,4,4,4,11,12,3,3,3,3],[3,3,3,3,3,3,3,3,3,3,3,3,3,1,3,3,3,3,3,4,19,3,19,4,3,19,19,4,3,1,19,19,19]] (.cons 0xfcfcfcfcfcf0fcf0fcfcfcccfc00fc00 (.branch [52,45,14] [[1,3,1,1,1,11,1,11,11,11,1,11,1,11,11,11,1,11,11,11,1,11,11,11,11,3,1,1,11,11,11,11,11,1,11,1,1,1,4,3,4,4,4,4,4,4,4,4,4,1,4,3,4,4,4,4,19,4,19,1,4,4,4,4],[4,4,1,4,1,1,1,1,4,4,4,4,1,4,4,4,4,1,4,4,4,4,19,4,19,1,1,4,4,4,4,4,1,1,4,1,1,3,1,1,3,1,3,3,3,1,3,1,3,3,3,1,3,3,3,1,3,3,3,3,1,3,1,3],[3,3,3,3,1,3,1,1,12,11,12,19,4,4,1,12,11,12,19,4,4,4,4,4,20,19,19,20,19,1,12,12,4,4,4,19,1,4,1,1,3,3,4,4,4,4,3,4,4,4,4,3,4,4,4,4,19,4,19,3,3,4,4,4],[4,4,3,3,4,3,1,3,1,11,1,11,11,11,3,11,1,11,11,11,1,11,11,11,1,11,11,11,11,3,1,1,11,11,11,11,11,3,11,1,1,3,3,4,4,4,4,3,4,4,4,4,3,4,4,4,4,19,4,19,3,3,4,4],[4,4,4,3,3,4,19,19,3,1,3,4,3,1,11,4,4,4,4,3,4,1,3,4,4,3,4,1,3,4,3,4,4,1,11,4,4,19,4,19,3,11,11,4,4,4,4,4,3,4,1,3,3,1,19,11,3,1,19,19,11,19,3,1],[19,11,3,1,19,19,19,19,3,19,19,19,3,1,19,19,19,19,19,3,3,1,19,19,19,19,19,3,19,3,3,4,4,4,4,3,4,4,4,4,3,4,4,4,4,19,4,19,3,3,4,4,4,4,4,3,3,4,1,1,3,3,3,3],[3,3,3,1,3,3,3,3,3,3,1,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,3,1,11,11,3,11,11,11,11,1,11,11,3,11,11,11,11,1,11,11,11,3,11,11,11,11,11,3,3,11,11,11,11,11],[11,1,11,12,4,12,4,4,4,12,11,12,4,4,4,4,3,4,4,0,4,19,13,19,12,12,4,4,4,4,4,3,3,3,3,3,3,3,3,3,3,3,3,11,11,11,11,11,11,11,11,11,11,11,11,1,12,12,12,12,12,12,19,12],[19,12,12,12,19,19,3,11,19,12,19,19,3,11,12,1,1,19,3,11,12,3,3,3,3,3,3,3,3,3,3,3,3,11,11,11,11,11,11,11,11,11,11,11,11,12,12,12,12,12,12,19,12,19,12,12,12,19,3,19,11,19,12,19],[3,11,12,1,19,1,3,11,12,19,3,11,12,3,11,12,1,3,11,12,19,3,11,12,19,5,3,3,11,11,12,12,19,19,1,3,11,12,3,11,12,3,11,12,1,20,3,11,12,19,3,11,12,19,3,3,11,11,12,12,20,19,1,3],[11,12,1,3,3,3,1,3,3,3,3,3,3,3,3,3,3,3,1,11,11,11,11,11,11,11,3,11,11,11,1,12,12,12,12,19,12,19,12,12,12,11,19,12,5,11,12,19,5,11,12,1,19,5,19]] (.cons 0xfefefefcfefafef0fefefeccfeaafe00 (.branch [49,26,39,56,21] [[3,3,3,1,3,1,3,1,3,1,3,1,1,1,3,1,3,3,3,1,3,1,3,3,3,1,3,3,3,1,3,3,3,3,3,1,1,3,3,3,3,3,1,3,3,11,3,11,11,1,11,3,3,1,1,11,1,1,3,1,11,11,1,3],[3,3,11,3,11,3,11,11,3,3,11,3,11,11,11,3,11,11,11,3,11,11,11,11,11,3,3,1,11,11,11,11,3,3,3,3,3,3,3,3,3,3,3,12,4,14,37,28,6,37,3,12,6,14,3,4,35,27,27,3,3,6,14,37],[3,11,3,3,1,3,1,3,3,3,1,3,1,3,1,3,1,3,3,3,3,3,1,3,3,3,1,3,3,3,1,3,3,3,3,3,1,1,3,3,3,3,3,3,3,1,1,1,4,3,1,1,1,1,1,3,3,3,14,21,3,6,37,3],[6,14,1,35,27,27,3,3,1,6,14,21,4,3,1,11,3,11,11,1,11,3,3,11,1,3,1,1,3,1,11,11,1,11,3,11,3,3,11,3,11,11,11,3,11,3,11,11,11,3,11,11,11,3,11,11,11,11,11,3,3,1,11,11],[11,11,3,1,1,1,4,1,11,11,1,11,1,4,1,11,21,37,11,6,37,1,6,14,11,35,27,27,11,1,11,6,21,37,4,1,11,11,3,11,11,1,11,3,3,11,1,3,1,1,3,1,11,11,1,11,3,11,3,3,11,3,11,11],[11,3,11,3,11,11,11,3,11,11,11,3,11,11,11,11,11,3,3,1,11,11,11,11,3,27,3,27,11,11,11,11,11,11,3,35,21,37,11,3,35,6,37,6,14,11,35,35,27,27,11,11,6,21,37,4,11,1,1,1,4,3,11,11],[1,11,1,4,3,11,21,21,4,6,21,3,6,21,11,35,27,27,4,3,11,6,21,21,4,3,11,1,1,35,27,3,11,1,1,1,35,3,1,11,1,11,4,4,1,11,1,11,4,4,3,11,4,4,1,3,35,27,27,1,3,1,11,11],[4,4,4,3,11,3,1,3,3,3,1,3,1,3,1,3,1,3,3,3,3,3,1,3,3,3,1,3,3,3,1,3,3,3,3,3,1,1,3,3,3,3,3,3,3,3,27,3,3,3,27,3,27,3,3,1,27,11,14,21,3,11,27,6],[37,3,27,14,14,35,27,27,3,3,14,14,21,4,3,35,27,27,3,11,3,1,1,1,1,3,1,35,4,3,1,3,11,12,1,3,11,4,28,36,3,11,1,3,11,28,12,36,1,3,11,12,4,28,1,3,11,4,35,27,27,4,3,3],[11,11,28,36,28,3,11,27,1,35,11,1,1,1,35,1,1,1,35,1,35,35,1,11,3,35,1,11,35,3,35,35,1,11,3,35,1,11,35,35,35,35,11,35,35,35,1,11,35,35,27,27,35,35,1,11,11,35,35,1,35,11,1,27],[3,3,11,27,27,27,11,3,11,27,27,11,27,3,11,27,3,1,27,27,3,1,11,27,11,27,3,1,11,27,3,1,27,27,27,27,3,1,27,27,27,27,3,27,27,27,27,27,3,3,1,27,27,1,27,3,4,3,11,11,11,27,11,4],[3,11,21,21,4,21,21,3,21,21,11,35,27,27,4,3,11,21,21,21,4,3,11,1,3,1,1,1,3,3,3,3,3,1,1,11,4,3,11,4,4,4,1,11,3,11,4,4,4,1,11,4,4,4,3,3,4,35,27,27,3,3,11,11],[4,4,4,4,1,11,3,1,1,1,3,3,3,3,1,1,3,3,3,3,3,3,3,1,3,3,3,3,3,3,3,1,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,3,3,3,11,11,11,11,3,1,11,11,11,3,3],[1,11,3,11,11,3,11,11,11,3,3,11,11,3,11,11,11,11,3,11,11,11,11,3,11,11,11,11,11,3,3,11,11,11,11,11,3,37,37,31,37,20,37,6,37,12,14,14,4,35,27,27,22,14,37,3,3,3,3,3,3,3,3,3],[3,3,3,11,4,4,4,4,1,4,4,4,11,4,4,4,4,35,27,27,4,4,4,4,11,1,4,4,1,4,4,1,4,4,35,27,27,4,4,4,11,4,4,4,4,4,4,35,27,27,4,4,4,1,3,35,4,4,1,3,35,4,4,1],[4,4,35,35,27,27,4,4,4,35,11,4,4,4,4,4,4,35,27,27,4,4,4,3,3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,35,27,27,4,4,4,11,4,4,4,4,11,4,4,4,11,4,4,4,4,35,27,27],[4,4,4,11,11,3,35,3,35,11,3,35,35,35,11,35,35,35,35,27,27,35,35,35,11,4,4,4,4,4,4,35,27,27,4,4,4,4,4,4,4,4,4,4,4,4,4,4,35,27,27,4,4,4,4,3,3,3,3,3,3,3,3,3],[3,3,3,3,3,3,3,3,3,11,4,4,4,4,11,3,4,4,4,11,4,4,4,1,4,35,27,27,4,4,4,4,1,4,4,4,4,4,4,35,27,27,4,4,4,3,3,3,3,3,3,3,3,3,3,3,3,11,11,11,11,11,11,11],[11,11,11,11,11,27,27,4,3,27,11,27,27,4,3,11,1,1,27,4,3,11,4,4,4,4,4,4,35,27,27,4,4,4,3,3,3,3,3,3,3,3,3,3,3,3,11,11,11,11,11,11,11,11,11,11,11,11,27,4,27,3,27,11],[27,4,3,11,1,27,1,4,3,11,27,4,3,11,4,3,11,1,4,3,11,35,4,3,11,27,27,4,4,3,3,11,11,35,27,1,4,3,11,4,3,11,4,3,11,1,27,4,3,11,27,4,3,11,35,4,4,3,3,11,11,27,27,1],[4,3,11,4,4,4,4,4,4,4,35,27,27,4,4,4,4,3,3,3,3,3,3,3,3,3,3,11,11,11,11,11,11,11,11,11,11,3,35,11,27,3,11,35,27,3,11,1,35,27,35]] (.nil)) (.nil))) (.cons 0xfafafaf0fafafaf0fafafa00faaafa00 (.branch [51,40,13] [[1,3,1,1,1,11,1,11,11,11,1,11,1,11,11,11,1,11,11,11,1,11,11,11,11,3,1,11,11,1,11,11,11,1,11,1,1,1,4,4,4,3,4,4,4,4,4,4,4,4,4,4,4,4,1,3,4,19,19,4,4,1,4,4],[4,4,4,1,1,1,1,1,4,4,4,4,1,4,4,4,4,4,4,4,4,1,4,19,19,1,4,4,1,4,4,4,1,4,1,1,3,1,3,1,11,1,11,11,11,3,11,1,11,11,11,1,11,11,11,1,11,11,11,11,3,1,11,11],[1,11,11,11,3,11,1,1,3,3,4,4,4,4,3,4,4,4,4,4,4,4,4,3,4,19,19,3,4,4,3,4,4,4,3,4,3,1,1,3,3,4,4,4,4,3,4,4,4,4,4,4,4,4,3,4,19,19,3,4,4,3,4,4],[4,3,4,3,1,3,1,3,1,3,1,3,3,3,1,3,1,3,3,3,1,3,3,3,1,3,3,3,1,3,3,3,1,3,3,3,3,1,1,1,12,19,12,11,4,4,1,12,11,12,19,4,4,20,19,4,4,4,20,19,19,1,12,12],[4,4,4,19,1,4,19,19,3,1,4,11,4,1,4,3,3,4,4,4,3,1,4,3,4,4,4,1,4,11,4,3,4,1,4,3,3,4,19,19,3,4,4,11,11,4,4,4,4,3,1,3,3,19,1,19,3,19,1,11,19,11,3,19],[1,11,3,19,1,19,19,19,3,19,1,19,19,19,3,19,19,19,19,3,3,19,19,1,19,19,19,3,19,3,3,4,4,4,4,3,4,4,4,4,4,4,4,4,3,4,19,19,3,4,4,3,4,4,4,3,4,3,1,3,3,3,3,1],[3,3,3,3,1,3,3,3,3,3,3,3,3,3,3,3,1,3,3,3,3,3,3,3,3,3,3,3,3,3,1,3,11,11,1,11,11,11,11,1,11,11,3,11,11,11,11,3,11,11,11,11,1,11,11,11,11,3,3,11,11,11,11,11],[11,1,11,12,4,12,4,4,4,12,11,12,4,4,4,0,4,4,4,4,3,13,19,19,12,12,4,4,4,4,4,3,1,3,3,3,3,1,3,3,3,3,1,3,3,3,3,3,3,3,3,3,3,3,3,3,3,12,12,3,3,12,12,3],[12,12,3,12,19,19,3,3,12,12,12,3,11,11,3,11,11,1,11,11,11,11,11,3,11,11,11,3,19,19,3,12,19,11,19,19,3,12,11,1,1,19,3,12,11,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3],[3,12,12,3,3,12,12,3,12,12,3,12,19,19,3,3,12,12,12,3,11,11,11,11,11,11,11,11,11,11,11,11,1,19,3,19,12,19,11,19,3,12,11,1,19,1,3,12,11,19,3,12,11,3,12,11,1,3,12,11,20,3,12,11],[19,19,3,3,12,12,11,11,20,19,1,3,12,11,3,12,11,3,12,11,1,19,3,12,11,19,3,12,11,5,3,3,12,12,11,11,19,19,1,3,12,11,3,1,3,3,3,3,3,3,3,3,3,3,1,3,3,3,3,3,3,3,3,3],[3,3,1,3,12,12,3,12,12,3,12,19,19,3,3,12,12,12,3,11,11,1,11,11,11,11,11,3,11,11,11,1,12,5,11,19,12,11,5,19,12,11,1,5,19,5]] (.cons 0xfefefefcfefafef0fefefeccfeaafe00 (.branch [42,33,39,21,56] [[3,3,11,3,11,1,11,11,3,3,1,1,3,1,1,11,1,11,11,1,3,3,3,11,3,11,3,11,11,3,3,11,3,11,11,11,3,11,11,11,3,11,11,11,11,11,1,3,3,11,11,11,11,3,3,1,3,3,3,1,1,3,1,3],[1,1,1,3,1,3,3,3,1,3,1,3,3,3,1,3,3,3,1,3,3,3,3,3,1,3,3,1,3,3,3,1,3,3,3,3,3,3,3,3,3,3,3,4,28,6,29,28,13,13,3,4,6,6,3,28,27,35,27,3,3,13,6,29],[11,3,3,11,3,11,1,11,11,3,3,11,1,3,1,1,3,1,11,11,1,11,3,11,11,3,3,3,11,11,11,3,11,3,11,11,11,3,11,11,11,3,11,11,11,11,11,1,3,3,11,11,11,11,3,1,1,1,4,11,1,11,1,11],[1,4,1,11,6,13,11,13,13,11,13,6,1,27,35,27,11,11,1,13,6,13,4,11,1,1,3,3,3,1,3,3,1,3,1,3,1,3,1,3,3,3,3,3,1,3,3,3,1,3,3,3,1,3,3,3,3,3,1,3,3,1,3,3],[3,3,3,1,1,1,4,1,3,1,1,1,1,3,3,3,21,13,3,13,13,1,13,6,3,27,35,27,3,1,3,13,21,13,4,1,3,1,11,1,27,35,11,3,1,1,1,35,3,11,1,11,1,4,4,11,1,11,1,4,4,3,1,4],[4,11,3,27,35,27,1,11,11,3,1,4,4,4,11,3,3,3,3,1,3,3,1,3,1,3,1,3,1,3,3,3,3,3,1,3,3,3,1,3,3,3,1,3,3,3,3,3,1,3,3,1,3,3,3,3,3,27,3,27,3,3,3,27],[3,27,3,3,1,11,27,21,13,3,11,27,13,13,13,6,3,27,27,35,27,3,3,13,21,13,4,3,1,1,1,4,11,3,11,1,11,1,4,3,11,21,13,4,13,13,11,13,21,3,27,35,27,4,11,3,13,21,13,4,11,3,11,1],[11,11,3,3,11,1,3,1,1,3,1,11,11,1,11,3,11,11,3,3,3,11,11,11,3,11,3,11,11,11,3,11,11,11,3,11,11,11,11,11,1,3,3,11,11,11,11,3,3,27,11,11,11,11,11,11,35,3,6,21,11,3,35,13],[13,11,35,6,6,27,35,27,11,11,6,6,13,4,11,27,35,27,11,3,3,1,3,1,1,1,1,35,4,3,1,11,3,4,1,11,3,28,36,28,11,3,1,11,3,28,4,28,1,11,3,4,28,36,1,11,3,28,27,35,27,4,11,11],[3,3,36,28,28,11,3,27,1,27,3,3,11,27,3,11,11,27,27,27,27,11,27,3,11,27,1,3,11,27,1,3,27,11,27,27,1,3,11,27,1,3,27,27,27,27,3,27,27,27,1,3,27,27,27,27,27,27,1,3,3,27,27,1],[27,3,1,35,11,1,1,1,1,1,1,35,35,1,35,35,11,1,35,35,11,1,3,35,3,35,11,1,3,35,11,1,35,35,35,35,11,1,35,35,35,35,11,27,35,27,35,35,11,11,1,35,35,1,35,11,4,11,3,11,11,27,11,4],[3,11,21,13,4,13,13,11,13,21,3,27,35,27,4,11,3,13,21,13,4,11,3,3,1,1,1,3,3,3,1,3,3,1,11,3,4,11,1,4,4,4,11,1,11,3,4,4,4,3,3,4,4,4,11,1,4,27,35,27,11,11,3,3],[4,4,4,4,11,1,3,3,3,11,3,1,11,11,11,11,11,11,3,3,1,11,3,11,11,3,11,11,11,3,3,11,11,3,11,11,11,11,3,11,11,11,3,11,11,11,11,11,11,3,3,11,11,11,11,11,3,1,1,3,3,1,3,3],[1,3,3,3,1,3,3,3,3,1,3,3,3,3,3,3,3,3,3,3,3,3,1,3,3,3,3,3,3,3,3,3,3,3,3,1,3,13,29,39,29,20,13,13,13,4,6,6,28,27,35,27,22,6,29,3,3,3,3,3,3,3,3,3],[3,3,3,4,4,4,4,1,4,4,4,4,4,4,4,27,35,27,4,4,4,4,11,4,4,4,4,4,4,27,35,27,4,4,4,3,3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,27,35,27,4,4,4,4,4,4,4,4],[4,27,35,27,4,4,4,4,4,4,4,4,4,27,35,27,4,4,4,35,3,4,4,3,35,4,4,35,4,4,27,35,27,4,4,4,35,4,4,4,4,11,4,4,4,4,4,4,4,27,35,27,4,4,4,11,35,3,35,3,3,35,35,35],[35,35,35,27,35,27,35,35,35,4,4,4,4,4,4,27,35,27,4,4,4,4,4,4,4,4,4,4,4,4,4,4,27,35,27,4,4,4,4,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,11,3,4],[4,4,1,4,4,4,4,27,35,27,4,4,4,4,1,4,4,4,4,4,4,27,35,27,4,4,4,11,11,11,11,11,11,11,11,11,11,11,11,3,3,3,3,3,3,3,3,3,3,3,3,27,27,4,11,27,3,27,27,4,11,3,1,1],[27,4,11,3,4,4,4,4,4,4,27,35,27,4,4,4,11,11,11,11,11,11,11,11,11,11,11,11,3,3,3,3,3,3,3,3,3,3,3,3,27,4,27,11,27,3,27,4,11,3,1,27,1,4,11,3,27,4,11,3,4,11,3,1],[4,11,3,27,4,11,3,27,35,4,4,11,11,3,3,27,27,1,4,11,3,4,11,3,4,11,3,1,35,4,11,3,27,4,11,3,27,4,4,11,11,3,3,35,27,1,4,11,3,4,4,4,4,4,4,4,27,35,27,4,4,4,4,11],[11,11,11,11,11,11,11,11,11,3,3,3,3,3,3,3,3,3,3,11,27,3,35,11,3,27,35,11,3,1,27,35,27]] (.nil)) (.nil))) (.nil)))) (.cons 0xeeeeeecceeaaee00eeeeeecceeaaee00 (.branch [47,38,54,1] [[1,3,1,1,11,1,11,11,11,1,11,11,11,1,11,11,11,11,11,3,1,1,11,11,11,11,1,1,1,1,4,3,4,4,4,4,4,4,1,3,27,19,19,4,4,1,4,4,4,27,4,1,1,1,1,1,4,4,4,4,1,4,4,4],[1,27,19,19,4,4,1,1,4,4,4,4,1,1,1,3,1,3,1,3,3,3,1,3,3,3,1,3,3,3,3,3,1,3,1,3,3,3,3,1,1,1,12,11,4,4,12,1,11,4,4,4,27,19,19,12,12,1,4,4,4,19,4,1],[19,1,3,27,1,3,3,27,27,27,3,27,3,27,1,3,3,27,19,19,27,27,1,11,3,27,27,27,27,3,1,3,19,3,1,11,19,11,19,3,1,11,19,19,19,3,19,19,19,19,19,3,3,1,19,19,19,19,3,3,3,4,4,4],[4,3,4,4,4,3,27,19,19,4,4,3,3,4,4,4,4,3,3,1,3,1,3,3,3,3,1,3,3,3,1,3,3,3,3,3,3,3,3,3,3,3,3,3,1,11,1,11,11,11,11,1,11,11,11,11,1,11,11,11,11,11,3,3],[11,11,11,11,11,1,12,4,4,4,12,11,4,4,4,3,27,19,19,12,12,4,4,4,4,4,3,11,12,12,3,11,12,12,3,11,27,19,19,12,3,3,11,11,12,12,12,3,11,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3],[11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,1,27,3,19,11,27,19,12,3,11,0,1,1,12,3,11,19,12,3,11,19,27,12,3,11,27,19,19,12,12,3,3,11,11,19,27,12,3,11,12,3,11,19,12,3,11,27,19,12],[12,3,3,11,11,19,1,12,3,11,3,11,12,12,3,11,27,19,19,12,3,3,11,11,12,12,12,3,11,1,3,3,3,1,3,3,3,3,3,3,3,3,3,3,3,1,11,11,11,11,11,11,11,11,3,11,11,11,11,1,19,11,19,19],[12,11,23,19,12,11,19,27,27,12,3,11,27,7,19,19,27,19,19,12,3,3,11,11,27,19,13,12,3,11,19,1]] (.cons 0xffffffffffffffffffffff00ff00ff00 (.branch [40,28,45] [[1,1,11,1,11,1,11,11,11,1,1,1,3,1,11,1,11,11,11,1,11,11,11,1,11,11,11,11,11,1,3,1,11,11,11,11,1,1,3,1,3,1,3,3,3,1,1,3,1,1,3,1,3,3,3,1,3,3,3,1,3,3,3,3],[3,3,1,1,3,3,3,3,1,4,4,4,4,4,1,1,1,1,4,4,4,4,1,4,4,4,1,4,4,4,4,4,1,1,4,4,4,4,1,1,1,11,1,11,1,11,11,11,1,1,1,3,1,11,1,11,11,11,1,11,11,11,1,11],[11,11,11,11,1,3,1,11,11,11,11,1,4,4,4,4,4,1,1,1,1,4,4,4,4,1,4,4,4,1,4,4,4,4,4,1,1,4,4,4,4,1,1,3,1,3,1,3,3,3,1,1,3,1,1,3,1,3,3,3,1,3,3,3],[1,3,3,3,3,3,3,1,1,3,3,3,3,1,4,4,4,4,4,1,1,1,1,4,4,4,4,1,4,4,4,1,4,4,4,4,4,1,1,4,4,4,4,1,1,11,3,11,3,12,12,11,3,3,12,4,11,4,4,4,4,11,3,12],[11,3,12,12,11,3,12,12,11,3,12,12,12,1,11,11,3,3,12,12,12,11,3,1,11,1,11,11,11,1,1,1,3,1,11,1,11,11,11,1,11,11,11,1,11,11,11,11,11,1,3,1,11,11,11,11,1,3,1,3,3,3,1,1],[3,1,1,3,1,3,3,3,1,3,3,3,1,3,3,3,3,3,3,1,1,3,3,3,3,1,5,5,12,11,3,11,3,11,3,4,11,5,3,5,5,12,11,3,1,1,5,12,11,3,11,3,12,12,11,3,3,12,4,11,4,4,4,4],[11,3,12,11,3,12,12,11,3,12,12,11,3,12,12,12,1,11,11,3,3,12,12,12,11,3,1,11,11,11,1,1,1,3,1,11,1,11,11,11,1,11,11,11,1,11,11,11,11,11,1,3,1,11,11,11,11,1,3,3,3,1,1,3],[1,1,3,1,3,3,3,1,3,3,3,1,3,3,3,3,3,3,1,1,3,3,3,3,1,5,12,11,3,11,3,11,3,4,5,11,5,3,5,12,11,3,1,5,1,12,11,3,5,12,11,3,3,4,4,11,4,11,4,4,11,3,4,12],[11,3,1,12,11,3,5,12,11,3,5,13,12,12,11,11,3,3,5,5,1,12,11,3,12,11,3,3,4,4,11,4,4,3,4,11,3,4,12,11,3,1,13,12,11,3,5,12,11,3,5,12,12,11,11,3,3,13,5,1,12,11,3,11],[3,3,20,4,11,4,4,4,4,11,3,0,11,3,12,12,12,11,3,12,12,12,11,3,12,5,21,5,11,11,3,3,12,12,12,12,11,3,1,1,1,3,1,11,1,11,11,11,1,11,11,11,1,11,11,11,11,11,1,3,1,11,11,11],[11,1,1,3,1,1,3,1,3,3,3,1,3,3,3,1,3,3,3,3,3,3,1,1,3,3,3,3,1,11,3,11,3,11,3,4,11,5,3,13,11,3,5,13,11,3,1,5,13,5]] (.cons 0xfefefefcfefafef0fefefeccfeaafe00 (.branch [40,31,21,13] [[1,1,11,1,11,4,1,27,11,1,1,1,11,1,11,1,4,4,3,1,1,1,3,1,11,1,4,4,11,1,4,4,11,1,19,27,19,11,11,1,3,1,4,4,4,11,1,1,3,3,1,3,3,1,3,1,1,1,3,1,3,1,3,3],[3,1,1,3,1,1,3,1,3,3,3,1,3,3,3,1,3,3,3,3,3,3,1,1,3,3,3,3,1,3,3,3,3,3,3,12,12,14,21,3,3,3,3,3,3,1,12,6,21,3,12,28,28,3,12,19,27,19,3,3,28,14,21,4],[3,1,11,1,3,4,1,27,11,1,1,1,11,1,3,1,4,4,11,1,1,1,3,1,11,1,4,4,11,1,4,4,11,1,19,27,19,11,11,1,3,1,4,4,4,11,1,1,1,1,11,4,1,28,21,11,19,1,19,1,4,1,11,28],[21,19,28,28,1,19,27,19,11,19,1,28,28,21,11,4,1,3,3,1,3,3,1,3,1,1,1,3,1,3,1,3,3,3,1,1,3,1,1,3,1,3,3,3,1,3,3,3,1,3,3,3,3,3,3,1,1,3,3,3,3,1,1,1],[1,11,1,3,28,21,3,1,3,1,3,1,3,3,28,21,1,28,28,3,19,27,19,3,1,3,28,28,21,11,1,3,3,11,1,11,11,11,3,11,3,1,11,1,3,1,11,3,11,3,11,11,11,3,3,1,1,11,11,11,11,1,3,3],[3,11,3,11,11,3,3,11,11,11,3,11,11,11,1,11,11,3,3,11,11,11,11,3,3,1,3,3,1,3,1,1,1,3,1,3,1,3,3,3,1,1,3,1,1,3,1,3,3,3,1,3,3,3,1,3,3,3,3,3,3,1,1,3],[3,3,3,1,11,3,11,3,3,19,19,14,21,3,19,3,3,3,3,19,6,21,28,28,3,19,19,27,19,3,3,6,28,21,11,3,1,1,1,11,4,3,28,21,11,11,3,11,3,4,3,11,28,21,11,28,28,3,19,27,19,11,11,3],[28,28,21,11,4,3,3,1,11,11,11,3,11,3,1,3,1,3,1,11,3,11,3,11,11,11,3,3,11,1,3,1,11,11,1,11,3,11,3,3,11,11,11,3,11,11,11,3,11,11,11,1,11,11,3,3,11,11,11,11,3,4,1,27],[11,1,1,1,11,1,3,1,4,4,11,1,1,1,3,1,11,1,4,4,11,1,4,4,11,1,19,27,19,11,11,1,3,1,4,4,4,11,1,3,11,11,11,27,3,28,21,11,3,11,11,11,11,27,28,21,11,27,28,28,19,27,19,11],[11,28,28,21,11,4,19,27,19,4,3,4,3,11,4,11,3,11,1,4,3,12,1,4,3,12,12,12,4,3,3,4,11,4,4,19,27,4,4,3,11,1,4,3,12,12,12,1,4,3,12,12,12,1,4,3,12,19,27,19,11,19,4,3],[3,12,12,12,4,3,19,1,11,3,1,3,1,1,1,3,1,11,1,3,19,11,1,3,19,19,19,11,1,3,19,3,1,1,1,19,1,3,11,1,3,19,19,19,11,3,19,19,11,1,3,19,19,19,19,11,11,1,3,3,19,19,1,11],[3,1,11,27,27,1,1,27,1,1,1,11,27,1,27,11,27,1,3,27,3,11,27,1,3,1,1,1,27,19,1,27,11,27,1,27,27,27,11,27,1,27,27,27,11,27,19,27,19,11,11,19,27,1,27,27,1,11,27,11,4,3,28,21],[11,11,11,11,11,4,3,11,28,21,19,28,28,3,19,27,19,11,19,3,28,28,21,11,4,3,3,3,11,3,1,11,11,3,11,11,3,11,11,3,11,11,11,11,3,3,3,11,11,11,11,11,11,3,3,1,11,3,11,11,11,3,3,11],[11,11,11,3,11,11,11,11,11,11,3,3,11,11,11,11,11,3,1,1,1,1,1,1,11,1,4,11,1,4,4,4,3,1,4,1,1,1,3,3,1,11,1,4,4,4,11,1,4,4,11,1,4,19,27,19,11,11,3,3,4,4,4,4],[11,1,1,1,1,1,1,3,1,3,3,1,3,3,3,3,1,3,1,1,1,3,3,1,3,1,3,3,3,3,1,3,3,3,3,1,3,3,3,3,3,3,3,3,3,3,3,3,1,21,28,14,21,4,28,6,21,13,28,28,20,19,27,19],[6,14,21,4,4,4,4,4,4,19,27,19,4,4,4,3,3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,19,27,19,4,4,4,1,4,4,4,4,4,4,19,27,19,4,4,4,4,4,4,4,4,4,19,27,19,4,4,4],[3,3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,19,27,19,4,4,4,11,11,11,11,11,11,11,11,11,11,11,11,4,4,4,4,4,4,19,27,19,4,4,4,3,3,3,3,3,3,3,3,3,3,3,3,19,19,11,19],[3,19,3,4,3,4,19,19,3,19,19,11,19,3,1,1,19,11,4,3,11,11,11,11,11,11,11,11,11,11,11,11,4,4,4,4,4,4,19,27,19,4,4,4,3,3,3,3,3,3,3,3,3,3,3,3,19,11,19,3,19,3,4,3],[4,19,19,19,3,19,11,19,3,1,19,1,11,4,3,19,11,4,3,3,4,4,4,4,19,27,4,4,3,4,11,4,3,1,11,4,3,19,11,4,3,19,27,11,11,19,4,3,3,19,19,1,11,4,3,11,4,3,3,4,4,4,4,19],[3,4,4,3,4,11,4,3,1,27,11,4,3,19,11,4,3,19,11,11,19,4,3,3,27,19,1,11,4,3,1,11,11,11,11,11,11,11,11,11,11,11,11,11,11,4,4,4,4,19,27,19,4,4,4,3,3,3,3,3,3,3,3,3],[3,19,3,19,3,4,3,4,19,19,3,27,19,3,19,27,4,3,1,19,27,19]] (.nil)) (.nil))) (.nil))) (.nil)))) (.nil))))))) (.nil)))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_14 : chkCheckNode s14_maskYF s14_edgePts s14_edgeTT s14_raw s14_masksTT s14_cuts [] s14_auts s14_cert = true := by decide +kernel

-- State #15: n=7 |E|=9 |F|=0 nodes=11 cands=1234 wits=1470 cuts=26
def s15_desc : StateDesc := ⟨7,[(0,3),(0,4),(1,3),(1,5),(2,4),(2,6),(3,5),(4,6),(5,6)],[]⟩
def s15_maskYF : Nat := 0xffffffffffffffffffffffffffffffff
def s15_edgePts : Nat := 0x1000100100000010400120600
def s15_edgeTT : Nat := 0xfffffffffffffef0fffeffccfefaee00
def s15_raw : List Nat := chkMkRaw 7 s15_maskYF
def s15_masksTT : List Nat := chkMkMasksTT 7 s15_desc.edges s15_maskYF
def s15_autIdxTbls : List (List Nat) := chkMkAutIdxTbls 7 [[0,2,1,4,3,6,5]]
def s15_auts : List (List Nat) := chkMkAutMaskTbls s15_autIdxTbls
def s15_cutSpecs : List CutSpecData := [⟨64,[],[2,4,0],2,[1,3,5]⟩,⟨1,[],[],0,[1,3,2,4,5,6]⟩,⟨2,[],[],6,[3,0,5,2,4,6]⟩,⟨4,[],[],6,[4,0,6,1,3,5]⟩,⟨0,[(3,5)],[],24,[1,0,2,3,5,4,6]⟩,⟨0,[(4,6)],[],24,[2,0,1,4,6,3,5]⟩,⟨0,[(5,6)],[],25,[1,2,0,5,6,3,4]⟩,⟨96,[],[1,2,3],17,[0,4]⟩,⟨17,[],[2,6],2,[1,3,5]⟩,⟨25,[],[1,2],17,[5,6]⟩,⟨42,[],[0],2,[2,4,6]⟩,⟨84,[],[0],2,[1,3,5]⟩,⟨84,[],[0],2,[1,3,5]⟩,⟨41,[],[],2,[2,4,6]⟩,⟨27,[],[2],17,[5,6]⟩,⟨43,[],[],2,[2,4,6]⟩,⟨43,[],[],2,[2,4,6]⟩,⟨85,[],[],2,[1,3,5]⟩,⟨43,[],[],2,[2,4,6]⟩,⟨31,[],[],17,[5,6]⟩,⟨31,[],[],17,[5,6]⟩,⟨110,[],[],17,[0,4]⟩,⟨118,[],[],17,[0,3]⟩,⟨118,[],[],17,[0,3]⟩,⟨59,[],[],17,[2,6]⟩,⟨110,[],[],17,[0,4]⟩]
def s15_cuts : List CutDefData := chkMkCuts s15_maskYF s15_raw [(3,[.v 6 [16,48]]),(2,[.v 0 [72,18,24,48]]),(2,[.v 1 [37,8]]),(2,[.v 2 [72,48]]),(1,[.e [(3,5)]]),(1,[.e [(4,6)]]),(1,[.e [(5,6)]]),(5,[.v 5 [12,18,72],.v 6 [12]]),(4,[.v 0 [48,8,18],.v 4 [12]]),(6,[.v 0 [72,18,12,24,48],.v 3 [18],.v 4 [36]]),(5,[.v 1 [72,37,24],.v 5 [24,72],.v 3 [65,1]]),(5,[.v 2 [48,64],.v 4 [72],.v 6 [32]]),(5,[.v 6 [6,24,18,48],.v 2 [16],.v 4 [33]]),(6,[.v 0 [72,18,12,48],.v 5 [72,8],.v 3 [18]]),(7,[.v 0 [72,18,24],.v 1 [24,48],.v 3 [48],.v 4 [36]]),(6,[.v 1 [32,12,48,72],.v 0 [8],.v 3 [48],.v 5 [64]]),(6,[.v 1 [8,36,72],.v 3 [1,36,48],.v 0 [48],.v 5 [64]]),(6,[.v 2 [64,18,24],.v 6 [16],.v 4 [33],.v 0 [8]]),(6,[.v 5 [18,24,72],.v 1 [72,24],.v 3 [1],.v 0 [16]]),(8,[.v 0 [12,18,48,72],.v 1 [32,24],.v 2 [48],.v 3 [48],.v 4 [64]]),(8,[.v 2 [64,18,72],.v 0 [72,18,48],.v 1 [8],.v 4 [72],.v 3 [32]]),(8,[.v 2 [18,72,64],.v 1 [48,72,33],.v 5 [24],.v 3 [65],.v 6 [16]]),(8,[.v 2 [64,18,72],.v 1 [24,32],.v 6 [16],.v 4 [33],.v 5 [8]]),(8,[.v 2 [64,18,72],.v 4 [33,72],.v 1 [8],.v 6 [32],.v 5 [8]]),(8,[.v 4 [12,72],.v 1 [32],.v 0 [12],.v 3 [32],.v 5 [64]]),(8,[.v 5 [8,72],.v 2 [72,18,65],.v 1 [8],.v 3 [65,1],.v 6 [16]])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
def s15_cert : CertNode := .branch [2,1,3,4,6,5] [[2,27,2,2,3,3,2,11,2,35,2,35,35,27,2,2,2,2,2,2,43,2,2,2,2,19,19,3,3,11,11,2,27,27,27,27,2,3,3,2,2,19,2,19,2,2,2,3,2,2,2,19,19,2,2,3,3,3,2,2,3,3,3,3],[3,2,3,2,3,3,11,2,11,11,2,11,2,11,2,2,11,0,2,2,2,2,2,0,0,19,3,11,0,2,2,2,19,3,11,3,2,3]] (.cons 0xffffffffffffffffffffffff00000000 (.branch [16,0] [[4,2,2,2,4,2,2,2,2,2,2,11,4,2,2,2,4,3,4,2,11,4,3,3,4,4,2,2,4,3,4,3,2,2,4,2,3,3,2,2,11,2,4,3,2,3,2,3,2,2,3,3,3,2,2,3,2,3,2,3,2,4,2,4],[2,3,5,1]] (.nil)) (.cons 0xffffffffffff0000ffffffffffff0000 (.branch [17,18,1,12] [[27,3,27,19,11,3,3,11,27,19,19,27,11,27,27,27,27,3,12,19,11,27,3,3,11,12,19,19,27,11,3,12,19,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,19,11,27,11,3,3,12,19,19,27,11,12,3,19,11,19],[11,3,3,11,19,19,19,19,19,19,19,3,12,19,27,0,3,12,19,11,3,11,12,19,19,27,27,27,3,27,19,1]] (.cons 0xffffffffffffff00ffffffffffffff00 (.branch [22,9,12,4] [[3,19,11,19,3,19,11,19,3,3,19,19,11,11,19,19,19,3,19,11,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,11,19,4,3,11,4,19,19,27,3,3,11,11,19,4,4,4,3,11,19,11,3,11,11,19],[19,27,3,3,4,4,11,11,11,11,11,11,3,19,3,19,3,19,11,19,1,27,3,4,4,11,11,19,19,19,3,19,11]] (.nil)) (.nil))) (.cons 0xffffffffff00ff00ffffffffff00ff00 (.branch [10,1,3,5,4,6] [[3,11,27,35,19,19,3,3,11,11,5,43,19,3,11,3,43,27,35,19,19,11,11,3,3,3,3,3,3,11,11,11,11,11,3,3,11,11,11,11,11,3,27,19,19,11,5,0,19,11,27,43,27,35,19,3,3,11,11,4,0,5,19,3],[11,4,1]] (.cons 0xffffffffffffff00ffffffffffffff00 (.branch [23,13,4,10] [[3,27,11,27,11,4,19,3,3,27,27,11,11,12,4,29,3,27,11,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,11,27,11,12,4,19,3,3,11,11,27,27,27,27,3,11,11,27,11,28,4,19,3,3,27,27],[11,11,11,11,11,11,3,6,3,27,11,29,1,19,3,27,27,11,11,12,4,29,3,27,11]] (.nil)) (.cons 0xffffffffffffffffffff0000ffff0000 (.branch [19,25,4,5] [[12,3,4,3,27,11,12,12,11,4,3,3,14,11,12,4,3,11,3,11,3,11,11,11,11,11,11,3,3,11,11,11,11,3,3,12,0,3,12,11,27,19,11,4,3,3,12,5,12,12,12,12,3,3,3,3,3,3,3,3,3,3,3,3],[3,3,3,3,3,4,3,14,11,11,4,3,11,6,4,3,14,11,1]] (.cons 0xfcfcfcfcfcf0fcf0fcfcccccfcf0cc00 (.branch [21,19,0,4,5] [[1,4,4,1,3,4,11,19,1,11,3,19,35,27,4,4,11,11,4,4,19,4,1,4,3,3,1,4,4,1,11,4,19,11,19,35,27,3,3,11,11,4,4,4,4,1,4,19,1,19,3,3,19,11,3,3,11,3,19,19,19,1,19,19],[11,11,19,19,19,3,19,4,1,3,4,4,3,11,4,19,11,19,35,27,3,3,1,11,11,4,4,4,3,4,4,3,3,4,11,19,3,11,3,19,35,27,1,4,4,11,11,4,4,4,3,4,3,4,4,3,11,4,19,11,19,35,27,3],[3,1,11,11,4,4,4,3,4,1,3,3,3,3,1,3,3,3,3,3,3,3,3,3,3,3,3,3,1,3,4,4,1,11,4,19,11,19,35,27,3,3,11,11,4,4,4,4,1,4,4,4,11,4,19,11,3,19,35,27,11,11,4,4],[4,4,4,3,11,4,11,19,27,3,3,4,4,11,11,19,5,3,4,11,3,11,4,11,19,27,3,3,4,4,11,11,19,5,3,4,11,3,1,3,3,3,3,3,3,3,3,1,11,11,11,11,11,11,11,11,4,11,6,27,4,4,11,5],[6,4,11,19,19,1]] (.nil)) (.nil))) (.nil)))) (.cons 0xffffff00ffffff00ffffff00ffffff00 (.branch [15,11,6,8,4] [[13,2,2,2,2,2,2,2,3,2,2,2,13,2,2,3,2,11,3,27,19,28,2,11,3,3,27,27,2,35,2,3,27,3,2,2,2,11,2,3,3,2,2,2,11,11,3,2,3,3,2,3,2,2,3,3,3,2,3,2,2,3,19,2],[35,2,2,3,3,2,27,2,27,2,27,19,2,3,2,0,2,3,2,19,2,2,3,3,2,19,2,19,2,19,19,28,2,11,2,11,2,2,3,2,27,2,27,13,2,2,2,2,2,0,5,11,3,27,1]] (.cons 0xffffffffffffff00ffffffffffffff00 (.branch [20,18,24] [[3,12,4,11,3,12,4,11,11,3,3,11,12,19,4,11,19,13,3,12,4,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,4,12,11,3,4,11,11,19,11,3,3,19,4,12,11,12,12,3,4,4,4,3,4,11],[19,11,3,3,11,20,4,4,4,4,21,4,3,23,3,11,3,12,4,0,1,11,3,11,12,19,4,11,19,13,3,12,4]] (.cons 0xffffffffffffffffffffff00ffffff00 (.branch [19,7,21] [[19,3,11,19,3,19,19,3,19,11,19,3,11,19,11,1,11,19,3,3,19,11,19,19,3,3,11,19,3,4,19,3,4,11,19,3,11,4,11,19,19,1,3,3,4,11,4,19,3,3,3,3,3,3,3,3,3,3,3,11,12,11,19,19],[11,20,3,3,3,3,3,3,19,11,19,11,1,1,19,4,11,11,3,11,11,11,3,11,11,11,3,1,7,19,19,11,4,3,3,11,11,11,11,11,3,19,3,19,19,3,19,19,11,19,3,19,11,12,11,11,4,3,3,19,11,19,19,19],[3,3,4,19,3,4,11,19,3,11,4,11,19,19,1,3,3,4,11,4,19,3,3,3,3,3,3,3,3,11,12,11,19,19,11,20,3,3,3,3,3,3,11,11,11,11,4,11,1,11]] (.nil)) (.nil))) (.cons 0xffffffffffff0000ffffffffffff0000 (.branch [17,14,12,4] [[3,11,19,3,19,11,19,3,19,19,1,19,3,3,19,19,11,11,19,19,19,19,19,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,11,11,3,11,11,11,3,11,11,11,11,3,3,11,11,1,11,11,11],[11,11,19,12,12,11,19,3,12,12,11,19,1,1,3,12,11,19,3,19,11,19,3,19,19,19,19,3,3,19,19,11,11,19,19,19,19,19,19,3,12,11,19,3,12,11,19,19,3,3,12,12,11,11,19,1,3,12,11,3,3,3,3,3],[3,3,3,3,3,3,3,3,3,3,3,3,3,3,11,19,12,3,12,11,12,19,19,27,3,3,12,11,11,19,12,12,3,11,11,11,3,11,11,11,11,3,3,11,11,1,11,11,11,11,11,12,11,13,3,12,11,19,13,3,12,11,1,19],[19,3,19,11,19,19,13,27,3,12,12,11,11,19,19,19,3,19,11,1]] (.nil)) (.nil)))) (.nil)))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_15 : chkCheckNode s15_maskYF s15_edgePts s15_edgeTT s15_raw s15_masksTT s15_cuts [] s15_auts s15_cert = true := by decide +kernel

-- State #16: n=6 |E|=6 |F|=1 nodes=1 cands=102 wits=103 cuts=7
def s16_desc : StateDesc := ⟨6,[(0,1),(0,4),(1,4),(2,3),(2,5),(3,5)],[(4,5)]⟩
def s16_maskYF : Nat := 0xffffffffffff
def s16_edgePts : Nat := 0x11000061008
def s16_edgeTT : Nat := 0xfff8feeef888
def s16_raw : List Nat := chkMkRaw 6 s16_maskYF
def s16_masksTT : List Nat := chkMkMasksTT 6 s16_desc.edges s16_maskYF
def s16_autIdxTbls : List (List Nat) := []
def s16_auts : List (List Nat) := []
def s16_cutSpecs : List CutSpecData := [⟨0,[(2,3)],[2,3],2,[0,1,4]⟩,⟨2,[],[0],2,[2,3,5]⟩,⟨8,[],[2],2,[0,1,4]⟩,⟨3,[],[],2,[2,3,5]⟩,⟨36,[],[],2,[0,1,4]⟩,⟨17,[],[],2,[2,3,5]⟩,⟨36,[],[],2,[0,1,4]⟩]
def s16_cuts : List CutDefData := chkMkCuts s16_maskYF s16_raw [(1,[.e [(2,3)]]),(2,[.v 1 [20,9]]),(2,[.v 3 [4,34]]),(3,[.v 0 [2,20,24,34],.v 1 [16]]),(3,[.v 2 [8,34,24],.v 5 []]),(3,[.v 4 [5,10],.v 0 [6,10]]),(3,[.v 5 [5,10],.v 2 [8]])]
def s16_cert : CertNode := .branch [5,6,1,0] [[11,11,3,3,11,11,11,11,11,11,3,3,11,11,11,11,11,3,3,19,27,27,27,27,3,3,3,3,3,3,3,3,3,3,3,19,19,19,19,0,11,11,11,11,3,3,3,3,12,19,4,19,4,19]] (.cons 0xffffffff0000 (.branch [3,4,2] [[11,19,3,11,11,19,3,3,19,11,19,3,11,3,11,11,11,3,3,11,11,11,3,3,19,11,11,3,3,12,19,11,3,3,3,3,3,3,3,3,3,3,11,3,19,11,4,3,1]] (.nil)) (.nil))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_16 : chkCheckNode s16_maskYF s16_edgePts s16_edgeTT s16_raw s16_masksTT s16_cuts [] s16_auts s16_cert = true := by decide +kernel

-- State #17: n=2 |E|=1 |F|=0 nodes=0 cands=0 wits=0 cuts=0
def s17_desc : StateDesc := ⟨2,[(0,1)],[]⟩
-- Unique trivial base state K_2 (|E| = 1, OrCostYF ≥ 0)

-- State #18: n=6 |E|=6 |F|=1 nodes=1 cands=89 wits=90 cuts=5
def s18_desc : StateDesc := ⟨6,[(0,1),(0,2),(1,4),(2,5),(3,4),(3,5)],[(4,5)]⟩
def s18_maskYF : Nat := 0xffffffffffff
def s18_edgePts : Nat := 0x11001040028
def s18_edgeTT : Nat := 0xfff8ffeca8a8
def s18_raw : List Nat := chkMkRaw 6 s18_maskYF
def s18_masksTT : List Nat := chkMkMasksTT 6 s18_desc.edges s18_maskYF
def s18_autIdxTbls : List (List Nat) := []
def s18_auts : List (List Nat) := []
def s18_cutSpecs : List CutSpecData := [⟨0,[(0,2)],[0,1,2,4],17,[3,5]⟩,⟨0,[(3,4)],[3,4,1,0],17,[2,5]⟩,⟨8,[],[4,1,0],17,[2,5]⟩,⟨40,[],[2,0],17,[1,4]⟩,⟨23,[],[],17,[3,5]⟩]
def s18_cuts : List CutDefData := chkMkCuts s18_maskYF s18_raw [(1,[.e [(0,2)]]),(1,[.e [(3,4)]]),(2,[.v 3 [20,17,34]]),(3,[.v 5 [9,4],.v 3 [20]]),(5,[.v 1 [9,20,33],.v 0 [20,12],.v 4 [12],.v 2 [32]])]
def s18_cert : CertNode := .branch [4,3,0,1] [[11,11,3,11,3,11,11,11,11,11,3,19,3,27,27,27,27,3,11,3,11,11,11,11,3,3,3,3,3,3,3,19,19,19,19,3,3,3,3,0,11,11,3,11,12,5,3,4,12,3,4,3,4,3]] (.cons 0xffffffff0000 (.branch [4,3,0,2] [[27,3,11,3,19,3,11,11,27,27,27,3,11,27,3,19,3,11,27,3,4,3,3,3,3,3,3,3,3,3,19,3,6,3,4,1]] (.nil)) (.nil))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_18 : chkCheckNode s18_maskYF s18_edgePts s18_edgeTT s18_raw s18_masksTT s18_cuts [] s18_auts s18_cert = true := by decide +kernel

-- State #19: n=6 |E|=6 |F|=0 nodes=0 cands=54 wits=54 cuts=4
def s19_desc : StateDesc := ⟨6,[(0,1),(0,2),(1,3),(2,4),(3,5),(4,5)],[]⟩
def s19_maskYF : Nat := 0xffffffffffffffff
def s19_edgePts : Nat := 0x1010000100428
def s19_edgeTT : Nat := 0xffffffa8fcf8eca8
def s19_raw : List Nat := chkMkRaw 6 s19_maskYF
def s19_masksTT : List Nat := chkMkMasksTT 6 s19_desc.edges s19_maskYF
def s19_autIdxTbls : List (List Nat) := []
def s19_auts : List (List Nat) := []
def s19_cutSpecs : List CutSpecData := [⟨0,[(1,3)],[1,0,2,3],17,[4,5]⟩,⟨0,[(2,4)],[2,0,1,3],17,[4,5]⟩,⟨48,[],[2,0],17,[1,3]⟩,⟨15,[],[],17,[4,5]⟩]
def s19_cuts : List CutDefData := chkMkCuts s19_maskYF s19_raw [(1,[.e [(1,3)]]),(1,[.e [(2,4)]]),(3,[.v 5 [12,18],.v 4 [12]]),(5,[.v 0 [12,18,34],.v 1 [12,24],.v 2 [24],.v 3 [32]])]
def s19_cert : CertNode := .branch [3,2,0,1] [[11,11,11,3,3,11,11,11,11,11,11,3,3,11,11,11,11,19,3,3,27,27,27,27,3,3,19,19,19,19,3,3,3,3,3,3,3,3,3,11,11,11,11,3,12,12,4,3,5,4,3,4,3,3]] (.nil)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_19 : chkCheckNode s19_maskYF s19_edgePts s19_edgeTT s19_raw s19_masksTT s19_cuts [] s19_auts s19_cert = true := by decide +kernel

-- State #20: n=7 |E|=7 |F|=1 nodes=1 cands=120 wits=121 cuts=4
def s20_desc : StateDesc := ⟨7,[(0,1),(0,2),(1,3),(2,5),(3,6),(4,5),(4,6)],[(5,6)]⟩
def s20_maskYF : Nat := 0xffffffffffffffffffffffff
def s20_edgePts : Nat := 0x101000001001000000428
def s20_edgeTT : Nat := 0xffffffa8fffffcf8eca8eca8
def s20_raw : List Nat := chkMkRaw 7 s20_maskYF
def s20_masksTT : List Nat := chkMkMasksTT 7 s20_desc.edges s20_maskYF
def s20_autIdxTbls : List (List Nat) := []
def s20_auts : List (List Nat) := []
def s20_cutSpecs : List CutSpecData := [⟨0,[(0,1)],[0,1,2,3,5],17,[4,6]⟩,⟨16,[],[5,2,0,1],17,[3,6]⟩,⟨88,[],[1,0],17,[2,5]⟩,⟨47,[],[],17,[4,6]⟩]
def s20_cuts : List CutDefData := chkMkCuts s20_maskYF s20_raw [(1,[.e [(0,1)]]),(2,[.v 4 [41,70]]),(4,[.v 3 [22,65,34],.v 6 [18],.v 4 [32]]),(6,[.v 2 [25,34,40,65],.v 0 [34,66],.v 1 [40],.v 5 [16],.v 3 [64]])]
def s20_cert : CertNode := .branch [3,2,1,0] [[19,11,3,11,3,19,19,19,19,19,19,11,3,11,3,19,19,19,19,19,19,3,11,3,11,11,11,11,11,11,3,3,3,3,3,3,3,3,3,11,11,11,11,11,11,3,3,3,3,3,3,27,27,27,27,27,0,19,11,3,12,4,19,11],[3,5,4,11,3,19,19,3,11,11,3,3,4]] (.cons 0xffffffffffffffff00000000 (.branch [3,2,1,0] [[11,3,11,3,11,3,27,19,19,19,19,19,19,3,11,11,3,11,3,11,11,11,3,11,11,3,3,3,3,3,3,3,3,3,3,3,11,3,27,11,3,5,4,1]] (.nil)) (.nil))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_20 : chkCheckNode s20_maskYF s20_edgePts s20_edgeTT s20_raw s20_masksTT s20_cuts [] s20_auts s20_cert = true := by decide +kernel

-- State #21: n=7 |E|=8 |F|=1 nodes=1 cands=165 wits=166 cuts=5
def s21_desc : StateDesc := ⟨7,[(0,1),(0,5),(1,5),(2,3),(2,6),(3,6),(4,5),(4,6)],[(5,6)]⟩
def s21_maskYF : Nat := 0xffffffffffffffffffffffff
def s21_edgePts : Nat := 0x101100001000600001008
def s21_edgeTT : Nat := 0xfffffff8fffffeeef888f888
def s21_raw : List Nat := chkMkRaw 7 s21_maskYF
def s21_masksTT : List Nat := chkMkMasksTT 7 s21_desc.edges s21_maskYF
def s21_autIdxTbls : List (List Nat) := []
def s21_auts : List (List Nat) := []
def s21_cutSpecs : List CutSpecData := [⟨0,[(1,5)],[1,0,5,4],2,[2,3,6]⟩,⟨0,[(3,6)],[3,2,6,4],2,[0,1,5]⟩,⟨16,[],[],16,[0,1,2,3,5,6]⟩,⟨76,[],[4],2,[0,1,5]⟩,⟨51,[],[],2,[2,3,6]⟩]
def s21_cuts : List CutDefData := chkMkCuts s21_maskYF s21_raw [(1,[.e [(1,5)]]),(1,[.e [(3,6)]]),(2,[.v 4 [40,66,36,65]]),(4,[.v 2 [26,65,40,66],.v 3 [66],.v 6 [18]]),(5,[.v 0 [22,40,66],.v 1 [40],.v 5 [24],.v 4 [64]])]
def s21_cert : CertNode := .branch [4,3,2,0,1] [[19,19,11,11,19,3,3,19,19,19,19,19,19,11,11,19,3,3,19,19,19,19,19,11,11,27,3,3,35,35,35,35,35,11,11,3,3,11,11,11,11,11,11,3,3,11,11,11,11,11,3,3,27,27,27,27,27,3,3,3,3,3,3,3],[3,3,3,3,0,19,12,11,13,3,19,5,11,4,3,19,11,19,3,11,4,3,11,3,3]] (.cons 0xffffffffffffffff00000000 (.branch [3,4,2,0,1] [[19,3,19,11,35,3,3,27,11,11,19,19,19,19,19,19,3,4,11,19,19,3,3,27,11,11,35,19,3,4,11,3,3,3,3,3,3,3,3,3,3,3,3,3,3,11,19,19,35,3,3,11,11,27,19,4,3,11,11,11,11,3,3,11],[11,11,11,11,3,11,3,11,4,3,12,11,1]] (.nil)) (.nil))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_21 : chkCheckNode s21_maskYF s21_edgePts s21_edgeTT s21_raw s21_masksTT s21_cuts [] s21_auts s21_cert = true := by decide +kernel

-- State #22: n=7 |E|=8 |F|=1 nodes=5 cands=531 wits=662 cuts=13
def s22_desc : StateDesc := ⟨7,[(0,1),(0,4),(1,5),(2,4),(2,6),(3,5),(3,6),(5,6)],[(4,6)]⟩
def s22_maskYF : Nat := 0xffff0000ffffffffffffffffffff
def s22_edgePts : Nat := 0x1000001100000010400120008
def s22_edgeTT : Nat := 0xffff0000fff8fffeffccfafa8888
def s22_raw : List Nat := chkMkRaw 7 s22_maskYF
def s22_masksTT : List Nat := chkMkMasksTT 7 s22_desc.edges s22_maskYF
def s22_autIdxTbls : List (List Nat) := []
def s22_auts : List (List Nat) := []
def s22_cutSpecs : List CutSpecData := [⟨32,[],[1,0,3,4],17,[2,6]⟩,⟨2,[],[0,4,2],2,[3,5,6]⟩,⟨4,[],[4,0,1],2,[3,5,6]⟩,⟨8,[],[],18,[1,0,5,2,4,6]⟩,⟨0,[(5,6)],[],26,[0,1,2,3,4,5,6]⟩,⟨76,[],[4,0],17,[1,5]⟩,⟨84,[],[0,1],17,[3,5]⟩,⟨104,[],[1,0],17,[2,4]⟩,⟨85,[],[1],17,[3,5]⟩,⟨108,[],[1],17,[0,4]⟩,⟨23,[],[],2,[3,5,6]⟩,⟨59,[],[],17,[2,6]⟩,⟨59,[],[],17,[2,6]⟩]
def s22_cuts : List CutDefData := chkMkCuts s22_maskYF s22_raw [(3,[.v 5 [64,26,66]]),(2,[.v 1 [65,48,1]]),(2,[.v 2 [48,66,24,65]]),(2,[.v 3 [37,66,48]]),(1,[.e [(5,6)]]),(5,[.v 2 [16,64],.v 3 [66],.v 6 [32]]),(5,[.v 2 [26,66,48,65],.v 6 [],.v 4 [33]]),(5,[.v 3 [37,66,48,65],.v 5 [64],.v 6 []]),(6,[.v 0 [2,48],.v 4 [],.v 2 [],.v 6 [32]]),(6,[.v 3 [],.v 2 [48,66,65],.v 6 [],.v 5 [2]]),(5,[.v 0 [14,48,24,66],.v 1 [32],.v 4 [36],.v 2 [64]]),(7,[.v 0 [2,24,18],.v 3 [66,48],.v 1 [48],.v 4 [],.v 5 [64]]),(7,[.v 1 [1,36],.v 3 [37,48,64],.v 0 [16],.v 4 [4],.v 5 [64]])]
def s22_cert : CertNode := .branch [10,3,2,4,1] [[11,11,19,19,27,3,3,27,27,27,27,27,11,11,11,11,3,3,11,11,11,11,11,11,11,11,3,3,11,11,11,11,11,19,19,3,3,19,19,19,19,19,19,3,3,19,19,19,19,19,3,3,35,35,35,35,35,3,3,3,3,3,3,3],[3,3,3,3,0,0,11,19,35,3,5,11,19,35,3,11,19,35,3,11,11,3,19,3,3]] (.cons 0xffff0000ffffffffffff00000000 (.branch [12,5,4,10] [[11,3,19,11,11,3,27,3,4,4,4,4,12,4,3,11,11,11,11,3,11,3,11,11,11,3,11,3,3,3,3,3,3,3,3,3,3,3,3,11,27,3,29,11,3,27,1]] (.nil)) (.cons 0xffff0000ffffffff0000ffff0000 (.branch [10,3,2,1,4] [[11,19,3,11,11,19,19,27,3,3,35,11,19,27,3,11,3,11,11,11,11,11,3,3,11,11,11,11,3,3,35,11,11,27,3,3,19,19,19,19,19,19,3,3,3,3,3,3,3,3,3,3,3,3,11,27,3,0,11,27,3,0,1]] (.cons 0xffff0000ffffffffffffffff0000 (.branch [11,6,0] [[11,4,3,19,11,3,19,19,11,11,19,3,3,4,19,4,11,4,3,11,3,11,11,3,19,4,19,19,3,3,11,11,11,11,11,11,3,19,4,11,3,19,19,4,19,11,11,3,3,12,5,4,11,3,3,3,3,3,3,3,3,3,3,3],[3,3,3,3,3,3,5,3,1]] (.nil)) (.cons 0xffff0000ffffffffffff00000000 (.branch [7,6,1,10] [[3,3,3,3,3,3,3,1,3,3,3,3,3,3,3,3,3,3,11,11,11,3,11,11,3,3,1,11,11,11,11,11,11,11,11,3,19,11,27,3,11,19,27,19,1,1,3,11,19,27,3,3,3,0,3,3,12,11,11,19,27,19,3,3],[3,3,3,3,11,11,3,11,11,3,3,1,11,11,11,11,11,3,11,11,19,3,11,19,19,19,3,3,11,11,19,19,19,19,3,11,19,11,27,4,11,27,19,4,11,19,27,4,1]] (.cons 0xfff00000fff0fff0ff00f0f00000 (.branch [9,8,0,4] [[1,3,1,1,1,1,4,4,1,11,27,1,3,1,19,11,11,4,4,1,4,4,1,1,1,3,4,4,1,11,3,27,1,19,11,11,19,4,4,1,4,4,1,1,1,1,1,4,4,1,11,27,1,1,19,11,11,4,4,1,1,4,4,1],[3,1,1,1,3,3,1,3,3,1,1,3,3,3,3,3,3,1,3,3,1,1,4,1,4,4,4,11,27,1,19,11,11,4,4,4,1,4,4,1,1,3,3,3,4,4,3,11,27,3,3,19,11,11,4,4,3,3,4,4,19,3,1,3],[3,3,19,3,1,3,11,3,19,1,3,19,19,11,11,19,19,3,19,19,3,3,1,4,3,1,4,4,4,3,11,27,3,3,1,19,11,11,4,4,3,4,4,1,1,3,1,3,3,1,3,3,3,3,3,3,3,3,3,3,3,1,3,3],[1,4,1,4,4,4,1,11,27,3,3,19,11,11,4,4,4,1,4,4,4,4,4,4,11,3,27,19,11,11,4,4,4,4,4,3,3,3,4,27,4,1,3,19,4,11,3,4,19,11,11,1,1,3,4,6,11,1,3,1,3,3,3,3],[1,4,27,4,1,19,19,19,19,4,11,19,4,11,11,19,4,6,11,19,1]] (.nil)) (.nil))) (.nil)))) (.nil)))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_22 : chkCheckNode s22_maskYF s22_edgePts s22_edgeTT s22_raw s22_masksTT s22_cuts [] s22_auts s22_cert = true := by decide +kernel

-- State #23: n=7 |E|=8 |F|=1 nodes=42 cands=4019 wits=6574 cuts=39
def s23_desc : StateDesc := ⟨7,[(0,3),(0,5),(1,4),(1,5),(2,5),(2,6),(3,6),(4,6)],[(3,4)]⟩
def s23_maskYF : Nat := 0xffffff00ffffff00ffffff00ffffff
def s23_edgePts : Nat := 0x101100000001600040200
def s23_edgeTT : Nat := 0xfffffe00fffff000fefefe00ccaa00
def s23_raw : List Nat := chkMkRaw 7 s23_maskYF
def s23_masksTT : List Nat := chkMkMasksTT 7 s23_desc.edges s23_maskYF
def s23_autIdxTbls : List (List Nat) := chkMkAutIdxTbls 7 [[1,0,2,4,3,5,6]]
def s23_auts : List (List Nat) := chkMkAutMaskTbls s23_autIdxTbls
def s23_cutSpecs : List CutSpecData := [⟨64,[],[2,3,0,4],17,[1,5]⟩,⟨0,[(0,5)],[0,3],4,[1,4,5,6,2]⟩,⟨0,[(4,6)],[4,1],4,[0,3,5,6,2]⟩,⟨2,[],[4],4,[0,3,5,6,2]⟩,⟨4,[],[],18,[5,0,1,6,3,4]⟩,⟨33,[],[1,2,3],17,[4,6]⟩,⟨34,[],[0,2,3],17,[4,6]⟩,⟨36,[],[0,1,3],17,[4,6]⟩,⟨9,[],[],4,[1,4,5,6,2]⟩,⟨9,[],[],4,[1,4,5,6,2]⟩,⟨38,[],[0,3],17,[4,6]⟩,⟨26,[],[0,5],17,[2,6]⟩,⟨26,[],[0,5],17,[2,6]⟩,⟨84,[],[1,3],17,[0,5]⟩,⟨100,[],[0],17,[1,4]⟩,⟨43,[],[2],17,[4,6]⟩,⟨77,[],[4],17,[1,5]⟩,⟨77,[],[4],17,[1,5]⟩,⟨77,[],[4],17,[1,5]⟩,⟨77,[],[4],17,[1,5]⟩,⟨86,[],[3],17,[0,5]⟩,⟨45,[],[1],17,[4,6]⟩,⟨77,[],[4],17,[1,5]⟩,⟨114,[],[],17,[0,3]⟩,⟨58,[],[],17,[2,6]⟩,⟨105,[],[],17,[1,4]⟩,⟨114,[],[],17,[0,3]⟩,⟨101,[],[],17,[1,4]⟩,⟨109,[],[],17,[1,4]⟩,⟨109,[],[],17,[1,4]⟩,⟨118,[],[],17,[0,3]⟩,⟨91,[],[],17,[2,5]⟩,⟨109,[],[],17,[1,4]⟩,⟨109,[],[],17,[1,4]⟩,⟨118,[],[],17,[0,3]⟩,⟨109,[],[],17,[1,4]⟩,⟨59,[],[],17,[2,6]⟩,⟨109,[],[],17,[1,4]⟩,⟨91,[],[],17,[2,5]⟩]
def s23_cuts : List CutDefData := chkMkCuts s23_maskYF s23_raw [(3,[.v 6 [7,40,17,48,12,4]]),(1,[.e [(0,5)]]),(1,[.e [(4,6)]]),(2,[.v 1 [21,96]]),(2,[.v 2 [65,40,96]]),(4,[.v 0 [96,12],.v 5 [66,10]]),(4,[.v 5 [66,21,10,65],.v 1 [16]]),(4,[.v 5 [20,67,10],.v 2 [67]]),(3,[.v 0 [14,96],.v 3 []]),(3,[.v 3 [7,96],.v 0 [96]]),(5,[.v 1 [21,40,96],.v 2 [40,65,96],.v 5 [1]]),(5,[.v 1 [17,40],.v 3 [],.v 4 [96]]),(5,[.v 1 [21,96,40],.v 4 [],.v 3 [1]]),(5,[.v 2 [65,40],.v 4 [2],.v 6 [40]]),(6,[.v 2 [67,40,48,96],.v 6 [],.v 5 [10,17]]),(6,[.v 0 [],.v 1 [48,16,32],.v 3 [],.v 5 []]),(6,[.v 0 [96,8,40],.v 2 [66,40],.v 3 [],.v 6 [48]]),(6,[.v 0 [8,32,40],.v 3 [],.v 2 [32],.v 6 [48]]),(6,[.v 0 [96,12],.v 3 [],.v 6 [4],.v 2 [32]]),(6,[.v 2 [],.v 0 [8,96,40],.v 3 [],.v 6 [48]]),(6,[.v 2 [65,40],.v 6 [17],.v 4 [],.v 1 [32]]),(6,[.v 3 [1,66,65],.v 2 [32],.v 0 [32],.v 5 [66]]),(6,[.v 3 [],.v 2 [67,48],.v 6 [],.v 0 [32]]),(7,[.v 1 [16,32,40,48],.v 4 [],.v 5 [65],.v 6 [5,8]]),(7,[.v 1 [21,96,40,48],.v 5 [17,12],.v 4 [],.v 3 [65,1,64]]),(7,[.v 5 [21,10],.v 0 [8],.v 3 [],.v 6 [6,20]]),(7,[.v 5 [66,65],.v 1 [16],.v 4 [],.v 6 [5,12]]),(7,[.v 6 [7,21,17,4,12],.v 0 [14,32,8,48,40],.v 2 [48,40],.v 5 [10]]),(7,[.v 0 [32,14],.v 2 [32,40],.v 3 [],.v 5 [66],.v 6 [16]]),(7,[.v 0 [],.v 3 [],.v 6 [6,16],.v 2 [48],.v 5 [2]]),(7,[.v 1 [40,16],.v 2 [40,65],.v 4 [],.v 5 [65],.v 6 [8]]),(7,[.v 1 [16,32,40,48],.v 4 [],.v 3 [1],.v 6 [],.v 0 [32]]),(7,[.v 2 [],.v 0 [10,96,48,40],.v 3 [],.v 6 [48],.v 5 []]),(7,[.v 2 [64,32,96],.v 0 [8],.v 5 [10],.v 3 [],.v 6 [16]]),(7,[.v 2 [],.v 1 [96,16,40,48],.v 4 [],.v 6 [],.v 5 [1]]),(7,[.v 2 [],.v 3 [],.v 6 [],.v 0 [32,48],.v 5 [2]]),(7,[.v 3 [],.v 4 [7,65,2],.v 0 [32],.v 1 [32],.v 5 [4]]),(7,[.v 3 [],.v 6 [21,6],.v 2 [],.v 0 [48],.v 5 [2]]),(7,[.v 4 [],.v 3 [1,65],.v 0 [],.v 6 [],.v 1 [32]])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
def s23_cert : CertNode := .branch [9,4,3,1,2] [[3,2,2,2,2,2,2,2,35,2,2,2,3,3,3,3,3,3,3,2,3,3,3,11,2,2,11,3,11,2,11,2,11,2,2,11,3,11,2,11,2,11,2,19,3,2,2,19,2,19,2,3,2,2,19,2,2,3,27,2,27,27,2,3],[3,2,3,3,0,2,3,11,2,4,2,3,11,2,4,0,2,2,2,3,3,3,2,11,19]] (.cons 0xffffff00ffffff00ffffff00000000 (.branch [21,6,13] [[3,2,2,2,2,2,2,2,2,2,2,2,20,2,2,2,3,3,3,3,3,3,3,3,3,3,3,2,3,3,3,2,19,2,3,2,2,11,3,11,19,2,19,2,19,12,2,3,2,2,2,2,3,2,2,3,2,12,2,3,19,11,11,2],[3,11,2,3,19,2,2,3,2,3,2,5,1]] (.nil)) (.cons 0xffff0000ffff0000ffff0000ffff00 (.branch [8,4] [[2,3,11,11,2,2,3,3,0,2,4,0,2,0,3,2,4,2,2,2,3,3,2,2,4,2,3,2,3,3,3,2,2,3,3,3,2,3,2,11,11,2,3,0,0,11,2,3,2,4,11,11,2,2,2,3,3,3,0,2,4,11,2,3],[2,4,11,2,3,1]] (.cons 0xffffff00ffff0000ffffff00000000 (.branch [16,11,4] [[19,2,3,2,3,19,19,2,2,3,3,1,2,12,19,2,3,19,2,3,2,3,19,19,2,2,3,3,1,2,12,19,2,3,1,2,2,2,2,2,1,2,2,2,2,2,2,2,12,2,2,2,19,11,3,11,3,1,19,19,11,11,3,3],[12,2,19,11,3,2,3,19,2,3,19,2,19,19,2,2,3,3,19,2,19,2,19,3,2,2,2,2,2,11,2,2,2,2,3,2,2,11,2,11,3,3,3,3,2,3,3,3,3,2,3,3,2,3,3,2,2,3,13,19,2,3,6,2],[12,19,2,3,1,2,3,13,13,19,2,2,3,3,6,2,12,19,2,3]] (.nil)) (.cons 0xfffff000fffff000f0f0f000f0f0f0 (.branch [18,4,0] [[11,2,3,1,11,2,2,3,3,6,2,4,1,2,3,11,2,3,11,11,2,2,3,3,0,2,19,1,2,19,2,4,11,2,3,11,2,19,11,2,2,3,3,11,2,4,2,0,1,2,2,1,2,2,2,2,2,2,2,4,2,2,2,4],[3,1,11,11,4,4,3,3,4,2,11,4,3,2,3,11,2,2,3,3,6,2,4,2,3,19,1,2,2,3,3,11,19,0,11,2,19,11,11,2,2,2,3,3,3,0,2,19,1,2,3,2,4,11,2,3]] (.cons 0xffffff00fffff000ffffff00000000 (.branch [19,12] [[2,4,2,4,3,2,2,4,4,1,2,5,2,0,1,1,2,2,2,2,1,2,2,1,2,2,2,2,2,2,2,12,2,2,2,1,3,11,4,5,1,11,4,1,3,3,11,11,4,4,5,2,3,5,13,1,2,4,3,2,4,1,3,2],[2,4,4,3,2,12,1,2,13,1,2,4,3,2,4,1,3,2,2,4,4,3,2,12,1,2,4,1,2,4,1,2,4,6,1,2,2,4,4,1,2,5,1,2,4,1,2,2,2,2,1,2,2,1,2,2,2,2,2,2,2,12,2,2],[2,3,11,4,5,1,11,4,1,3,3,11,11,4,4,5,2,3,11,4,2,3,1,1,2,3,1,2,3,3,2,3,2,2,3,3,1,3,2,3,2,3,11,2,2,2,2,11,2,2,2,2,2,2,11,2,2,2,2,11,2,2,11,2],[11,4,4,4,2,4,4,4,11,4,4,2,4,3,3,11,2,4,4,2,4,3,2,2,4,0,2,4,2,5,2,4,1,1,1,2,4,6,1,2,2,4,4,1,2,5,1,2,4]] (.cons 0xfffffa00fffffa00fafafa00aaaaaa (.branch [35,12,26] [[5,1,4,1,1,11,3,1,11,5,5,1,11,11,3,4,1,12,4,1,5,3,6,4,11,11,6,6,11,11,4,1,12,4,0,1,1,1,19,4,3,1,1,3,11,4,19,1,11,4,1,3,3,11,11,19,4,19,4,3,6,4,1,19],[1,3,1,1,3,11,4,19,1,11,1,1,3,3,11,11,19,1,19,4,3,4,4,3,4,1,1,11,3,3,11,1,1,3,11,11,3,4,3,4,4,1,6,3,3,1,4,11,1,11,3,3,11,11,1,4,1,4,4,11,1,1,19,4],[3,1,1,3,11,4,19,1,11,4,1,3,3,11,11,19,4,19,4,3,11,4,19,1,3,1,1,3,11,4,19,1,11,1,1,3,3,11,11,19,1,19,4,3,4,4,3,4,1,1,11,3,3,11,1,1,3,11,11,3,4,3,4,4],[1,11,3,5,19,3,3,5,3,11,6,6,3,3,3,11,3,3,11,11,19,5,19,4,3,11,3,1,4,1,1,11,19,1,11,5,5,1,11,11,19,4,1,12,4,1,5,3,19,19,3,1,19,19,3,19,1,19,19,3,11,3,1,19],[19,1,3,11,19,19,19,19,3,11,11,19,1,19,19,3,19,19,1,3,1,1,3,11,12,19,1,11,4,1,3,3,11,11,19,4,19,1,3,11,4,3,4,4,4,4,4,4,3,11,4,4,4,4,19,4,4,4,11,4,3,3,11,11],[19,4,19,4,3,4,4,3,3,1,1,1,3,3,3,3,1,1,3,3,1,3,3,3,3,3,3,3,3,3,1,3,3,3,3,3,11,19,11,13,11,11,19,12,11,11,11,1,5,1,19,19,3,3,1,11,19,1,11,5,5,1,11,11],[19,4,1,12,4,1,11,19,19,19,1,3,11,11,11,11,19,11,6,0,11,4,12,4,11,19,1,1,1,11,5,5,1,11,11,19,4,1,12,4,1,11,5]] (.cons 0xfffffe00fffffc00fefefe00cccccc (.term) (.cons 0xffffff00fffff000ffffff00ffff00 (.term) (.nil)))) (.cons 0xffffff00fffff000ffffff00ffff00 (.branch [27,10,11] [[2,4,2,4,2,4,12,2,2,4,4,1,2,20,2,4,2,4,2,3,1,1,1,2,12,2,4,1,1,2,3,1,2,4,12,2,3,2,2,4,4,1,12,2,12,2,4,11,2,2,5,2,2,2,2,11,2,2,2,2,2,2,2,5],[2,2,2,2,2,3,2,2,2,4,2,2,2,11,2,11,0,2,20,21,4,3,2,4,12,11,4,4,3,13,2,4,4,3,11,4,2,3,3,12,11,2,3,4,2,4,4,2,2,3,1,2,3,1,2,4,1,2,3,3,1,2,2,3],[3,1,2,3,1,2,3]] (.cons 0xfffffa00fffff000fafafa00aaaa00 (.term) (.nil))) (.nil)))) (.cons 0xfffffa00aaaaaa00fafafa00aaaaaa (.branch [37,10,6] [[12,3,12,4,5,3,4,11,12,12,4,3,4,11,11,1,3,4,5,3,11,1,19,12,5,4,19,5,3,5,4,11,4,3,4,19,11,11,19,4,19,3,12,11,3,19,19,19,3,19,19,11,19,19,19,3,19,11,11,3,19,19,3,19],[19,1,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,12,4,12,3,4,11,12,12,4,3,4,11,11,19,3,4,12,3,11,19,5,4,5,3,5,4,11,6,4,3,4,11,11,4,19,6,3,12,11,19,11],[19,0,4,4,11,19,19,1,19,3,11,19,19,11,5,4,11,11,4,19,4,19,4,3,12,19,11,11,11,19,3,3,19,4,3,1,11,4,19,3,19,11,19]] (.cons 0xffffff00fffff000ffffff00000000 (.branch [34,25,8] [[11,12,12,12,12,11,12,12,3,4,19,19,12,11,12,12,11,12,4,19,12,12,12,3,11,4,19,11,12,12,3,12,1,3,3,3,3,1,3,3,3,3,3,3,3,1,3,3,3,3,3,3,3,3,1,3,3,3,3,1,3,3,3,3],[12,12,3,3,1,12,12,4,1,3,19,3,1,12,12,3,4,3,3,12,12,1,11,4,1,19,1,12,12,12,1,11,11,19,11,19,19,4,19,3,11,4,11,19,1,5,20,14,19,1,1,3,4,19,12,20,11,20,3,5,11,1,4,19],[1,3,3,11,4,11,19,11,20,3,14,19,1,3,4,19,12,20,11,19,3,20,11,1,4,19,1,3,3,11,4,11,19,11,20,3,20,19,1,4,19,3,19,11,19,3,6,3,4,19,1,3,11,4,11,19,3,20,20,1,14,19,1,4],[19,3,19,11,19,3,7,3,4,19,1,3,11,4,11,19,3,20,20,1,4,19,1,11,11,1,6,11,20,1,6,1,4,19,6,1,11,4,11,19,1,5,20,1,4,19,1,3,4,19,12,20,11,20,3,5,11,1,4,19,1,3,3,11],[4,11,19,11,20,3,4,19,3,4,19,12,20,11,19,3,20,11,1,4,19,1,3,3,11,4,11,19,11,20,3,4,19,3,3,3,3,3,3,1,1,3,3,1,3,3,3,3,3,3,3,3,3,1,3,3,3,3,3,19,4,4,11,4],[3,4,4,11,11,4,4,11,4,4,19,4,4,4,3,3,4,11,19,11,4,4,3,19,1,19,19,3,19,11,1,19,19,11,19,19,19,19,19,19,3,3,11,19,19,11,19,19,3,19,19,19,19,4,19,14,4,19,5,20,4,19,1,6],[11,20,1,6,1,1,1,4,19,6,1,11,4,11,19,1,5,20,1,4,19]] (.nil)) (.nil))) (.cons 0xffffff00ffff0000ffffff00ffff00 (.branch [27,25,8] [[1,2,3,3,2,3,1,3,2,2,3,3,3,2,3,1,2,3,2,19,3,2,19,11,3,2,2,11,19,3,11,2,20,1,2,19,1,2,3,3,2,3,1,3,2,2,3,3,3,2,3,1,2,3,2,19,1,3,2,3,1,2,19,11],[2,3,3,2,2,11,19,3,2,20,2,19,19,2,2,2,2,20,2,2,2,2,2,3,2,2,2,19,2,2,2,20,2,19,19,3,11,2,19,19,3,19,11,2,3,3,11,11,2,3,11,2,19,19,2,3,5,3,3,5,0,11,11,2],[3,3,1,11,2,2,11,19,0,2,3,1,2,3]] (.cons 0xffffff00fffff000ffffff00000000 (.branch [19,26] [[4,2,2,2,2,12,2,2,2,2,12,2,4,2,2,2,2,12,2,2,2,2,12,2,2,1,2,2,2,12,2,2,2,2,4,2,2,12,2,12,3,11,11,2,4,11,11,11,2,4,3,2,11,11,11,3,2,11,11,11,2,4,11,11],[4,1,11,2,4,3,3,11,2,4,11,2,4,3,2,1,1,1,2,4,1,1,2,4,1,1,2,4,1,2,5,1,2,4,2,3,1,1,1,2,3,2,3,1,1,2,3,1,1,2,3,1,2,3,3,2,3,1,2,2,3,3,1,2],[3,2,3,1,1,2,4,2,14,1,2,4,3,1,2,2,11,4,1,1,2,5,1,2,14,2,11,2,0,3,2,4,3,2,2,11,4,1,2,5,2,14,1,1,2,2,2,2,2,2,2,1,2,2,1,2,2,2,2,2,2,2,5,2],[2,2,1,3,12,4,3,5,14,11,1,5,4,1,3,3,11,5,11,4,11,2,3,5,14,1,2,4,1,2,14,1,2,4,1,1,2,2,11,4,1,2,5,1,2,14,1,2,4,1,2,4,1,2,4,1,1,2,2,11,4,1,2,5],[1,2,4,1,2,11,1,1,2,4,3,1,2,4,6,1,2,2,11,4,1,2,5,1,2,4,1,2,2,2,2,2,2,2,1,2,2,1,2,2,2,2,2,2,2,5,2,2,2,3,12,4,3,5,4,11,1,5,4,1,3,3,11,5],[11,4,11,2,3,5,4,2,3,1,1,1,2,3,3,1,1,2,3,1,2,3,3,2,3,2,2,3,3,1,3,2,3,2,3,4,2,2,2,2,2,2,2,2,2,12,2,2,1,2,2,2,12,2,2,2,2,4,2,2,12,2,12,4],[4,4,3,4,4,11,11,2,4,11,4,4,1,4,2,4,3,3,11,2,4,11,2,4,3,2,2,4,3,2,4,3,2,4,2,5,2,4,1,1,2,4,3,3,3,6,3,1,1,1,2,4,6,1,2,2,11,4,1,2,5,1,2,4]] (.cons 0xfffffa00fffff000fafafa00aaaa00 (.term) (.nil))) (.cons 0xffffff00ffffff00ffffff00000000 (.branch [19,26] [[4,2,2,2,2,12,2,2,2,12,2,4,2,2,2,2,12,2,2,2,2,12,2,2,1,2,2,2,12,2,2,2,2,4,2,2,12,2,12,3,11,11,2,4,11,11,2,4,3,2,11,11,11,3,2,11,11,11,2,4,11,11,4,1],[11,2,4,3,3,11,2,4,11,2,4,3,2,3,3,2,4,3,3,2,4,1,3,2,4,1,2,5,3,2,4,2,3,1,1,2,3,2,3,1,1,2,3,1,1,2,3,1,2,3,3,2,3,1,2,2,3,3,1,2,3,2,3,1],[2,4,2,14,1,2,4,3,1,2,2,11,4,1,1,2,5,1,2,14,2,4,2,0,3,2,4,3,2,2,11,4,3,2,5,2,14,1,1,2,2,2,2,2,2,2,1,2,2,1,2,2,2,2,2,2,2,5,2,2,2,1,3,12],[4,3,5,14,11,1,5,4,1,3,3,11,5,11,4,11,2,3,5,14,1,2,4,1,2,14,1,2,4,1,1,2,2,11,4,1,2,5,1,2,14,1,2,4,1,2,4,1,2,4,1,1,2,2,11,4,1,2,5,1,2,4,1,2],[2,2,2,2,2,2,1,2,2,1,2,2,2,2,2,2,2,5,2,2,2,3,12,4,3,5,4,11,1,5,4,1,3,3,11,5,11,4,11,2,3,5,4,2,3,1,1,1,2,3,3,1,1,2,3,1,2,3,3,2,3,2,2,3],[3,1,3,2,3,2,3,4,2,2,2,2,2,2,2,2,2,12,2,2,1,2,2,2,12,2,2,2,2,4,2,2,12,2,12,4,4,4,3,4,4,4,11,2,4,4,4,4,1,4,2,4,3,3,11,2,4,11,2,4,3,2,2,4],[6,2,4,6,2,4,2,5,2,4,6,1]] (.cons 0xfffffa00fffff000fafafa00aaaa00 (.term) (.nil))) (.nil)))) (.cons 0xffffff00ffffff00ffffff00000000 (.branch [19,26] [[2,4,2,4,3,2,2,11,4,6,2,5,2,14,1,1,2,2,2,2,1,2,2,1,2,2,2,2,2,2,2,5,2,2,2,1,3,12,4,11,1,5,4,1,3,3,11,5,11,4,5,2,3,5,14,1,2,4,3,2,4,1,3,2],[2,11,4,6,2,5,1,2,14,1,2,4,3,2,4,1,3,2,2,11,4,6,2,5,1,2,4,1,2,2,2,2,1,2,2,1,2,2,2,2,2,2,2,5,2,2,2,3,12,4,11,1,5,4,1,3,3,11,5,11,4,5,2,3],[5,4,2,3,1,1,2,3,1,2,3,3,2,3,2,2,3,3,1,3,2,3,2,3,4,2,2,2,2,12,2,2,2,2,2,2,12,2,2,2,2,4,2,2,12,2,12,4,4,11,2,4,4,4,4,4,4,2,4,3,3,11,2,4],[11,2,4,3,2,2,4,14,2,4,2,5,2,4,1]] (.nil)) (.nil)))))) (.cons 0xffffaa00ffffaa00aaaaaa00aaaaaa (.branch [36,20,3,1] [[27,19,11,11,19,19,27,4,4,3,4,19,1,27,3,19,1,11,11,19,19,27,3,5,4,3,11,5,1,4,3,27,19,4,27,4,3,11,11,19,19,3,27,13,3,0,0,1,19,3,1,11,11,19,19,27,3,4,1,4,19,3,3,3],[3,3,3,3,3,3,3,3,3,3,3,3,19,4,11,11,19,19,12,5,4,11,19,11,11,19,4,4,4,1,19,19,4,4,11,11,19,4,0,11,19,4,4,3,11,11,19,19,19,27,3,3,0,4,3,11,19,12,13,3,11,19,5]] (.cons 0xfffffa00f0f0f000fafafa00f0f0f0 (.branch [29,6,3] [[3,3,3,4,4,3,19,3,3,4,4,3,1,11,19,3,3,4,4,1,19,11,3,5,5,3,5,4,5,5,19,3,5,5,4,11,11,19,3,3,5,5,4,5,3,11,11,11,11,11,11,11,3,11,11,11,11,11,11,3,11,11,11,1],[11,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,5,5,5,4,5,5,19,3,6,5,4,11,19,3,5,11,6,4,19,3,3,11,5,11,5,5,3,1,11,3,4,5,11,3,11,5,5,19,11,3,3,5],[11,5,4,5,11,11,19,19,3,3,3,11,5,4,5,19,3,11,11,11,11,3]] (.nil)) (.cons 0xffffee00cccccc00eeeeee00cccccc (.branch [36,7,0] [[4,4,4,19,4,3,19,4,4,4,19,3,19,11,1,4,3,19,4,3,12,1,11,4,4,19,11,4,3,4,19,4,19,3,19,11,11,11,3,4,11,3,4,4,11,11,11,11,3,11,11,11,11,11,11,3,11,11,11,3,11,11,3,11],[1,11,4,4,19,11,4,3,4,19,4,19,3,19,11,11,11,3,4,4,3,4,4,4,19,4,3,19,4,4,4,19,3,19,11,11,4,3,19,4,3,12,11,4,19,4,3,5,19,4,4,19,3,19,11,3,19,11,4,3,12,5,19,11],[19,4,4,19,11,11,11,19,19,11,11,11,11,1,4,3,3,19,11,11,19,11,12,5,19,11,19,19,4,11,19,4,19,11,19,11,4,19,3,19,11,11,4,4,11,3,3,11,19,3,19,19,19,11,3,11,11,11]] (.nil)) (.cons 0xffffff00ffff0000ffffff00ffff00 (.branch [24,27,4] [[11,11,1,11,11,3,1,11,11,3,3,11,11,11,11,11,11,11,1,19,3,3,4,11,19,3,3,11,4,12,12,3,11,3,1,11,11,3,1,11,11,3,3,11,11,11,11,11,11,3,1,3,19,19,11,19,19,19,19,11,3,19,19,11],[11,11,3,3,19,19,11,19,19,3,19,3,3,11,12,3,12,3,11,3,3,11,11,11,19,12,12,3,3,3,3,3,3,1,1,11,11,1,3,4,11,11,11,19,3,3,11,4,12,12,12,3,11,11,19,11,11,4,6,11,4,3,11,11],[1,19,3,3,4,6,0,11,6,11,3,11]] (.cons 0xffffff00ffffff00ffffff00000000 (.branch [23,27,16] [[3,19,12,12,4,12,12,20,4,20,3,19,11,20,11,20,19,12,11,12,4,12,20,11,3,19,20,11,11,1,3,3,19,19,11,4,20,20,19,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,3],[3,3,3,3,3,3,3,3,3,3,3,3,3,11,19,3,19,19,19,19,3,19,1,11,3,19,1,4,4,20,3,19,11,11,1,1,19,19,19,3,1,1,19,19,1,1,19,19,1,3,1,19,11,11,11,19,3,3,19,11,19,19,19,19],[12,3,12,12,1,1,19,3,1,19,11,12,3,3,19,11,1,4,12,12,12,1,12,3,12,12,1,1,19,3,1,19,11,12,3,3,19,11,1,4,12,12,12,1,1,1,4,3,11,4,12,11,11,19,3,11,1,11,4,3,3,11,19,11],[4,4,12,11,1,12,3,11,12,12,11,11,1,3,1,1,11,12,3,3,11,1,11,4,12,12,11,12,3,1,12,12,1,1,19,3,1,11,12,3,3,1,19,1,4,4,12,12,1,20,3,1,20,3,1,1,19,3,1,11,20,3,3,1],[19,1,4,4,20,3,1,1,4,3,19,4,3,19,4,4,3,19,1,11,4,3,3,19,19,11,4,4,3,19,20,3,19,20,3,19,12,1,3,1,1,11,20,3,3,19,1,11,4,20,3,19,3,19,11,0,11,0,19,11,12,11,12,4],[12,6,11,3,19,20,11,11,3,3,19,19,11,11,4,20,20,19,3,3,3,3,3,3,3,3,3,3,3,3,3,1,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,1,19,19,1,1,19,19,1,3,1,19,11,11,11,19,3,3],[19,11,19,19,19,19,19,3,19,11,19,19,19,3,19,11,3,19,4,21,3,19,11,1]] (.cons 0xfffffa00fffff000fafafa00aaaa00 (.term) (.cons 0xfcfcfc00fcfcf000fcfcfc00cccc00 (.term) (.nil)))) (.nil))) (.cons 0xffffff00ffffff00ffffff00000000 (.branch [31,22,5,36] [[12,3,19,11,3,19,19,12,12,3,3,11,19,13,4,11,12,0,1,1,1,4,3,11,4,11,3,11,1,4,4,3,3,19,11,4,11,4,28,11,1,11,3,11,11,1,3,1,1,11,11,3,3,11,1,11,11,11,11,11,28,3,1,19],[11,3,1,12,12,3,3,19,11,28,11,11,28,28,1,12,3,1,19,11,3,1,12,12,3,3,19,11,28,11,11,12,3,1,1,4,3,19,4,11,3,19,1,4,4,3,3,19,11,4,11,4,3,19,11,3,11,11,1,3,1,1,11,11],[3,3,11,1,11,11,11,3,11,3,19,28,12,20,4,11,12,28,3,19,12,4,11,3,3,19,11,12,12,4,11,12,19,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,19,1,19,11,1,3,19,19],[11,11,19,19,3,3,11,19,19,11,19,19,19,11,19,3,19,28,3,11,4,11,3,19,1]] (.cons 0xffffee00ffffee00eeeeee00cccccc (.branch [38,16,18,27] [[4,3,12,11,11,11,4,11,4,27,12,3,11,27,27,3,4,12,1,11,1,1,3,1,3,1,1,3,3,3,3,3,1,3,1,3,3,3,1,3,3,3,3,3,3,3,1,27,3,11,1,1,4,4,11,4,1,3,1,1,27,4,4,3],[11,1,27,3,4,4,11,27,3,1,4,11,1,11,11,1,1,27,4,4,3,11,11,27,3,3,4,11,1,11,28,3,28,1,11,11,11,11,11,27,12,28,3,11,11,28,3,4,28,1,1,1,3,1,3,1,1,3,3,3,3,3,1,3],[1,3,3,3,1,3,3,3,3,3,3,3,4,3,3,1,1,4,4,11,4,1,3,1,1,27,4,4,3,11,1,4,3,4,4,3,4,3,1,4,11,1,11,3,1,1,27,4,4,3,11,3,4,3,3,4,11,1,4,11,11,4,4,11],[4,11,11,11,11,11,27,4,4,11,11,27,4,3,4,11,11,1,3,1,27,11,1,1,11,27,1,27,27,11,3,1,11,27,3,27,27,11,1,3,4,27,3,27,27,4,3,4,0,21,27,3,20,5,27,4,11,30,3,27,27,12,3,11],[27,3,20,0,27,11,1,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,11,1,1,4,4,11,4,1,3,1,1,27,4,4,3,11,1,4,1,4,4,11,3,3,1,1,3,11],[11,11,11,1,3,11,1,11,11,11,3,3,11,11,11,3,11,11,3,11,11,11,12,30,11,11,11,11,4,27,12,11,27,30,4,12,11,28,27,12,11,27,28,1,3,27,4,27,4,27,4,4,27,4,27,4,3,27,21,27,28,5,27,12],[27,27,27,11,11,11,11,4,11,4,3,11,3,4,30,11,1]] (.cons 0xfffffe00f0f0f000fefefe00000000 (.term) (.cons 0xfffffe00f0f0f000fefefe00f0f0f0 (.term) (.nil)))) (.nil))) (.nil)))))) (.cons 0xffffff00ffffff00ffff0000ffff00 (.branch [28] [[2,3,4,2,3,4,2,4,4,2,2,3,3,4,2,4,2,3,3,2,2,2,5,2,2,2,2,3,2,2,5,2,3,3,3,2,3,3,3,3,2,3,3,3,2,3,2,4,2,3,6,4,2,3,1,6]] (.nil)) (.cons 0xffffff00ffff0000ffffff00ffff00 (.branch [33,11,5] [[3,2,19,2,19,3,3,2,2,19,19,13,2,12,3,2,19,2,3,3,2,3,3,2,3,3,2,2,3,3,3,2,3,2,3,11,2,2,2,2,6,2,2,2,19,2,2,2,11,2,11,0,11,19,2,12,3,3,11,2,19,19,2,19],[19,2,3,7,3,2,19,13,1,3,2,2,19,19,0,2,12,3,2,19]] (.cons 0xffffaa00ffff0000aaaaaa00aaaa00 (.branch [27,24] [[1,4,11,1,11,3,4,11,11,1,3,4,4,4,11,1,3,3,3,3,1,3,1,3,3,3,3,3,3,3,3,3,3,3,1,4,4,3,4,4,3,11,1,4,3,3,3,4,11,11,4,12,4,4,4,4,1,4,11,3,11,3,1,3],[4,11,11,4,3,4,1,4,11,3,3,4,4,3,3,11,3,3,4,11,11,4,14,4,4,4,4,3,4,11,11,4,3,12,11,11,3,4,4,4,11,3,3,1,3,1,3,3,3,3,3,3,3,3,3,3,3,1,3,12,3,3,11,11],[11,1,4,3,4,3,3,5,11,3,3,1,12,11,11,12,14,0,3,14,3,3,3]] (.cons 0xffffff00ffffff00ffffff00000000 (.branch [24,14,11] [[11,3,1,21,3,1,1,20,11,13,1,3,1,11,11,3,3,1,20,1,20,20,21,13,1,1,11,3,12,1,5,3,12,4,20,11,13,12,3,12,1,11,11,3,3,4,20,4,20,5,13,12,11,3,12,1,20,3,12,4,1,11,13,12],[3,1,1,11,11,3,3,4,1,4,20,20,13,12,11,3,6,3,1,20,11,13,1,3,1,4,11,11,3,3,20,4,1,5,20,6,13,1,3,11,11,11,11,3,11,11,11,11,11,11,11,11,11,11,11,3,11,11,11,11,1,3,3,11],[11,11,11,11,11,11,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,5,20,6,3,1,1,20,20,1,11,13,1,3,1,4,12,12,11,11,3,3,20,4,5,20,6],[13,11,4,20,4,3,4,3,4,1,11,3,20,1,20,20,11,3,13,11,3,1,1,20,11,3,1,3,1,11,11,3,3,1,20,1,20,20,11,3,1,1,11,3,5,4,20,11,3,5,3,5,1,11,11,3,3,4,20,4,20,11,3,5],[11,3,20,4,1,11,3,20,3,1,1,11,11,3,3,4,1,4,20,11,3,20,3,11,21,6,4,5,20,0,11,0,6,11,21,3,21,11,5,20,3,3,4,20,11,11,11,11,11,11,3,3,3,3,3,3,3,3,3,3,3,1,3,3],[3,3,3,3,3,3,3,3,3,3,3,3,1,1,5,20,1,11,13,1,3,1,13,12,12,11,11,3,3,20,4,5,20,11,13,13,20,13,3,13,12,3,13,12,3,20,5,20,3,13,12,1]] (.cons 0xfffffa00fffff000fafafa00aaaa00 (.term) (.cons 0xfcfcfc00fcfcf000fcfcfc00cccc00 (.term) (.nil)))) (.nil))) (.cons 0xffffff00ffffff00ffffff00000000 (.branch [17,10] [[2,3,12,2,4,2,3,12,2,12,12,2,3,12,2,4,1,2,2,3,3,12,2,4,2,12,3,2,2,11,2,3,2,2,11,2,1,2,2,2,11,2,2,2,2,3,2,2,11,2,11,3,2,3,3,2,3,3,2,3,3,1,3,2],[3,3,3,3,2,3,3,2,3,3,2,12,2,3,2,3,1,12,2,3,1,2,4,12,2,3,12,2,3,12,2,3,2,3,12,12,2,2,3,3,1,2,4,12,2,3,1,2,2,2,2,2,2,2,2,1,2,2,2,2,2,2,2,4],[2,2,2,4,11,3,4,11,3,11,3,1,4,4,11,11,3,3,4,2,4,11,3,2,3,12,2,0,12,0,2,3,12,2,4,2,2,3,3,12,12,2,4,2,12,3,2,2,2,2,1,2,2,2,11,2,2,2,2,3,2,2,11,2],[11,3,3,3,3,3,1,3,2,3,3,3,3,2,3,3,2,3,3,2,2,3,6,2,3,6,2,3,2,4,2,3,6,1]] (.cons 0xfafafa00fafaf000fafafa00aaaa00 (.branch [32,15,0] [[1,1,3,11,1,1,11,11,11,11,1,11,11,1,11,11,11,1,11,11,11,3,1,11,11,11,11,11,11,1,11,1,1,11,1,4,3,4,4,4,4,4,4,1,3,4,4,1,4,19,19,4,4,11,4,19,4,4,4,1,1,1,11,1],[1,4,4,4,4,1,4,4,4,1,4,4,1,4,19,19,1,4,4,11,4,4,4,1,4,1,3,1,3,1,3,1,3,3,3,3,1,3,3,1,3,3,3,3,3,3,1,3,3,1,3,3,3,3,3,1,1,1,12,11,4,4,4,1],[12,11,4,4,14,4,4,19,19,1,12,12,4,4,4,4,1,4,19,1,3,3,4,1,11,11,4,4,3,4,1,11,4,3,4,4,4,19,19,3,3,4,4,1,4,4,4,3,4,1,19,3,1,19,3,3,19,19,19,19,3,3,1,19],[3,3,19,19,11,19,19,19,1,19,19,3,11,19,19,19,19,3,4,3,3,4,4,4,4,3,4,4,4,3,4,4,3,4,19,19,3,4,4,11,4,4,4,3,4,3,3,3,4,11,11,11,4,11,3,4,11,11,4,3,4,4,4,19],[19,3,3,4,4,11,4,4,4,3,4,1,3,1,3,3,3,3,3,1,3,3,1,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,1,11,11,11,11,11,1,11,11,11,1,11,11,11,11,11,11,3,3,11,11,11,11,11],[11,1,11,12,4,4,4,4,12,11,4,4,3,0,4,4,19,19,12,12,4,4,4,4,4,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,12,12,3,12,3,12,12,19,3,3,12,12,3,11,11,11,11,11,11,11,11,1,3,12],[11,12,11,1,3,12,11,1,5,5,3,12,11,3,12,11,3,12,11,12,11,3,3,12,12,11,11,1,5,5,3,12,11,1,3,12,11,3,12,11,12,11,1,3,3,12,12,11,11,19,5,3,12,11,1,19,5,3,1,3,3,1,3,3],[3,3,3,3,3,3,3,3,3,1,12,3,12,12,19,3,3,12,12,3,11,11,11,11,3,11,11,1,12,11,19,12,11,19,12,11,6,5,12,11,19,1]] (.cons 0xfffffa00fffff000fafafa00aaaa00 (.term) (.nil))) (.cons 0xfffff000fffff000f0f0f000000000 (.branch [23,27] [[1,1,2,11,1,2,11,1,2,11,2,11,1,1,2,2,11,11,1,2,11,1,2,11,1,2,12,1,2,12,2,6,2,12,5,1,2,2,12,12,1,1,2,5,1,2,6,1,1,2,12,1,2,12,1,2,6,2,12,1,1,2,2,12],[12,1,2,4,1,2,6,1,1,2,11,11,1,2,11,1,2,11,11,2,11,11,1,2,2,11,11,11,2,11,1,2,11,2,11,2,12,1,2,5,2,12,1,2,5,1,2,12,5,2,11,1,2,2,12,12,1,2,5,2,5,1,2,2],[2,1,2,2,2,2,2,2,2,2,1,2,2,2,2,2,2,2,4,2,2,2,11,3,12,1,11,3,12,11,13,6,3,12,1,11,11,3,3,12,12,11,2,11,13,6,2,12,11,2,12,2,0,11,2,12,13,2,2,12,12,11,2,13],[2,6,1,1,2,2,11,11,11,2,12,2,12,1,11,2,12,1,2,4,13,2,12,1,1,1,1,2,11,1,11,1,13,1,11,2,2,11,11,2,12,11,2,12,11,2,12,2,6,2,12,11,1]] (.cons 0xfffffa00fffff000fafafa00aaaa00 (.term) (.nil))) (.nil)))) (.nil)))) (.cons 0xffffff00ffffff00ffffff00000000 (.branch [17,30] [[12,2,3,2,3,12,12,2,2,3,3,6,2,4,12,2,3,1,2,2,2,2,2,1,2,2,2,2,2,2,2,4,2,2,2,4,11,3,11,3,1,4,4,11,11,3,3,4,2,4,11,3,2,3,0,2,3,12,2,4,2,2,3,3],[12,12,2,4,2,12,3,2,2,2,2,2,11,2,2,2,2,3,2,2,11,2,11,3,3,3,3,2,3,3,3,3,2,3,3,2,3,3,2,2,3,15,2,3,2,4,2,3,1]] (.cons 0xfffff000fffff000f0f0f000000000 (.branch [16,23] [[4,1,2,3,2,3,1,4,2,2,3,3,6,2,12,1,2,14,1,1,2,3,2,3,4,1,2,2,3,3,6,2,5,1,2,14,2,5,4,2,5,2,3,4,2,3,4,2,5,1,2,2,3,3,1,2,5,2,13,1,1,2,2,2],[2,2,1,2,2,2,2,2,2,2,12,2,2,2,1,4,11,3,11,3,1,4,4,11,11,3,3,5,2,4,5,14,2,3,2,3,4,2,2,3,3,6,2,5,2,14,1,1,6,1,2,5,1,4,1,4,2,3,2,3,14,2,3,2],[5,2,3,1]] (.nil)) (.nil))) (.nil)))))))) (.nil)))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_23 : chkCheckNode s23_maskYF s23_edgePts s23_edgeTT s23_raw s23_masksTT s23_cuts [] s23_auts s23_cert = true := by decide +kernel

-- State #24: n=7 |E|=8 |F|=1 nodes=5 cands=574 wits=628 cuts=11
def s24_desc : StateDesc := ⟨7,[(0,3),(0,4),(1,3),(1,5),(2,5),(2,6),(4,6),(5,6)],[(3,4)]⟩
def s24_maskYF : Nat := 0xffffff00ffffff00ffffff00ffffff
def s24_edgePts : Nat := 0x1000100100000001400020600
def s24_edgeTT : Nat := 0xffffff00fffef000fefefc00aaee00
def s24_raw : List Nat := chkMkRaw 7 s24_maskYF
def s24_masksTT : List Nat := chkMkMasksTT 7 s24_desc.edges s24_maskYF
def s24_autIdxTbls : List (List Nat) := []
def s24_auts : List (List Nat) := []
def s24_cutSpecs : List CutSpecData := [⟨0,[(0,3)],[0,3,1,4],2,[2,5,6]⟩,⟨4,[],[],18,[5,1,6,0,3,4]⟩,⟨0,[(5,6)],[],27,[1,0,2,3,5,4,6]⟩,⟨34,[],[2,3,0],17,[4,6]⟩,⟨17,[],[3,1],2,[2,5,6]⟩,⟨84,[],[0,3],17,[1,5]⟩,⟨27,[],[],2,[2,5,6]⟩,⟨27,[],[],2,[2,5,6]⟩,⟨93,[],[],17,[1,5]⟩,⟨47,[],[],17,[4,6]⟩,⟨110,[],[],17,[0,4]⟩]
def s24_cuts : List CutDefData := chkMkCuts s24_maskYF s24_raw [(1,[.e [(0,3)]]),(2,[.v 2 [72,33,48]]),(1,[.e [(5,6)]]),(4,[.v 5 [12,72,18],.v 1 [12]]),(3,[.v 4 [7,64,33],.v 0 [40,72]]),(5,[.v 4 [1,64],.v 2 [66],.v 6 [32]]),(5,[.v 0 [72,22,40],.v 4 [],.v 3 [2,66],.v 1 [32]]),(5,[.v 1 [33,72,12,48],.v 3 [33,65],.v 0 [16],.v 4 [64]]),(7,[.v 0 [48,8],.v 4 [],.v 2 [66,40,72],.v 3 [2,66],.v 6 [32]]),(7,[.v 1 [8,32,48],.v 2 [72,33,48],.v 3 [33],.v 0 [48],.v 5 [64]]),(7,[.v 2 [64,33,72],.v 1 [72,32],.v 5 [72],.v 3 [],.v 6 [16]])]
def s24_cert : CertNode := .branch [7,1,4,2,0] [[19,11,11,3,3,19,27,27,27,27,27,27,11,11,3,3,19,19,19,19,19,19,19,11,3,3,11,11,11,11,11,11,11,3,3,11,11,11,11,11,11,11,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,19,19,19,19,19,19,35],[35,35,35,35,0,19,4,11,3,20,19,4,11,3,20,0,11,3,19,11,3,4,3,11,3]] (.cons 0xffffff00ffffff00ffffff00000000 (.branch [9,5,0,2] [[11,3,11,11,11,3,3,11,11,11,11,11,3,11,3,27,11,3,3,11,19,4,4,4,4,12,4,3,3,3,3,3,3,3,3,3,3,3,3,3,11,19,11,5,3,6,1]] (.nil)) (.cons 0xffff0000ffff0000ffff0000ffff00 (.branch [6,7,1,2,4] [[11,3,27,19,19,11,11,3,3,5,35,19,11,3,3,11,11,11,11,11,3,3,11,11,11,11,3,27,35,19,19,11,11,3,3,3,3,3,3,27,19,19,11,5,0,19,11,27,19,19,11,11,3,3,27,27,27,27,27,35,19,19,11,11],[11,3,3,3,3,0,35,12,19,11,3,35,12,19,11,3,1]] (.cons 0xffffff00ffff0000ffffff00ffff00 (.branch [10,6,3,4] [[3,4,11,4,11,19,3,3,19,4,11,11,19,27,13,3,4,11,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,11,4,11,19,19,27,3,3,11,11,4,19,27,4,20,11,11,11,19,27,3,3,19,4,11,11,11,11],[3,11,3,7,3,4,11,13,1,3,19,4,11,11,19,27,13,3,4,11]] (.nil)) (.cons 0xffffff00ffffff00ffffff00000000 (.branch [8,9,2] [[12,11,11,3,19,12,12,11,11,3,3,6,4,12,11,3,4,11,11,3,19,4,4,11,11,3,3,4,4,4,11,3,11,12,11,0,12,19,4,11,11,3,3,12,12,4,12,5,12,11,11,11,11,11,11,11,11,11,3,3,11,11,11,11],[11,11,3,6,11,3,3,4,13,11,3,1]] (.cons 0xfafaf000fafaf000fafaf000aaaa00 (.branch [8,9,2] [[1,3,3,1,12,4,11,5,11,1,12,19,4,11,11,3,3,5,5,4,5,5,1,12,12,1,3,4,1,11,3,5,11,19,4,12,12,11,11,5,5,4,4,1,5,1,4,5,3,12,4,11,12,11,3,12,19,4,1,11,11,3,3,5],[4,5,5,3,4,5,3,12,4,11,5,11,3,12,19,4,1,11,11,3,3,5,4,5,5,3,1,3,3,3,3,11,3,4,11,19,4,4,4,11,11,1,4,4,4,3,4,3,3,4,3,11,3,5,11,19,4,12,12,11,11,1,5,5],[4,3,5,1,12,4,11,12,11,1,12,19,4,11,11,3,3,12,12,4,12,5,1,3,3,1,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,3,5,4,11,3,5,11,12,19,4,11,11,5,5,4,5,5,12,11,11,3,19,12],[12,11,11,3,3,6,4,12,11,3,4,11,11,3,19,4,4,11,11,3,3,4,4,4,11,3,11,12,11,1,12,19,4,11,12,12,4,5,1,11,11,11,11,11,11,11,11,11,11,3,6,11,3,3,4,13,11,3,1]] (.nil)) (.nil))) (.nil)))) (.nil)))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_24 : chkCheckNode s24_maskYF s24_edgePts s24_edgeTT s24_raw s24_masksTT s24_cuts [] s24_auts s24_cert = true := by decide +kernel

-- State #25: n=7 |E|=8 |F|=1 nodes=4 cands=226 wits=440 cuts=10
def s25_desc : StateDesc := ⟨7,[(0,3),(0,5),(1,4),(1,6),(2,5),(2,6),(3,5),(4,6)],[(3,4)]⟩
def s25_maskYF : Nat := 0xffffff00ffffff00ffffff00ffffff
def s25_edgePts : Nat := 0x100140000011200040200
def s25_edgeTT : Nat := 0xfffffe00fffefc00fefffa00ccaa00
def s25_raw : List Nat := chkMkRaw 7 s25_maskYF
def s25_masksTT : List Nat := chkMkMasksTT 7 s25_desc.edges s25_maskYF
def s25_autIdxTbls : List (List Nat) := chkMkAutIdxTbls 7 [[1,0,2,4,3,6,5]]
def s25_auts : List (List Nat) := chkMkAutMaskTbls s25_autIdxTbls
def s25_cutSpecs : List CutSpecData := [⟨0,[(0,5)],[0,3,5,2],2,[1,4,6]⟩,⟨16,[],[1,6,2],2,[0,3,5]⟩,⟨4,[],[],16,[0,5,1,6,3,4]⟩,⟨18,[],[6,2],2,[0,3,5]⟩,⟨36,[],[0],2,[1,4,6]⟩,⟨100,[],[0],17,[1,4]⟩,⟨41,[],[2],2,[1,4,6]⟩,⟨82,[],[2],2,[0,3,5]⟩,⟨41,[],[2],2,[1,4,6]⟩,⟨105,[],[],17,[1,4]⟩]
def s25_cuts : List CutDefData := chkMkCuts s25_maskYF s25_raw [(1,[.e [(0,5)]]),(2,[.v 4 [2]]),(2,[.v 2 [48,72,65]]),(3,[.v 1 [48,65],.v 4 [96]]),(4,[.v 5 [72],.v 2 [65,72]]),(6,[.v 2 [48,72,65],.v 6 [34],.v 5 [10,17]]),(4,[.v 0 [14,34,72,48],.v 3 [],.v 5 [4,20]]),(4,[.v 1 [96],.v 4 [],.v 6 [4]]),(4,[.v 3 [7,34,65],.v 0 [34],.v 5 [4]]),(7,[.v 0 [14,48,72,34],.v 3 [],.v 6 [34],.v 5 [20]])]
def s25_cert : CertNode := .branch [8,2,3,0] [[3,2,2,2,2,2,2,20,2,2,2,2,3,3,3,3,3,3,2,3,3,3,3,11,2,2,11,3,11,2,11,2,11,2,2,11,3,2,2,11,2,11,2,19,3,19,2,19,2,2,2,3,2,19,19,2,2,3,2,2,27,27,27,2],[3,2,3,3,0,2,2,2,2,2,20,3,11,19,4,0,2,2,2,3,3,3,2,11,19]] (.cons 0xffffff00ffffff00ffffff00000000 (.branch [8,4,1] [[3,2,2,2,3,2,2,2,2,2,2,19,19,2,2,2,3,3,3,2,3,3,3,3,3,3,2,2,3,3,3,2,12,2,3,2,2,11,3,2,5,2,12,2,12,4,2,3,2,2,2,11,3,5,2,3,2,4,2,3,12,11,2,2],[3,2,2,3,12,2,2,3,2,3,2,4,1]] (.nil)) (.cons 0xffff0000ffff0000ffff0000ffff00 (.branch [6,7,2] [[5,2,2,2,2,2,2,2,3,2,13,2,2,2,3,11,3,12,19,19,2,11,3,3,2,4,19,2,3,3,2,11,2,2,2,3,3,2,11,11,2,3,2,3,3,3,2,2,3,2,3,2,3,2,2,19,2,3,2,5,19,2,3,12],[2,19,2,11,2,11,2,2,3,0,2,2,2,2,2,12,4,19,11,3,1]] (.cons 0xffffff00ffffff00ffffff00000000 (.branch [6,2] [[11,2,3,2,3,2,11,2,2,3,3,2,5,2,4,11,2,3,1,2,2,2,4,2,2,4,2,2,2,2,2,2,5,4,2,2,2,11,4,3,2,4,3,2,11,11,4,4,3,3,2,2,11,4,3,2,3,2,11,2,3,11,2,4],[2,2,3,3,2,11,2,11,2,11,3,2,2,2,2,2,2,4,2,2,2,3,3,5,2,4,2,3,3,3,3,3,3,2,3,3,3,2,2,3,2,2,3,3,2,2,3,0,2,3,2,4,2,3,1]] (.cons 0xffffff00ffffff00ffffff00ffff00 (.branch [9,5] [[2,3,11,2,11,2,3,2,11,2,3,11,2,4,2,2,3,3,2,11,2,11,2,3,3,2,2,4,2,2,2,2,2,2,2,2,4,2,2,3,3,2,13,2,4,2,3,3,2,3,11,3,3,3,3,3,3,2,13,11,11,2,2,2],[3,2,3,3,2,1]] (.nil)) (.nil))) (.nil))) (.nil)))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_25 : chkCheckNode s25_maskYF s25_edgePts s25_edgeTT s25_raw s25_masksTT s25_cuts [] s25_auts s25_cert = true := by decide +kernel

-- State #26: n=7 |E|=7 |F|=2 nodes=2 cands=164 wits=166 cuts=7
def s26_desc : StateDesc := ⟨7,[(0,1),(0,4),(1,5),(2,4),(2,6),(3,5),(3,6)],[(4,6),(5,6)]⟩
def s26_maskYF : Nat := 0xffffffffffffffffffff
def s26_edgePts : Nat := 0x1100000010400120008
def s26_edgeTT : Nat := 0xfff8fffeffccfafa8888
def s26_raw : List Nat := chkMkRaw 7 s26_maskYF
def s26_masksTT : List Nat := chkMkMasksTT 7 s26_desc.edges s26_maskYF
def s26_autIdxTbls : List (List Nat) := []
def s26_auts : List (List Nat) := []
def s26_cutSpecs : List CutSpecData := [⟨0,[(1,5)],[1,0,4,2,5],17,[3,6]⟩,⟨4,[],[4,0,1,5],17,[3,6]⟩,⟨34,[],[0,3,4],17,[2,6]⟩,⟨84,[],[0,1],17,[3,5]⟩,⟨76,[],[4,0],17,[1,5]⟩,⟨55,[],[],17,[3,6]⟩,⟨55,[],[],17,[3,6]⟩]
def s26_cuts : List CutDefData := chkMkCuts s26_maskYF s26_raw [(1,[.e [(1,5)]]),(2,[.v 2 [26,64,48]]),(3,[.v 5 [24,2],.v 1 [65]]),(4,[.v 2 [26,65,48],.v 6 [],.v 4 [1]]),(4,[.v 3 [37,66,48],.v 6 [6],.v 2 [16]]),(6,[.v 0 [14,48,24,66],.v 1 [48],.v 4 [36],.v 5 [8],.v 2 [64]]),(6,[.v 1 [1,36],.v 0 [16],.v 4 [36],.v 5 [],.v 2 [64]])]
def s26_cert : CertNode := .branch [5,4,1,0] [[11,11,11,11,3,3,11,11,11,11,11,11,11,11,3,3,11,11,11,11,11,19,19,3,3,19,19,19,19,19,19,3,3,19,19,19,19,19,3,3,27,27,27,27,27,3,3,3,3,3,3,3,3,3,3,3,0,0,11,19,12,3,5,11],[19,4,3,11,19,4,3,11,11,3,19,3,3]] (.cons 0xffffffffffff00000000 (.branch [6,4,1,5] [[11,3,19,19,3,27,3,11,11,11,11,11,11,3,11,11,19,3,19,3,19,19,11,3,19,3,3,3,3,3,3,3,3,3,3,3,19,27,3,5,19,3,27,1]] (.nil)) (.cons 0xffffffff0000ffff0000 (.branch [3,2,5,4] [[3,19,11,3,3,11,19,19,11,27,3,27,19,3,27,11,11,19,19,3,3,3,3,3,3,19,11,3,3,11,19,19,19,19,3,19,11,11,19,11,27,12,19,4,1]] (.nil)) (.nil)))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_26 : chkCheckNode s26_maskYF s26_edgePts s26_edgeTT s26_raw s26_masksTT s26_cuts [] s26_auts s26_cert = true := by decide +kernel

-- State #27: n=7 |E|=7 |F|=2 nodes=4 cands=351 wits=438 cuts=9
def s27_desc : StateDesc := ⟨7,[(0,3),(0,4),(1,3),(1,5),(2,4),(2,6),(5,6)],[(3,5),(4,6)]⟩
def s27_maskYF : Nat := 0xff0000ffff00ff00ffffffffff
def s27_edgePts : Nat := 0x1000000100000000400120600
def s27_edgeTT : Nat := 0xff0000fef000fe00ccfefaee00
def s27_raw : List Nat := chkMkRaw 7 s27_maskYF
def s27_masksTT : List Nat := chkMkMasksTT 7 s27_desc.edges s27_maskYF
def s27_autIdxTbls : List (List Nat) := chkMkAutIdxTbls 7 [[0,2,1,4,3,6,5]]
def s27_auts : List (List Nat) := chkMkAutMaskTbls s27_autIdxTbls
def s27_cutSpecs : List CutSpecData := [⟨1,[],[3,1,4,2],17,[5,6]⟩,⟨4,[],[4,0,3,1],17,[5,6]⟩,⟨20,[],[0,3,1],17,[5,6]⟩,⟨21,[],[3,1],17,[5,6]⟩,⟨42,[],[0,4],17,[2,6]⟩,⟨25,[],[1,2],17,[5,6]⟩,⟨106,[],[0],17,[2,4]⟩,⟨107,[],[],17,[2,4]⟩,⟨118,[],[],17,[0,3]⟩]
def s27_cuts : List CutDefData := chkMkCuts s27_maskYF s27_raw [(2,[.v 0 [72,16,8]]),(2,[.v 2 [48,67,72]]),(3,[.v 2 [72,16],.v 4 [33]]),(4,[.v 0 [8,48,16],.v 4 [],.v 2 [64]]),(4,[.v 1 [],.v 3 [],.v 5 [64]]),(4,[.v 3 [18,1],.v 0 [18,48],.v 4 [6]]),(5,[.v 1 [72,37,24],.v 5 [],.v 3 [1],.v 6 [4]]),(6,[.v 1 [48,8],.v 5 [],.v 3 [65],.v 6 [],.v 0 [16]]),(6,[.v 5 [65,6,18],.v 6 [12,4],.v 2 [16],.v 1 [8,24],.v 4 [1]])]
def s27_cert : CertNode := .branch [8,5,1] [[2,3,3,2,3,2,3,2,2,3,3,2,3,2,2,2,19,2,2,2,2,3,11,19,11,2,19,2,19,19,3,3,3,2,3,3,3,3,2,2,2,11,11,2,2,11,2,12,2,2,12,2,11,11,2,11,3,2,2,2,2,2,3,0],[3,3,3,11,2,13,12,2,11,2,19,2,12]] (.cons 0xff0000ff0000ff00ffff00ff00 (.branch [6,2,0,8] [[3,19,11,11,3,3,19,19,28,27,11,3,19,3,27,11,11,19,19,3,3,3,3,3,3,19,11,11,3,3,19,19,19,19,19,3,11,11,19,28,12,11,19,11,3,3,19,19,27,0,28,11,3,19,1]] (.cons 0xff0000ffff00ff0000ffff0000 (.branch [7,3,1] [[19,11,3,11,19,19,3,3,11,11,12,4,19,3,11,19,11,3,11,19,19,3,3,11,11,4,4,19,3,11,11,19,0,11,19,4,3,3,11,11,19,19,19,19,19,19,11,11,11,11,11,11,11,3,3,11,11,11,11,11,11,3,11,5],[3,3,11,4,5,3,11,5,4,1]] (.cons 0xfc0000fcf000fc00ccfcf0cc00 (.branch [8,4,0] [[1,3,3,1,5,3,19,4,1,19,5,3,3,3,19,19,4,3,4,12,1,6,4,4,1,11,3,1,19,11,4,19,3,4,4,19,19,4,3,13,3,1,13,3,1,4,11,4,3,19,4,11,19,4,3,1,3,11,19,19,3,4,4,11],[4,3,1,3,3,3,3,3,3,3,3,3,3,3,1,3,3,3,3,3,3,3,4,11,5,3,19,4,11,19,5,3,1,3,11,19,19,4,3,12,11,6,3,11,3,3,19,11,4,19,3,4,4,1,19,19,4,3,12,11,12,1,5,3],[19,4,1,19,5,3,3,3,19,19,4,3,5,12,1,5,11,3,1,11,11,11,11,3,11,11,11,11,11,3,11,11,1,11,6,3,19,11,4,19,5,3,19,19,4,3,6,12,0,5,19,11,19,4,5,3,11,19,19,4,3,5,11,19],[3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,4,1,5,3,4,3,1,19,19,3,19,3,11,19,13,3,11,19,3,12,11,19,4,3,1]] (.cons 0xfe0000fefa00fe00eefefaeeaa (.term) (.nil))) (.nil))) (.nil))) (.nil))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_27 : chkCheckNode s27_maskYF s27_edgePts s27_edgeTT s27_raw s27_masksTT s27_cuts [] s27_auts s27_cert = true := by decide +kernel

def allStates : List StateDesc := [s0_desc,s1_desc,s2_desc,s3_desc,s4_desc,s5_desc,s6_desc,s7_desc,s8_desc,s9_desc,s10_desc,s11_desc,s12_desc,s13_desc,s14_desc,s15_desc,s16_desc,s17_desc,s18_desc,s19_desc,s20_desc,s21_desc,s22_desc,s23_desc,s24_desc,s25_desc,s26_desc,s27_desc]
def allGraphCores : List GraphCoreSpec := [
  ⟨0,6,[(0,1),(0,2),(0,3),(1,2),(3,4),(3,5),(4,5)],10,0,[],[1,2,4,5,0,3]⟩,
  ⟨1,7,[(0,1),(0,2),(0,3),(0,4),(1,2),(3,4),(5,6)],10,1,[5],[1,2,3,4,0]⟩,
  ⟨2,7,[(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(4,6)],10,2,[5,3,6,4],[0,1,2]⟩,
  ⟨3,7,[(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,6)],10,2,[5,3,6,4],[0,1,2]⟩,
  ⟨4,7,[(0,1),(0,2),(0,3),(1,2),(3,4),(3,5),(4,6)],10,2,[5,6,4,3],[0,1,2]⟩,
  ⟨5,7,[(0,1),(0,2),(0,3),(1,2),(3,4),(4,5),(5,6)],10,2,[6,5,4,3],[0,1,2]⟩,
  ⟨6,7,[(0,1),(0,2),(0,3),(1,2),(4,5),(4,6),(5,6)],10,3,[3],[0,1,2,4,5,6]⟩,
  ⟨7,7,[(0,1),(0,2),(0,3),(1,4),(2,5),(3,6),(4,5)],10,4,[6,3],[0,1,2,4,5]⟩,
  ⟨8,7,[(0,1),(0,2),(1,3),(2,4),(3,5),(4,6),(5,6)],10,5,[],[0,1,2,3,4,5,6]⟩,
  ⟨9,7,[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(3,4)],10,1,[5,6],[1,2,3,4,0]⟩,
  ⟨10,7,[(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,6),(3,4)],10,1,[5,6],[1,2,3,4,0]⟩,
  ⟨11,7,[(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(3,4),(5,6)],11,1,[6,5],[1,2,3,4,0]⟩,
  ⟨12,7,[(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(1,6),(3,4)],10,1,[5,6],[1,2,3,4,0]⟩,
  ⟨13,7,[(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(2,6),(3,4)],11,1,[5,6],[1,2,3,4,0]⟩,
  ⟨14,7,[(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(3,6)],10,1,[5,6],[1,2,3,4,0]⟩,
  ⟨15,7,[(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(5,6)],11,1,[6,5],[1,2,3,4,0]⟩,
  ⟨16,7,[(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,6),(5,6)],10,6,[4],[6,3,5,2,0,1]⟩,
  ⟨17,7,[(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(3,6),(5,6)],11,0,[4],[1,2,5,6,0,3]⟩,
  ⟨18,7,[(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(4,6),(5,6)],11,7,[],[5,6,3,4,1,2,0]⟩,
  ⟨19,7,[(0,1),(0,2),(0,3),(1,2),(1,4),(2,5),(3,6),(4,6)],11,6,[5],[6,3,4,2,0,1]⟩,
  ⟨20,7,[(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(3,6),(4,5)],11,6,[6],[5,3,4,2,0,1]⟩,
  ⟨21,7,[(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(3,6),(5,6)],11,0,[4],[1,2,5,6,0,3]⟩,
  ⟨22,7,[(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,5),(5,6)],10,6,[6],[5,3,4,2,0,1]⟩,
  ⟨23,7,[(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,6),(5,6)],11,8,[],[5,6,3,4,2,0,1]⟩,
  ⟨24,7,[(0,1),(0,2),(0,3),(1,2),(3,4),(4,5),(4,6),(5,6)],11,9,[],[1,2,5,6,3,0,4]⟩,
  ⟨25,7,[(0,1),(0,2),(0,3),(1,4),(2,5),(3,6),(4,5),(4,6)],11,10,[],[2,5,3,6,1,0,4]⟩,
  ⟨26,7,[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(3,4),(5,6)],12,11,[],[1,2,3,4,5,6,0]⟩,
  ⟨27,7,[(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(1,6),(3,4),(5,6)],12,12,[],[3,4,5,6,2,0,1]⟩,
  ⟨28,7,[(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(3,6),(5,6)],12,13,[],[5,6,2,4,1,3,0]⟩,
  ⟨29,7,[(0,1),(0,2),(0,3),(1,2),(1,4),(2,5),(3,6),(4,6),(5,6)],12,14,[],[3,4,5,6,0,1,2]⟩,
  ⟨30,7,[(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(3,6),(4,5),(5,6)],12,15,[],[4,2,6,1,5,0,3]⟩,
]


def allEntries : List StateCertEntry := [
  ⟨s0_desc, s0_maskYF, s0_edgePts, s0_edgeTT, s0_raw, s0_masksTT, s0_autIdxTbls, s0_auts, s0_cuts, s0_cutSpecs, s0_cert⟩,
  ⟨s1_desc, s1_maskYF, s1_edgePts, s1_edgeTT, s1_raw, s1_masksTT, s1_autIdxTbls, s1_auts, s1_cuts, s1_cutSpecs, s1_cert⟩,
  ⟨s2_desc, s2_maskYF, s2_edgePts, s2_edgeTT, s2_raw, s2_masksTT, s2_autIdxTbls, s2_auts, s2_cuts, s2_cutSpecs, s2_cert⟩,
  ⟨s3_desc, s3_maskYF, s3_edgePts, s3_edgeTT, s3_raw, s3_masksTT, s3_autIdxTbls, s3_auts, s3_cuts, s3_cutSpecs, s3_cert⟩,
  ⟨s4_desc, s4_maskYF, s4_edgePts, s4_edgeTT, s4_raw, s4_masksTT, s4_autIdxTbls, s4_auts, s4_cuts, s4_cutSpecs, s4_cert⟩,
  ⟨s5_desc, s5_maskYF, s5_edgePts, s5_edgeTT, s5_raw, s5_masksTT, s5_autIdxTbls, s5_auts, s5_cuts, s5_cutSpecs, s5_cert⟩,
  ⟨s6_desc, s6_maskYF, s6_edgePts, s6_edgeTT, s6_raw, s6_masksTT, s6_autIdxTbls, s6_auts, s6_cuts, s6_cutSpecs, s6_cert⟩,
  ⟨s7_desc, s7_maskYF, s7_edgePts, s7_edgeTT, s7_raw, s7_masksTT, s7_autIdxTbls, s7_auts, s7_cuts, s7_cutSpecs, s7_cert⟩,
  ⟨s8_desc, s8_maskYF, s8_edgePts, s8_edgeTT, s8_raw, s8_masksTT, s8_autIdxTbls, s8_auts, s8_cuts, s8_cutSpecs, s8_cert⟩,
  ⟨s9_desc, s9_maskYF, s9_edgePts, s9_edgeTT, s9_raw, s9_masksTT, s9_autIdxTbls, s9_auts, s9_cuts, s9_cutSpecs, s9_cert⟩,
  ⟨s10_desc, s10_maskYF, s10_edgePts, s10_edgeTT, s10_raw, s10_masksTT, s10_autIdxTbls, s10_auts, s10_cuts, s10_cutSpecs, s10_cert⟩,
  ⟨s11_desc, s11_maskYF, s11_edgePts, s11_edgeTT, s11_raw, s11_masksTT, s11_autIdxTbls, s11_auts, s11_cuts, s11_cutSpecs, s11_cert⟩,
  ⟨s12_desc, s12_maskYF, s12_edgePts, s12_edgeTT, s12_raw, s12_masksTT, s12_autIdxTbls, s12_auts, s12_cuts, s12_cutSpecs, s12_cert⟩,
  ⟨s13_desc, s13_maskYF, s13_edgePts, s13_edgeTT, s13_raw, s13_masksTT, s13_autIdxTbls, s13_auts, s13_cuts, s13_cutSpecs, s13_cert⟩,
  ⟨s14_desc, s14_maskYF, s14_edgePts, s14_edgeTT, s14_raw, s14_masksTT, s14_autIdxTbls, s14_auts, s14_cuts, s14_cutSpecs, s14_cert⟩,
  ⟨s15_desc, s15_maskYF, s15_edgePts, s15_edgeTT, s15_raw, s15_masksTT, s15_autIdxTbls, s15_auts, s15_cuts, s15_cutSpecs, s15_cert⟩,
  ⟨s16_desc, s16_maskYF, s16_edgePts, s16_edgeTT, s16_raw, s16_masksTT, s16_autIdxTbls, s16_auts, s16_cuts, s16_cutSpecs, s16_cert⟩,
  ⟨s17_desc, 0, 0, 0, [], [], [], [], [], [], .term⟩,
  ⟨s18_desc, s18_maskYF, s18_edgePts, s18_edgeTT, s18_raw, s18_masksTT, s18_autIdxTbls, s18_auts, s18_cuts, s18_cutSpecs, s18_cert⟩,
  ⟨s19_desc, s19_maskYF, s19_edgePts, s19_edgeTT, s19_raw, s19_masksTT, s19_autIdxTbls, s19_auts, s19_cuts, s19_cutSpecs, s19_cert⟩,
  ⟨s20_desc, s20_maskYF, s20_edgePts, s20_edgeTT, s20_raw, s20_masksTT, s20_autIdxTbls, s20_auts, s20_cuts, s20_cutSpecs, s20_cert⟩,
  ⟨s21_desc, s21_maskYF, s21_edgePts, s21_edgeTT, s21_raw, s21_masksTT, s21_autIdxTbls, s21_auts, s21_cuts, s21_cutSpecs, s21_cert⟩,
  ⟨s22_desc, s22_maskYF, s22_edgePts, s22_edgeTT, s22_raw, s22_masksTT, s22_autIdxTbls, s22_auts, s22_cuts, s22_cutSpecs, s22_cert⟩,
  ⟨s23_desc, s23_maskYF, s23_edgePts, s23_edgeTT, s23_raw, s23_masksTT, s23_autIdxTbls, s23_auts, s23_cuts, s23_cutSpecs, s23_cert⟩,
  ⟨s24_desc, s24_maskYF, s24_edgePts, s24_edgeTT, s24_raw, s24_masksTT, s24_autIdxTbls, s24_auts, s24_cuts, s24_cutSpecs, s24_cert⟩,
  ⟨s25_desc, s25_maskYF, s25_edgePts, s25_edgeTT, s25_raw, s25_masksTT, s25_autIdxTbls, s25_auts, s25_cuts, s25_cutSpecs, s25_cert⟩,
  ⟨s26_desc, s26_maskYF, s26_edgePts, s26_edgeTT, s26_raw, s26_masksTT, s26_autIdxTbls, s26_auts, s26_cuts, s26_cutSpecs, s26_cert⟩,
  ⟨s27_desc, s27_maskYF, s27_edgePts, s27_edgeTT, s27_raw, s27_masksTT, s27_autIdxTbls, s27_auts, s27_cuts, s27_cutSpecs, s27_cert⟩
]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem allEntries_meta_bool : allEntries.all (checkStateEntryDAG allStates) = true := by decide +kernel

theorem allEntries_certs : ∀ e ∈ allEntries, e.desc.edges.length ≤ 1 ∨
    chkCheckNode e.maskYF e.edgePts e.edgeTT e.raw e.masksTT e.cuts [] e.auts e.cert = true := by
  intro e he
  simp only [allEntries, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr cert_ok_0
  · exact Or.inr cert_ok_1
  · exact Or.inr cert_ok_2
  · exact Or.inr cert_ok_3
  · exact Or.inr cert_ok_4
  · exact Or.inr cert_ok_5
  · exact Or.inr cert_ok_6
  · exact Or.inr cert_ok_7
  · exact Or.inr cert_ok_8
  · exact Or.inr cert_ok_9
  · exact Or.inr cert_ok_10
  · exact Or.inr cert_ok_11
  · exact Or.inr cert_ok_12
  · exact Or.inr cert_ok_13
  · exact Or.inr cert_ok_14
  · exact Or.inr cert_ok_15
  · exact Or.inr cert_ok_16
  · exact Or.inl (by decide)
  · exact Or.inr cert_ok_18
  · exact Or.inr cert_ok_19
  · exact Or.inr cert_ok_20
  · exact Or.inr cert_ok_21
  · exact Or.inr cert_ok_22
  · exact Or.inr cert_ok_23
  · exact Or.inr cert_ok_24
  · exact Or.inr cert_ok_25
  · exact Or.inr cert_ok_26
  · exact Or.inr cert_ok_27

theorem allStates_lb : ∀ (i : ℕ) (ch : StateDesc), allStates[i]? = some ch →
    OrCostLB ch.n ch.edges ch.forb (ch.edges.length - 1) :=
  allStates_orCostLB allEntries (List.all_eq_true.mp allEntries_meta_bool) allEntries_certs

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem allGraphCores_ok : allGraphCores.all (checkGraphCore allStates) = true := by decide +kernel

end OrYF

theorem combine_bound {n a b : ℕ} {H : List (ℕ × ℕ)} {f : (Fin n → Bool) → Bool}
    (hf : ∀ x : Fin n → Bool, f x = OrYF.edgeFnList n H x)
    (idx : ℕ) (gc : OrYF.GraphCoreSpec) (hget : OrYF.allGraphCores[idx]? = some gc)
    (hn : gc.n = n) (hH : gc.edges = H)
    (hand : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) → a ≤ AndPart.andCount C)
    (hsum : b ≤ a + (H.length - 1)) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) → b ≤ C.size := by
  intro C hc he
  have h1 : a ≤ AndPart.andCount C := hand C hc he
  have h2 : H.length - 1 ≤ OrYF.countOrGates C.gates :=
    OrYF.graph_or_bound_of_entry hf OrYF.allStates_lb OrYF.allGraphCores_ok idx gc hget hn hH C hc he
  have h3 := OrYF.countOr_add_countAnd C hc
  change AndPart.andCount C + OrYF.countOrGates C.gates = C.size at h3
  omega

theorem bound_0 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = OrYF.g0_fn x) → 10 ≤ C.size :=
  combine_bound OrYF.g0_fn_eq 0 _ rfl rfl rfl AndPart.and_bound_0 (by decide)
theorem bound_1 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g1_fn x) → 10 ≤ C.size :=
  combine_bound OrYF.g1_fn_eq 1 _ rfl rfl rfl AndPart.and_bound_1 (by decide)
theorem bound_2 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g2_fn x) → 10 ≤ C.size :=
  combine_bound OrYF.g2_fn_eq 2 _ rfl rfl rfl AndPart.and_bound_2 (by decide)
theorem bound_3 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g3_fn x) → 10 ≤ C.size :=
  combine_bound OrYF.g3_fn_eq 3 _ rfl rfl rfl AndPart.and_bound_3 (by decide)
theorem bound_4 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g4_fn x) → 10 ≤ C.size :=
  combine_bound OrYF.g4_fn_eq 4 _ rfl rfl rfl AndPart.and_bound_4 (by decide)
theorem bound_5 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g5_fn x) → 10 ≤ C.size :=
  combine_bound OrYF.g5_fn_eq 5 _ rfl rfl rfl AndPart.and_bound_5 (by decide)
theorem bound_6 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g6_fn x) → 10 ≤ C.size :=
  combine_bound OrYF.g6_fn_eq 6 _ rfl rfl rfl AndPart.and_bound_6 (by decide)
theorem bound_7 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g7_fn x) → 10 ≤ C.size :=
  combine_bound OrYF.g7_fn_eq 7 _ rfl rfl rfl AndPart.and_bound_7 (by decide)
theorem bound_8 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g8_fn x) → 10 ≤ C.size :=
  combine_bound OrYF.g8_fn_eq 8 _ rfl rfl rfl AndPart.and_bound_8 (by decide)
theorem bound_9 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g9_fn x) → 10 ≤ C.size :=
  combine_bound OrYF.g9_fn_eq 9 _ rfl rfl rfl AndPart.and_bound_9 (by decide)
theorem bound_10 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g10_fn x) → 10 ≤ C.size :=
  combine_bound OrYF.g10_fn_eq 10 _ rfl rfl rfl AndPart.and_bound_10 (by decide)
theorem bound_11 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g11_fn x) → 11 ≤ C.size :=
  combine_bound OrYF.g11_fn_eq 11 _ rfl rfl rfl AndPart.and_bound_11 (by decide)
theorem bound_12 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g12_fn x) → 10 ≤ C.size :=
  combine_bound OrYF.g12_fn_eq 12 _ rfl rfl rfl AndPart.and_bound_12 (by decide)
theorem bound_13 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g13_fn x) → 11 ≤ C.size :=
  combine_bound OrYF.g13_fn_eq 13 _ rfl rfl rfl AndPart.and_bound_13 (by decide)
theorem bound_14 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g14_fn x) → 10 ≤ C.size :=
  combine_bound OrYF.g14_fn_eq 14 _ rfl rfl rfl AndPart.and_bound_14 (by decide)
theorem bound_15 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g15_fn x) → 11 ≤ C.size :=
  combine_bound OrYF.g15_fn_eq 15 _ rfl rfl rfl AndPart.and_bound_15 (by decide)
theorem bound_16 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g16_fn x) → 10 ≤ C.size :=
  combine_bound OrYF.g16_fn_eq 16 _ rfl rfl rfl AndPart.and_bound_16 (by decide)
theorem bound_17 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g17_fn x) → 11 ≤ C.size :=
  combine_bound OrYF.g17_fn_eq 17 _ rfl rfl rfl AndPart.and_bound_17 (by decide)
theorem bound_18 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g18_fn x) → 11 ≤ C.size :=
  combine_bound OrYF.g18_fn_eq 18 _ rfl rfl rfl AndPart.and_bound_18 (by decide)
theorem bound_19 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g19_fn x) → 11 ≤ C.size :=
  combine_bound OrYF.g19_fn_eq 19 _ rfl rfl rfl AndPart.and_bound_19 (by decide)
theorem bound_20 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g20_fn x) → 11 ≤ C.size :=
  combine_bound OrYF.g20_fn_eq 20 _ rfl rfl rfl AndPart.and_bound_20 (by decide)
theorem bound_21 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g21_fn x) → 11 ≤ C.size :=
  combine_bound OrYF.g21_fn_eq 21 _ rfl rfl rfl AndPart.and_bound_21 (by decide)
theorem bound_22 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g22_fn x) → 10 ≤ C.size :=
  combine_bound OrYF.g22_fn_eq 22 _ rfl rfl rfl AndPart.and_bound_22 (by decide)
theorem bound_23 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g23_fn x) → 11 ≤ C.size :=
  combine_bound OrYF.g23_fn_eq 23 _ rfl rfl rfl AndPart.and_bound_23 (by decide)
theorem bound_24 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g24_fn x) → 11 ≤ C.size :=
  combine_bound OrYF.g24_fn_eq 24 _ rfl rfl rfl AndPart.and_bound_24 (by decide)
theorem bound_25 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g25_fn x) → 11 ≤ C.size :=
  combine_bound OrYF.g25_fn_eq 25 _ rfl rfl rfl AndPart.and_bound_25 (by decide)
theorem bound_26 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g26_fn x) → 12 ≤ C.size :=
  combine_bound OrYF.g26_fn_eq 26 _ rfl rfl rfl AndPart.and_bound_26 (by decide)
theorem bound_27 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g27_fn x) → 12 ≤ C.size :=
  combine_bound OrYF.g27_fn_eq 27 _ rfl rfl rfl AndPart.and_bound_27 (by decide)
theorem bound_28 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g28_fn x) → 12 ≤ C.size :=
  combine_bound OrYF.g28_fn_eq 28 _ rfl rfl rfl AndPart.and_bound_28 (by decide)
theorem bound_29 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g29_fn x) → 12 ≤ C.size :=
  combine_bound OrYF.g29_fn_eq 29 _ rfl rfl rfl AndPart.and_bound_29 (by decide)
theorem bound_30 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g30_fn x) → 12 ≤ C.size :=
  combine_bound OrYF.g30_fn_eq 30 _ rfl rfl rfl AndPart.and_bound_30 (by decide)

end PEqualNP.Outside.L_meta_984_aux

theorem PEqualNP.Outside.L_meta_984 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) x) → 12 ≤ C.size) :=
  ⟨PEqualNP.Outside.L_meta_984_aux.bound_0, PEqualNP.Outside.L_meta_984_aux.bound_1, PEqualNP.Outside.L_meta_984_aux.bound_2, PEqualNP.Outside.L_meta_984_aux.bound_3, PEqualNP.Outside.L_meta_984_aux.bound_4, PEqualNP.Outside.L_meta_984_aux.bound_5, PEqualNP.Outside.L_meta_984_aux.bound_6, PEqualNP.Outside.L_meta_984_aux.bound_7, PEqualNP.Outside.L_meta_984_aux.bound_8, PEqualNP.Outside.L_meta_984_aux.bound_9, PEqualNP.Outside.L_meta_984_aux.bound_10, PEqualNP.Outside.L_meta_984_aux.bound_11, PEqualNP.Outside.L_meta_984_aux.bound_12, PEqualNP.Outside.L_meta_984_aux.bound_13, PEqualNP.Outside.L_meta_984_aux.bound_14, PEqualNP.Outside.L_meta_984_aux.bound_15, PEqualNP.Outside.L_meta_984_aux.bound_16, PEqualNP.Outside.L_meta_984_aux.bound_17, PEqualNP.Outside.L_meta_984_aux.bound_18, PEqualNP.Outside.L_meta_984_aux.bound_19, PEqualNP.Outside.L_meta_984_aux.bound_20, PEqualNP.Outside.L_meta_984_aux.bound_21, PEqualNP.Outside.L_meta_984_aux.bound_22, PEqualNP.Outside.L_meta_984_aux.bound_23, PEqualNP.Outside.L_meta_984_aux.bound_24, PEqualNP.Outside.L_meta_984_aux.bound_25, PEqualNP.Outside.L_meta_984_aux.bound_26, PEqualNP.Outside.L_meta_984_aux.bound_27, PEqualNP.Outside.L_meta_984_aux.bound_28, PEqualNP.Outside.L_meta_984_aux.bound_29, PEqualNP.Outside.L_meta_984_aux.bound_30⟩
