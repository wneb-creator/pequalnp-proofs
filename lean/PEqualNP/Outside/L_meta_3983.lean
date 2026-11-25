import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3983
open PEqualNP.MetaComplexity
abbrev Row := Fin 9 → Bool
abbrev Wire := Row → Bool
def ff : Wire := fun _ => false
def Cst (v : Wire) : Prop := ∃ c : Bool, v = fun _ => c
def Av (B : Set Wire) (v : Wire) : Prop := v ∈ B ∨ (fun r => !v r) ∈ B ∨ Cst v
def Comp : Nat → Set Wire → Wire → Prop
  | 0,B,T => Av B T
  | k+1,B,T => ∃ a b, Av B a ∧ Av B b ∧ Comp k (insert (fun r => a r && b r) B) T
theorem av_mem {B : Set Wire} {v} (h : v ∈ B) : Av B v := Or.inl h
theorem av_cst {B : Set Wire} (c : Bool) : Av B (fun _ => c) := Or.inr (Or.inr ⟨c,rfl⟩)
theorem av_not {B : Set Wire} {v} (h : Av B v) : Av B (fun r => !v r) := by
  rcases h with h | h | ⟨c,rfl⟩
  · exact Or.inr (Or.inl (by simpa using h))
  · exact Or.inl h
  · exact av_cst (!c)
theorem av_of_not {B : Set Wire} {v} (h : Av B (fun r => !v r)) : Av B v := by
  simpa using av_not h
theorem av_mono {B C : Set Wire} (h : ∀ b ∈ B, Av C b) {v} (hv : Av B v) : Av C v := by
  rcases hv with hv | hv | hv
  · exact h _ hv
  · exact av_of_not (h _ hv)
  · exact Or.inr (Or.inr hv)
theorem av_insert {B : Set Wire} {z v} (h : Av B v) : Av (insert z B) v :=
  av_mono (fun _ hb => av_mem (Set.mem_insert_of_mem _ hb)) h
theorem comp_mono {k} {B C : Set Wire} {T} (h : ∀ b ∈ B, Av C b) (hc : Comp k B T) : Comp k C T := by
  induction k generalizing B C with
  | zero => exact av_mono h hc
  | succ k ih =>
    obtain ⟨a,b,ha,hb,hc⟩ := hc
    refine ⟨a,b,av_mono h ha,av_mono h hb,ih ?_ hc⟩
    intro x hx
    rcases hx with rfl | hx
    · exact av_mem (Set.mem_insert _ _)
    · exact av_insert (h x hx)
theorem comp_map {k} {B : Set Wire} {T : Wire} (f : Row → Row) (h : Comp k B T) :
    Comp k ((fun v : Wire => v ∘ f) '' B) (T ∘ f) := by
  have av : ∀ {B : Set Wire} {v : Wire}, Av B v → Av ((fun v : Wire => v ∘ f) '' B) (v ∘ f) := by
    intro B v h
    rcases h with h | h | ⟨c,rfl⟩
    · exact Or.inl ⟨v,h,rfl⟩
    · exact Or.inr (Or.inl ⟨_,h,rfl⟩)
    · exact av_cst c
  induction k generalizing B with
  | zero => exact av h
  | succ k ih =>
    obtain ⟨a,b,ha,hb,hc⟩ := h
    refine ⟨a∘f,b∘f,av ha,av hb,?_⟩
    have := ih hc
    rw [Set.image_insert_eq] at this
    exact this

def op : Nat → Bool → Bool → Bool
  | 0,x,y => x && y
  | 1,x,y => x || y
  | 2,x,y => x && !y
  | _,x,y => !x && y
def wop (d : Nat) (a b : Wire) : Wire := fun r => op d (a r) (b r)
def swapOp (d : Nat) : Nat := if d=2 then 3 else if d=3 then 2 else d
theorem wop_swap {d} (hd : d<4) (a b : Wire) : wop d a b = wop (swapOp d) b a := by
  funext r
  interval_cases d <;> simp [wop,op,swapOp] <;> cases a r <;> cases b r <;> rfl
theorem swap_lt {d} (hd : d<4) : swapOp d < 4 := by interval_cases d <;> decide

theorem comp_gate {k} {B : Set Wire} {a b T : Wire} {d : Nat} (hd : d<4) (ha : Av B a) (hb : Av B b)
    (h : Comp k (insert (wop d a b) B) T) : Comp (k+1) B T := by
  have key : ∃ x y, Av B x ∧ Av B y ∧ Av (insert (fun r => x r && y r) B) (wop d a b) := by
    interval_cases d
    · exact ⟨a,b,ha,hb,av_mem (Set.mem_insert _ _)⟩
    · refine ⟨_,_,av_not ha,av_not hb,av_of_not (av_mem ?_)⟩
      have : (fun r => !(wop 1 a b r)) = fun r => (!a r) && (!b r) := by funext r; simp [wop,op]
      rw [this]; exact Set.mem_insert _ _
    · exact ⟨a,_,ha,av_not hb,av_mem (Set.mem_insert _ _)⟩
    · exact ⟨_,b,av_not ha,hb,av_mem (Set.mem_insert _ _)⟩
  obtain ⟨x,y,hx,hy,hz⟩ := key
  refine ⟨x,y,hx,hy,comp_mono ?_ h⟩
  intro v hv
  rcases hv with rfl | hv
  · exact hz
  · exact av_insert (av_mem hv)

def Live : Nat → Finset Wire → Wire → Prop
  | 0,S,T => S={T}
  | k+1,S,T => ∃ (U : Finset Wire) (a b : Wire) (d : Nat), S = insert a (insert b U) ∧ a ≠ b ∧ d<4 ∧
      wop d a b ∉ S ∧ wop d a b ≠ ff ∧ Live k (insert (wop d a b) U) T

theorem live_card {k S T} (h : Live k S T) : S.card ≤ k+1 := by
  induction k generalizing S with
  | zero => rw [show S={T} from h]; simp
  | succ k ih =>
    obtain ⟨U,a,b,d,rfl,hab,hd,hf,hz,h⟩ := h
    have hu : wop d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have := ih h
    rw [Finset.card_insert_of_notMem hu] at this
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    omega

theorem live_diff {k S T} (h : Live k S T) {r s : Row} (hT : T r ≠ T s) : ∃ a ∈ S, a r ≠ a s := by
  induction k generalizing S with
  | zero => rw [show S={T} from h]; exact ⟨T,by simp,hT⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,rfl,hab,hd,hf,hz,h⟩ := h
    obtain ⟨v,hv,e⟩ := ih h
    rcases Finset.mem_insert.mp hv with rfl | hv
    · by_cases ha : a r = a s
      · by_cases hb : b r = b s
        · simp [wop,ha,hb] at e
        · exact ⟨b,by simp,hb⟩
      · exact ⟨a,by simp,ha⟩
    · exact ⟨v,by simp [hv],e⟩

theorem live_map {k S T} (h : Live k S T) (f : Row → Row) (onto : Function.Surjective f) :
    Live k (S.image (fun v => v∘f)) (T∘f) := by
  have inj : Function.Injective (fun v : Wire => v∘f) := onto.injective_comp_right
  induction k generalizing S with
  | zero => rw [show S={T} from h]; simp [Live]
  | succ k ih =>
    obtain ⟨U,a,b,d,rfl,hab,hd,hf,hz,h⟩ := h
    have e : wop d (a∘f) (b∘f) = (wop d a b)∘f := rfl
    refine ⟨U.image (fun v => v∘f),a∘f,b∘f,d,by simp [Finset.image_insert],fun h => hab (inj h),hd,?_,?_,?_⟩
    · rw [e]
      intro hm
      obtain ⟨v,hv,hh⟩ := Finset.mem_image.mp hm
      exact hf (inj hh ▸ hv)
    · rw [e]
      intro hh
      exact hz (inj (hh.trans (rfl : ff = ff∘f)))
    · rw [e]
      have := ih h
      rwa [Finset.image_insert] at this

def Norm (v : Wire) : Prop := v (fun _ => false) = false ∧ v ≠ ff
def nrm (v : Wire) : Wire := if v (fun _ => false) then fun r => !v r else v
theorem nrm_zero (v : Wire) : nrm v (fun _ => false) = false := by
  unfold nrm; cases h : v (fun _ => false) <;> simp [h]
theorem av_nrm {B : Set Wire} {v} : Av B (nrm v) ↔ Av B v := by
  unfold nrm; split
  · exact ⟨av_of_not,av_not⟩
  · rfl
theorem nrm_and (a b : Wire) : ∃ d, d<4 ∧ nrm (fun r => a r && b r) = wop d (nrm a) (nrm b) := by
  cases ha : a (fun _ => false) <;> cases hb : b (fun _ => false)
  · exact ⟨0,by omega,by funext r; simp [nrm,ha,hb,wop,op]⟩
  · exact ⟨2,by omega,by funext r; simp [nrm,ha,hb,wop,op]⟩
  · exact ⟨3,by omega,by funext r; simp [nrm,ha,hb,wop,op]⟩
  · exact ⟨1,by omega,by funext r; simp [nrm,ha,hb,wop,op]⟩
theorem wop_self {d} (hd : d<4) (a : Wire) : wop d a a = a ∨ wop d a a = ff := by
  interval_cases d
  · left; funext r; simp [wop,op]
  · left; funext r; simp [wop,op]
  · right; funext r; simp [wop,op,ff]
  · right; funext r; simp [wop,op,ff]
theorem wop_ff_left {d} (hd : d<4) (b : Wire) : wop d ff b = b ∨ wop d ff b = ff := by
  interval_cases d
  · right; funext r; simp [wop,op,ff]
  · left; funext r; simp [wop,op,ff]
  · right; funext r; simp [wop,op,ff]
  · left; funext r; simp [wop,op,ff]
theorem av_ff {B : Set Wire} : Av B ff := av_cst false

theorem extract {k} {B : Set Wire} {T : Wire} (h : Comp k B T) (hT : Norm T) :
    ∃ j S, j ≤ k ∧ Live j S T ∧ ∀ s ∈ S, Av B s ∧ Norm s := by
  induction k generalizing B with
  | zero => exact ⟨0,{T},le_rfl,rfl,by simpa using ⟨h,hT⟩⟩
  | succ k ih =>
    obtain ⟨a,b,ha,hb,h⟩ := h
    obtain ⟨j,S,hj,hl,hs⟩ := ih h
    obtain ⟨d,hd,hz⟩ := nrm_and a b
    set w : Wire := fun r => a r && b r with hw
    have key : ∀ s ∈ S, s = nrm w ∨ Av B s := by
      intro s hs'
      obtain ⟨hv,hn⟩ := hs s hs'
      rcases hv with hv | hv | hv
      · rcases hv with rfl | hv
        · left; simp [nrm,hn.1]
        · right; exact av_mem hv
      · rcases hv with e | hv
        · left
          rw [← e]; funext r; simp [nrm,hn.1]
        · right; exact Or.inr (Or.inl hv)
      · right; exact Or.inr (Or.inr hv)
    by_cases easy : Av B (nrm w)
    · refine ⟨j,S,by omega,hl,fun s hs' => ⟨?_,(hs s hs').2⟩⟩
      rcases key s hs' with rfl | h
      · exact easy
      · exact h
    by_cases mem : nrm w ∈ S
    · have hab : nrm a ≠ nrm b := by
        intro e
        rw [hz,e] at easy
        rcases wop_self hd (nrm b) with e | e <;> rw [e] at easy
        · exact easy (av_nrm.mpr hb)
        · exact easy av_ff
      have ha' : nrm a ≠ ff := by
        intro e
        rw [hz,e] at easy
        rcases wop_ff_left hd (nrm b) with e | e <;> rw [e] at easy
        · exact easy (av_nrm.mpr hb)
        · exact easy av_ff
      have hb' : nrm b ≠ ff := by
        intro e
        rw [hz,e,wop_swap hd] at easy
        rcases wop_ff_left (swap_lt hd) (nrm a) with e | e <;> rw [e] at easy
        · exact easy (av_nrm.mpr ha)
        · exact easy av_ff
      have all : ∀ s ∈ insert (nrm a) (insert (nrm b) (S.erase (nrm w))), Av B s ∧ Norm s := by
        intro s hs'
        simp only [Finset.mem_insert,Finset.mem_erase] at hs'
        rcases hs' with rfl | rfl | ⟨hne,hs'⟩
        · exact ⟨av_nrm.mpr ha,nrm_zero a,ha'⟩
        · exact ⟨av_nrm.mpr hb,nrm_zero b,hb'⟩
        · exact ⟨(key s hs').resolve_left hne,(hs s hs').2⟩
      refine ⟨j+1,_,by omega,⟨S.erase (nrm w),nrm a,nrm b,d,rfl,hab,hd,?_,?_,?_⟩,all⟩
      · rw [← hz]; exact fun hm => easy (all _ hm).1
      · rw [← hz]; exact (hs _ mem).2.2
      · rw [← hz,Finset.insert_erase mem]; exact hl
    · refine ⟨j,S,by omega,hl,fun s hs' => ⟨?_,(hs s hs').2⟩⟩
      rcases key s hs' with rfl | h
      · exact absurd hs' mem
      · exact h

theorem wop_cst {B : Set Wire} {d} (hd : d<4) {a b : Wire} (ha : Cst a) (hb : Av B b) : Av B (wop d a b) := by
  obtain ⟨c,rfl⟩ := ha
  have e : wop d (fun _ => c) b = b ∨ wop d (fun _ => c) b = (fun r => !b r) ∨ Cst (wop d (fun _ => c) b) := by
    interval_cases d <;> cases c
    · exact Or.inr (Or.inr ⟨false,by funext r; simp [wop,op]⟩)
    · exact Or.inl (by funext r; simp [wop,op])
    · exact Or.inl (by funext r; simp [wop,op])
    · exact Or.inr (Or.inr ⟨true,by funext r; simp [wop,op]⟩)
    · exact Or.inr (Or.inr ⟨false,by funext r; simp [wop,op]⟩)
    · exact Or.inr (Or.inl (by funext r; simp [wop,op]))
    · exact Or.inl (by funext r; simp [wop,op])
    · exact Or.inr (Or.inr ⟨false,by funext r; simp [wop,op]⟩)
  rcases e with e | e | e
  · rw [e]; exact hb
  · rw [e]; exact av_not hb
  · exact Or.inr (Or.inr e)
theorem wop_cst' {B : Set Wire} {d} (hd : d<4) {a b : Wire} (ha : Av B a) (hb : Cst b) : Av B (wop d a b) := by
  rw [wop_swap hd]; exact wop_cst (swap_lt hd) hb ha

open Classical in
noncomputable def ccount (f : Row → Row) (S : Finset Wire) : Nat := (S.filter (fun s => Cst (s∘f))).card

theorem ccount_insert_le (f : Row → Row) (a : Wire) (S : Finset Wire) : ccount f (insert a S) ≤ ccount f S + 1 := by
  classical
  unfold ccount
  rw [Finset.filter_insert]
  split
  · exact Finset.card_insert_le _ _
  · omega
theorem ccount_insert_not (f : Row → Row) {a : Wire} {S : Finset Wire} (h : ¬Cst (a∘f)) : ccount f (insert a S) = ccount f S := by
  classical
  unfold ccount
  rw [Finset.filter_insert,ite_eq_right h]
theorem ccount_insert_cst (f : Row → Row) {a : Wire} {S : Finset Wire} (h : Cst (a∘f)) (hn : a ∉ S) :
    ccount f (insert a S) = ccount f S + 1 := by
  classical
  unfold ccount
  rw [Finset.filter_insert,ite_eq_left h,Finset.card_insert_of_notMem (by simp [hn])]
theorem ccount_mono (f : Row → Row) {S U : Finset Wire} (h : S ⊆ U) : ccount f S ≤ ccount f U := by
  classical
  exact Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem elim {k} (f : Row → Row) {S : Finset Wire} {B : Set Wire} {T : Wire} (h : Live k S T)
    (hs : ∀ s ∈ S, Av B (s∘f)) (nc : ¬Cst (T∘f)) : ∃ j, j + ccount f S ≤ k ∧ Comp j B (T∘f) := by
  induction k generalizing S B with
  | zero =>
    obtain rfl : S={T} := h
    refine ⟨0,?_,hs T (by simp)⟩
    have : ccount f ({T} : Finset Wire) = 0 := by
      classical
      unfold ccount
      simp [Finset.filter_singleton,nc]
    omega
  | succ k ih =>
    obtain ⟨U,a,b,d,rfl,hab,hd,hf,hz,h⟩ := h
    have ha : Av B (a∘f) := hs a (by simp)
    have hb : Av B (b∘f) := hs b (by simp)
    have hu : ∀ s ∈ U, Av B (s∘f) := fun s hm => hs s (by simp [hm])
    have zu : wop d a b ∉ U := fun hm => hf (by simp [hm])
    have e : (wop d a b)∘f = wop d (a∘f) (b∘f) := rfl
    have one := ccount_insert_le f a (insert b U)
    have two := ccount_insert_le f b U
    have mono : ccount f U ≤ ccount f (insert (wop d a b) U) := ccount_mono f (Finset.subset_insert _ _)
    by_cases ca : Cst (a∘f)
    · obtain ⟨j,hj,hc⟩ := ih (S:=insert (wop d a b) U) (B:=B) h (by
        intro s hm
        rcases Finset.mem_insert.mp hm with rfl | hm
        · rw [e]; exact wop_cst hd ca hb
        · exact hu s hm)
      refine ⟨j,?_,hc⟩
      by_cases cb : Cst (b∘f)
      · have cz : Cst ((wop d a b)∘f) := by
          obtain ⟨x,hx⟩ := ca
          obtain ⟨y,hy⟩ := cb
          exact ⟨op d x y,by rw [e,hx,hy]; rfl⟩
        rw [ccount_insert_cst f cz zu] at hj
        omega
      · have := ccount_insert_not f (S:=U) cb
        omega
    · have ea := ccount_insert_not f (S:=insert b U) ca
      by_cases cb : Cst (b∘f)
      · obtain ⟨j,hj,hc⟩ := ih (S:=insert (wop d a b) U) (B:=B) h (by
          intro s hm
          rcases Finset.mem_insert.mp hm with rfl | hm
          · rw [e]; exact wop_cst' hd ha cb
          · exact hu s hm)
        exact ⟨j,by omega,hc⟩
      · have eb := ccount_insert_not f (S:=U) cb
        obtain ⟨j,hj,hc⟩ := ih (S:=insert (wop d a b) U) (B:=insert (wop d (a∘f) (b∘f)) B) h (by
          intro s hm
          rcases Finset.mem_insert.mp hm with rfl | hm
          · rw [e]; exact av_mem (Set.mem_insert _ _)
          · exact av_insert (hu s hm))
        exact ⟨j+1,by omega,comp_gate hd ha hb hc⟩

def xv (i : Fin 9) : Wire := fun r => r i
def Inp : Set Wire := Set.range xv
def edges : List (Fin 9 × Fin 9) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
def inS (m : Nat) (i : Fin 9) : Bool := m.testBit i.val
def edgesOf (q : Nat) : List (Fin 9 × Fin 9) := edges.filter (fun e => inS q e.1 && inS q e.2)
def gr (q : Nat) (s : List (Fin 9)) : Wire := fun r => (edgesOf q).any (fun e => r e.1 && r e.2) || s.any r
def Lower (g : Wire) (L : Nat) : Prop := ∀ j, Comp j Inp g → L ≤ j
def fixR (z o : Nat) (r : Row) : Row := fun i => if inS z i then false else if inS o i then true else r i
def perm (p : List (Fin 9)) (r : Row) : Row := fun i => r (p.getD i.val 0)

theorem inp_fix (z o : Nat) (i : Fin 9) : Av Inp (xv i ∘ fixR z o) := by
  cases hz : inS z i
  · cases ho : inS o i
    · have : xv i ∘ fixR z o = xv i := by funext r; simp [xv,fixR,hz,ho]
      rw [this]; exact av_mem ⟨i,rfl⟩
    · have : xv i ∘ fixR z o = fun _ => true := by funext r; simp [xv,fixR,hz,ho]
      rw [this]; exact av_cst true
  · have : xv i ∘ fixR z o = fun _ => false := by funext r; simp [xv,fixR,hz]
    rw [this]; exact av_cst false
theorem inp_perm (p : List (Fin 9)) (i : Fin 9) : Av Inp (xv i ∘ perm p) :=
  av_mem ⟨p.getD i.val 0,rfl⟩
theorem comp_inp {f : Row → Row} (hf : ∀ i, Av Inp (xv i ∘ f)) {j T} (h : Comp j Inp T) : Comp j Inp (T∘f) := by
  refine comp_mono ?_ (comp_map f h)
  rintro _ ⟨_,⟨i,rfl⟩,rfl⟩
  exact hf i

theorem xv_zero (i : Fin 9) : xv i (fun _ => false) = false := rfl
theorem av_inp_norm {v : Wire} (R : Fin 9 → Prop) (h : Av {w | ∃ i, R i ∧ w = xv i} v) (hn : Norm v) :
    ∃ i, R i ∧ v = xv i := by
  rcases h with h | ⟨i,_,h⟩ | ⟨c,h⟩
  · exact h
  · have := congrFun h (fun _ => false)
    simp [hn.1,xv] at this
  · exfalso
    cases c
    · exact hn.2 h
    · have := hn.1; rw [h] at this; simp at this
theorem inp_eq : Inp = {w | ∃ i, True ∧ w = xv i} := by
  ext w; simp [Inp,eq_comm]

def single (i : Fin 9) : Row := fun j => j == i
theorem gr_zero (q s) : gr q s (fun _ => false) = false := by simp [gr]
def grow (g : Wire) (i : Fin 9) : Wire := fun r => r i || g r
theorem bit_self : ∀ i : Fin 9, inS (1 <<< i.val) i = true := by decide
theorem bit_other : ∀ i t : Fin 9, t ≠ i → inS (1 <<< i.val) t = false := by decide
theorem lower_single {g : Wire} {L : Nat} (i : Fin 9) (h : Lower g L) (hz : g (fun _ => false) = false)
    (nc : g ≠ ff) (ind : g ∘ fixR (1 <<< i.val) 0 = g) : Lower (grow g i) (L+1) := by
  intro j hj
  have hb : inS (1 <<< i.val) i = true := bit_self i
  have hT : Norm (grow g i) := by
    refine ⟨by simp [grow,hz],fun e => ?_⟩
    have := congrFun e (single i)
    simp [grow,single,ff] at this
  obtain ⟨k,S,hk,hl,hs⟩ := extract hj hT
  have e : grow g i ∘ fixR (1 <<< i.val) 0 = g := by
    funext r
    have := congrFun ind r
    simp only [Function.comp] at this
    simp [grow,this,fixR,hb]
  have ncg : ¬Cst g := by
    rintro ⟨c,hc⟩
    have : c = false := by rw [hc] at hz; exact hz
    exact nc (by rw [hc,this]; rfl)
  have mem : xv i ∈ S := by
    obtain ⟨a,ha,hd⟩ := live_diff (r:=single i) (s:=fun _ => false) hl (by simp [grow,single,hz])
    obtain ⟨hv,hn⟩ := hs a ha
    rw [inp_eq] at hv
    obtain ⟨t,-,rfl⟩ := av_inp_norm _ hv hn
    have : t = i := by simpa [xv,single] using hd
    exact this ▸ ha
  obtain ⟨n,hn,hc⟩ := elim (B:=Inp) (fixR (1 <<< i.val) 0) hl (by
    intro s hm
    obtain ⟨hv,hn⟩ := hs s hm
    rw [inp_eq] at hv
    obtain ⟨t,-,rfl⟩ := av_inp_norm _ hv hn
    exact inp_fix _ _ t) (by rw [e]; exact ncg)
  rw [e] at hc
  have one : 1 ≤ ccount (fixR (1 <<< i.val) 0) S := by
    classical
    refine Finset.card_pos.mpr ⟨xv i,?_⟩
    simp only [Finset.mem_filter]
    exact ⟨mem,false,by funext r; simp [xv,fixR,hb]⟩
  have := h n hc
  omega

def indep (q : Nat) (s : List (Fin 9)) (i : Fin 9) : Bool := !(inS q i) && !(s.contains i)
theorem gr_indep {q s i} (h : indep q s i = true) : gr q s ∘ fixR (1 <<< i.val) 0 = gr q s := by
  simp only [indep,Bool.and_eq_true,Bool.not_eq_true'] at h
  have hb : ∀ t, t ≠ i → inS (1 <<< i.val) t = false := bit_other i
  have h0 : ∀ t, inS 0 t = false := by decide
  funext r
  have key : ∀ t, t ≠ i → fixR (1 <<< i.val) 0 r t = r t := by
    intro t ht; simp [fixR,hb t ht,h0 t]
  have e1 : (edgesOf q).any (fun e => fixR (1 <<< i.val) 0 r e.1 && fixR (1 <<< i.val) 0 r e.2) =
      (edgesOf q).any (fun e => r e.1 && r e.2) := by
    rw [Bool.eq_iff_iff,List.any_eq_true,List.any_eq_true]
    have : ∀ e ∈ edgesOf q, e.1 ≠ i ∧ e.2 ≠ i := by
      intro e he
      simp only [edgesOf,List.mem_filter,Bool.and_eq_true] at he
      exact ⟨fun c => by rw [← c,he.2.1] at h; simp at h,fun c => by rw [← c,he.2.2] at h; simp at h⟩
    constructor
    · rintro ⟨e,he,hh⟩
      rw [key _ (this e he).1,key _ (this e he).2] at hh
      exact ⟨e,he,hh⟩
    · rintro ⟨e,he,hh⟩
      refine ⟨e,he,?_⟩
      rw [key _ (this e he).1,key _ (this e he).2]
      exact hh
  have e2 : s.any (fixR (1 <<< i.val) 0 r) = s.any r := by
    rw [Bool.eq_iff_iff,List.any_eq_true,List.any_eq_true]
    have : ∀ e ∈ s, e ≠ i := by
      intro e he c
      have := h.2
      rw [← c,List.contains_iff_mem.mpr he] at this
      simp at this
    constructor
    · rintro ⟨e,he,hh⟩; rw [key _ (this e he)] at hh; exact ⟨e,he,hh⟩
    · rintro ⟨e,he,hh⟩; exact ⟨e,he,by rw [key _ (this e he)]; exact hh⟩
  simp only [Function.comp,gr,e1,e2]
theorem gr_grow (q s i) : gr q (i::s) = grow (gr q s) i := by
  funext r
  simp only [gr,grow,List.any_cons]
  cases r i <;> simp
def nonempty (q : Nat) (s : List (Fin 9)) : Bool := !(edgesOf q).isEmpty || !s.isEmpty
theorem gr_ne {q s} (h : nonempty q s = true) : gr q s ≠ ff := by
  intro e
  have := congrFun e (fun _ => true)
  simp only [nonempty,Bool.or_eq_true,Bool.not_eq_true',List.isEmpty_eq_false_iff] at h
  simp only [gr,ff,Bool.and_self,Bool.or_eq_false_iff] at this
  rcases h with h | h
  · obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil _ h
    have h2 := List.any_eq_false.mp this.1 x hx
    simp at h2
  · obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil _ h
    have h2 := List.any_eq_false.mp this.2 x hx
    simp at h2
def growOK (q : Nat) : List (Fin 9) → Bool
  | [] => true
  | i::s => growOK q s && indep q s i && nonempty q s
theorem lower_grow {q L} (h : Lower (gr q []) L) (s : List (Fin 9)) (ok : growOK q s = true) :
    Lower (gr q s) (L+s.length) := by
  induction s with
  | nil => simpa using h
  | cons i s ih =>
    simp only [growOK,Bool.and_eq_true] at ok
    rw [gr_grow]
    exact lower_single i (ih ok.1.1) (gr_zero _ _) (gr_ne ok.2) (gr_indep ok.1.2)
theorem lower_grow0 (s : List (Fin 9)) (ok : growOK 0 s = true) :
    s ≠ [] → Lower (gr 0 s) (s.length-1) := by
  induction s with
  | nil => intro h; exact absurd rfl h
  | cons i s ih =>
    intro _
    by_cases hs : s = []
    · subst hs; intro j _; simp
    · simp only [growOK,Bool.and_eq_true] at ok
      rw [gr_grow]
      have := lower_single i (ih ok.1.1 hs) (gr_zero _ _) (gr_ne ok.2) (gr_indep ok.1.2)
      have hl : 0 < s.length := List.length_pos_iff.mpr hs
      rw [List.length_cons,show s.length+1-1 = s.length-1+1 by omega]
      exact this

def colEdge (z o q s : Nat) (e : Fin 9 × Fin 9) : Bool :=
  (inS z e.1 || inS z e.2) ||
  (!(inS o e.1) && !(inS o e.2) && inS q e.1 && inS q e.2) ||
  (inS o e.1 && !(inS o e.2) && inS s e.2) || (inS o e.2 && !(inS o e.1) && inS s e.1) ||
  (!(inS o e.1) && inS s e.1) || (!(inS o e.2) && inS s e.2)
def sL (s : Nat) : List (Fin 9) := (List.finRange 9).filter (inS s)
def freeV (z o : Nat) (i : Fin 9) : Bool := !(inS z i) && !(inS o i)
def colEq (m z o q s : Nat) : Bool :=
  (edgesOf m).all (colEdge z o q s) &&
  (edgesOf q).all (fun e => inS m e.1 && inS m e.2 && freeV z o e.1 && freeV z o e.2) &&
  (sL s).all (fun i => freeV z o i && (edgesOf m).any (fun e =>
    (e.1 == i && inS o e.2 && !(inS z e.2)) || (e.2 == i && inS o e.1 && !(inS z e.1))))
theorem fix_free {z o i} (h : freeV z o i = true) (r : Row) : fixR z o r i = r i := by
  simp only [freeV,Bool.and_eq_true,Bool.not_eq_true'] at h
  simp [fixR,h.1,h.2]
theorem mem_edgesOf {m e} : e ∈ edgesOf m ↔ e ∈ edges ∧ inS m e.1 = true ∧ inS m e.2 = true := by
  simp [edgesOf]
theorem gr_fix {m z o q s} (h : colEq m z o q s = true) : gr m [] ∘ fixR z o = gr q (sL s) := by
  simp only [colEq,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨⟨h1,h2⟩,h3⟩ := h
  have ms : ∀ i, inS s i = true → i ∈ sL s := fun i hi => by simp [sL,hi]
  funext r
  simp only [Function.comp,gr,List.any_nil,Bool.or_false]
  rw [Bool.eq_iff_iff,Bool.or_eq_true,List.any_eq_true,List.any_eq_true,List.any_eq_true]
  constructor
  · rintro ⟨⟨u,v⟩,he,hh⟩
    simp only [Bool.and_eq_true] at hh
    have c := h1 _ he
    have hzu : inS z u = false := by
      by_contra hc; simp only [Bool.not_eq_false] at hc; simp [fixR,hc] at hh
    have hzv : inS z v = false := by
      by_contra hc; simp only [Bool.not_eq_false] at hc; simp [fixR,hc] at hh
    simp only [colEdge,hzu,hzv,Bool.or_false,Bool.false_or,Bool.or_eq_true,Bool.and_eq_true,Bool.not_eq_true'] at c
    rcases c with (((⟨⟨⟨ou,ov⟩,qu⟩,qv⟩ | ⟨⟨-,ov⟩,sv⟩) | ⟨⟨-,ou⟩,su⟩) | ⟨ou,su⟩) | ⟨ov,sv⟩
    · left
      refine ⟨(u,v),mem_edgesOf.mpr ⟨(mem_edgesOf.mp he).1,qu,qv⟩,?_⟩
      simpa [fixR,hzu,hzv,ou,ov] using hh
    · right
      exact ⟨v,ms v sv,by simpa [fixR,hzv,ov] using hh.2⟩
    · right
      exact ⟨u,ms u su,by simpa [fixR,hzu,ou] using hh.1⟩
    · right
      exact ⟨u,ms u su,by simpa [fixR,hzu,ou] using hh.1⟩
    · right
      exact ⟨v,ms v sv,by simpa [fixR,hzv,ov] using hh.2⟩
  · rintro (⟨e,he,hh⟩ | ⟨i,hi,hh⟩)
    · have c := h2 e he
      refine ⟨e,mem_edgesOf.mpr ⟨(mem_edgesOf.mp he).1,c.1.1.1,c.1.1.2⟩,?_⟩
      rw [fix_free c.1.2,fix_free c.2]; exact hh
    · have c := h3 i hi
      simp only [Bool.and_eq_true,List.any_eq_true,Bool.or_eq_true,beq_iff_eq,Bool.not_eq_true'] at c
      obtain ⟨fr,e,he,hc⟩ := c
      refine ⟨e,he,?_⟩
      rcases hc with ⟨⟨hi',oo⟩,zz⟩ | ⟨⟨hi',oo⟩,zz⟩
      · rw [hi',fix_free fr,hh]; simp [fixR,oo,zz]
      · rw [hi',fix_free fr,hh]; simp [fixR,oo,zz]

abbrev Col := Nat × Nat × Nat × Nat × Nat
def Known (K : List (Nat × Nat)) : Prop := ∀ e ∈ K, Lower (gr e.1 []) e.2
def boundOK (K : List (Nat × Nat)) (q s L : Nat) : Bool :=
  if q = 0 then !(sL s).isEmpty && (L == (sL s).length-1) else K.any (fun e => e.1 == q && L == e.2+(sL s).length)
def colOK (K : List (Nat × Nat)) (m : Nat) (c : Col) : Bool :=
  colEq m c.1 c.2.1 c.2.2.1 c.2.2.2.1 && growOK c.2.2.1 (sL c.2.2.2.1) && nonempty c.2.2.1 (sL c.2.2.2.1) &&
  boundOK K c.2.2.1 c.2.2.2.1 c.2.2.2.2
def Slice (m : Nat) (c : Col) : Prop :=
  Lower (gr m [] ∘ fixR c.1 c.2.1) c.2.2.2.2 ∧ ¬Cst (gr m [] ∘ fixR c.1 c.2.1)
theorem col_sound {K m c} (hK : Known K) (h : colOK K m c = true) : Slice m c := by
  obtain ⟨z,o,q,s,L⟩ := c
  simp only [colOK,Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  show Lower (gr m [] ∘ fixR z o) L ∧ ¬Cst (gr m [] ∘ fixR z o)
  change colEq m z o q s = true at h1
  change growOK q (sL s) = true at h2
  change nonempty q (sL s) = true at h3
  change boundOK K q s L = true at h4
  rw [gr_fix h1]
  refine ⟨?_,?_⟩
  · unfold boundOK at h4
    split at h4
    · rename_i hq
      subst hq
      simp only [Bool.and_eq_true,Bool.not_eq_true',List.isEmpty_eq_false_iff,beq_iff_eq] at h4
      rw [h4.2]; exact lower_grow0 _ h2 h4.1
    · simp only [List.any_eq_true,Bool.and_eq_true,beq_iff_eq] at h4
      obtain ⟨e,he,hq,hL⟩ := h4
      rw [hL]; exact lower_grow (hq ▸ hK e he) _ h2
  · rintro ⟨c,hc⟩
    have : c = false := by rw [← gr_zero q (sL s),hc]
    exact gr_ne h3 (by rw [hc,this]; rfl)

def relOK (q' q : Nat) (p : List (Fin 9)) : Bool :=
  let f := fun e : Fin 9 × Fin 9 => (p.getD e.1.val 0,p.getD e.2.val 0)
  (edgesOf q').all (fun e => (edgesOf q).contains (f e) || (edgesOf q).contains (f e).swap) &&
  (edgesOf q).all (fun e => (edgesOf q').any (fun d => f d == e || (f d).swap == e))
theorem gr_perm {q' q p} (h : relOK q' q p = true) : gr q' [] ∘ perm p = gr q [] := by
  simp only [relOK,Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,List.contains_iff_mem,List.any_eq_true,beq_iff_eq] at h
  obtain ⟨h1,h2⟩ := h
  funext r
  simp only [Function.comp,gr,List.any_nil,Bool.or_false]
  rw [Bool.eq_iff_iff,List.any_eq_true,List.any_eq_true]
  constructor
  · rintro ⟨e,he,hh⟩
    simp only [Bool.and_eq_true] at hh
    rcases h1 e he with h | h
    · exact ⟨_,h,by simpa [perm] using hh⟩
    · exact ⟨_,h,by simpa [perm,and_comm] using hh⟩
  · rintro ⟨e,he,hh⟩
    obtain ⟨d,hd,h | h⟩ := h2 e he
    · exact ⟨d,hd,by rw [← h] at hh; simpa [perm] using hh⟩
    · exact ⟨d,hd,by rw [← h] at hh; simpa [perm,and_comm] using hh⟩
theorem lower_rel {q' q p L} (h : relOK q' q p = true) (low : Lower (gr q []) L) : Lower (gr q' []) L := by
  intro j hj
  have := comp_inp (inp_perm p) hj
  rw [gr_perm h] at this
  exact low j this
def extend (K : List (Nat × Nat)) (L : Nat) (maps : List (Nat × List (Fin 9))) : List (Nat × Nat) :=
  maps.map (fun e => (e.1,L)) ++ K
theorem extend_ok {K L q maps} (hK : Known K) (low : Lower (gr q []) L)
    (h : maps.all (fun e => relOK e.1 q e.2) = true) : Known (extend K L maps) := by
  intro e he
  simp only [extend,List.mem_append,List.mem_map] at he
  rcases he with ⟨d,hd,rfl⟩ | he
  · exact lower_rel (List.all_eq_true.mp h d hd) low
  · exact hK e he

def bt (r : Row) : Nat := Nat.ofBits r
theorem bt_lt (r : Row) : bt r < 512 := Nat.ofBits_lt_two_pow r
def obs (n : Nat) : Wire := fun r => n.testBit (bt r)
theorem bt_surj {i : Nat} (h : i < 512) : ∃ r, bt r = i := by
  refine ⟨fun j => i.testBit j.val,?_⟩
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 9
  · simp [bt,Nat.testBit_ofBits_lt _ _ ht]
  · rw [bt,Nat.testBit_ofBits_ge _ _ (by omega),Nat.testBit_lt_two_pow]
    exact lt_of_lt_of_le h (Nat.pow_le_pow_right (n:=2) (by omega) (show 9 ≤ t by omega))
theorem obs_inj {x y : Nat} (hx : x < 2^512) (hy : y < 2^512) (h : obs x = obs y) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 512
  · obtain ⟨r,rfl⟩ := bt_surj hi
    exact congrFun h r
  · have hp : 2^512 ≤ 2^i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx hp),Nat.testBit_lt_two_pow (lt_of_lt_of_le hy hp)]
def Xs : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
  0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
  0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
  0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
  0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
  0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
  0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
  0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
theorem Xs_bit : ∀ (i : Fin 9) (t : Fin 512), (Xs.getD i.val 0).testBit t.val = t.val.testBit i.val := by decide +kernel
theorem obs_X (i : Fin 9) : obs (Xs.getD i.val 0) = xv i := by
  funext r
  rw [obs,Xs_bit i ⟨bt r,bt_lt r⟩]
  simp [bt,xv,Nat.testBit_ofBits_lt]
def full512 : Nat := 2^512-1
theorem full_bit (r : Row) : full512.testBit (bt r) = true := by
  rw [full512,Nat.testBit_two_pow_sub_one]
  simpa using bt_lt r

def opN (d x y : Nat) : Nat :=
  match d with
  | 0 => x &&& y
  | 1 => x ||| y
  | 2 => x ^^^ (x &&& y)
  | _ => y ^^^ (x &&& y)
theorem opN_bit (d x y i : Nat) : (opN d x y).testBit i = op d (x.testBit i) (y.testBit i) := by
  unfold opN
  split <;> simp [op,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor] <;>
    cases x.testBit i <;> cases y.testBit i <;> rfl
theorem obs_op (d x y : Nat) : obs (opN d x y) = wop d (obs x) (obs y) := by
  funext r; exact opN_bit d x y _
theorem opN_lt {d x y n : Nat} (hx : x < 2^n) (hy : y < 2^n) : opN d x y < 2^n := by
  unfold opN
  split
  · exact Nat.and_lt_two_pow _ hy
  · exact Nat.or_lt_two_pow hx hy
  · exact Nat.xor_lt_two_pow hx (Nat.and_lt_two_pow _ hy)
  · exact Nat.xor_lt_two_pow hy (Nat.and_lt_two_pow _ hy)

def evalW : List Nat → List Nat → List Nat
  | [],b => b
  | c::cs,b => evalW cs (b ++ [opN (c % 4) (b.getD (c/4 % 16) 0) (b.getD (c/64) 0)])
theorem getD_map_bit {l m : List Nat} {i j : Nat} (h : l.map (fun x => x.testBit i) = m.map (fun x => x.testBit j))
    (t : Nat) : (l.getD t 0).testBit i = (m.getD t 0).testBit j := by
  have a : (l.getD t 0).testBit i = (l.map (fun x => x.testBit i)).getD t false := by
    simp [List.getD_eq_getElem?_getD]
    cases l[t]? <;> simp
  have b : (m.getD t 0).testBit j = (m.map (fun x => x.testBit j)).getD t false := by
    simp [List.getD_eq_getElem?_getD]
    cases m[t]? <;> simp
  rw [a,b,h]
theorem evalW_bit (cs : List Nat) {l m : List Nat} {i j : Nat}
    (h : l.map (fun x => x.testBit i) = m.map (fun x => x.testBit j)) :
    (evalW cs l).map (fun x => x.testBit i) = (evalW cs m).map (fun x => x.testBit j) := by
  induction cs generalizing l m with
  | nil => exact h
  | cons c cs ih =>
    apply ih
    simp only [List.map_append,List.map_cons,List.map_nil,h,opN_bit,getD_map_bit h]
theorem Xs_map (r : Row) : Xs.map (fun x => x.testBit (bt r)) = List.ofFn r := by
  apply List.ext_getElem
  · simp [Xs]
  intro t h1 h2
  have ht : t < 9 := by simpa using h2
  have := congrFun (obs_X ⟨t,ht⟩) r
  simp only [obs,xv,List.getD_eq_getElem?_getD] at this
  rw [List.getElem?_eq_getElem (by simpa [Xs] using ht),Option.getD_some] at this
  rw [List.getElem_map,List.getElem_ofFn]
  exact this
def Xp (p : List (Fin 9)) : List Nat := (List.finRange 9).map (fun i => Xs.getD (p.getD i.val 0).val 0)
theorem Xp_map (p : List (Fin 9)) (r : Row) :
    (Xp p).map (fun x => x.testBit (bt r)) = Xs.map (fun x => x.testBit (bt (perm p r))) := by
  rw [Xs_map]
  unfold Xp
  rw [List.map_map,List.ofFn_eq_map]
  congr 1
  funext i
  have := congrFun (obs_X (p.getD i.val 0)) r
  simpa [obs,xv,perm] using this
theorem evalW_perm (cs : List Nat) (p : List (Fin 9)) (t : Nat) :
    obs ((evalW cs (Xp p)).getD t 0) = obs ((evalW cs Xs).getD t 0) ∘ perm p := by
  funext r
  exact getD_map_bit (evalW_bit cs (Xp_map p r)) t

def dom (z o : Nat) : Nat :=
  (List.finRange 9).foldl (fun d i => if inS z i then d ^^^ (d &&& Xs.getD i.val 0) else if inS o i then d &&& Xs.getD i.val 0 else d) full512
theorem dom_bit (z o : Nat) (r : Row) : (dom z o).testBit (bt (fixR z o r)) = true := by
  unfold dom
  generalize List.finRange 9 = l
  have : ∀ d : Nat, d.testBit (bt (fixR z o r)) = true → (l.foldl (fun d i => if inS z i then d ^^^ (d &&& Xs.getD i.val 0) else if inS o i then d &&& Xs.getD i.val 0 else d) d).testBit (bt (fixR z o r)) = true := by
    induction l with
    | nil => intro d hd; exact hd
    | cons i l ih =>
      intro d hd
      apply ih
      have hx : (Xs.getD i.val 0).testBit (bt (fixR z o r)) = fixR z o r i := congrFun (obs_X i) (fixR z o r)
      cases hz : inS z i
      · cases ho : inS o i
        · simpa [hz,ho] using hd
        · simp only [hz,ho,Bool.false_eq_true,ite_false,ite_true,Nat.testBit_and,hd,hx,Bool.true_and]
          simp [fixR,hz,ho]
      · simp only [hz,ite_true,Nat.testBit_xor,Nat.testBit_and,hd,hx]
        simp [fixR,hz]
  exact this _ (full_bit _)
def Bset (f : Row → Row) (pool : List Nat) : Set Wire := {v | ∃ b ∈ pool, v = obs b ∘ f}
def cstN (d w : Nat) : Bool := let m := w &&& d; m == 0 || m == d
def avN (d : Nat) (pool : List Nat) (w : Nat) : Bool :=
  let m := w &&& d
  m == 0 || m == d || pool.contains m || pool.contains (m ^^^ d)
section
variable {f : Row → Row} {d : Nat} (hd : ∀ r, d.testBit (bt (f r)) = true)
include hd
theorem obs_mask (w : Nat) : obs (w &&& d) ∘ f = obs w ∘ f := by
  funext r; simp [obs,Nat.testBit_and,hd]
theorem cstN_sound {w} (h : cstN d w = true) : Cst (obs w ∘ f) := by
  rw [← obs_mask hd w]
  simp only [cstN,Bool.or_eq_true,beq_iff_eq] at h
  rcases h with h | h <;> rw [h]
  · exact ⟨false,by funext r; simp [obs]⟩
  · exact ⟨true,by funext r; simp [obs,hd]⟩
theorem avN_sound {pool w} (h : avN d pool w = true) : Av (Bset f pool) (obs w ∘ f) := by
  simp only [avN,Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem] at h
  rcases h with ((h | h) | h) | h
  · exact Or.inr (Or.inr (cstN_sound hd (by simp [cstN,h])))
  · exact Or.inr (Or.inr (cstN_sound hd (by simp [cstN,h])))
  · exact av_mem ⟨_,h,(obs_mask hd w).symm⟩
  · refine Or.inr (Or.inl ⟨_,h,?_⟩)
    funext r
    simp [obs,Nat.testBit_and,Nat.testBit_xor,hd]

def pay (d : Nat) (mask : Nat) : List Nat → Nat → List Nat → List Nat × Nat → List Nat × Nat
  | [],_,_,st => st
  | c::cs,i,b,st =>
    let x := b.getD (c/4 % 16) 0
    let y := b.getD (c/64) 0
    let z := opN (c % 4) x y
    pay d mask cs (i+1) (b ++ [z])
      (if mask.testBit i && avN d st.1 x && avN d st.1 y then ((z &&& d)::st.1,st.2+1) else st)
theorem pay_sound {mask cs i b st} {T : Wire} {j : Nat}
    (h : Comp j (Bset f (pay d mask cs i b st).1) T) :
    ∃ n, n + st.2 = j + (pay d mask cs i b st).2 ∧ Comp n (Bset f st.1) T := by
  induction cs generalizing i b st with
  | nil => exact ⟨j,rfl,h⟩
  | cons c cs ih =>
    simp only [pay] at h ⊢
    obtain ⟨n,hn,hc⟩ := ih h
    split at hc
    · rename_i hcond
      rw [ite_eq_left hcond] at hn ⊢
      simp only [Bool.and_eq_true] at hcond
      refine ⟨n+1,by simp only at hn; omega,?_⟩
      refine comp_gate (d:=c % 4) (Nat.mod_lt _ (by omega)) (avN_sound hd hcond.1.2) (avN_sound hd hcond.2) ?_
      refine comp_mono ?_ hc
      rintro v ⟨w,hw,rfl⟩
      rcases List.mem_cons.mp hw with rfl | hw
      · rw [obs_mask hd,obs_op]
        exact av_mem (Set.mem_insert _ _)
      · exact av_insert (av_mem ⟨w,hw,rfl⟩)
    · rename_i hcond
      rw [ite_eq_right hcond] at hn ⊢
      exact ⟨n,hn,hc⟩
end
def wset (ws : List Nat) : Finset Wire := (ws.map obs).toFinset
theorem ccount_list (f : Row → Row) {ws : List Nat} (nd : (ws.map obs).Nodup) (c : Nat → Bool)
    (hc : ∀ w, c w = true → Cst (obs w ∘ f)) : (ws.filter c).length ≤ ccount f (wset ws) := by
  classical
  have e : ((ws.filter c).map obs).toFinset ⊆ (wset ws).filter (fun s => Cst (s∘f)) := by
    intro v hv
    simp only [List.mem_toFinset,List.mem_map,List.mem_filter] at hv
    obtain ⟨w,⟨hw,hcw⟩,rfl⟩ := hv
    simp only [wset,Finset.mem_filter,List.mem_toFinset,List.mem_map]
    exact ⟨⟨w,hw,rfl⟩,hc w hcw⟩
  have nd2 : ((ws.filter c).map obs).Nodup := nd.sublist (List.Sublist.map _ List.filter_sublist)
  have := Finset.card_le_card e
  rw [List.toFinset_card_of_nodup nd2,List.length_map] at this
  exact this

def Imp (T : Wire) (k : Nat) (S : Finset Wire) : Prop := ∀ j, j ≤ k → ¬Live j S T

abbrev BP := Nat × Nat × Nat × List Nat
def BP.ok (m : Nat) (b : BP) : Prop := ∃ f : Row → Row, (∀ r, b.1.testBit (bt (f r)) = true) ∧ ¬Cst (gr m [] ∘ f) ∧
  ∀ j, Comp j (Bset f b.2.2.2) (gr m [] ∘ f) → b.2.1 ≤ j + b.2.2.1
def mkBP (cols : List Col) (ops : List Nat) (rule : Nat) : BP :=
  let c := cols.getD (rule % 64) (0,0,0,0,0)
  let d := dom c.1 c.2.1
  let st := pay d (rule/64) ops 0 Xs (Xs.map (fun x => x &&& d),0)
  (d,c.2.2.2.2,st.2,st.1)
theorem mkBP_ok {m cols ops rule} (h : ∀ c ∈ cols, Slice m c) (hr : rule % 64 < cols.length) : (mkBP cols ops rule).ok m := by
  set c := cols.getD (rule % 64) (0,0,0,0,0) with hc
  have sl : Slice m c := by
    apply h
    rw [hc,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hr]
    simp
  refine ⟨fixR c.1 c.2.1,dom_bit _ _,sl.2,?_⟩
  intro j hj
  obtain ⟨n,hn,hp⟩ := pay_sound (dom_bit c.1 c.2.1) hj
  have : Comp n Inp (gr m [] ∘ fixR c.1 c.2.1) := by
    refine comp_mono ?_ hp
    rintro v ⟨b,hb,rfl⟩
    simp only [List.mem_map] at hb
    obtain ⟨x,hx,rfl⟩ := hb
    rw [obs_mask (dom_bit _ _)]
    obtain ⟨t,ht,rfl⟩ := List.mem_iff_getElem.mp hx
    have e := obs_X ⟨t,by simpa [Xs] using ht⟩
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ht,Option.getD_some] at e
    rw [e]
    exact inp_fix _ _ _
  have := sl.1 n this
  have hn' : n + 0 = j + (mkBP cols ops rule).2.2.1 := hn
  have e : (mkBP cols ops rule).2.1 = c.2.2.2.2 := rfl
  rw [e]
  omega

def cutOK (k : Nat) (x y z : Nat) (kept : List Nat) (b : BP) : Bool :=
  let cc := ((z::kept).filter (cstN b.1)).length
  kept.all (avN b.1 b.2.2.2) &&
  ((decide (k + b.2.2.1 < b.2.1 + cc) && avN b.1 b.2.2.2 z) ||
   (decide (k + b.2.2.1 + 1 < b.2.1 + cc) && avN b.1 b.2.2.2 x && avN b.1 b.2.2.2 y))
theorem cutOK_sound {m k x y z d kept b} (hb : BP.ok m b) (hd4 : d<4) (hz : z = opN d x y)
    (nd : ((z::kept).map obs).Nodup) (h : cutOK k x y z kept b = true) : Imp (gr m []) k (wset (z::kept)) := by
  obtain ⟨f,hd,nc,hL⟩ := hb
  simp only [cutOK,Bool.and_eq_true,Bool.or_eq_true,List.all_eq_true,decide_eq_true_eq] at h
  obtain ⟨hk,h⟩ := h
  intro j hj hl
  have cnt := ccount_list f nd (cstN b.1) (fun w hw => cstN_sound hd hw)
  have mem : ∀ s ∈ wset (z::kept), s = obs z ∨ ∃ w ∈ kept, s = obs w := by
    intro s hs
    simp only [wset,List.mem_toFinset,List.mem_map,List.mem_cons] at hs
    obtain ⟨w,rfl | hw,rfl⟩ := hs
    · exact Or.inl rfl
    · exact Or.inr ⟨w,hw,rfl⟩
  rcases h with ⟨hlt,hav⟩ | ⟨⟨hlt,hx⟩,hy⟩
  · obtain ⟨n,hn,hc⟩ := elim (B:=Bset f b.2.2.2) f hl (by
      intro s hs
      rcases mem s hs with rfl | ⟨w,hw,rfl⟩
      · exact avN_sound hd hav
      · exact avN_sound hd (hk w hw)) nc
    have := hL n hc
    omega
  · obtain ⟨n,hn,hc⟩ := elim (B:=insert (wop d (obs x ∘ f) (obs y ∘ f)) (Bset f b.2.2.2)) f hl (by
      intro s hs
      rcases mem s hs with rfl | ⟨w,hw,rfl⟩
      · rw [hz,obs_op]; exact av_mem (Set.mem_insert _ _)
      · exact av_insert (avN_sound hd (hk w hw))) nc
    have := hL (n+1) (comp_gate hd4 (avN_sound hd hx) (avN_sound hd hy) hc)
    omega

def picks {α : Type} : List α → List (α × List α)
  | [] => []
  | x::xs => (x,xs) :: (picks xs).map (fun p => (p.1,x::p.2))
def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | x::xs => (picks xs).map (fun p => (x,p.1,p.2)) ++ (pairs xs).map (fun p => (p.1,p.2.1,x::p.2.2))
theorem picks_perm {α : Type} {l : List α} {p} (h : p ∈ picks l) : (p.1::p.2).Perm l := by
  induction l generalizing p with
  | nil => simp [picks] at h
  | cons x xs ih =>
    simp only [picks,List.mem_cons,List.mem_map] at h
    rcases h with rfl | ⟨q,hq,rfl⟩
    · exact List.Perm.refl _
    · exact (List.Perm.swap _ _ _).trans ((ih hq).cons x)
theorem picks_mem {α : Type} {l : List α} {a} (h : a ∈ l) : ∃ p ∈ picks l, p.1 = a := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [picks,List.mem_cons,List.mem_map]
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_,Or.inl rfl,rfl⟩
    · obtain ⟨p,hp,e⟩ := ih h
      exact ⟨_,Or.inr ⟨p,hp,rfl⟩,e⟩
theorem pairs_perm {α : Type} {l : List α} {p} (h : p ∈ pairs l) : (p.1::p.2.1::p.2.2).Perm l := by
  induction l generalizing p with
  | nil => simp [pairs] at h
  | cons x xs ih =>
    simp only [pairs,List.mem_append,List.mem_map] at h
    rcases h with ⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩
    · exact (picks_perm hq).cons x
    · refine List.Perm.trans ?_ ((ih hq).cons x)
      exact ((List.Perm.swap _ _ _).cons _).trans (List.Perm.swap _ _ _)
theorem pairs_mem {α : Type} {l : List α} {a b} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    ∃ p ∈ pairs l, (p.1 = a ∧ p.2.1 = b) ∨ (p.1 = b ∧ p.2.1 = a) := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [pairs,List.mem_append,List.mem_map]
    rcases List.mem_cons.mp ha with e1 | ha'
    · rcases List.mem_cons.mp hb with e2 | hb'
      · exact absurd (e1.trans e2.symm) hab
      · obtain ⟨p,hp,e⟩ := picks_mem hb'
        exact ⟨_,Or.inl ⟨p,hp,rfl⟩,Or.inl ⟨e1.symm,e⟩⟩
    · rcases List.mem_cons.mp hb with e2 | hb'
      · obtain ⟨p,hp,e⟩ := picks_mem ha'
        exact ⟨_,Or.inl ⟨p,hp,rfl⟩,Or.inr ⟨e2.symm,e⟩⟩
      · obtain ⟨p,hp,e⟩ := ih ha' hb'
        exact ⟨_,Or.inr ⟨p,hp,rfl⟩,e⟩

abbrev Node := List Nat × List Nat × List Nat × List Nat
abbrev Ent := Nat × Nat × Nat
def nodeWords (n : Node) (b : List Nat) : List Nat := n.2.1.map (fun l => (evalW n.1 b).getD l 0)
def nodeSet (n : Node) : Finset Wire := wset (nodeWords n Xs)
def sameL (a b : List Nat) : Bool := a.all (fun x => b.contains x) && b.all (fun x => a.contains x)
theorem sameL_sound {a b} (h : sameL a b = true) : wset a = wset b := by
  simp only [sameL,Bool.and_eq_true,List.all_eq_true,List.contains_iff_mem] at h
  ext v
  simp only [wset,List.mem_toFinset,List.mem_map]
  constructor
  · rintro ⟨w,hw,rfl⟩; exact ⟨w,h.1 w hw,rfl⟩
  · rintro ⟨w,hw,rfl⟩; exact ⟨w,h.2 w hw,rfl⟩
def invOK (p t : List (Fin 9)) : Bool := (List.finRange 9).all (fun i => t.getD (p.getD i.val 0).val 0 == i)
def autoOK (m : Nat) (p : List (Fin 9) × List (Fin 9)) : Bool := relOK m m p.1 && invOK p.1 p.2
theorem auto_imp {m p k S} (h : autoOK m p = true) (hi : Imp (gr m []) k S) :
    Imp (gr m []) k (S.image (fun v => v ∘ perm p.1)) := by
  simp only [autoOK,Bool.and_eq_true,invOK,List.all_eq_true,beq_iff_eq] at h
  obtain ⟨h1,h2⟩ := h
  have id1 : ∀ r, perm p.1 (perm p.2 r) = r := by
    intro r; funext i
    simp only [perm]
    rw [h2 i (List.mem_finRange i)]
  have onto : Function.Surjective (perm p.2) := by
    apply Finite.injective_iff_surjective.mp
    intro x y e
    have := congrArg (perm p.1) e
    rwa [id1,id1] at this
  have T2 : gr m [] ∘ perm p.2 = gr m [] := by
    have e := gr_perm h1
    conv_lhs => rw [← e]
    funext r
    simp only [Function.comp]
    rw [id1]
  intro j hj hl
  have := live_map hl (perm p.2) onto
  rw [T2,Finset.image_image] at this
  apply hi j hj
  have e : ((fun v : Wire => v ∘ perm p.2) ∘ fun v : Wire => v ∘ perm p.1) = id := by
    funext v r
    simp only [Function.comp,id]
    rw [id1]
  rwa [e,Finset.image_id] at this
theorem wset_perm (n : Node) (p : List (Fin 9)) :
    wset (nodeWords n (Xp p)) = (nodeSet n).image (fun v => v ∘ perm p) := by
  ext v
  simp only [nodeSet,wset,nodeWords,List.mem_toFinset,List.mem_map,Finset.mem_image]
  constructor
  · rintro ⟨w,⟨l,hl,rfl⟩,rfl⟩
    exact ⟨_,⟨_,⟨l,hl,rfl⟩,rfl⟩,(evalW_perm n.1 p l).symm⟩
  · rintro ⟨v,⟨w,⟨l,hl,rfl⟩,rfl⟩,rfl⟩
    exact ⟨_,⟨l,hl,rfl⟩,evalW_perm n.1 p l⟩

def rowOf (Ps : List Nat) (i : Nat) : Row := fun j => (Ps.getD j.val 0).testBit i
def Faith (Ps Ns : List Nat) (x : Ent) : Prop :=
  ∀ i, x.2.1.testBit i = obs x.1 (rowOf Ps i) ∧ x.2.2.testBit i = obs x.1 (rowOf Ns i)
def opE (d : Nat) (x y : Ent) : Ent := (opN d x.1 y.1,opN d x.2.1 y.2.1,opN d x.2.2 y.2.2)
theorem faith_op {Ps Ns d x y} (hx : Faith Ps Ns x) (hy : Faith Ps Ns y) : Faith Ps Ns (opE d x y) := by
  intro i
  have e := obs_op d x.1 y.1
  simp only [opE,opN_bit,e,wop,(hx i).1,(hx i).2,(hy i).1,(hy i).2,and_self]
theorem faith_bank {Ps : List Nat} (hl : Ps.length = 9) (cs : List Nat) (i t : Nat) :
    ((evalW cs Ps).getD t 0).testBit i = obs ((evalW cs Xs).getD t 0) (rowOf Ps i) := by
  refine getD_map_bit (evalW_bit cs ?_) t
  rw [Xs_map]
  apply List.ext_getElem
  · simp [hl]
  intro n h1 h2
  have hn : n < Ps.length := by simpa using h1
  rw [List.getElem_map,List.getElem_ofFn]
  simp only [rowOf,List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem hn,Option.getD_some]
def ents (n : Node) (Ps Ns : List Nat) : List Ent :=
  let w := evalW n.1 Xs
  let p := evalW n.1 Ps
  let q := evalW n.1 Ns
  n.2.1.map (fun l => (w.getD l 0,p.getD l 0,q.getD l 0))
theorem ents_words (n : Node) (Ps Ns) : (ents n Ps Ns).map Prod.fst = nodeWords n Xs := by
  simp [ents,nodeWords]
theorem ents_faith {n : Node} {Ps Ns : List Nat} (hp : Ps.length = 9) (hn : Ns.length = 9) :
    ∀ x ∈ ents n Ps Ns, Faith Ps Ns x := by
  intro x hx
  simp only [ents,List.mem_map] at hx
  obtain ⟨l,_,rfl⟩ := hx
  exact fun i => ⟨faith_bank hp _ i l,faith_bank hn _ i l⟩
def cov (l : List Ent) : Nat := l.foldr (fun x c => c ||| (x.2.1 ^^^ x.2.2)) 0
theorem cov_bit (l : List Ent) (i : Nat) (h : (cov l).testBit i = true) : ∃ x ∈ l, x.2.1.testBit i ≠ x.2.2.testBit i := by
  induction l with
  | nil => simp [cov] at h
  | cons x l ih =>
    simp only [cov,List.foldr_cons,Nat.testBit_or,Nat.testBit_xor,Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨y,hy,e⟩ := ih h
      exact ⟨y,List.mem_cons_of_mem _ hy,e⟩
    · exact ⟨x,by simp,by simpa using h⟩

def Sepr (m K : Nat) (Ps Ns : List Nat) : Prop := ∀ i, i < K → gr m [] (rowOf Ps i) ≠ gr m [] (rowOf Ns i)
def tgt (m : Nat) (b : List Nat) : Nat := (edgesOf m).foldl (fun t e => t ||| (b.getD e.1.val 0 &&& b.getD e.2.val 0)) 0
theorem tgt_bit (m : Nat) (b : List Nat) (i : Nat) : (tgt m b).testBit i = gr m [] (rowOf b i) := by
  unfold tgt gr
  simp only [List.any_nil,Bool.or_false]
  generalize edgesOf m = l
  have : ∀ t : Nat, (l.foldl (fun t e => t ||| (b.getD e.1.val 0 &&& b.getD e.2.val 0)) t).testBit i =
      (t.testBit i || l.any (fun e => rowOf b i e.1 && rowOf b i e.2)) := by
    induction l with
    | nil => intro t; simp
    | cons e l ih =>
      intro t
      rw [List.foldl_cons,ih,List.any_cons,Nat.testBit_or,Nat.testBit_and,Bool.or_assoc]
      rfl
  rw [this]; simp
def samplesOK (m K : Nat) (Ps Ns : List Nat) : Bool :=
  Ps.length == 9 && Ns.length == 9 && tgt m Ps ^^^ tgt m Ns == 2^K-1
theorem samples_sound {m K Ps Ns} (h : samplesOK m K Ps Ns = true) : Ps.length = 9 ∧ Ns.length = 9 ∧ Sepr m K Ps Ns := by
  simp only [samplesOK,Bool.and_eq_true,beq_iff_eq] at h
  refine ⟨h.1.1,h.1.2,fun i hi e => ?_⟩
  have := congrArg (fun x => x.testBit i) h.2
  simp only [Nat.testBit_xor,tgt_bit,e,Nat.testBit_two_pow_sub_one,Bool.xor_self] at this
  simp [hi] at this
theorem cover_sound {m K Ps Ns} {l : List Ent} (sp : Sepr m K Ps Ns) (hf : ∀ x ∈ l, Faith Ps Ns x)
    (hc : cov l ≠ 2^K-1) (hb : cov l < 2^K) (k : Nat) : Imp (gr m []) k (wset (l.map Prod.fst)) := by
  intro j _ hl
  apply hc
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_two_pow_sub_one]
  by_cases hi : i < K
  · obtain ⟨a,ha,hd⟩ := live_diff hl (sp i hi)
    simp only [wset,List.mem_toFinset,List.mem_map] at ha
    obtain ⟨w,⟨x,hx,rfl⟩,rfl⟩ := ha
    rw [← (hf x hx i).1,← (hf x hx i).2] at hd
    have : ∀ l : List Ent, x ∈ l → (cov l).testBit i = true := by
      intro l hl
      induction l with
      | nil => simp at hl
      | cons y l ih =>
        simp only [cov,List.foldr_cons,Nat.testBit_or,Nat.testBit_xor,Bool.or_eq_true]
        rcases List.mem_cons.mp hl with rfl | hl
        · right; simpa using hd
        · left; exact ih hl
    simp [this l hx,hi]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [hi]

abbrev Ctx := Nat × Nat × List BP × List (List Nat)
def childOK (c : Ctx) (k x y z : Nat) (cv : Nat) (kept : List Nat) : Bool :=
  decide (k < kept.length) || cv != c.1 || c.2.2.1.any (cutOK k x y z kept) || c.2.2.2.any (sameL (z::kept))
def keepL (ka kb : Bool) (x y : Ent) (l : List Ent) : List Ent :=
  (if ka then [x] else []) ++ (if kb then [y] else []) ++ l
def pairOK (c : Ctx) (k : Nat) (ws : List Nat) (p : Ent × Ent × List Ent) : Bool :=
  let x := p.1; let y := p.2.1; let l := p.2.2
  [0,1,2,3].all (fun d =>
    let z := opE d x y
    z.1 == 0 || ws.contains z.1 ||
    [false,true].all (fun ka => [false,true].all (fun kb =>
      childOK c k x.1 y.1 z.1 (cov (z :: keepL ka kb x y l)) ((keepL ka kb x y l).map Prod.fst))))
def small (w : Nat) : Bool := w < 2^512
def nodupN : List Nat → Bool
  | [] => true
  | x::xs => !(xs.contains x) && nodupN xs
theorem nodupN_ok {l} (h : nodupN l = true) : l.Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [nodupN,Bool.and_eq_true,Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨fun hm => ?_,ih h.2⟩
    rw [List.contains_iff_mem.mpr hm] at h
    simp at h
theorem obs_nodup {l : List Nat} (hs : ∀ w ∈ l, w < 2^512) (nd : l.Nodup) : (l.map obs).Nodup := by
  refine List.Nodup.map_on ?_ nd
  intro x hx y hy e
  exact obs_inj (hs x hx) (hs y hy) e
def linkWords (next : List Node) (autos : List (List (Fin 9) × List (Fin 9))) (e : Nat) : List Nat :=
  nodeWords (next.getD (e/16) ([],[],[],[])) (Xp (autos.getD (e % 16) ([],[])).1)
def linkOK (next : List Node) (autos : List (List (Fin 9) × List (Fin 9))) (e : Nat) : Bool :=
  decide (e/16 < next.length) && decide (e % 16 < autos.length)

abbrev Env := Nat × Nat × List Nat × List Nat × List Col × List (List (Fin 9) × List (Fin 9))
def Env.ok (g : Env) : Prop :=
  samplesOK g.1 g.2.1 g.2.2.1 g.2.2.2.1 = true ∧ (∀ c ∈ g.2.2.2.2.1, Slice g.1 c) ∧ ∀ p ∈ g.2.2.2.2.2, autoOK g.1 p = true
def nodeOK (g : Env) (next : List Node) (k : Nat) (n : Node) : Bool :=
  let es := ents n g.2.2.1 g.2.2.2.1
  let ws := es.map Prod.fst
  let full := 2^g.2.1-1
  decide (2 ≤ ws.length) && ws.all small && nodupN ws && es.all (fun e => decide (e.2.1 < 2^g.2.1) && decide (e.2.2 < 2^g.2.1)) &&
  n.2.2.1.all (fun r => decide (r % 64 < g.2.2.2.2.1.length)) && n.2.2.2.all (linkOK next g.2.2.2.2.2) &&
  (let c : Ctx := (full,0,n.2.2.1.map (mkBP g.2.2.2.2.1 n.1),n.2.2.2.map (linkWords next g.2.2.2.2.2))
   (pairs es).all (pairOK c k ws))
theorem cov_lt {K : Nat} {l : List Ent} (h : ∀ e ∈ l, e.2.1 < 2^K ∧ e.2.2 < 2^K) : cov l < 2^K := by
  induction l with
  | nil => simp [cov]
  | cons x l ih =>
    simp only [cov,List.foldr_cons]
    exact Nat.or_lt_two_pow (ih (fun e he => h e (List.mem_cons_of_mem _ he))) (Nat.xor_lt_two_pow (h x (by simp)).1 (h x (by simp)).2)
theorem opE_lt {K d : Nat} {x y : Ent} (hx : x.2.1 < 2^K ∧ x.2.2 < 2^K) (hy : y.2.1 < 2^K ∧ y.2.2 < 2^K) :
    (opE d x y).2.1 < 2^K ∧ (opE d x y).2.2 < 2^K := ⟨opN_lt hx.1 hy.1,opN_lt hx.2 hy.2⟩
theorem childOK_sound {g : Env} {next : List Node} {k : Nat} {n : Node} {d : Nat} {x y : Ent} {l : List Ent} (hd : d<4)
    (hg : g.ok) (hnext : ∀ q ∈ next, Imp (gr g.1 []) k (nodeSet q))
    (hr : ∀ r ∈ n.2.2.1, r % 64 < g.2.2.2.2.1.length) (hk : ∀ e ∈ n.2.2.2, linkOK next g.2.2.2.2.2 e = true)
    (hf : ∀ e ∈ opE d x y :: l, Faith g.2.2.1 g.2.2.2.1 e)
    (hb : ∀ e ∈ opE d x y :: l, e.2.1 < 2^g.2.1 ∧ e.2.2 < 2^g.2.1)
    (nd : (((opE d x y :: l).map Prod.fst).map obs).Nodup)
    (h : childOK (2^g.2.1-1,0,n.2.2.1.map (mkBP g.2.2.2.2.1 n.1),n.2.2.2.map (linkWords next g.2.2.2.2.2)) k x.1 y.1
      (opE d x y).1 (cov (opE d x y :: l)) (l.map Prod.fst) = true) :
    Imp (gr g.1 []) k (wset ((opE d x y :: l).map Prod.fst)) := by
  obtain ⟨hs,hcol,haut⟩ := hg
  simp only [childOK,Bool.or_eq_true,decide_eq_true_eq,bne_iff_ne,List.any_map,List.any_eq_true,Function.comp] at h
  rcases h with ((h | h) | ⟨r,hrm,h⟩) | ⟨e,hem,h⟩
  · intro j hj hl
    have := live_card hl
    rw [wset,List.toFinset_card_of_nodup nd] at this
    simp only [List.map_cons,List.length_cons,List.length_map] at this h
    omega
  · exact cover_sound (samples_sound hs).2.2 hf h (cov_lt hb) k
  · exact cutOK_sound (mkBP_ok hcol (hr r hrm)) hd rfl (by simpa using nd) h
  · have hlk := hk e hem
    simp only [linkOK,Bool.and_eq_true,decide_eq_true_eq] at hlk
    rw [List.map_cons,sameL_sound h]
    unfold linkWords
    rw [wset_perm]
    apply auto_imp
    · apply haut
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hlk.2]
      simp
    · apply hnext
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hlk.1]
      simp

theorem node_sound {g : Env} {next : List Node} {k : Nat} {n : Node} (hg : g.ok)
    (hnext : ∀ q ∈ next, Imp (gr g.1 []) k (nodeSet q)) (h : nodeOK g next k n = true) :
    Imp (gr g.1 []) (k+1) (nodeSet n) := by
  have hsam := samples_sound hg.1
  simp only [nodeOK,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h2,hsm⟩,hnd⟩,hbd⟩,hr⟩,hk⟩,hp⟩ := h
  set es := ents n g.2.2.1 g.2.2.2.1 with hes
  have hw : es.map Prod.fst = nodeWords n Xs := ents_words n _ _
  have hfa : ∀ x ∈ es, Faith g.2.2.1 g.2.2.2.1 x := ents_faith hsam.1 hsam.2.1
  have hsm' : ∀ w ∈ es.map Prod.fst, w < 2^512 := fun w hw => by simpa [small] using hsm w hw
  have ndw := nodupN_ok hnd
  have ndo := obs_nodup hsm' ndw
  have hS : nodeSet n = wset (es.map Prod.fst) := by rw [nodeSet,hw]
  intro j hj hl
  rw [hS] at hl
  cases j with
  | zero =>
    have : wset (es.map Prod.fst) = {gr g.1 []} := hl
    have c := congrArg Finset.card this
    rw [wset,List.toFinset_card_of_nodup ndo,List.length_map,Finset.card_singleton] at c
    omega
  | succ j =>
    obtain ⟨U,a,b,d,hSU,hab,hd,hfresh,hzne,hl⟩ := hl
    have ent : ∀ v ∈ wset (es.map Prod.fst), ∃ e ∈ es, obs e.1 = v := by
      intro v hv
      simp only [wset,List.mem_toFinset,List.mem_map] at hv
      obtain ⟨w,⟨e,he,rfl⟩,rfl⟩ := hv
      exact ⟨e,he,rfl⟩
    obtain ⟨ea,hea,ra⟩ := ent a (by rw [hSU]; simp)
    obtain ⟨eb,heb,rb⟩ := ent b (by rw [hSU]; simp)
    obtain ⟨p,hpm,horder⟩ := pairs_mem hea heb (fun e => hab (by rw [← ra,← rb,e]))
    have key : ∃ dd, dd < 4 ∧ obs (opE dd p.1 p.2.1).1 = wop d a b ∧
        wset (es.map Prod.fst) = insert (obs p.1.1) (insert (obs p.2.1.1) U) := by
      rcases horder with ⟨e1,e2⟩ | ⟨e1,e2⟩
      · exact ⟨d,hd,by rw [e1,e2,opE,obs_op,ra,rb],by rw [e1,e2,ra,rb,hSU]⟩
      · refine ⟨swapOp d,swap_lt hd,by rw [e1,e2,opE,obs_op,ra,rb,← wop_swap hd],?_⟩
        rw [e1,e2,ra,rb,hSU,Finset.insert_comm]
    obtain ⟨dd,hdd,hz,hSp⟩ := key
    obtain ⟨x,y,l⟩ := p
    simp only at hz hSp
    have pm : (x::y::l).Perm es := pairs_perm hpm
    have hpair := hp _ hpm
    simp only [pairOK,List.all_eq_true] at hpair
    have hq := hpair dd (by interval_cases dd <;> simp)
    simp only [Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem] at hq
    rw [← hz] at hfresh hzne hl
    have znot : (opE dd x y).1 ∉ es.map Prod.fst := by
      intro hm
      exact hfresh (by simp only [wset,List.mem_toFinset]; exact List.mem_map_of_mem hm)
    have hq1 := hq.resolve_left (by
      rintro (h0 | hm)
      · apply hzne
        rw [h0]; funext r; simp [obs,ff]
      · exact znot hm)
    have bm : ∀ t : Bool, t ∈ [false,true] := by decide
    have hq2 := List.all_eq_true.mp (List.all_eq_true.mp hq1 (decide (obs x.1 ∈ U)) (bm _)) (decide (obs y.1 ∈ U)) (bm _)
    set kl := keepL (decide (obs x.1 ∈ U)) (decide (obs y.1 ∈ U)) x y l with hkl
    have sub : kl.Sublist (x::y::l) := by
      rw [hkl,keepL]
      have s1 : (if decide (obs x.1 ∈ U) = true then [x] else []).Sublist [x] := by split <;> simp
      have s2 : (if decide (obs y.1 ∈ U) = true then [y] else []).Sublist [y] := by split <;> simp
      exact (s1.append s2).append (List.Sublist.refl l)
    have mes : ∀ e ∈ kl, e ∈ es := fun e he => pm.subset (sub.subset he)
    have hxe : x ∈ es := pm.subset (by simp)
    have hye : y ∈ es := pm.subset (by simp)
    have ndx : ((x::y::l).map Prod.fst).Nodup := (pm.map Prod.fst).nodup_iff.mpr ndw
    have ndxo : (((x::y::l).map Prod.fst).map obs).Nodup := ((pm.map Prod.fst).map obs).nodup_iff.mpr ndo
    have zsm : (opE dd x y).1 < 2^512 := opN_lt (hsm' _ (List.mem_map_of_mem hxe)) (hsm' _ (List.mem_map_of_mem hye))
    have ndc : (((opE dd x y :: kl).map Prod.fst).map obs).Nodup := by
      apply obs_nodup
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact zsm
        · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hw
          exact hsm' _ (List.mem_map_of_mem (mes e he))
      · rw [List.map_cons,List.nodup_cons]
        refine ⟨?_,ndx.sublist (sub.map _)⟩
        intro hm
        obtain ⟨e,he,e2⟩ := List.mem_map.mp hm
        exact znot (e2 ▸ List.mem_map_of_mem (mes e he))
    have hc := childOK_sound (d:=dd) hdd hg hnext hr hk (by
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact faith_op (hfa x hxe) (hfa y hye)
        · exact hfa e (mes e he)) (by
        intro e he
        have b : ∀ e ∈ es, e.2.1 < 2^g.2.1 ∧ e.2.2 < 2^g.2.1 := hbd
        rcases List.mem_cons.mp he with rfl | he
        · exact opE_lt (b x hxe) (b y hye)
        · exact b e (mes e he)) ndc hq2
    apply hc j (by omega)
    have es2 : insert (obs (opE dd x y).1) U = wset ((opE dd x y :: kl).map Prod.fst) := by
      have mk : ∀ v, v ∈ wset (kl.map Prod.fst) ↔ v ∈ U := by
        have inl : ∀ v, v ∈ U → v = obs x.1 ∨ v = obs y.1 ∨ ∃ e ∈ l, v = obs e.1 := by
          intro v hv
          have : v ∈ wset (es.map Prod.fst) := by rw [hSp]; simp [hv]
          obtain ⟨e,he,rfl⟩ := ent v this
          have := pm.symm.subset he
          simp only [List.mem_cons] at this
          rcases this with rfl | rfl | h
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr ⟨e,h,rfl⟩)
        have lin : ∀ e ∈ l, obs e.1 ∈ U := by
          intro e he
          have hm : obs e.1 ∈ wset (es.map Prod.fst) := by
            simp only [wset,List.mem_toFinset,List.mem_map]
            exact ⟨e.1,⟨e,pm.subset (by simp [he]),rfl⟩,rfl⟩
          rw [hSp] at hm
          simp only [List.map_cons,List.nodup_cons,List.mem_cons,List.mem_map,not_or] at ndxo
          rcases Finset.mem_insert.mp hm with h | hm
          · exact absurd ⟨e.1,⟨e,he,rfl⟩,h⟩ ndxo.1.2
          rcases Finset.mem_insert.mp hm with h | hm
          · exact absurd ⟨e.1,⟨e,he,rfl⟩,h⟩ ndxo.2.1
          · exact hm
        intro v
        simp only [wset,List.mem_toFinset,List.mem_map]
        constructor
        · rintro ⟨w,⟨e,he,rfl⟩,rfl⟩
          rw [hkl,keepL] at he
          simp only [List.mem_append] at he
          rcases he with (he | he) | he
          · by_cases hu : obs x.1 ∈ U
            · simp only [hu,decide_true,ite_true,List.mem_singleton] at he
              rw [he]; exact hu
            · simp [hu] at he
          · by_cases hu : obs y.1 ∈ U
            · simp only [hu,decide_true,ite_true,List.mem_singleton] at he
              rw [he]; exact hu
            · simp [hu] at he
          · exact lin e he
        · intro hv
          rcases inl v hv with rfl | rfl | ⟨e,he,rfl⟩
          · exact ⟨x.1,⟨x,by rw [hkl,keepL]; simp [hv],rfl⟩,rfl⟩
          · exact ⟨y.1,⟨y,by rw [hkl,keepL]; simp [hv],rfl⟩,rfl⟩
          · exact ⟨e.1,⟨e,by rw [hkl,keepL]; simp [he],rfl⟩,rfl⟩
      ext v
      rw [List.map_cons]
      have : wset ((opE dd x y).1 :: kl.map Prod.fst) = insert (obs (opE dd x y).1) (wset (kl.map Prod.fst)) := by
        simp [wset]
      rw [this,Finset.mem_insert,Finset.mem_insert,mk]
    rw [← es2]; exact hl

theorem level_sound {g : Env} {next : List Node} {k : Nat} {l : List Node} (hg : g.ok)
    (hnext : ∀ q ∈ next, Imp (gr g.1 []) k (nodeSet q)) (h : l.all (nodeOK g next k) = true) :
    ∀ q ∈ l, Imp (gr g.1 []) (k+1) (nodeSet q) :=
  fun q hq => node_sound hg hnext (List.all_eq_true.mp h q hq)

def rootSet (m : Nat) : Finset Wire := (Finset.univ.filter (fun i : Fin 9 => inS m i = true)).image xv
def noIso (m : Nat) : Bool := (List.finRange 9).all (fun i => !(inS m i) || (edgesOf m).any (fun e => e.1 == i || e.2 == i))
theorem edges_ne : ∀ e ∈ edges, e.1 ≠ e.2 := by decide
theorem colEq_out (m : Nat) : gr m [] ∘ fixR (511 ^^^ m) 0 = gr m [] := by
  have h0 : ∀ t, inS 0 t = false := by decide
  have h5 : ∀ t : Fin 9, Nat.testBit 511 t.val = true := by decide
  funext r
  simp only [Function.comp,gr,List.any_nil,Bool.or_false]
  rw [Bool.eq_iff_iff,List.any_eq_true,List.any_eq_true]
  have key : ∀ t, inS m t = true → fixR (511 ^^^ m) 0 r t = r t := by
    intro t ht
    have : inS (511 ^^^ m) t = false := by simp only [inS] at ht ⊢; simp [Nat.testBit_xor,h5,ht]
    simp [fixR,this,h0]
  constructor
  · rintro ⟨e,he,hh⟩
    obtain ⟨-,h1,h2⟩ := mem_edgesOf.mp he
    exact ⟨e,he,by rwa [key _ h1,key _ h2] at hh⟩
  · rintro ⟨e,he,hh⟩
    obtain ⟨-,h1,h2⟩ := mem_edgesOf.mp he
    exact ⟨e,he,by rwa [key _ h1,key _ h2]⟩
theorem root_lower {m L : Nat} (hm : nonempty m [] = true) (hi : noIso m = true) (h : Imp (gr m []) L (rootSet m)) :
    Lower (gr m []) (L+1) := by
  intro j hj
  by_contra hlt
  have hc := comp_map (fixR (511 ^^^ m) 0) hj
  rw [colEq_out] at hc
  have hc2 : Comp j {w | ∃ i, inS m i = true ∧ w = xv i} (gr m []) := by
    refine comp_mono ?_ hc
    rintro _ ⟨_,⟨i,rfl⟩,rfl⟩
    have h5 : ∀ t : Fin 9, Nat.testBit 511 t.val = true := by decide
    have h0 : ∀ t, inS 0 t = false := by decide
    cases hb : inS m i
    · have : inS (511 ^^^ m) i = true := by simp only [inS] at hb ⊢; simp [Nat.testBit_xor,h5,hb]
      have e : (xv i ∘ fixR (511 ^^^ m) 0) = fun _ => false := by funext r; simp [xv,fixR,this]
      exact Or.inr (Or.inr ⟨false,e⟩)
    · have : inS (511 ^^^ m) i = false := by simp only [inS] at hb ⊢; simp [Nat.testBit_xor,h5,hb]
      have e : (xv i ∘ fixR (511 ^^^ m) 0) = xv i := by funext r; simp [xv,fixR,this,h0]
      exact Or.inl ⟨i,hb,e⟩
  obtain ⟨k,S,hk,hl,hs⟩ := extract hc2 ⟨gr_zero _ _,gr_ne hm⟩
  apply h k (by omega)
  have e : S = rootSet m := by
    ext v
    simp only [rootSet,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro hv
      obtain ⟨i,hi,rfl⟩ := av_inp_norm _ (hs v hv).1 (hs v hv).2
      exact ⟨i,hi,rfl⟩
    · rintro ⟨i,hb,rfl⟩
      simp only [noIso,List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true',List.any_eq_true,beq_iff_eq] at hi
      obtain ⟨⟨u,w⟩,he,hor⟩ := (hi i (List.mem_finRange i)).resolve_left (by simp [hb])
      have huw : u ≠ w := edges_ne _ (mem_edgesOf.mp he).1
      have main : ∀ o : Fin 9, i ≠ o → gr m [] (fun t => t == i || t == o) = true → xv i ∈ S := by
        intro o hio ht
        have hz : gr m [] (fun t => t == o) = false := by
          simp only [gr,List.any_nil,Bool.or_false,List.any_eq_false,Bool.and_eq_true,beq_iff_eq]
          rintro e he ⟨e1,e2⟩
          exact edges_ne _ (mem_edgesOf.mp he).1 (e1.trans e2.symm)
        obtain ⟨a,ha,hd⟩ := live_diff hl (show gr m [] (fun t => t == i || t == o) ≠ gr m [] (fun t => t == o) by rw [ht,hz]; simp)
        obtain ⟨t,-,rfl⟩ := av_inp_norm _ (hs a ha).1 (hs a ha).2
        have : t = i := by
          by_contra hne
          simp [xv,hne] at hd
        exact this ▸ ha
      rcases hor with h | h
      · simp only at h
        subst h
        refine main w huw ?_
        simp only [gr,List.any_nil,Bool.or_false,List.any_eq_true]
        exact ⟨_,he,by simp⟩
      · simp only at h
        subst h
        refine main u huw.symm ?_
        simp only [gr,List.any_nil,Bool.or_false,List.any_eq_true]
        exact ⟨_,he,by simp⟩
  rw [← e]; exact hl
def rootNode (m : Nat) : Node := ([],((List.finRange 9).filter (inS m)).map Fin.val,[],[])
theorem root_node (n : Node) (m : Nat) (h1 : n.1 = []) (h2 : n.2.1 = ((List.finRange 9).filter (inS m)).map Fin.val) :
    nodeSet n = rootSet m := by
  ext v
  simp only [nodeSet,nodeWords,h1,h2,evalW,wset,rootSet,List.mem_toFinset,List.mem_map,List.mem_filter,List.mem_finRange,true_and,
    Finset.mem_image,Finset.mem_filter,Finset.mem_univ]
  constructor
  · rintro ⟨w,⟨l,⟨i,hi,rfl⟩,rfl⟩,rfl⟩
    exact ⟨i,hi,(obs_X i).symm⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨_,⟨i.val,⟨i,hi,rfl⟩,rfl⟩,obs_X i⟩

def rootCutOK (m L : Nat) (c : Col) : Bool :=
  decide (L < c.2.2.2.2 + ((List.finRange 9).filter (fun i => inS m i && (inS c.1 i || inS c.2.1 i))).length)
theorem root_cut {m L c} (hc : Slice m c) (h : rootCutOK m L c = true) : Imp (gr m []) L (rootSet m) := by
  intro j hj hl
  simp only [rootCutOK,decide_eq_true_eq] at h
  obtain ⟨n,hn,hcomp⟩ := elim (B:=Inp) (fixR c.1 c.2.1) hl (by
    intro s hs
    simp only [rootSet,Finset.mem_image] at hs
    obtain ⟨i,-,rfl⟩ := hs
    exact inp_fix _ _ i) hc.2
  have := hc.1 n hcomp
  have cnt : ((List.finRange 9).filter (fun i => inS m i && (inS c.1 i || inS c.2.1 i))).length ≤ ccount (fixR c.1 c.2.1) (rootSet m) := by
    classical
    have nd : ((List.finRange 9).filter (fun i => inS m i && (inS c.1 i || inS c.2.1 i))).Nodup := (List.nodup_finRange 9).filter _
    have inj : Function.Injective xv := by
      intro a b e
      have := congrFun e (fun t => t == a)
      simp only [xv,beq_self_eq_true] at this
      exact (beq_iff_eq.mp this.symm).symm
    rw [← List.toFinset_card_of_nodup nd,← Finset.card_image_of_injective _ inj]
    apply Finset.card_le_card
    intro v hv
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_filter,Bool.and_eq_true,Bool.or_eq_true] at hv
    obtain ⟨i,⟨-,hi,hzo⟩,rfl⟩ := hv
    simp only [Finset.mem_filter,rootSet,Finset.mem_image,Finset.mem_univ,true_and]
    refine ⟨⟨i,hi,rfl⟩,?_⟩
    cases hz : inS c.1 i
    · have ho := hzo.resolve_left (by simp [hz])
      exact ⟨true,by funext r; simp [xv,fixR,hz,ho]⟩
    · exact ⟨false,by funext r; simp [xv,fixR,hz]⟩
  omega
theorem step_cut {K : List (Nat × Nat)} {m L : Nat} (c : Col) (maps : List (Nat × List (Fin 9))) (hK : Known K)
    (h : (colOK K m c && rootCutOK m L c && nonempty m [] && noIso m && maps.all (fun e => relOK e.1 m e.2)) = true) :
    Known (extend K (L+1) maps) := by
  simp only [Bool.and_eq_true] at h
  exact extend_ok hK (root_lower h.1.1.2 h.1.2 (root_cut (col_sound hK h.1.1.1.1) h.1.1.1.2)) h.2
def envOK (K : List (Nat × Nat)) (g : Env) : Bool :=
  samplesOK g.1 g.2.1 g.2.2.1 g.2.2.2.1 && g.2.2.2.2.1.all (colOK K g.1) && g.2.2.2.2.2.all (autoOK g.1)
theorem env_ok {K g} (hK : Known K) (h : envOK K g = true) : g.ok := by
  simp only [envOK,Bool.and_eq_true,List.all_eq_true] at h
  exact ⟨h.1.1,fun c hc => col_sound hK (h.1.2 c hc),h.2⟩
theorem step_forest {K : List (Nat × Nat)} {g : Env} {L : Nat} (maps : List (Nat × List (Fin 9))) (hK : Known K) (n : Node) (l : List Node)
    (hl : ∀ q ∈ l, Imp (gr g.1 []) L (nodeSet q)) (hn : n ∈ l)
    (h1 : n.1 = []) (h2 : n.2.1 = ((List.finRange 9).filter (inS g.1)).map Fin.val)
    (h : (nonempty g.1 [] && noIso g.1 && maps.all (fun e => relOK e.1 g.1 e.2)) = true) :
    Known (extend K (L+1) maps) := by
  simp only [Bool.and_eq_true] at h
  exact extend_ok hK (root_lower h.1.1 h.1.2 (root_node n g.1 h1 h2 ▸ hl n hn)) h.2
theorem known_base : Known [] := by intro e he; simp at he
theorem append_imp {T k} {a b : List Node} (ha : ∀ q ∈ a, Imp T k (nodeSet q)) (hb : ∀ q ∈ b, Imp T k (nodeSet q)) :
    ∀ q ∈ a ++ b, Imp T k (nodeSet q) := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact ha q h
  · exact hb q h
theorem nil_imp {T k} : ∀ q ∈ ([] : List Node), Imp T k (nodeSet q) := by intro q hq; simp at hq

theorem comp_neg {k} {B : Set Wire} {T : Wire} (h : Comp k B T) : Comp k B (fun r => !T r) := by
  induction k generalizing B with
  | zero => exact av_not h
  | succ k ih =>
    obtain ⟨a,b,ha,hb,hc⟩ := h
    exact ⟨a,b,ha,hb,ih hc⟩
def AndOp (g : BinaryGate) : Prop := ∃ p q : Bool, g.op = fun x y => x == p && y == q
def memS (w : List Wire) : Set Wire := {v | v ∈ w}
theorem av_lit (w : List Wire) (i : Nat) (p : Bool) : Av (memS w) (fun r => (w.map (fun v => v r)).getD i false == p) := by
  have base : Av (memS w) (fun r => (w.map (fun v => v r)).getD i false) := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases h : w[i]? with
    | none => exact av_cst false
    | some v => exact av_mem (List.mem_of_getElem? h)
  cases p
  · have e : (fun r => (w.map (fun v => v r)).getD i false == false) = fun r => !((w.map (fun v => v r)).getD i false) := by
      funext r; cases (w.map (fun v => v r)).getD i false <;> rfl
    rw [e]; exact av_not base
  · have e : (fun r => (w.map (fun v => v r)).getD i false == true) = fun r => ((w.map (fun v => v r)).getD i false) := by
      funext r; cases (w.map (fun v => v r)).getD i false <;> rfl
    rw [e]; exact base
theorem comp_gates (gs : List BinaryGate) (hg : ∀ g ∈ gs, AndOp g) (o : Nat) (w : List Wire) :
    Comp gs.length (memS w) (fun r => ((gs.foldl (fun l g => l ++ [g.op (l.getD g.left false) (l.getD g.right false)])
      (w.map (fun v => v r))).getD o false)) := by
  induction gs generalizing w with
  | nil =>
    have := av_lit w o true
    change Av (memS w) _
    simpa using this
  | cons g gs ih =>
    obtain ⟨p,q,hop⟩ := hg g (by simp)
    refine ⟨_,_,av_lit w g.left p,av_lit w g.right q,?_⟩
    have := ih (fun g hm => hg g (by simp [hm])) (w ++ [fun r => ((w.map (fun v => v r)).getD g.left false == p) && ((w.map (fun v => v r)).getD g.right false == q)])
    refine comp_mono ?_ (B:=memS (w ++ [fun r => ((w.map (fun v => v r)).getD g.left false == p) && ((w.map (fun v => v r)).getD g.right false == q)])) ?_
    · intro v hv
      rcases List.mem_append.mp hv with h | h
      · exact av_mem (Set.mem_insert_of_mem _ h)
      · rw [List.mem_singleton.mp h]; exact av_mem (Set.mem_insert _ _)
    · convert this using 2 with r
      simp only [List.foldl_cons,List.map_append,List.map_cons,List.map_nil,hop]
def known0 : List (Nat × Nat) := []
theorem kok0 : Known known0 := known_base
def env15 : Env := (15,21,[0x47473,0x97a7f,0x1f8f9c,0x168de0,0x0,0x0,0x0,0x0,0x0],[0x173652,0x8c829,0x21714,0x1de8e0,0x0,0x0,0x0,0x0,0x0],[],[([0,1,2,3,4,5,6,7,8],[0,1,2,3,4,5,6,7,8]),([3,2,1,0,4,5,6,7,8],[3,2,1,0,4,5,6,7,8])])
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem eok15 : env15.ok := env_ok kok0 (by decide +kernel)
def n15_3_0 : List Node := [([],[0,1,2,3],[],[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn15_3_0 : ∀ q ∈ n15_3_0, Imp (gr env15.1 []) 3 (nodeSet q) :=
  level_sound (g:=env15) (next:=([] : List Node)) eok15 nil_imp (by decide +kernel)
def lv15_3 : List Node := n15_3_0
theorem plv15_3 : ∀ q ∈ lv15_3, Imp (gr env15.1 []) 3 (nodeSet q) := pn15_3_0
def known15 := extend known0 4 [(15,[0,1,2,3,4,5,6,7,8]),(23,[1,2,3,4,0,5,6,7,8]),(27,[1,0,4,3,2,5,6,7,8]),(29,[0,4,3,2,1,5,6,7,8]),(30,[4,0,1,2,3,5,6,7,8]),(39,[1,2,3,4,5,0,6,7,8]),(57,[1,4,5,3,2,0,6,7,8]),(78,[4,1,2,3,5,6,0,7,8]),(99,[1,2,4,5,6,0,3,7,8]),(135,[0,1,2,4,5,6,7,3,8]),(156,[4,5,1,2,3,6,7,0,8]),(163,[1,0,4,5,6,2,7,3,8]),(165,[0,4,3,5,6,1,7,2,8]),(166,[4,0,1,5,6,3,7,2,8]),(172,[4,5,1,0,6,3,7,2,8]),(177,[1,4,5,6,0,2,7,3,8])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem kok15 : Known known15 := step_forest (g:=env15) (L:=3) [(15,[0,1,2,3,4,5,6,7,8]),(23,[1,2,3,4,0,5,6,7,8]),(27,[1,0,4,3,2,5,6,7,8]),(29,[0,4,3,2,1,5,6,7,8]),(30,[4,0,1,2,3,5,6,7,8]),(39,[1,2,3,4,5,0,6,7,8]),(57,[1,4,5,3,2,0,6,7,8]),(78,[4,1,2,3,5,6,0,7,8]),(99,[1,2,4,5,6,0,3,7,8]),(135,[0,1,2,4,5,6,7,3,8]),(156,[4,5,1,2,3,6,7,0,8]),(163,[1,0,4,5,6,2,7,3,8]),(165,[0,4,3,5,6,1,7,2,8]),(166,[4,0,1,5,6,3,7,2,8]),(172,[4,5,1,0,6,3,7,2,8]),(177,[1,4,5,6,0,2,7,3,8])] kok0 (n15_3_0.headD ([],[],[],[])) lv15_3 plv15_3 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def env31 : Env := (31,50,[0x115d16630b273,0x290c286464e7f,0x18c06d986cd9c,0x27e6c59e90980,0x3ebbb2079b000,0x0,0x0,0x0,0x0],[0x11525c6a12412,0x2c2d009524869,0x1290662058794,0x2166995b04820,0xe892284e92c0,0x0,0x0,0x0,0x0],[(1,0,30,0,4),(2,0,29,0,4),(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)],[([0,1,2,3,4,5,6,7,8],[0,1,2,3,4,5,6,7,8]),([0,4,3,2,1,5,6,7,8],[0,4,3,2,1,5,6,7,8]),([1,0,4,3,2,5,6,7,8],[1,0,4,3,2,5,6,7,8]),([1,2,3,4,0,5,6,7,8],[4,0,1,2,3,5,6,7,8]),([2,1,0,4,3,5,6,7,8],[2,1,0,4,3,5,6,7,8]),([2,3,4,0,1,5,6,7,8],[3,4,0,1,2,5,6,7,8]),([3,2,1,0,4,5,6,7,8],[3,2,1,0,4,5,6,7,8]),([3,4,0,1,2,5,6,7,8],[2,3,4,0,1,5,6,7,8]),([4,0,1,2,3,5,6,7,8],[1,2,3,4,0,5,6,7,8]),([4,3,2,1,0,5,6,7,8],[4,3,2,1,0,5,6,7,8])])
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem eok31 : env31.ok := env_ok kok15 (by decide +kernel)
def n31_4_0 : List Node := [([129,583],[0,2,3,4,10],[],[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn31_4_0 : ∀ q ∈ n31_4_0, Imp (gr env31.1 []) 4 (nodeSet q) :=
  level_sound (g:=env31) (next:=([] : List Node)) eok31 nil_imp (by decide +kernel)
def lv31_4 : List Node := n31_4_0
theorem plv31_4 : ∀ q ∈ lv31_4, Imp (gr env31.1 []) 4 (nodeSet q) := pn31_4_0
def n31_5_0 : List Node := [([65],[0,1,2,3,4,9],[],[]),
 ([129],[0,1,2,3,4,9],[1],[0])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn31_5_0 : ∀ q ∈ n31_5_0, Imp (gr env31.1 []) 5 (nodeSet q) :=
  level_sound (g:=env31) (next:=lv31_4) eok31 plv31_4 (by decide +kernel)
def lv31_5 : List Node := n31_5_0
theorem plv31_5 : ∀ q ∈ lv31_5, Imp (gr env31.1 []) 5 (nodeSet q) := pn31_5_0
def n31_6_0 : List Node := [([],[0,1,2,3,4],[0,4,3,2,1],[0,1,3,5,7,16,17,18,19,21])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn31_6_0 : ∀ q ∈ n31_6_0, Imp (gr env31.1 []) 6 (nodeSet q) :=
  level_sound (g:=env31) (next:=lv31_5) eok31 plv31_5 (by decide +kernel)
def lv31_6 : List Node := n31_6_0
theorem plv31_6 : ∀ q ∈ lv31_6, Imp (gr env31.1 []) 6 (nodeSet q) := pn31_6_0
def known31 := extend known15 7 [(31,[0,1,2,3,4,5,6,7,8]),(167,[0,1,2,5,6,4,7,3,8])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem kok31 : Known known31 := step_forest (g:=env31) (L:=6) [(31,[0,1,2,3,4,5,6,7,8]),(167,[0,1,2,5,6,4,7,3,8])] kok15 (n31_6_0.headD ([],[],[],[])) lv31_6 plv31_6 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def known55 := extend known31 5 [(55,[0,1,2,3,4,5,6,7,8])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem kok55 : Known known55 := step_cut (m:=55) (L:=4) (16,0,39,0,4) [(55,[0,1,2,3,4,5,6,7,8])] kok31 (by decide +kernel)
def env111 : Env := (111,75,[0x2d506dc8c692839f653,0x1aa3b7e53917e26487f,0x544c503731eb1c38f9c,0x6d8c223200ec1fc0fc0,0x0,0x71d0482cce001fff020,0x7fe3c2000ee7f040020,0x0,0x0],[0xf04d190d4828112652,0xa02a6201004224829,0x1449d09c60531818514,0x6bb62f6391ac07c0ac0,0x0,0x70fb0c6f2b181eed020,0x7f5fd599feffb040000,0x0,0x0],[(0,8,99,4,5),(1,32,78,0,4),(12,0,99,0,4),(96,0,15,0,4)],[([0,1,2,3,4,5,6,7,8],[0,1,2,3,4,5,6,7,8]),([2,1,0,5,4,3,6,7,8],[2,1,0,5,4,3,6,7,8])])
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem eok111 : env111.ok := env_ok kok55 (by decide +kernel)
def n111_5_0 : List Node := [([390],[0,1,2,3,5,9],[],[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn111_5_0 : ∀ q ∈ n111_5_0, Imp (gr env111.1 []) 5 (nodeSet q) :=
  level_sound (g:=env111) (next:=([] : List Node)) eok111 nil_imp (by decide +kernel)
def lv111_5 : List Node := n111_5_0
theorem plv111_5 : ∀ q ∈ lv111_5, Imp (gr env111.1 []) 5 (nodeSet q) := pn111_5_0
def n111_6_0 : List Node := [([],[0,1,2,3,5,6],[1,2,3,0],[0])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn111_6_0 : ∀ q ∈ n111_6_0, Imp (gr env111.1 []) 6 (nodeSet q) :=
  level_sound (g:=env111) (next:=lv111_5) eok111 plv111_5 (by decide +kernel)
def lv111_6 : List Node := n111_6_0
theorem plv111_6 : ∀ q ∈ lv111_6, Imp (gr env111.1 []) 6 (nodeSet q) := pn111_6_0
def known111 := extend known55 7 [(187,[1,6,4,3,2,0,7,5,8]),(190,[4,6,1,0,5,3,7,2,8])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem kok111 : Known known111 := step_forest (g:=env111) (L:=6) [(187,[1,6,4,3,2,0,7,5,8]),(190,[4,6,1,0,5,3,7,2,8])] kok55 (n111_6_0.headD ([],[],[],[])) lv111_6 plv111_6 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def env189 : Env := (189,79,[0x1da64108012bd832f47c,0x0,0x2c458a9750042f2dc84f,0x1958e417a60021ce0f8f,0x67780400a62f50f10f70,0x52c2796909d080fbf080,0x0,0x7b3dbae059d52e010080,0x0],[0x1d85960021199906a42c,0x0,0x4c61e4544061425c84a,0x1909e00a3a18e18a0685,0x627201f4c42600710950,0x4042684f5e8240f95000,0x0,0x3b3981b0a179ab000080,0x0],[(12,0,177,0,4),(17,0,172,0,4),(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)],[([0,1,2,3,4,5,6,7,8],[0,1,2,3,4,5,6,7,8]),([0,1,2,7,5,4,6,3,8],[0,1,2,7,5,4,6,3,8]),([2,1,0,4,3,7,6,5,8],[2,1,0,4,3,7,6,5,8]),([2,1,0,5,7,3,6,4,8],[2,1,0,5,7,3,6,4,8]),([3,1,5,0,4,2,6,7,8],[3,1,5,0,4,2,6,7,8]),([3,1,5,7,2,4,6,0,8],[7,1,4,0,5,2,6,3,8]),([4,1,7,2,3,0,6,5,8],[5,1,3,4,0,7,6,2,8]),([4,1,7,5,0,3,6,2,8],[4,1,7,5,0,3,6,2,8]),([5,1,3,2,7,0,6,4,8],[5,1,3,2,7,0,6,4,8]),([5,1,3,4,0,7,6,2,8],[4,1,7,2,3,0,6,5,8]),([7,1,4,0,5,2,6,3,8],[3,1,5,7,2,4,6,0,8]),([7,1,4,3,2,5,6,0,8],[7,1,4,3,2,5,6,0,8])])
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem eok189 : env189.ok := env_ok kok111 (by decide +kernel)
def n189_5_0 : List Node := [([193,595],[0,2,3,5,7,10],[],[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn189_5_0 : ∀ q ∈ n189_5_0, Imp (gr env189.1 []) 5 (nodeSet q) :=
  level_sound (g:=env189) (next:=([] : List Node)) eok189 nil_imp (by decide +kernel)
def lv189_5 : List Node := n189_5_0
theorem plv189_5 : ∀ q ∈ lv189_5, Imp (gr env189.1 []) 5 (nodeSet q) := pn189_5_0
def n189_6_0 : List Node := [([129],[0,2,3,4,5,7,9],[],[]),
 ([193],[0,2,3,4,5,7,9],[2],[0])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn189_6_0 : ∀ q ∈ n189_6_0, Imp (gr env189.1 []) 6 (nodeSet q) :=
  level_sound (g:=env189) (next:=lv189_5) eok189 plv189_5 (by decide +kernel)
def lv189_6 : List Node := n189_6_0
theorem plv189_6 : ∀ q ∈ lv189_6, Imp (gr env189.1 []) 6 (nodeSet q) := pn189_6_0
def n189_7_0 : List Node := [([],[0,2,3,4,5,7],[5,2,4,3,1,0],[0,4,6,16,17,18,19,21,23])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn189_7_0 : ∀ q ∈ n189_7_0, Imp (gr env189.1 []) 7 (nodeSet q) :=
  level_sound (g:=env189) (next:=lv189_6) eok189 plv189_6 (by decide +kernel)
def lv189_7 : List Node := n189_7_0
theorem plv189_7 : ∀ q ∈ lv189_7, Imp (gr env189.1 []) 7 (nodeSet q) := pn189_7_0
def known189 := extend known111 8 [(189,[0,1,2,3,4,5,6,7,8])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem kok189 : Known known189 := step_forest (g:=env189) (L:=7) [(189,[0,1,2,3,4,5,6,7,8])] kok111 (n189_7_0.headD ([],[],[],[])) lv189_7 plv189_7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def env191 : Env := (191,182,[0x1a8e80efa31334f8b77110a294fa2c140112476e217263,0x2550613dee46b171e50184200e13000163a237ccc4483f,0xb8767821ad46b844808258e2a3253cf6ea13881040d8c,0x2669d07e8c08ca07a98c101ac024d2c2804ca411f909a0,0x1554139111eda5cf49d49289dc948100804cc031fe5240,0x253ba84144b4c40e1226cad10169ac341018648a03a410,0x0,0x38f01e2cfde810414683fb572913092a5d010800038410,0x0],[0x1a8204e622010a10823154424006181028000900212202,0x2550c011dc22916965caaa243f59e4c1d3e726bcc44879,0x287218002942c96181045804080031c00109841008504,0x2428c05eec0a4201a424385293645c4328c32710b10ae0,0x154130111e4b5ce49ca82ad2c98a38c923cd0654ed000,0x2509e8114094c4ae18468a9400a0a6cc00bdf6de028450,0x0,0x1870162cbd68114126a930633d5f5823ff420120010200,0x0],[(0,16,166,9,6),(1,0,190,0,7),(2,0,189,0,8),(4,0,187,0,7),(9,16,166,0,4),(14,0,177,0,4),(19,0,172,0,4),(20,8,163,0,4),(24,0,167,0,7),(25,0,166,0,4),(26,0,165,0,4),(35,0,156,0,4),(36,128,27,0,4),(56,0,135,0,4),(129,32,30,0,4),(134,0,57,0,4),(136,0,55,0,5),(152,0,39,0,4),(160,0,31,0,7),(162,0,29,0,4),(168,0,23,0,4)],[([0,1,2,3,4,5,6,7,8],[0,1,2,3,4,5,6,7,8]),([0,1,2,7,5,4,6,3,8],[0,1,2,7,5,4,6,3,8]),([2,1,0,4,3,7,6,5,8],[2,1,0,4,3,7,6,5,8]),([2,1,0,5,7,3,6,4,8],[2,1,0,5,7,3,6,4,8])])
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem eok191 : env191.ok := env_ok kok189 (by decide +kernel)
def n191_6_0 : List Node := [([65,595,649,711],[0,2,3,4,5,7,12],[],[]),
 ([193,599,649,711],[0,2,3,4,5,7,12],[],[]),
 ([129,589,583,659],[0,2,3,5,7,11,12],[],[]),
 ([129,589,580,746],[0,2,3,4,5,7,12],[],[]),
 ([129,583,653,723],[0,2,3,5,7,10,12],[],[]),
 ([129,589,580,659],[0,2,3,5,7,11,12],[],[]),
 ([258,458,677,711],[0,2,3,4,5,7,12],[],[]),
 ([129,193,583,659],[0,2,3,5,7,11,12],[],[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_6_0 : ∀ q ∈ n191_6_0, Imp (gr env191.1 []) 6 (nodeSet q) :=
  level_sound (g:=env191) (next:=([] : List Node)) eok191 nil_imp (by decide +kernel)
def n191_6_8 : List Node := [([193,329,595,671],[0,1,2,3,5,11,12],[],[]),
 ([257,599,649,711],[0,2,3,4,5,7,12],[],[]),
 ([193,449,595,663],[0,1,2,3,7,11,12],[],[]),
 ([130,585,644,746],[0,2,3,4,5,7,12],[],[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_6_8 : ∀ q ∈ n191_6_8, Imp (gr env191.1 []) 6 (nodeSet q) :=
  level_sound (g:=env191) (next:=([] : List Node)) eok191 nil_imp (by decide +kernel)
def lv191_6 : List Node := n191_6_0 ++ (n191_6_8)
theorem plv191_6 : ∀ q ∈ lv191_6, Imp (gr env191.1 []) 6 (nodeSet q) := append_imp pn191_6_0 (pn191_6_8)
def n191_7_0 : List Node := [([66,201,197],[0,2,4,5,7,9,10,11],[2],[]),
 ([461,579,645],[0,2,3,4,5,7,11],[],[]),
 ([129,193,580],[2,3,4,5,7,9,10,11],[328],[]),
 ([333,193,583],[0,1,2,4,5,7,10,11],[],[]),
 ([129,591,583],[0,2,3,4,5,7,10,11],[],[]),
 ([129,589,580],[0,2,3,4,5,7,10,11],[328],[48,80]),
 ([193,449,461],[0,1,2,4,5,9,10,11],[14,136,82],[]),
 ([129,583,653],[0,2,3,4,5,7,10,11],[200],[64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_7_0 : ∀ q ∈ n191_7_0, Imp (gr env191.1 []) 7 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_6) eok191 plv191_6 (by decide +kernel)
def n191_7_8 : List Node := [([65,589,659],[0,1,2,3,5,7,9,11],[],[]),
 ([258,585,647],[0,2,3,4,5,7,11],[],[]),
 ([461,585,647],[0,1,2,3,4,5,7,11],[],[]),
 ([130,201,605],[0,1,2,3,4,5,10,11],[],[]),
 ([258,133,585],[0,1,3,4,5,7,10,11],[14],[]),
 ([197,577,659],[0,1,2,3,5,7,11],[],[]),
 ([197,321,647],[0,2,3,4,5,7,9,11],[14],[]),
 ([197,133,129],[0,3,4,5,7,9,10,11],[7,2],[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_7_8 : ∀ q ∈ n191_7_8, Imp (gr env191.1 []) 7 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_6) eok191 plv191_6 (by decide +kernel)
def n191_7_16 : List Node := [([197,449,647],[0,2,3,4,5,7,9,11],[12],[]),
 ([66,593,135],[0,2,3,4,5,7,10,11],[],[]),
 ([129,589,659],[0,1,2,3,5,7,11],[],[]),
 ([333,129,647],[0,2,3,4,5,7,9,11],[],[]),
 ([65,265,655],[0,1,2,4,5,7,9,11],[],[]),
 ([129,193,583],[2,3,4,5,7,9,10,11],[328],[]),
 ([66,201,647],[0,2,3,4,5,7,9,11],[7],[]),
 ([258,581,265],[0,1,2,3,5,7,10,11],[136],[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_7_16 : ∀ q ∈ n191_7_16, Imp (gr env191.1 []) 7 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_6) eok191 plv191_6 (by decide +kernel)
def n191_7_24 : List Node := [([197,599,669],[0,1,2,3,4,5,11],[14],[]),
 ([129,589,659],[0,1,2,3,5,7,9,11],[],[32,80]),
 ([129,65,583],[0,2,3,4,5,7,10,11],[6],[]),
 ([129,591,580],[0,2,3,4,5,7,10,11],[],[]),
 ([257,599,649],[0,1,2,3,4,5,7,11],[2],[144]),
 ([65,595,649],[0,1,2,3,4,5,7,11],[7],[0]),
 ([194,129,644],[2,3,4,5,7,9,10,11],[],[]),
 ([65,193,659],[0,1,2,3,5,7,9,11],[],[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_7_24 : ∀ q ∈ n191_7_24, Imp (gr env191.1 []) 7 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_6) eok191 plv191_6 (by decide +kernel)
def n191_7_32 : List Node := [([66,593,453],[0,2,3,4,5,7,10,11],[],[]),
 ([258,605,663],[0,1,2,3,4,7,11],[12],[]),
 ([194,585,133],[0,1,3,4,5,7,10,11],[7],[]),
 ([193,449,595],[0,1,2,3,5,7,10,11],[338],[160]),
 ([129,583,65],[2,3,4,5,7,9,10,11],[66],[]),
 ([257,587,337],[0,1,2,3,5,7,10,11],[],[]),
 ([258,585,647],[0,1,2,3,4,5,7,11],[],[]),
 ([461,583,641],[0,1,2,3,4,5,7,11],[],[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_7_32 : ∀ q ∈ n191_7_32, Imp (gr env191.1 []) 7 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_6) eok191 plv191_6 (by decide +kernel)
def n191_7_40 : List Node := [([129,591,645],[0,1,2,3,4,5,7,11],[],[]),
 ([66,135,129],[3,4,5,7,9,10,11],[6,5],[]),
 ([66,202,677],[0,1,2,3,4,5,7,11],[67],[]),
 ([197,193,607],[0,1,2,4,5,7,10,11],[264],[]),
 ([257,583,649],[0,1,2,3,4,5,7,11],[4],[]),
 ([197,577,325],[0,2,3,4,5,7,10,11],[12],[]),
 ([461,129,647],[0,2,3,4,5,7,9,11],[],[]),
 ([129,589,647],[0,1,2,3,4,5,7,11],[],[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_7_40 : ∀ q ∈ n191_7_40, Imp (gr env191.1 []) 7 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_6) eok191 plv191_6 (by decide +kernel)
def n191_7_48 : List Node := [([197,607,66],[0,2,3,4,5,7,10,11],[],[]),
 ([258,597,265],[0,1,2,3,5,7,10,11],[136],[]),
 ([66,589,659],[0,1,2,3,5,7,11],[],[]),
 ([461,577,659],[0,1,2,3,5,7,11],[],[]),
 ([197,587,329],[0,1,3,4,5,7,10,11],[7,210],[]),
 ([194,581,649],[0,1,2,3,4,5,7,11],[],[]),
 ([129,583,655],[0,2,3,4,5,7,10,11],[],[]),
 ([66,585,197],[0,2,3,4,5,7,10,11],[],[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_7_48 : ∀ q ∈ n191_7_48, Imp (gr env191.1 []) 7 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_6) eok191 plv191_6 (by decide +kernel)
def n191_7_56 : List Node := [([65,265,129],[1,3,4,5,7,9,10,11],[4],[]),
 ([129,193,583],[0,2,3,4,5,7,10,11],[328],[112]),
 ([130,589,133],[0,1,2,4,5,7,10,11],[],[]),
 ([197,579,325],[0,2,3,4,5,7,10,11],[],[]),
 ([461,583,649],[0,1,2,3,4,5,7,11],[],[]),
 ([197,607,641],[0,1,2,3,4,5,7,11],[14],[]),
 ([129,589,583],[0,2,3,4,5,7,10,11],[328,5],[32]),
 ([461,201,583],[0,1,2,4,5,7,10,11],[],[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_7_56 : ∀ q ∈ n191_7_56, Imp (gr env191.1 []) 7 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_6) eok191 plv191_6 (by decide +kernel)
def n191_7_64 : List Node := [([257,329,671],[0,1,2,3,4,5,9,11],[],[]),
 ([461,585,643],[0,1,2,3,4,5,7,11],[],[]),
 ([66,461,645],[0,2,3,4,5,7,9,11],[67,16],[]),
 ([65,586,657],[0,1,2,3,5,7,9,11],[],[]),
 ([193,599,645],[0,1,2,3,4,5,7,11],[],[]),
 ([333,583,641],[0,1,2,3,4,5,7,11],[],[]),
 ([197,129,66],[2,3,4,5,7,9,10,11],[5],[]),
 ([194,581,129],[1,2,3,4,5,7,10,11],[],[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_7_64 : ∀ q ∈ n191_7_64, Imp (gr env191.1 []) 7 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_6) eok191 plv191_6 (by decide +kernel)
def n191_7_72 : List Node := [([193,583,649],[0,1,2,3,4,5,7,11],[7],[]),
 ([197,449,663],[0,1,2,3,4,7,9,11],[],[]),
 ([66,202,641],[1,2,3,4,5,7,9,11],[2],[]),
 ([258,585,644],[0,2,3,4,5,7,10,11],[],[0]),
 ([130,197,605],[0,1,2,3,4,5,10,11],[],[]),
 ([461,587,129],[0,1,3,4,5,7,10,11],[7,194],[]),
 ([193,607,645],[0,1,2,3,4,5,7,11],[],[]),
 ([461,581,643],[0,1,2,3,4,5,7,11],[16],[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_7_72 : ∀ q ∈ n191_7_72, Imp (gr env191.1 []) 7 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_6) eok191 plv191_6 (by decide +kernel)
def n191_7_80 : List Node := [([193,329,595],[0,1,2,3,5,7,10,11],[338],[128]),
 ([65,586,641],[1,2,3,4,5,7,9,11],[7],[]),
 ([130,65,585],[1,2,3,4,5,7,10,11],[7],[]),
 ([197,193,325],[0,2,4,5,7,9,10,11],[264,4],[]),
 ([130,585,647],[0,1,2,3,4,5,7,11],[],[]),
 ([258,458,677],[0,1,2,3,4,5,7,11],[2],[96]),
 ([129,589,647],[0,2,3,4,5,7,9,11],[328,2],[]),
 ([461,193,583],[0,1,2,4,5,7,10,11],[264],[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_7_80 : ∀ q ∈ n191_7_80, Imp (gr env191.1 []) 7 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_6) eok191 plv191_6 (by decide +kernel)
def n191_7_88 : List Node := [([461,581,651],[0,1,3,4,5,7,11],[],[]),
 ([258,585,647],[0,2,3,4,5,7,10,11],[2],[]),
 ([333,577,659],[0,1,2,3,5,7,11],[],[]),
 ([66,585,647],[0,2,3,4,5,7,10,11],[],[]),
 ([197,129,647],[0,2,3,4,5,7,9,11],[8],[]),
 ([197,321,325],[0,2,3,4,7,9,10,11],[2],[]),
 ([258,581,649],[0,1,2,3,4,5,7,11],[],[0]),
 ([129,583,66],[2,3,4,5,7,9,10,11],[5,66],[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_7_88 : ∀ q ∈ n191_7_88, Imp (gr env191.1 []) 7 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_6) eok191 plv191_6 (by decide +kernel)
def n191_7_96 : List Node := [([193,583,129],[1,2,3,4,5,7,10,11],[7],[]),
 ([129,589,647],[0,2,3,4,5,7,11],[],[]),
 ([194,133,129],[1,3,4,5,7,9,10,11],[],[]),
 ([461,579,645],[0,1,2,3,4,5,7,11],[],[]),
 ([333,577,647],[0,1,2,3,4,5,7,11],[],[]),
 ([129,257,583],[0,2,3,4,5,7,10,11],[],[]),
 ([461,577,647],[0,1,2,3,4,5,7,11],[],[]),
 ([129,193,659],[0,1,2,3,5,7,9,11],[386],[112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_7_96 : ∀ q ∈ n191_7_96, Imp (gr env191.1 []) 7 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_6) eok191 plv191_6 (by decide +kernel)
def n191_7_104 : List Node := [([129,581,647],[0,2,3,4,5,7,9,11],[2],[]),
 ([257,449,663],[0,1,2,3,4,7,9,11],[],[]),
 ([193,599,649],[0,1,2,3,4,5,7,11],[2],[16]),
 ([129,581,583],[0,2,3,4,5,7,10,11],[7],[]),
 ([193,329,129],[1,3,4,5,7,9,10,11],[7],[]),
 ([129,581,647],[0,2,3,4,5,7,11],[],[]),
 ([194,129,647],[2,3,4,5,7,9,10,11],[],[]),
 ([197,329,671],[0,1,2,3,4,5,9,11],[],[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_7_104 : ∀ q ∈ n191_7_104, Imp (gr env191.1 []) 7 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_6) eok191 plv191_6 (by decide +kernel)
def n191_7_112 : List Node := [([130,581,133],[0,2,3,4,5,7,10,11],[7],[]),
 ([461,579,649],[0,1,2,3,4,5,7,11],[14],[]),
 ([65,586,677],[0,1,2,3,4,5,7,11],[129],[]),
 ([130,585,644],[0,2,3,4,5,7,10,11],[],[176])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_7_112 : ∀ q ∈ n191_7_112, Imp (gr env191.1 []) 7 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_6) eok191 plv191_6 (by decide +kernel)
def lv191_7 : List Node := n191_7_0 ++ (n191_7_8 ++ (n191_7_16 ++ (n191_7_24 ++ (n191_7_32 ++ (n191_7_40 ++ (n191_7_48 ++ (n191_7_56 ++ (n191_7_64 ++ (n191_7_72 ++ (n191_7_80 ++ (n191_7_88 ++ (n191_7_96 ++ (n191_7_104 ++ (n191_7_112))))))))))))))
theorem plv191_7 : ∀ q ∈ lv191_7, Imp (gr env191.1 []) 7 (nodeSet q) := append_imp pn191_7_0 (append_imp pn191_7_8 (append_imp pn191_7_16 (append_imp pn191_7_24 (append_imp pn191_7_32 (append_imp pn191_7_40 (append_imp pn191_7_48 (append_imp pn191_7_56 (append_imp pn191_7_64 (append_imp pn191_7_72 (append_imp pn191_7_80 (append_imp pn191_7_88 (append_imp pn191_7_96 (append_imp pn191_7_104 (pn191_7_112))))))))))))))
def n191_8_0 : List Node := [([197,607],[0,1,2,3,4,5,7,10],[5,12,10,1],[688,768,976]),
 ([461,585],[0,1,2,3,4,5,7,10],[7,12,6],[160,1040]),
 ([258,585],[0,1,2,3,4,5,7,10],[14,136,12,2],[144,192,608,1186,1200,1424,1504]),
 ([197,325],[0,2,3,4,5,7,9,10],[136,82,2,65,131,11,5],[720,723,944,947,1328,1331,1488,1491]),
 ([197,129],[0,1,2,3,4,5,7,9,10],[7,5],[240,1120,1472]),
 ([257,449],[0,1,2,3,4,5,7,9,10],[14,12,82],[1680]),
 ([197,457],[0,1,2,3,4,5,7,9,10],[7,5],[]),
 ([193,583],[0,1,2,3,4,5,7,10],[4,7,18,66,14,12],[257,1152,1536])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_8_0 : ∀ q ∈ n191_8_0, Imp (gr env191.1 []) 8 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_7) eok191 plv191_7 (by decide +kernel)
def n191_8_8 : List Node := [([193,595],[0,1,2,3,5,7,10],[7,4,210,194],[322,496,560,1027,1169,1280,1648,1681,1779]),
 ([193,599],[0,1,2,3,4,5,7,10],[14,4,5,82],[1088,1696]),
 ([66,593],[0,1,2,3,4,5,7,10],[6,4],[272,512]),
 ([461,201],[0,1,2,4,5,7,9,10],[7,12,18,146],[594,1008]),
 ([194,457],[0,1,2,3,4,5,7,9,10],[1,12,15],[]),
 ([130,581],[0,1,2,3,4,5,7,10],[6,14,12,8,7],[1792,1824]),
 ([194,129],[1,2,3,4,5,7,9,10],[7,14,12,5],[480,1136,1568,1760]),
 ([258,457],[0,1,2,3,4,5,7,9,10],[1,12,15],[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_8_8 : ∀ q ∈ n191_8_8, Imp (gr env191.1 []) 8 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_7) eok191 plv191_7 (by decide +kernel)
def n191_8_16 : List Node := [([129,589],[0,1,2,3,4,5,7,10],[7,19,72,2,14,12,5],[288,752,1552]),
 ([197,449],[0,1,2,3,4,5,7,9,10],[14,12,82,2],[256,1168]),
 ([461,579],[0,1,2,3,4,5,7,10],[17,12,146,2],[16,1584,1808]),
 ([257,599],[0,1,2,3,4,5,7,10],[14,6,7,82,8],[448]),
 ([197,329],[0,1,2,3,4,5,7,9,10],[12,14,82,2],[723,832,1331,1776]),
 ([65,589],[0,1,2,3,4,5,7,9,10],[6,4,5],[128]),
 ([129,591],[0,1,2,3,4,5,7,10],[7,14,72,12,2],[640]),
 ([461,133],[0,1,2,3,4,5,7,9,10],[12,16],[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_8_16 : ∀ q ∈ n191_8_16, Imp (gr env191.1 []) 8 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_7) eok191 plv191_7 (by decide +kernel)
def n191_8_24 : List Node := [([258,581],[0,1,2,3,4,5,7,10],[6,12,14,136],[368,1504]),
 ([194,581],[0,1,2,3,4,5,7,10],[6,12,14,136],[848,1136]),
 ([130,193],[1,2,3,4,5,7,9,10],[4,7,8],[]),
 ([65,591],[0,1,2,3,4,5,7,10],[6,7,11,18,12],[]),
 ([257,607],[0,1,2,3,4,5,7,10],[6,12,9],[]),
 ([193,587],[0,1,2,3,4,5,7,10],[4,7,1],[]),
 ([194,133],[0,1,2,3,4,5,7,9,10],[5,14],[544,848,1568]),
 ([66,202],[0,1,2,3,4,5,7,9,10],[6,7,8,67],[672,1184])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_8_24 : ∀ q ∈ n191_8_24, Imp (gr env191.1 []) 8 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_7) eok191 plv191_7 (by decide +kernel)
def n191_8_32 : List Node := [([461,581],[0,1,2,3,4,5,7,10],[12,7,66,146,136,14,3],[1056,1264,1408]),
 ([194,453],[0,1,2,3,4,5,7,9,10],[12,15],[]),
 ([197,577],[0,1,2,3,4,5,7,10],[7,130,18,8,12,14,65,5],[208,720]),
 ([130,201],[0,1,2,3,4,5,7,9,10],[5,7,146],[176]),
 ([197,585],[0,1,2,3,4,5,7,10],[7,5],[]),
 ([66,201],[0,1,2,3,4,5,7,9,10],[6,7,5],[0,352]),
 ([333,193],[0,1,2,4,5,7,9,10],[7,14,18],[48]),
 ([129,591],[0,1,2,3,4,5,7,9,10],[7,8,72],[64,432])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_8_32 : ∀ q ∈ n191_8_32, Imp (gr env191.1 []) 8 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_7) eok191 plv191_7 (by decide +kernel)
def n191_8_40 : List Node := [([66,197],[0,2,3,4,5,7,9,10],[4,8,67,2,5],[0,513,768,880,1056,1120]),
 ([130,133],[0,1,2,3,4,5,7,9,10],[5,146,66],[928,929,1314,1792,1824]),
 ([65,586],[0,1,2,3,4,5,7,9,10],[6,82,129],[1072,1073,1296,1794,1824]),
 ([257,133],[0,1,2,3,4,5,7,9,10],[6,4],[]),
 ([197,599],[0,1,2,3,4,5,7,10],[5,14,10,18],[384]),
 ([197,193],[0,1,2,4,5,7,9,10],[7,4,8,2,130,14],[688,1328]),
 ([333,129],[0,1,2,3,4,5,7,9,10],[7,13,66,14],[304]),
 ([461,587],[0,1,2,3,4,5,7,10],[7,16,194],[1232])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_8_40 : ∀ q ∈ n191_8_40, Imp (gr env191.1 []) 8 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_7) eok191 plv191_7 (by decide +kernel)
def n191_8_48 : List Node := [([129,193],[1,2,3,4,5,7,9,10],[7,72,12,1],[32,336,898,1536,1728]),
 ([257,457],[0,1,2,3,4,5,7,9,10],[12,15],[]),
 ([66,585],[0,1,2,3,4,5,7,10],[14,130,4,7,12,67],[880,881,1456,1744]),
 ([258,265],[0,1,2,3,5,7,9,10],[4,8,12,3],[368,784]),
 ([197,579],[0,1,2,3,4,5,7,10],[10,12,14,8,7,65,5],[944]),
 ([333,583],[0,1,2,3,4,5,7,10],[13,14,12],[48,51,1104,1107]),
 ([128,589],[0,1,2,3,4,5,7,10],[7,5],[]),
 ([258,133],[0,1,2,3,4,5,7,9,10],[5,14],[192,1504])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_8_48 : ∀ q ∈ n191_8_48, Imp (gr env191.1 []) 8 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_7) eok191 plv191_7 (by decide +kernel)
def n191_8_56 : List Node := [([129,65],[0,1,2,3,4,5,7,9,10],[6,7,66,1],[416]),
 ([130,589],[0,1,2,3,4,5,7,10],[7,4],[]),
 ([258,605],[0,1,2,3,4,5,7,10],[12,14,18],[528]),
 ([130,593],[0,1,2,3,4,5,7,10],[6,4],[]),
 ([333,581],[0,1,2,3,4,5,7,10],[7,14,66],[]),
 ([65,587],[0,1,2,3,4,5,7,10],[6,20,7,14,12],[1824]),
 ([130,589],[0,1,2,4,5,7,10],[7,14,11,4,1],[177,928,1217]),
 ([257,583],[0,1,2,3,4,5,7,10],[6,12,9,14],[225,354,704])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_8_56 : ∀ q ∈ n191_8_56, Imp (gr env191.1 []) 8 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_7) eok191 plv191_7 (by decide +kernel)
def n191_8_64 : List Node := [([197,321],[0,1,2,3,4,5,7,9,10],[5,7],[224,1488]),
 ([130,197],[0,1,2,3,4,5,7,9,10],[7,5,129,146],[1216]),
 ([194,605],[0,1,2,3,4,5,7,10],[14,12],[]),
 ([461,129],[0,1,2,3,4,5,7,9,10],[7,16,12,66,3],[736,1232]),
 ([129,583],[0,1,2,3,4,5,7,9,10],[66,7,14],[576,578,1520,1522,1712]),
 ([65,265],[0,1,2,3,4,5,7,9,10],[4,7,72],[320,896]),
 ([461,577],[0,1,2,3,4,5,7,10],[7,12,2,18,8,16],[816,817,1632]),
 ([333,65],[0,1,2,3,4,5,7,9,10],[7,13],[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_8_64 : ∀ q ∈ n191_8_64, Imp (gr env191.1 []) 8 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_7) eok191 plv191_7 (by decide +kernel)
def n191_8_72 : List Node := [([193,607],[0,1,2,3,4,5,7,10],[4,12,2],[1248]),
 ([193,595],[0,1,2,3,5,7,9,10],[7,4,8],[]),
 ([461,583],[0,1,2,3,4,5,7,10],[17,12,14,146],[624,960,1008,1009,1392,1393]),
 ([197,133],[0,2,3,4,5,7,9,10],[5,7,8,65],[240,723]),
 ([65,585],[0,1,2,3,4,5,7,9,10],[5,6],[416]),
 ([129,193],[0,1,2,3,4,5,7,9,10],[4,7,130,72],[912,1648]),
 ([258,453],[0,1,2,3,4,5,7,9,10],[14,12,15],[]),
 ([129,589],[0,1,2,3,4,5,7,9,10],[72,7,66,5,4],[80,400,992,1376])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_8_72 : ∀ q ∈ n191_8_72, Imp (gr env191.1 []) 8 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_7) eok191 plv191_7 (by decide +kernel)
def n191_8_80 : List Node := [([197,587],[0,1,2,3,4,5,7,10],[5,7,210],[832]),
 ([461,65],[0,1,2,3,4,5,7,9,10],[7,16],[]),
 ([193,449],[0,1,2,3,4,5,7,9,10],[14,12,136,82],[96,560,561]),
 ([129,65],[1,2,3,4,5,7,9,10],[6,66,7,12,1],[242,243,576,896,897,1570,1571]),
 ([130,461],[0,1,2,3,4,5,7,9,10],[7,16,12],[]),
 ([129,583],[0,1,2,3,4,5,7,10],[66,13,14,7,12,200,210,4,129,131],[416,418,1472,1473,1474,1475,1712]),
 ([65,193],[0,1,2,3,4,5,7,9,10],[6,4,7],[496]),
 ([66,135],[0,2,3,4,5,7,9,10],[129,67],[272,273,274,275,656,1744])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_8_80 : ∀ q ∈ n191_8_80, Imp (gr env191.1 []) 8 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_7) eok191 plv191_7 (by decide +kernel)
def n191_8_88 : List Node := [([194,597],[0,1,2,3,4,5,7,10],[11,14],[]),
 ([333,577],[0,1,2,3,4,5,7,10],[7,14,2,8],[1440,1600]),
 ([333,579],[0,1,2,3,4,5,7,10],[13,14],[]),
 ([66,589],[0,1,2,3,4,5,7,10],[7,4,8],[800]),
 ([194,585],[0,1,2,3,4,5,7,10],[7,14,12,2,136],[544,848]),
 ([197,201],[0,1,2,4,5,7,9,10],[5,7,2],[0,1491]),
 ([461,193],[0,1,2,4,5,7,9,10],[7,146,8,14],[96,1392]),
 ([65,595],[0,1,2,3,4,5,7,10],[4,11,12,14,72],[464])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_8_88 : ∀ q ∈ n191_8_88, Imp (gr env191.1 []) 8 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_7) eok191 plv191_7 (by decide +kernel)
def n191_8_96 : List Node := [([257,329],[0,1,2,3,4,5,7,9,10],[14,12,82],[1024]),
 ([128,581],[0,1,2,3,4,5,7,10],[5,6,14,12],[]),
 ([258,597],[0,1,2,3,4,5,7,10],[11,14,136],[784]),
 ([130,65],[1,2,3,4,5,7,9,10],[6,7,14,12],[1312]),
 ([129,583],[0,2,3,4,5,7,9,10],[129,131,200,210,66],[64,65,66,67,336,337,338,339,992,993,994,995,1520,1522,1760,1761,1762,1763]),
 ([258,458],[0,1,2,3,4,5,7,9,10],[12,4,8,18],[1360]),
 ([257,587],[0,1,2,3,4,5,7,10],[6,9,14,12,4],[592]),
 ([129,257],[0,1,2,3,4,5,7,9,10],[6,4],[1616])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_8_96 : ∀ q ∈ n191_8_96, Imp (gr env191.1 []) 8 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_7) eok191 plv191_7 (by decide +kernel)
def n191_8_104 : List Node := [([66,461],[0,1,2,3,4,5,7,9,10],[16,7,12,2],[1056]),
 ([66,129],[1,2,3,4,5,7,9,10],[1,130,7,14,4,12,5,67],[656,1120,1121,1520]),
 ([129,583],[0,2,3,4,5,7,10],[200,210,129,131],[112,113,114,115,304,305,736,738,864,865,866,867,912,913,914,915,1456,1458,1616,1617,1618,1619,1664]),
 ([129,581],[0,1,2,3,4,5,7,9,10],[5,66,6],[1664,1712]),
 ([130,585],[0,1,2,3,4,5,7,10],[7,14,12,4,2,1,3],[1312,1314,1344,1664,1744,1824,1840]),
 ([129,581],[0,1,2,3,4,5,7,10],[13,14,7,12,4,5,6,66],[1712,1744]),
 ([257,321],[0,1,2,3,4,5,7,9,10],[6,4],[]),
 ([193,329],[0,1,2,3,4,5,7,9,10],[7,4,14,12,136,82],[1280,1283,1728])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_8_104 : ∀ q ∈ n191_8_104, Imp (gr env191.1 []) 8 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_7) eok191 plv191_7 (by decide +kernel)
def n191_8_112 : List Node := [([129,580],[0,2,3,4,5,7,9,10],[66,6,5,210],[32,33,34,35,80,81,82,83,432,433,434,435,480,481,482,483,1664,1744])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_8_112 : ∀ q ∈ n191_8_112, Imp (gr env191.1 []) 8 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_7) eok191 plv191_7 (by decide +kernel)
def lv191_8 : List Node := n191_8_0 ++ (n191_8_8 ++ (n191_8_16 ++ (n191_8_24 ++ (n191_8_32 ++ (n191_8_40 ++ (n191_8_48 ++ (n191_8_56 ++ (n191_8_64 ++ (n191_8_72 ++ (n191_8_80 ++ (n191_8_88 ++ (n191_8_96 ++ (n191_8_104 ++ (n191_8_112))))))))))))))
theorem plv191_8 : ∀ q ∈ lv191_8, Imp (gr env191.1 []) 8 (nodeSet q) := append_imp pn191_8_0 (append_imp pn191_8_8 (append_imp pn191_8_16 (append_imp pn191_8_24 (append_imp pn191_8_32 (append_imp pn191_8_40 (append_imp pn191_8_48 (append_imp pn191_8_56 (append_imp pn191_8_64 (append_imp pn191_8_72 (append_imp pn191_8_80 (append_imp pn191_8_88 (append_imp pn191_8_96 (append_imp pn191_8_104 (pn191_8_112))))))))))))))
def n191_9_0 : List Node := [([257],[0,1,2,3,4,5,7,9],[8,6,82,0,2,3,1],[18,80,99,178,195,243,258,304,448,562,578,594,688,784,1008,1025,1425,1490,1536,1632,1648,1760]),
 ([461],[0,1,2,3,4,5,7,9],[18,8,12,66,16,3,1],[16,176,177,288,368,512,752,1072,1120,1184,1296,1344,1504,1505,1664]),
 ([128],[0,1,2,3,4,5,7,9],[3,6,14,4,12,18,8,1,2,7],[864,865,866,867,1552]),
 ([197],[0,1,2,3,4,5,7,9],[8,5,82,2,7,3,1],[0,48,64,96,272,320,512,529,544,576,640,704,720,832,960,1024,1040,1200,1249,1280,1488]),
 ([130],[0,1,2,3,4,5,7,9],[1,82,72,3,6,14,4,18,8,2],[208,416,417,560,561,656,912,913,944,945,992,993,1040,1041,1344,1584,1728]),
 ([258],[0,1,2,3,4,5,7,9],[8,1,82,11,14,2,3],[32,240,384,498,816,880,928,1248,1568,1616]),
 ([66],[0,1,2,3,4,5,7,9],[1,2,82,72,14,4,3],[160,161,496,497,592,593,640,641,800,1392,1456,1457,1664,1680]),
 ([333],[0,1,2,3,4,5,7,9],[18,8,14,7,66,3,1,13],[608,611,736,848,960,1136,1139,1424,1427,1440,1443])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_9_0 : ∀ q ∈ n191_9_0, Imp (gr env191.1 []) 9 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_8) eok191 plv191_8 (by decide +kernel)
def n191_9_8 : List Node := [([65],[0,1,2,3,4,5,7,9],[6,82,2,72,3,1,11],[336,337,370,432,433,482,483,544,545,578,579,658,672,690,691,882,883,896,976,1104,1105,1136,1137,1202,1203,1216,1296,1328,1376,1377,1520,1521,1584,1744]),
 ([193],[0,1,2,3,4,5,7,9],[8,82,7,4,66,3,1],[81,112,128,144,256,273,323,416,464,544,608,720,768,818,1106,1120,1152,1168,1232,1312,1376,1424,1504,1539,1776]),
 ([194],[0,1,2,3,4,5,7,9],[1,8,82,11,7,2,3,14],[192,224,400,480,528,1056,1408,1472]),
 ([129],[0,1,2,3,4,5,7,9],[82,72,3,1,66,2],[64,65,66,67,224,225,226,227,256,257,258,259,352,353,354,355,624,625,626,627,736,737,768,769,770,771,896,898,1072,1074,1088,1232,1233,1234,1235,1264,1265,1266,1267,1328,1330,1360,1600,1648,1649,1650,1651,1680,1682,1696,1712,1744,1792])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_9_8 : ∀ q ∈ n191_9_8, Imp (gr env191.1 []) 9 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_8) eok191 plv191_8 (by decide +kernel)
def lv191_9 : List Node := n191_9_0 ++ (n191_9_8)
theorem plv191_9 : ∀ q ∈ lv191_9, Imp (gr env191.1 []) 9 (nodeSet q) := append_imp pn191_9_0 (pn191_9_8)
def n191_10_0 : List Node := [([],[0,1,2,3,4,5,7],[18,8,2],[0,1,2,3,16,18,32,48,49,50,51,64,66,80,81,82,83,96,98,112,113,128,130,144,145,146,147,160,161,162,163,176])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pn191_10_0 : ∀ q ∈ n191_10_0, Imp (gr env191.1 []) 10 (nodeSet q) :=
  level_sound (g:=env191) (next:=lv191_9) eok191 plv191_9 (by decide +kernel)
def lv191_10 : List Node := n191_10_0
theorem plv191_10 : ∀ q ∈ lv191_10, Imp (gr env191.1 []) 10 (nodeSet q) := pn191_10_0
def known191 := extend known189 11 [(191,[0,1,2,3,4,5,6,7,8])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem kok191 : Known known191 := step_forest (g:=env191) (L:=10) [(191,[0,1,2,3,4,5,6,7,8])] kok189 (n191_10_0.headD ([],[],[],[])) lv191_10 plv191_10 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem low191 : Lower (gr 191 []) 11 := kok191 (191, 11) (by decide)
def f7 (x : Fin 7 → Bool) : Bool :=
  [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (63 : ℕ)].any fun e =>
    x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10))
def idx7 : Fin 7 → Fin 9
  | ⟨0, _⟩ => 4
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 7
  | ⟨4, _⟩ => 3
  | ⟨5, _⟩ => 5
  | ⟨6, _⟩ => 2
def proj7 (r : Row) : Fin 7 → Bool := fun i => r (idx7 i)
theorem f7_eq_gr191 (r : Row) : f7 (proj7 r) = gr 191 [] r := by
  revert r
  decide +kernel
def roots7 : List Wire := [xv 4, xv 0, xv 1, xv 7, xv 3, xv 5, xv 2, ff]
theorem roots7_av : ∀ v ∈ memS roots7, Av Inp v := by
  intro v hv
  simp only [memS, Set.mem_setOf_eq, roots7, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact av_mem ⟨4, rfl⟩
  · exact av_mem ⟨0, rfl⟩
  · exact av_mem ⟨1, rfl⟩
  · exact av_mem ⟨7, rfl⟩
  · exact av_mem ⟨3, rfl⟩
  · exact av_mem ⟨5, rfl⟩
  · exact av_mem ⟨2, rfl⟩
  · exact av_ff
theorem roots7_map (r : Row) : roots7.map (fun v => v r) = List.ofFn (proj7 r) ++ [false] := by
  apply List.ext_getElem
  · simp [roots7]
  · intro i h1 _
    simp only [roots7, List.length_map, List.length_cons, List.length_nil] at h1
    interval_cases i <;> simp [roots7, proj7, idx7, xv, ff, List.getElem_append]
theorem bound : have x1 : (Fin (7 : ℕ) → Bool) → Bool := fun (x1 : Fin (7 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (63 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (7 : ℕ) → Bool) → List Bool := fun (x2 : Fin (7 : ℕ) → Bool) => List.ofFn x2 ++ [Bool.false]; have x3 : ℕ → PEqualNP.MetaComplexity.BinaryGate → Prop := fun (x3 : ℕ) (x4 : PEqualNP.MetaComplexity.BinaryGate) => (∃ (x5 : Bool) (x6 : Bool), x4.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) ∧ x4.left < x3 ∧ x4.right < x3 ∧ x4.left ≠ (7 : ℕ) ∧ x4.right ≠ (7 : ℕ) ∧ x4.left ≠ x4.right; ¬∃ (x4 : List PEqualNP.MetaComplexity.BinaryGate) (x5 : PEqualNP.MetaComplexity.BinaryGate) (x6 : Bool),     have x7 : List ℕ := List.flatMap (fun (x7 : PEqualNP.MetaComplexity.BinaryGate) => [x7.left, x7.right]) (x4 ++ [x5]);     (7 : ℕ) ≤ x4.length ∧ x4.length ≤ (9 : ℕ) ∧ (∀ (x8 : ℕ) (x9 : x8 < x4.length), x3 ((8 : ℕ) + x8) x4[x8]) ∧ x3 ((8 : ℕ) + x4.length) x5 ∧ (8 : ℕ) ≤ x5.left ∧ (8 : ℕ) ≤ x5.right ∧ (∀ x8 < x4.length, ∃ x10 ∈ List.drop (x8 + (1 : ℕ)) (x4 ++ [x5]), x10.left = (8 : ℕ) + x8 ∨ x10.right = (8 : ℕ) + x8) ∧ (12 : ℕ) ≤ x4.length + {x8 ∈ Finset.range (7 : ℕ) | List.count x8 x7 = (1 : ℕ)}.card ∧ (∀ x8 ∈ x4 ++ [x5], x8.left < (7 : ℕ) → x8.right < (7 : ℕ) → List.count x8.left x7 ≠ (1 : ℕ) ∨ List.count x8.right x7 ≠ (1 : ℕ)) ∧ ∀ (x8 : Fin (7 : ℕ) → Bool), ({ gates := x4 ++ [x5], output := (8 : ℕ) + x4.length : PEqualNP.MetaComplexity.BinaryCircuit }.eval (x2 x8) != x6) = x1 x8 := by
  dsimp only
  rintro ⟨gs, g, q, _, hle9, hgs_v, hg_v, _, _, _, _, _, heval⟩
  have hAnd : ∀ t ∈ gs ++ [g], AndOp t := by
    intro t ht
    rcases List.mem_append.mp ht with h1 | h2
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h1
      exact (hgs_v i hi).1
    · rw [List.mem_singleton.mp h2]
      exact hg_v.1
  have hcomp0 := comp_mono roots7_av (comp_gates (gs ++ [g]) hAnd (8 + gs.length) roots7)
  have hcomp1 : Comp (gs ++ [g]).length Inp (gr 191 []) := by
    cases q
    · convert hcomp0 using 1
      funext r
      rw [← f7_eq_gr191 r]
      have hr := heval (proj7 r)
      simpa [BinaryCircuit.eval, BinaryCircuit.wires, f7, roots7_map r] using hr.symm
    · convert comp_neg hcomp0 using 1
      funext r
      rw [← f7_eq_gr191 r]
      have hr := heval (proj7 r)
      simpa [BinaryCircuit.eval, BinaryCircuit.wires, f7, roots7_map r] using hr.symm
  have hlow := low191 (gs ++ [g]).length hcomp1
  simp only [List.length_append, List.length_singleton] at hlow
  omega
end PEqualNP.Outside.L_meta_3983

theorem PEqualNP.Outside.L_meta_3983 : have x1 : (Fin (7 : ℕ) → Bool) → Bool := fun (x1 : Fin (7 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (63 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (7 : ℕ) → Bool) → List Bool := fun (x2 : Fin (7 : ℕ) → Bool) => List.ofFn x2 ++ [Bool.false]; have x3 : ℕ → PEqualNP.MetaComplexity.BinaryGate → Prop := fun (x3 : ℕ) (x4 : PEqualNP.MetaComplexity.BinaryGate) => (∃ (x5 : Bool) (x6 : Bool), x4.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) ∧ x4.left < x3 ∧ x4.right < x3 ∧ x4.left ≠ (7 : ℕ) ∧ x4.right ≠ (7 : ℕ) ∧ x4.left ≠ x4.right; ¬∃ (x4 : List PEqualNP.MetaComplexity.BinaryGate) (x5 : PEqualNP.MetaComplexity.BinaryGate) (x6 : Bool),     have x7 : List ℕ := List.flatMap (fun (x7 : PEqualNP.MetaComplexity.BinaryGate) => [x7.left, x7.right]) (x4 ++ [x5]);     (7 : ℕ) ≤ x4.length ∧ x4.length ≤ (9 : ℕ) ∧ (∀ (x8 : ℕ) (x9 : x8 < x4.length), x3 ((8 : ℕ) + x8) x4[x8]) ∧ x3 ((8 : ℕ) + x4.length) x5 ∧ (8 : ℕ) ≤ x5.left ∧ (8 : ℕ) ≤ x5.right ∧ (∀ x8 < x4.length, ∃ x10 ∈ List.drop (x8 + (1 : ℕ)) (x4 ++ [x5]), x10.left = (8 : ℕ) + x8 ∨ x10.right = (8 : ℕ) + x8) ∧ (12 : ℕ) ≤ x4.length + {x8 ∈ Finset.range (7 : ℕ) | List.count x8 x7 = (1 : ℕ)}.card ∧ (∀ x8 ∈ x4 ++ [x5], x8.left < (7 : ℕ) → x8.right < (7 : ℕ) → List.count x8.left x7 ≠ (1 : ℕ) ∨ List.count x8.right x7 ≠ (1 : ℕ)) ∧ ∀ (x8 : Fin (7 : ℕ) → Bool), ({ gates := x4 ++ [x5], output := (8 : ℕ) + x4.length : PEqualNP.MetaComplexity.BinaryCircuit }.eval (x2 x8) != x6) = x1 x8 :=
  PEqualNP.Outside.L_meta_3983.bound
