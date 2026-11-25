import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore
open DagTools
namespace Compact
open Resolution

theorem construct_layout_budget {k I : Nat} {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bp : Bplus 14 D + (mask I).card = 14 + k) (eq : mask I=ineligSet 14 D) :
    Nonempty (Layout D k I) := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have el := inelig_card_add 14 D
  have diff := card_residual h.1 b hb
  rw [←eq] at el
  have count : Fintype.card ↥(residualUnits 14 D b)=k := by rw [Fintype.card_coe]; omega
  let f := (Fintype.equivFinOfCardEq count).symm
  have lim (x : V) : countAt D x ≤ cap k I x := by
    unfold cap countAt
    split
    · rename_i hx
      obtain ⟨p,_,_,_,_,_,sw,_⟩ := sem_inelig_consumer graph_ok h hc (eq ▸ hx)
      change sem_W 14 D x={p} at sw
      rw [sw,Finset.card_singleton]
    · have one := Finset.card_le_card (Finset.inter_subset_left : ({x}:Finset V)∩eligSet 14 D ⊆ {x})
      have two := Finset.card_filter_le (residualUnits 14 D b) (fun u => x∈supp 14 D u.1)
      have cc := sem_code_count graph_ok h hc b hb x
      simp only [Finset.card_singleton] at one
      omega
  have has (x : V) : 0<countAt D x := by
    obtain ⟨y,xy,_⟩ := graph_ok.2.2.2 x x
    obtain ⟨p,hp,_⟩ := sem_edge_slots graph_ok h.1 hc xy
    exact Finset.card_pos.mpr ⟨p,hp⟩
  let enum (x : V) : Fin (countAt D x) ≃ ↥(sem_W 14 D x) :=
    (Fintype.equivFinOfCardEq (by simp [countAt])).symm
  let atIdx (x : V) (j : Nat) : Fin (countAt D x) := if hj : j<countAt D x then ⟨j,hj⟩ else ⟨0,has x⟩
  let w (x : V) (j : Nat) := ((enum x) (atIdx x j)).val
  have onto (x : V) (e) (he : e∈sem_W 14 D x) : ∃ j<countAt D x, w x j=e := by
    obtain ⟨i,hf⟩ := (enum x).surjective ⟨e,he⟩
    exact ⟨i.val,i.isLt,by simpa [w,atIdx,i.isLt] using congrArg Subtype.val hf⟩
  obtain ⟨P,hp⟩ := get_slots h hc
  choose readAt spec using (fun s e => onto (endpoint s e) _ (hp s e))
  refine ⟨⟨w,P,readAt,b,f,hb,lim,fun x j => ((enum x) (atIdx x j)).property,?_,onto,fun s e => (spec s e).1,fun s e => (spec s e).2⟩⟩
  intro x j k hj hk same
  have e := (enum x).injective (Subtype.ext same)
  simpa [atIdx,hj,hk] using congrArg Fin.val e

def weakScheme : Scheme → Bool
  | .exactAt _ _ _ => false
  | _ => true

theorem scheme_sound_weak {D : Dag} {k I : Nat} (Z : Layout D k I) (h : StrictLive 14 D)
    (hc : sem_Comp 14 adj D) (eq : mask I=ineligSet 14 D)
    (q : Scheme) (no : weakScheme q = true) (en : enabled k I q=true) : EvalClause Z (expand k I q) := by
  classical
  cases q with
  | self x j =>
    simpa only [expand,pos_iff,none_iff,or_false,evalFact] using Z.selfLab x j
  | earlier x j =>
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,evalFact,Layout.Live]
    omega
  | labCommon x c j =>
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,commonF_iff]
    simp only [evalFact]
    have := Z.commonLab x c j; tauto
  | someRes x =>
    simp only [expand,neg_iff,range_iff,evalFact]
    by_cases active : Z.Live x 2
    · obtain ⟨t,ht⟩ := Z.some_code h hc x active
      exact Or.inr ⟨t.val,t.isLt,(atRes Z t x).2 ht⟩
    · exact Or.inl active
  | allRes x t =>
    simp only [enabled,decide_eq_true_eq] at en
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,evalFact]
    by_cases active : Z.Live x (1+k)
    · let i : Fin k := ⟨t,en⟩
      exact Or.inr ((atRes Z i x).2 (Z.all_code h hc x active i))
    · exact Or.inl active
  | exposure x a =>
    simp only [enabled,decide_eq_true_eq] at en
    exact (range_iff _ _ _).2 (Z.expose h hc x a en.1 en.2)
  | exactAt x i p => simp [weakScheme] at no
  | avoidLive x a j =>
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,evalFact]
    by_cases v : Z.avoid x a j; exact Or.inr v.1; exact Or.inl v
  | seeLive x i p j =>
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,evalFact]
    by_cases v : Z.see x i p j; exact Or.inr v.1; exact Or.inl v
  | avoidNot x c a j =>
    simp only [enabled,decide_eq_true_eq] at en
    simp only [expand,neg_iff,none_iff,or_false,evalFact]
    by_cases v : Z.avoid x a j; exact Or.inr (v.2 c en); exact Or.inl v
  | seeLab x i c p j =>
    simp only [enabled,decide_eq_true_eq] at en
    by_cases a : adj i c <;> simp only [expand,a,if_true,if_false,neg_iff,pos_iff,none_iff,or_false,evalFact]
    · by_cases v : Z.see x i p j; exact Or.inr ((v.2 c en).2 a); exact Or.inl v
    · by_cases v : Z.see x i p j; exact Or.inr (fun u => a ((v.2 c en).1 u)); exact Or.inl v
  | diffX t x c => simp only [expand,neg_iff,pos_iff,none_iff,or_false,evalFact]; tauto
  | diffC t x c => simp only [expand,neg_iff,none_iff,or_false,evalFact]; tauto
  | adjacentCommon x c i =>
    simp only [enabled,decide_eq_true_eq] at en
    simp only [expand,pos_iff,none_iff,or_false,commonF_iff]
    exact share h hc (i:=i) (eq ▸ en.1) en.2.1 en.2.2
  | resCommon x c t =>
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,commonF_iff]
    simp only [evalFact]
    by_cases rx : rAt Z t x <;> by_cases rc : rAt Z t c
    · obtain ⟨i,eqi,hx⟩ := rx; obtain ⟨j,eqj,hc⟩ := rc
      have same : i=j := Fin.ext (eqi.trans eqj.symm)
      exact Or.inr (Or.inr (Z.commonRes i x c hx (same ▸ hc)))
    all_goals tauto
  | residual x c j l =>
    simp only [enabled,decide_eq_true_eq] at en
    simp only [expand,neg_iff,pos_iff,commonF_iff,range_iff]
    simp only [evalFact]
    by_cases com : Together D x c
    · right; by_cases active : Z.Live x l
      · right
        have elig : x∈eligSet 14 D := by by_contra no; exact en.2.1 (eq ▸ sem_mem_inelig.mpr no)
        rcases Z.ri_slots h hc x c en.1 elig en.2.2 active com with v|v|⟨t,hx,miss⟩
        · exact Or.inl v
        · exact Or.inr (Or.inl v)
        · exact Or.inr (Or.inr ⟨t.val,t.isLt,(atRes Z t x).2 hx,fun u => miss ((atRes Z t c).1 u)⟩)
      · exact Or.inl active
    · exact Or.inl com
  | readerAny s e => exact (range_iff _ _ _).2 ⟨_,Z.boundReader s e,rfl⟩
  | readerLive s e j =>
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,evalFact]
    by_cases r : Z.reader s e=j; exact Or.inr (r ▸ Z.reader_live s e); exact Or.inl r
  | readerLab s e j c dir =>
    cases dir <;> change EvalClause Z (negF _ :: _)
    all_goals simp only [Bool.not_true,Bool.not_false,neg_iff,pos_iff,none_iff,or_false,evalFact]
    all_goals by_cases r : Z.reader s e=j
    all_goals first | exact Or.inl r | have v := Z.readerLab s e j c _ rfl r; tauto
  | eqLab s e f c dir =>
    cases dir <;> change EvalClause Z (negF _ :: _)
    all_goals simp only [Bool.not_true,Bool.not_false,neg_iff,pos_iff,none_iff,or_false,evalFact]
    all_goals by_cases r : Z.edge e=Z.edge f
    all_goals first | exact Or.inl r | have v := Z.eqLab s e f c r; tauto
  | gateEq s e f j =>
    simp only [enabled,decide_eq_true_eq] at en
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,evalFact]
    have v := Z.readerEq s e f j en
    tauto

def localCheckWeak (k I : Nat) (a : Array Fact) (r : Scheme) (c : Clause) : Bool :=
  weakScheme r && localCheck k I a r c

def inputsOKWeak (k I : Nat) (a : Array Fact) : List Scheme → List Clause → Bool
  | [], [] => true
  | r::rs, c::cs => localCheckWeak k I a r c && inputsOKWeak k I a rs cs
  | _, _ => false

theorem localSound_weak {D : Dag} {k I : Nat} (Z : Layout D k I) (h : StrictLive 14 D)
    (hc : sem_Comp 14 adj D) (eq : mask I=ineligSet 14 D)
    (a : Array Fact) (r : Scheme) (c : Clause) (ok : localCheckWeak k I a r c=true) :
    Holds (truth Z a) c := by
  simp only [localCheckWeak, localCheck, Bool.and_eq_true] at ok
  obtain ⟨p,hm,hval⟩ := scheme_sound_weak Z h hc eq r ok.1 ok.2.1
  have mem := List.contains_iff_mem.mp (List.all_eq_true.mp ok.2.2 p hm)
  obtain ⟨l,hl,eqp⟩ := List.mem_map.mp mem
  subst p
  refine ⟨l,hl,?_⟩
  rcases l with ⟨i,b⟩
  cases b <;> simp [truth,Yes,atLit] at hval ⊢ <;> exact hval

theorem inputs_sound_weak {D : Dag} {k I : Nat} (Z : Layout D k I) (h : StrictLive 14 D)
    (hc : sem_Comp 14 adj D) (eq : mask I=ineligSet 14 D)
    (a : Array Fact) (R : List Scheme) (F : Array Clause)
    (ok : inputsOKWeak k I a R F.toList=true) : Valid (truth Z a) F := by
  have all (rs : List Scheme) (cs : List Clause) (good : inputsOKWeak k I a rs cs=true) : List.Forall (Holds (truth Z a)) cs := by
    induction rs generalizing cs with
    | nil => cases cs <;> simp_all [inputsOKWeak,List.Forall]
    | cons r rs ih =>
      cases cs with
      | nil => contradiction
      | cons c cs =>
        simp only [inputsOKWeak,Bool.and_eq_true] at good
        apply List.forall_iff_forall_mem.mpr
        intro item mem
        rcases List.mem_cons.mp mem with rfl|rest
        · exact localSound_weak Z h hc eq a r _ good.1
        · exact List.forall_iff_forall_mem.mp (ih cs good.2) item rest
  intro c cF
  exact List.forall_iff_forall_mem.mp (all R F.toList ok) c (Array.mem_toList_iff.mpr cF)

theorem book_start_weak {D k I} (Z : Layout D k I) (h : StrictLive 14 D)
    (hc : sem_Comp 14 adj D) (eq : mask I=ineligSet 14 D)
    (a : Array Fact) (R : List Scheme) (book : Nat → Clause) (n : Nat)
    (ok : inputsOKWeak k I a R (baseBook book n).toList=true) : ValidThrough (truth Z a) book n := by
  have sat := inputs_sound_weak Z h hc eq a R (baseBook book n) ok
  intro j hj
  apply sat
  exact Array.mem_ofFn.mpr ⟨⟨j,hj⟩,rfl⟩


end Compact
end PEqualNP.Outside.L_meta_9775.UpstreamCore
