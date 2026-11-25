import PetersenSeventeenFull

namespace PEqualNP.Outside.L_meta_2373.Live1024.FreeBank
open PEqualNP.CircuitLowerBounds

private lemma bit_zero (i : Fin 1024) : bit i zero = false := by simp [bit, zero]
private lemma bit_one (i : Fin 1024) : bit i one = true := by
  unfold bit one
  rw [BitVec.getLsbD_allOnes]
  simp

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

theorem positive_tail_extract (gs : List Gate) (w : List Sig) {target : Sig}
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (mono : ∀ g ∈ gs, isNot g = false)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k S, k ≤ gs.length ∧ Live false target k S ∧ ∀ a ∈ S, a ∈ w := by
  have identity : nrm false = id := by funext a; rfl
  have output : target ∈ (execute gs w).map (nrm false) := by
    simpa only [identity, List.map_id] using hout
  obtain ⟨k, S, bound, trace, sub⟩ := extract gs w legal (fun _ => mono) hp output
  refine ⟨k, S, le_trans bound List.countP_le_length, trace, ?_⟩
  simpa only [identity, List.map_id] using sub

lemma gate_rep_free (w free : List Sig) (g : Gate)
    (legal : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (mono : isNot g = false) :
    represented (w ++ free) (gv w g) ∨ (1 = 1 ∧ witness false (w ++ free) (gv w g)) := by
  have rep := gate_rep false w g legal (fun _ => mono)
  have identity : nrm false = id := by funext a; rfl
  simp only [identity, List.map_id] at rep
  change represented w (gv w g) ∨ (isNot g = false ∧ witness false w (gv w g)) at rep
  rcases rep with h | ⟨_, d, a, b, hd, ha, hb, pa, pb, ne, eq⟩
  · left
    exact h.imp (List.mem_append_left free) id
  · right
    exact ⟨rfl, d, a, b, hd, List.mem_append_left free ha,
      List.mem_append_left free hb, pa, pb, ne, eq⟩

lemma pull_positive_chunk (gs : List Gate) (w free : List Sig) {target : Sig} {k : Nat}
    {S : Finset Sig}
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (mono : ∀ g ∈ gs, isNot g = false)
    (run : Live false target k S) (sub : ∀ a ∈ S, a ∈ execute gs w ++ free) :
    ∃ k' S', k' ≤ k + gs.length ∧ Live false target k' S' ∧ ∀ a ∈ S', a ∈ w ++ free := by
  induction gs generalizing w with
  | nil => exact ⟨k, S, by simp, run, sub⟩
  | cons g gs ih =>
    obtain ⟨l, U, bound, trace, subset⟩ := ih (w ++ [gv w g])
      (fun q hq => legal q (by simp [hq])) (fun q hq => mono q (by simp [hq])) sub
    have sub' : ∀ a ∈ U, a ∈ (w ++ free) ++ [gv w g] := by
      intro a ha
      have h := subset a ha
      simpa only [List.mem_append, List.mem_singleton, or_assoc, or_left_comm, or_comm] using h
    obtain ⟨l', U', hb, hr, hs⟩ := pull_gate trace
      (gate_rep_free w free g (legal g (by simp)) (mono g (by simp))) sub'
    exact ⟨l', U', by simp only [List.length_cons]; omega, hr, hs⟩

lemma skip_free_gate (w free : List Sig) (g : Gate) {S : Finset Sig}
    (known : gv w g ∈ free) (sub : ∀ a ∈ S, a ∈ (w ++ [gv w g]) ++ free) :
    ∀ a ∈ S, a ∈ w ++ free := by
  intro a ha
  have h := sub a ha
  simp only [List.mem_append, List.mem_singleton] at h ⊢
  rcases h with (old | rfl) | fixed
  · exact Or.inl old
  · exact Or.inr known
  · exact Or.inr fixed

end PEqualNP.Outside.L_meta_2373.Live1024.FreeBank

