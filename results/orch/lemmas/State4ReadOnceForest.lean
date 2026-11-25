import State4Copy14

namespace PEqualNP.Outside.L_meta_2373.Live1024

def LabelPartition {α : Type} [DecidableEq α] (roots : Finset α)
    (S : Finset Sig) (label : Sig → Finset α) : Prop :=
  (∀ v ∈ S, label v ⊆ roots) ∧
  (∀ v ∈ S, ∀ w ∈ S, v ≠ w → Disjoint (label v) (label w)) ∧
  (∀ r ∈ roots, ∃ v ∈ S, r ∈ label v)

def liftLabels {α : Type} [DecidableEq α] (A : Finset α) : Finset (Sum α Bool) :=
  A.image Sum.inl

def duplicateRoots {α : Type} [DecidableEq α] (roots A : Finset α) : Finset (Sum α Bool) :=
  liftLabels (roots \ A) ∪ {Sum.inr false, Sum.inr true}

def duplicateRaw {α : Type} (raw : α → Sig) (w : Sig) : Sum α Bool → Sig :=
  Sum.elim raw (fun _ => w)


theorem kept_append {α : Type} (save : Bool) (a : α) (xs ys : List α) :
    kept save a xs ++ ys = kept save a (xs ++ ys) := by
  cases save <;> rfl

theorem Run.substitute {R : Type} {u : Bool} {goal target : Wire R}
    {k l : Nat} {xs rest : List (Wire R)}
    (trace : Run u goal k xs) (tail : Run u target l (goal :: rest)) :
    Run u target (k + l) (xs ++ rest) := by
  induction k generalizing xs with
  | zero =>
    have perm : [goal].Perm xs := trace
    exact Run.perm (perm.append_right rest) (by simpa using tail)
  | succ k ih =>
    obtain ⟨op, ka, kb, a, b, mid, hd, perm, trace⟩ := trace
    have next := ih trace
    have next' : Run u target (k + l)
        (comb op a b :: kept ka a (kept kb b (mid ++ rest))) := by
      simpa only [List.cons_append, kept_append] using next
    have step := Run.two op hd ka kb next'
    have framed : Run u target (k + 1 + l) ((a :: b :: mid) ++ rest) := by
      simpa only [List.cons_append, Nat.add_right_comm] using step
    exact Run.perm (perm.append_right rest) framed

theorem Run.combine_traces {R : Type} {u : Bool} {a b : Wire R}
    {k l : Nat} {xs ys : List (Wire R)}
    (left : Run u a k xs) (right : Run u b l ys) (d : Nat) (hd : allowed u d) :
    Run u (comb d a b) (k + l + 1) (xs ++ ys) := by
  have finish : Run u (comb d a b) 1 [a, b] :=
    Run.two d hd false false (by simpa [kept] using (Run.stop (goal := comb d a b) (u := u)))
  have swap : ([a, b] : List (Wire R)).Perm [b, a] := List.Perm.swap _ _ _
  have reversed : Run u (comb d a b) 1 [b, a] := Run.perm swap finish
  have first : Run u (comb d a b) (l + 1) (ys ++ [a]) := Run.substitute right reversed
  have second : Run u (comb d a b) (l + 1) (a :: ys) :=
    Run.perm List.perm_append_comm first
  simpa only [Nat.add_assoc] using Run.substitute left second

def ReadOnce {α : Type} [DecidableEq α] (raw : α → Sig) (u : Bool)
    (A : Finset α) (v : Sig) : Prop :=
  A.Nonempty ∧ Run u (observe v) (A.card - 1) (A.toList.map (fun r => observe (raw r)))

theorem ReadOnce.leaf {α : Type} [DecidableEq α] (raw : α → Sig) (u : Bool) (r : α) :
    ReadOnce raw u {r} (raw r) := by
  have perm : [r].Perm ({r} : Finset α).toList := by
    apply List.perm_of_nodup_nodup_toFinset_eq (by simp) (Finset.nodup_toList _)
    simp
  refine ⟨by simp, ?_⟩
  simpa only [Finset.card_singleton, Nat.sub_self, List.map_cons, List.map_nil] using
    Run.perm (perm.map (fun q => observe (raw q))) (Run.stop (u := u) (goal := observe (raw r)))

theorem ReadOnce.combine {α : Type} [DecidableEq α] (raw : α → Sig) (u : Bool)
    {A B : Finset α} {a b : Sig} (left : ReadOnce raw u A a) (right : ReadOnce raw u B b)
    (disjoint : Disjoint A B) (d : Nat) (legal : allowed u d) :
    ReadOnce raw u (A ∪ B) (bin d a b) := by
  have nd : (A.toList ++ B.toList).Nodup := by
    simp only [List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, ?_⟩
    intro x hx y hy eq
    subst y
    exact Finset.disjoint_left.mp disjoint (Finset.mem_toList.mp hx) (Finset.mem_toList.mp hy)
  have perm : (A.toList ++ B.toList).Perm (A ∪ B).toList := by
    apply List.perm_of_nodup_nodup_toFinset_eq nd (Finset.nodup_toList _)
    simp
  have combined := Run.combine_traces left.2 right.2 d legal
  have lifted : (A.toList.map (fun r => observe (raw r)) ++
      B.toList.map (fun r => observe (raw r))).Perm
      ((A ∪ B).toList.map (fun r => observe (raw r))) := by
    simpa only [List.map_append] using perm.map (fun r => observe (raw r))
  have ordered := Run.perm lifted combined
  have count : (A ∪ B).card - 1 = A.card - 1 + (B.card - 1) + 1 := by
    rw [Finset.card_union_of_disjoint disjoint]
    have pa := Finset.card_pos.mpr left.1
    have pb := Finset.card_pos.mpr right.1
    omega
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := left.1
    exact ⟨r, Finset.mem_union_left _ hr⟩
  · simpa only [count, obs_bin] using ordered

theorem ReadOnce.map {α β : Type} [DecidableEq α] [DecidableEq β]
    (raw : α → Sig) (nextRaw : β → Sig) (u : Bool)
    (f : α → β) (injective : Function.Injective f)
    (same : ∀ r, nextRaw (f r) = raw r)
    {A : Finset α} {v : Sig} (trace : ReadOnce raw u A v) :
    ReadOnce nextRaw u (A.image f) v := by
  have nd : (A.toList.map f).Nodup := (Finset.nodup_toList A).map injective
  have perm : (A.toList.map f).Perm (A.image f).toList := by
    apply List.perm_of_nodup_nodup_toFinset_eq nd (Finset.nodup_toList _)
    ext r
    simp
  have count : (A.image f).card = A.card := by
    simpa using perm.length_eq.symm
  have mapped : (A.toList.map f).map (fun r => observe (nextRaw r)) =
      A.toList.map (fun r => observe (raw r)) := by
    simp only [List.map_map, Function.comp_def, same]
  have moved : Run u (observe v) (A.card - 1)
      ((A.toList.map f).map (fun r => observe (nextRaw r))) := by
    rw [mapped]
    exact trace.2
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := trace.1
    exact ⟨f r, Finset.mem_image_of_mem f hr⟩
  · rw [count]
    exact Run.perm (perm.map (fun r => observe (nextRaw r))) moved
theorem Run.substitute_list {R : Type} {u : Bool} {target : Wire R}
    (xs : List (Wire R)) (leaves : Wire R → List (Wire R)) (cost : Wire R → Nat)
    (traces : ∀ v ∈ xs, Run u v (cost v) (leaves v))
    {rest : List (Wire R)} {k : Nat} (tail : Run u target k (xs ++ rest)) :
    Run u target ((xs.map cost).sum + k) (xs.flatMap leaves ++ rest) := by
  induction xs generalizing rest k with
  | nil => simpa using tail
  | cons v xs ih =>
    have perm : ((v :: xs) ++ rest).Perm (xs ++ v :: rest) := by
      have small : ([v] ++ xs).Perm (xs ++ [v]) := List.perm_append_comm
      simpa only [List.cons_append, List.nil_append, List.append_assoc] using
        small.append_right rest
    have shifted := Run.perm perm tail
    have expanded := ih (fun w hw => traces w (List.mem_cons_of_mem v hw)) shifted
    have permBack : (xs.flatMap leaves ++ v :: rest).Perm
        (v :: (xs.flatMap leaves ++ rest)) := by
      have small : (xs.flatMap leaves ++ [v]).Perm ([v] ++ xs.flatMap leaves) :=
        List.perm_append_comm
      simpa only [List.cons_append, List.nil_append, List.append_assoc] using
        small.append_right rest
    have atHead := Run.perm permBack expanded
    have result := Run.substitute (traces v (by simp)) atHead
    simpa only [List.map_cons, List.sum_cons, List.flatMap_cons, List.append_assoc,
      Nat.add_assoc] using result
lemma partition_flatMap_perm {α : Type} [DecidableEq α]
    (roots : Finset α) (S : Finset Sig) (label : Sig → Finset α)
    (part : LabelPartition roots S label) :
    (S.toList.flatMap fun v => (label v).toList).Perm roots.toList := by
  have pair : List.Pairwise
      (fun v w => List.Disjoint (label v).toList (label w).toList) S.toList := by
    apply List.Pairwise.imp_of_mem _ (Finset.nodup_toList S)
    intro v w hv hw hne
    apply List.disjoint_left.mpr
    intro r hrv hrw
    exact Finset.disjoint_left.mp
      (part.2.1 v (Finset.mem_toList.mp hv) w (Finset.mem_toList.mp hw) hne)
      (Finset.mem_toList.mp hrv) (Finset.mem_toList.mp hrw)
  have nodup : (S.toList.flatMap fun v => (label v).toList).Nodup :=
    List.nodup_flatMap.mpr ⟨fun v _ => Finset.nodup_toList (label v), pair⟩
  apply (List.perm_ext_iff_of_nodup nodup (Finset.nodup_toList roots)).mpr
  intro r
  constructor
  · intro hr
    obtain ⟨v, hv, hrv⟩ := List.mem_flatMap.mp hr
    exact Finset.mem_toList.mpr
      (part.1 v (Finset.mem_toList.mp hv) (Finset.mem_toList.mp hrv))
  · intro hr
    obtain ⟨v, hv, hrv⟩ := part.2.2 r (Finset.mem_toList.mp hr)
    exact List.mem_flatMap.mpr
      ⟨v, Finset.mem_toList.mpr hv, Finset.mem_toList.mpr hrv⟩

lemma partition_cost_sum {α : Type} [DecidableEq α]
    (roots : Finset α) (S : Finset Sig) (label : Sig → Finset α)
    (part : LabelPartition roots S label)
    (nonempty : ∀ v ∈ S, (label v).Nonempty) :
    (S.toList.map fun v => (label v).card - 1).sum + S.card = roots.card := by
  have cardinal : (S.toList.map fun v => (label v).card).sum = roots.card := by
    simpa only [List.length_flatMap, Finset.length_toList] using
      (partition_flatMap_perm roots S label part).length_eq
  have sumIdentity (vs : List Sig) : (∀ v ∈ vs, v ∈ S) →
      (vs.map fun v => (label v).card - 1).sum + vs.length =
        (vs.map fun v => (label v).card).sum := by
    induction vs with
    | nil => intro _; simp
    | cons v vs ih =>
      intro hv
      have positive : 0 < (label v).card :=
        Finset.card_pos.mpr (nonempty v (hv v (by simp)))
      have tail := ih (fun w hw => hv w (List.mem_cons_of_mem v hw))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega
  have total := sumIdentity S.toList (fun v hv => Finset.mem_toList.mp hv)
  simpa only [Finset.length_toList] using total.trans cardinal
theorem readOnce_forest_run {α : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (u : Bool) (T : Sig)
    {k : Nat} {S : Finset Sig} (run : Live u T k S)
    (label : Sig → Finset α) (part : LabelPartition roots S label)
    (entries : ∀ v ∈ S, ReadOnce raw u (label v) v) :
    Run u (observe T) (k + roots.card - S.card)
      (roots.toList.map (fun r => observe (raw r))) := by
  classical
  let leaves (w : Wire Row) := (label (table w)).toList.map (fun r => observe (raw r))
  let cost (w : Wire Row) := (label (table w)).card - 1
  have traces : ∀ w ∈ S.toList.map observe, Run u w (cost w) (leaves w) := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    simpa only [cost, leaves, table_observe] using (entries v (Finset.mem_toList.mp hv)).2
  have trace := list_run run S.toList (Finset.nodup_toList S) (by simp)
  have expanded := Run.substitute_list (S.toList.map observe) leaves cost traces
    (rest := []) (by simpa only [List.append_nil] using trace)
  have flat : (S.toList.map observe).flatMap leaves =
      (S.toList.flatMap (fun v => (label v).toList)).map (fun r => observe (raw r)) := by
    simp only [List.flatMap_map, leaves, table_observe, List.map_flatMap]
  have expanded' : Run u (observe T)
      ((S.toList.map (fun v => (label v).card - 1)).sum + k)
      ((S.toList.flatMap (fun v => (label v).toList)).map (fun r => observe (raw r))) := by
    simpa only [List.append_nil, List.map_map, Function.comp_def, cost, table_observe, flat]
      using expanded
  have moved := Run.perm
    ((partition_flatMap_perm roots S label part).map (fun r => observe (raw r))) expanded'
  have count := partition_cost_sum roots S label part (fun v hv => (entries v hv).1)
  have costEq : (S.toList.map (fun v => (label v).card - 1)).sum + k =
      k + roots.card - S.card := by omega
  simpa only [costEq] using moved

theorem readOnce_forest_exclusion_state {α : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (u : Bool) (T : Sig) (depth : Nat)
    (blocked : ∀ n, n + 1 ≤ roots.card + depth →
      ¬ Run u (observe T) n (roots.toList.map (fun r => observe (raw r))))
    {k : Nat} {S : Finset Sig} (run : Live u T k S) (cap : k + 1 ≤ S.card + depth)
    (label : Sig → Finset α) (part : LabelPartition roots S label)
    (entries : ∀ v ∈ S, ReadOnce raw u (label v) v) : False := by
  have count := partition_cost_sum roots S label part (fun v hv => (entries v hv).1)
  exact blocked (k + roots.card - S.card) (by omega)
    (readOnce_forest_run roots raw u T run label part entries)
namespace State4Copy14

def rawValues : Array Sig := #[s1, s11, s3, s4, s5, s14, s6, s7, s8, s15, s9, s16]
def baseRaw (i : Fin 12) : Sig := rawValues.getD i.val zero
def roots : Finset (Sum (Fin 12) Bool) :=
  duplicateRoots (Finset.univ : Finset (Fin 12)) {5, 9, 11}
def raw : Sum (Fin 12) Bool → Sig := duplicateRaw baseRaw s20

def basisLabels : List (Sum (Fin 12) Bool) :=
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4,
   Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 10, Sum.inr false, Sum.inr true]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem forest_excluded {u : Bool} {k : Nat} {S : Finset Sig}
    (run : Live u graph k S) (cap : k + 1 ≤ S.card + 1)
    (label : Sig → Finset (Sum (Fin 12) Bool))
    (part : LabelPartition roots S label)
    (entries : ∀ v ∈ S, ReadOnce raw u (label v) v) : False := by
  apply readOnce_forest_exclusion_state roots raw u graph 1 ?_ run cap label part entries
  intro n hn trace
  have count : roots.card = 11 := by decide +kernel
  have noRun := excluded (u := u) (k := n) (by omega)
  have labelsEqual : basisLabels.toFinset = roots := by decide +kernel
  have distinct : basisLabels.Nodup := by decide +kernel
  have perm : roots.toList.Perm basisLabels := by
    apply List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList roots) distinct
    simpa using labelsEqual.symm
  have rawEqual : basisLabels.map raw = ws := by decide +kernel
  have observed : basisLabels.map (fun r => observe (raw r)) = ws.map observe := by
    simpa only [List.map_map, Function.comp_def] using congrArg (List.map observe) rawEqual
  have moved := Run.perm (perm.map (fun r => observe (raw r))) trace
  apply noRun
  simpa only [observed] using moved

end State4Copy14

end PEqualNP.Outside.L_meta_2373.Live1024
