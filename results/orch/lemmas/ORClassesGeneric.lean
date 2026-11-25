import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9502

variable {α : Type*} [DecidableEq α]

def Dep (F : (α → Bool) → Bool) (N : Finset α) : Prop :=
  ∀ x y : α → Bool, (∀ i ∈ N, x i = y i) → F x = F y

def ORClass (F : (α → Bool) → Bool) (S : Finset α) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ x : α → Bool,
    F (Function.update x a true) = F (Function.update x b true)

def classRest (S : Finset α) (t p q : α) : Finset α :=
  ((S.erase t).erase p).erase q

def classSub (F : (α → Bool) → Bool) (op : Bool → Bool → Bool)
    (t p q : α) : (α → Bool) → Bool :=
  fun x => F (Function.update x t (op (x p) (x q)))

lemma classRest_mem {S : Finset α} {t p q a : α} (ha : a ∈ classRest S t p q) :
    a ∈ S ∧ a ≠ t ∧ a ≠ p ∧ a ≠ q := by
  simpa only [classRest, Finset.mem_erase, and_assoc, and_left_comm, and_comm] using ha

lemma classSub_force (F : (α → Bool) → Bool) (op : Bool → Bool → Bool)
    (t p q a : α) (x : α → Bool) (hat : a ≠ t) (hap : a ≠ p) (haq : a ≠ q) :
    classSub F op t p q (Function.update x a true) =
      F (Function.update (Function.update x t (op (x p) (x q))) a true) := by
  simp only [classSub, Function.update_of_ne hap.symm, Function.update_of_ne haq.symm]
  rw [Function.update_comm hat]

lemma orClass_survive {F : (α → Bool) → Bool} {S : Finset α}
    (hclass : ORClass F S) (op : Bool → Bool → Bool) (t p q : α) :
    ORClass (classSub F op t p q) (classRest S t p q) := by
  intro a ha b hb x
  obtain ⟨ha, hat, hap, haq⟩ := classRest_mem ha
  obtain ⟨hb, hbt, hbp, hbq⟩ := classRest_mem hb
  rw [classSub_force F op t p q a x hat hap haq,
    classSub_force F op t p q b x hbt hbp hbq]
  exact hclass a ha b hb _

lemma orClass_empty (F : (α → Bool) → Bool) : ORClass F ∅ := by
  intro a ha
  simp only [Finset.notMem_empty] at ha

lemma orClass_singleton (F : (α → Bool) → Bool) (a : α) : ORClass F {a} := by
  intro b hb c hc x
  simp only [Finset.mem_singleton] at hb hc
  subst b
  subst c
  rfl

lemma orClass_subset {F : (α → Bool) → Bool} {S T : Finset α}
    (hclass : ORClass F S) (hTS : T ⊆ S) : ORClass F T := by
  exact fun a ha b hb => hclass a (hTS ha) b (hTS hb)

lemma class_ignore {F : (α → Bool) → Bool} {N : Finset α} (hd : Dep F N)
    {a : α} (ha : a ∉ N) (x : α → Bool) (v : Bool) :
    F (Function.update x a v) = F x := by
  apply hd
  intro i hi
  have hia : i ≠ a := by
    intro h
    subst i
    exact ha hi
  exact Function.update_of_ne hia v x

lemma class_or_force_old {F : (α → Bool) → Bool} {S : Finset α}
    (hclass : ORClass F S) {t p q a : α} (ht : t ∈ S)
    (ha : a ∈ classRest S t p q) (x : α → Bool) :
    classSub F (· || ·) t p q (Function.update x a true) =
      F (Function.update x t true) := by
  obtain ⟨ha, hat, hap, haq⟩ := classRest_mem ha
  rw [classSub_force F (· || ·) t p q a x hat hap haq, hclass a ha t ht]
  rw [Function.update_idem]

lemma class_or_force_left {F : (α → Bool) → Bool} {N : Finset α}
    (hd : Dep F N) {t p q : α} (hpt : p ≠ t) (hp : p ∉ N) (x : α → Bool) :
    classSub F (· || ·) t p q (Function.update x p true) =
      F (Function.update x t true) := by
  simp only [classSub, Function.update_self, Bool.true_or]
  rw [Function.update_comm hpt]
  exact class_ignore hd hp _ true

lemma class_or_force_right {F : (α → Bool) → Bool} {N : Finset α}
    (hd : Dep F N) {t p q : α} (hqt : q ≠ t) (hq : q ∉ N) (x : α → Bool) :
    classSub F (· || ·) t p q (Function.update x q true) =
      F (Function.update x t true) := by
  simp only [classSub, Function.update_self, Bool.or_true]
  rw [Function.update_comm hqt]
  exact class_ignore hd hq _ true

lemma orClass_or_inherit {F : (α → Bool) → Bool} {N S B : Finset α}
    (hd : Dep F N) (hclass : ORClass F S) {t p q : α} (ht : t ∈ S)
    (hB : ∀ b ∈ B, (b = p ∨ b = q) ∧ b ≠ t ∧ b ∉ N) :
    ORClass (classSub F (· || ·) t p q) (classRest S t p q ∪ B) := by
  have hforce : ∀ a ∈ classRest S t p q ∪ B, ∀ x : α → Bool,
      classSub F (· || ·) t p q (Function.update x a true) =
        F (Function.update x t true) := by
    intro a ha x
    rcases Finset.mem_union.mp ha with ha | ha
    · exact class_or_force_old hclass ht ha x
    · obtain ⟨ha, hat, haN⟩ := hB a ha
      rcases ha with rfl | rfl
      · exact class_or_force_left hd hat haN x
      · exact class_or_force_right hd hat haN x
  intro a ha b hb x
  exact (hforce a ha x).trans (hforce b hb x).symm

end PEqualNP.Outside.L_meta_9502
