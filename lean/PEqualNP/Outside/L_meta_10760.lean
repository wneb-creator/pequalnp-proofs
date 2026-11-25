import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10760

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

lemma compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

lemma live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

lemma live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

lemma first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

variable {width : Nat}

def ops (x y : BitVec width) : List (BitVec width) :=
  [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]

abbrev basicOps (a b : BitVec width) : Finset (BitVec width) := (ops a b).toFinset

def uniqueSep {width : Nat} (S : Finset (BitVec width)) (a : BitVec width)
    (p q : Fin width) : Prop :=
  a[p.val] ≠ a[q.val] ∧ ∀ w ∈ S, w ≠ a → w[p.val] = w[q.val]

def criticalPair {width : Nat} (target : BitVec width) (S : Finset (BitVec width))
    (a b : BitVec width) : Prop :=
  a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ ∃ p q ra rb sa sb : Fin width,
    target[p.val] = true ∧ target[q.val] = false ∧
    target[ra.val] = false ∧ target[rb.val] = false ∧
    target[sa.val] = true ∧ target[sb.val] = true ∧
    uniqueSep S a p ra ∧ uniqueSep S b p rb ∧
    uniqueSep S a sa q ∧ uniqueSep S b sb q ∧
    a[p.val] = a[sa.val] ∧ b[p.val] = b[sb.val]


lemma ops_equal_bits {width : Nat} {a b z : BitVec width} {p q : Fin width}
    (hz : z ∈ basicOps a b) (ha : a[p.val] = a[q.val])
    (hb : b[p.val] = b[q.val]) : z[p.val] = z[q.val] := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons,
    List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> simp [ha, hb]

lemma live_target_separates {width k : Nat} {target g : BitVec width}
    {S : Finset (BitVec width)} (run : live basicOps g k S)
    (hg : g = target ∨ g = ~~~target) {p q : Fin width}
    (different : target[p.val] ≠ target[q.val]) :
    ∃ w ∈ S, w[p.val] ≠ w[q.val] := by
  apply live_separates (fun w : BitVec width => w[p.val] ≠ w[q.val]) ?_ ?_ run
  · rcases hg with rfl | rfl
    · exact different
    · simpa using different
  · intro a b z hz hd
    by_cases ha : a[p.val] = a[q.val]
    · right
      intro hb
      exact hd (ops_equal_bits hz ha hb)
    · exact Or.inl ha

lemma uniqueSep_step {width k : Nat} {target g a b z c : BitVec width}
    {U : Finset (BitVec width)} {p q : Fin width}
    (hz : z ∈ basicOps a b) (run : live basicOps g k (insert z U))
    (hg : g = target ∨ g = ~~~target)
    (different : target[p.val] ≠ target[q.val])
    (ha : c = a → a ∉ U) (hb : c = b → b ∉ U)
    (hs : uniqueSep (insert a (insert b U)) c p q) :
    uniqueSep (insert z U) (if c = a ∨ c = b then z else c) p q := by
  by_cases hc : c = a ∨ c = b
  · rw [ite_eq_left hc]
    have hcU : c ∉ U := by
      rcases hc with rfl | rfl
      · exact ha rfl
      · exact hb rfl
    have hU : ∀ w ∈ U, w[p.val] = w[q.val] := by
      intro w hw
      apply hs.2 w (by simp [hw])
      intro eq
      exact hcU (eq ▸ hw)
    constructor
    · obtain ⟨w, hw, hd⟩ := live_target_separates run hg different
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hd
      · exact False.elim (hd (hU w hw))
    · intro w hw hne
      exact hU w ((Finset.mem_insert.mp hw).resolve_left hne)
  · rw [ite_eq_right hc]
    refine ⟨hs.1, ?_⟩
    intro w hw hne
    rcases Finset.mem_insert.mp hw with rfl | hw
    · apply ops_equal_bits hz
      · exact hs.2 a (by simp) (fun eq => hc (.inl eq.symm))
      · exact hs.2 b (by simp) (fun eq => hc (.inr eq.symm))
    · exact hs.2 w (by simp [hw]) hne

namespace ChromGate

def eval (d : Fin 4) (a b : Bool) : Bool :=
  match d.val with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | _ => b && !a

lemma left_transport : ∀ (d : Fin 4)
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Bool),
    b₀ = b₁ → b₂ = b₃ →
    eval d a₀ b₀ ≠ eval d a₁ b₁ →
    eval d a₂ b₂ ≠ eval d a₃ b₃ →
    a₀ = a₂ → eval d a₀ b₀ = eval d a₂ b₂ := by
  decide

lemma right_transport : ∀ (d : Fin 4)
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Bool),
    a₀ = a₁ → a₂ = a₃ →
    eval d a₀ b₀ ≠ eval d a₁ b₁ →
    eval d a₂ b₂ ≠ eval d a₃ b₃ →
    b₀ = b₂ → eval d a₀ b₀ = eval d a₂ b₂ := by
  decide

lemma rectangle_false : ∀ (d : Fin 4) (a b c e : Bool),
    eval d a b ≠ eval d c b →
    eval d a b ≠ eval d a e →
    eval d c e ≠ eval d a e →
    eval d c e ≠ eval d c b → False := by
  decide

lemma sensitive_corner_unique : ∀ (d : Fin 4) (a b c e : Bool),
    eval d a b ≠ eval d (!a) b →
    eval d a b ≠ eval d a (!b) →
    eval d c e ≠ eval d (!c) e →
    eval d c e ≠ eval d c (!e) → a = c ∧ b = e := by
  decide

lemma opposite_corners_false : ∀ (d : Fin 4) (a b : Bool),
    eval d a b ≠ eval d (!a) b →
    eval d a b ≠ eval d a (!b) →
    eval d (!a) (!b) ≠ eval d a (!b) →
    eval d (!a) (!b) ≠ eval d (!a) b → False := by
  decide

def word {width : Nat} (d : Fin 4) (a b : BitVec width) : BitVec width :=
  match d.val with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a &&& ~~~b
  | _ => b &&& ~~~a

lemma word_get {width : Nat} (d : Fin 4) (a b : BitVec width) (p : Fin width) :
    (word d a b)[p.val] = eval d a[p.val] b[p.val] := by
  fin_cases d <;> simp [word, eval]

lemma of_basicOps {width : Nat} {a b z : BitVec width}
    (hz : z ∈ basicOps a b) : ∃ d : Fin 4, z = word d a b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil,
    or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

end ChromGate

namespace ChromGeneric

variable {α : Type} [DecidableEq α]

lemma retained_card {a b z : α} {rest : Finset α}
    (hab : a ≠ b) (hz : z ∉ insert a (insert b rest)) :
    (insert a (insert b rest)).card +
        ((if a ∈ rest then 1 else 0) + (if b ∈ rest then 1 else 0)) =
      (insert z rest).card + 1 := by
  have hzr : z ∉ rest := fun h => hz (by simp [h])
  rw [Finset.card_insert_of_notMem hzr]
  by_cases ha : a ∈ rest <;> by_cases hb : b ∈ rest
  · simp [ha, hb]
  · have ha' : a ∈ insert b rest := by simp [ha]
    simp [Finset.insert_eq_of_mem ha', Finset.card_insert_of_notMem hb, ha, hb]
  · have ha' : a ∉ insert b rest := by simp [hab, ha]
    simp [Finset.card_insert_of_notMem ha', Finset.insert_eq_of_mem hb, ha, hb]
  · have ha' : a ∉ insert b rest := by simp [hab, ha]
    simp [Finset.card_insert_of_notMem ha', Finset.card_insert_of_notMem hb, ha, hb]

def collapse (a b z c : α) : α := if c = a ∨ c = b then z else c

lemma collapse_mem {a b z c : α} {rest : Finset α}
    (hc : c ∈ insert a (insert b rest)) :
    collapse a b z c ∈ insert z rest := by
  unfold collapse
  split_ifs with h
  · simp
  · simp only [Finset.mem_insert] at hc ⊢
    exact Or.inr ((hc.resolve_left (fun hca => h (Or.inl hca))).resolve_left
      (fun hcb => h (Or.inr hcb)))


lemma extend_coloring {edge : Finset α → α → α → Prop}
    (irrefl : ∀ S c, ¬ edge S c c)
    {a b z : α} {U : Finset α} (hab : a ≠ b)
    (hnew : z ∉ insert a (insert b U))
    (transport : ∀ c ∈ insert a (insert b U), ∀ d ∈ insert a (insert b U),
      edge (insert a (insert b U)) c d →
      (c = a → a ∉ U) → (c = b → b ∉ U) →
      (d = a → a ∉ U) → (d = b → b ∉ U) →
      edge (insert z U) (collapse a b z c) (collapse a b z d))
    {x : Nat} {f : α → Nat}
    (fbound : ∀ c ∈ insert z U, f c ≤ x)
    (fproper : ∀ c ∈ insert z U, ∀ d ∈ insert z U,
      edge (insert z U) c d → f c ≠ f d) :
    ∃ g : α → Nat,
      (∀ c ∈ insert a (insert b U),
        g c ≤ x + ((if a ∈ U then 1 else 0) + (if b ∈ U then 1 else 0))) ∧
      ∀ c ∈ insert a (insert b U), ∀ d ∈ insert a (insert b U),
        edge (insert a (insert b U)) c d → g c ≠ g d := by
  let base : α → Nat := fun c => f (collapse a b z c)
  have hbase : ∀ c ∈ insert a (insert b U), base c ≤ x := by
    intro c hc
    exact fbound _ (collapse_mem hc)
  have hproper : ∀ c ∈ insert a (insert b U), ∀ d ∈ insert a (insert b U),
      edge (insert a (insert b U)) c d →
      ¬ (c = a ∧ a ∈ U) → ¬ (c = b ∧ b ∈ U) →
      ¬ (d = a ∧ a ∈ U) → ¬ (d = b ∧ b ∈ U) → base c ≠ base d := by
    intro c hc d hd he hca hcb hda hdb
    apply fproper _ (collapse_mem hc) _ (collapse_mem hd)
    apply transport c hc d hd he
    · intro h hmem; exact hca ⟨h, hmem⟩
    · intro h hmem; exact hcb ⟨h, hmem⟩
    · intro h hmem; exact hda ⟨h, hmem⟩
    · intro h hmem; exact hdb ⟨h, hmem⟩
  let g : α → Nat := fun c =>
    if c = a ∧ a ∈ U then x + 1
    else if c = b ∧ b ∈ U then x + 1 + (if a ∈ U then 1 else 0)
    else base c
  refine ⟨g, ?_, ?_⟩
  · intro c hc
    have hh := hbase c hc
    dsimp only [g]
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U
    all_goals simp only [ha, hb, and_true, and_false, ite_true, ite_false]
    all_goals first | omega | (split_ifs <;> omega)
  · intro c hc d hd he heq
    have hcBound := hbase c hc
    have hdBound := hbase d hd
    have hcd : c ≠ d := by
      intro h
      subst d
      exact irrefl _ _ he
    by_cases hca : c = a ∧ a ∈ U
    · by_cases hda : d = a ∧ a ∈ U
      · exact hcd (hca.1.trans hda.1.symm)
      · by_cases hdb : d = b ∧ b ∈ U
        · simp only [g, ite_eq_left hca, ite_eq_right hda, ite_eq_left hdb, ite_eq_left hca.2] at heq
          omega
        · simp only [g, ite_eq_left hca, ite_eq_right hda, ite_eq_right hdb] at heq
          omega
    · by_cases hcb : c = b ∧ b ∈ U
      · by_cases hda : d = a ∧ a ∈ U
        · simp only [g, ite_eq_right hca, ite_eq_left hcb, ite_eq_left hda, ite_eq_left hda.2] at heq
          omega
        · by_cases hdb : d = b ∧ b ∈ U
          · exact hcd (hcb.1.trans hdb.1.symm)
          · simp only [g, ite_eq_right hca, ite_eq_left hcb, ite_eq_right hda, ite_eq_right hdb] at heq
            split_ifs at heq <;> omega
      · by_cases hda : d = a ∧ a ∈ U
        · simp only [g, ite_eq_right hca, ite_eq_right hcb, ite_eq_left hda] at heq
          omega
        · by_cases hdb : d = b ∧ b ∈ U
          · simp only [g, ite_eq_right hca, ite_eq_right hcb, ite_eq_right hda, ite_eq_left hdb] at heq
            split_ifs at heq <;> omega
          · exact hproper c hc d hd he hca hcb hda hdb
              (by simpa only [g, ite_eq_right hca, ite_eq_right hcb, ite_eq_right hda, ite_eq_right hdb] using heq)

lemma live_coloring {ops : α → α → Finset α} {goal : α}
    (edge : Finset α → α → α → Prop)
    (irrefl : ∀ S c, ¬ edge S c c)
    (transport : ∀ (k : Nat) (a b z : α) (U : Finset α),
      a ≠ b → z ∉ insert a (insert b U) → z ∈ ops a b →
      live ops goal k (insert z U) →
      ∀ c ∈ insert a (insert b U), ∀ d ∈ insert a (insert b U),
      edge (insert a (insert b U)) c d →
      (c = a → a ∉ U) → (c = b → b ∉ U) →
      (d = a → a ∉ U) → (d = b → b ∉ U) →
      edge (insert z U) (collapse a b z c) (collapse a b z d))
    {k : Nat} {S : Finset α} (hlive : live ops goal k S) :
    ∃ x : Nat, ∃ f : α → Nat, S.card + x ≤ k + 1 ∧
      (∀ c ∈ S, f c ≤ x) ∧
      ∀ c ∈ S, ∀ d ∈ S, edge S c d → f c ≠ f d := by
  induction k generalizing S with
  | zero =>
    change S = {goal} at hlive
    subst S
    refine ⟨0, fun _ => 0, by simp, by simp, ?_⟩
    intro c hc d hd he
    simp only [Finset.mem_singleton] at hc hd
    subst c
    subst d
    exact False.elim (irrefl _ _ he)
  | succ k ih =>
    rcases hlive with hskip | ⟨a, ha, b, hb, hab, z, hz, hnew, U, rfl, htail⟩
    · obtain ⟨x, f, hcard, hbound, hproper⟩ := ih hskip
      exact ⟨x, f, by omega, hbound, hproper⟩
    · obtain ⟨x, f, hcard, hbound, hproper⟩ := ih htail
      obtain ⟨g, gbound, gproper⟩ := extend_coloring irrefl hab hnew
        (transport k a b z U hab hnew hz htail) hbound hproper
      refine ⟨x + ((if a ∈ U then 1 else 0) + (if b ∈ U then 1 else 0)),
        g, ?_, gbound, gproper⟩
      have hcount := retained_card hab hnew
      omega

end ChromGeneric

namespace ChromRelation

variable {width : Nat}

def moved (a b z c : BitVec width) : BitVec width :=
  if c = a ∨ c = b then z else c

lemma moved_mem {a b z c : BitVec width} {U : Finset (BitVec width)}
    (hc : c ∈ insert a (insert b U)) : moved a b z c ∈ insert z U := by
  unfold moved
  split_ifs with h
  · exact Finset.mem_insert_self ..
  · rcases Finset.mem_insert.mp hc with rfl | hc
    · exact False.elim (h (.inl rfl))
    · rcases Finset.mem_insert.mp hc with rfl | hc
      · exact False.elim (h (.inr rfl))
      · exact Finset.mem_insert_of_mem hc

lemma moved_ne {a b z c d : BitVec width} {U : Finset (BitVec width)}
    (hc : c ∈ insert a (insert b U)) (hd : d ∈ insert a (insert b U))
    (hz : z ∉ insert a (insert b U)) (hne : c ≠ d)
    (notboth : ¬ ((c = a ∨ c = b) ∧ (d = a ∨ d = b))) :
    moved a b z c ≠ moved a b z d := by
  unfold moved
  split_ifs with h₁ h₂ h₂
  · exact False.elim (notboth ⟨h₁, h₂⟩)
  · intro eq
    exact hz (eq ▸ hd)
  · intro eq
    exact hz (eq ▸ hc)
  · exact hne

lemma criticalPair_symm {target : BitVec width} {S : Finset (BitVec width)}
    {a b : BitVec width} (h : criticalPair target S a b) : criticalPair target S b a := by
  obtain ⟨ha, hb, hab, p, q, ra, rb, sa, sb, hp, hq, hra, hrb, hsa, hsb,
    u₁, u₂, u₃, u₄, phase₁, phase₂⟩ := h
  exact ⟨hb, ha, hab.symm, p, q, rb, ra, sb, sa, hp, hq, hrb, hra, hsb, hsa,
    u₂, u₁, u₄, u₃, phase₂, phase₁⟩

lemma bool_other_eq {x y z : Bool} (hy : x ≠ y) (hz : x ≠ z) : y = z := by
  cases x <;> cases y <;> cases z <;> simp_all

lemma moved_phase {a b z c : BitVec width} {U : Finset (BitVec width)}
    {p r s q : Fin width} (hab : a ≠ b) (hz : z ∈ basicOps a b)
    (u₁ : uniqueSep (insert a (insert b U)) c p r)
    (u₂ : uniqueSep (insert a (insert b U)) c s q)
    (v₁ : uniqueSep (insert z U) (moved a b z c) p r)
    (v₂ : uniqueSep (insert z U) (moved a b z c) s q)
    (phase : c[p.val] = c[s.val]) :
    (moved a b z c)[p.val] = (moved a b z c)[s.val] := by
  by_cases hc : c = a ∨ c = b
  · simp only [moved, ite_eq_left hc] at v₁ v₂ ⊢
    obtain ⟨d, rfl⟩ := ChromGate.of_basicOps hz
    rcases hc with rfl | rfl
    · have e₁ := u₁.2 b (by simp) hab.symm
      have e₂ := u₂.2 b (by simp) hab.symm
      have d₁ := v₁.1
      have d₂ := v₂.1
      simp only [ChromGate.word_get] at d₁ d₂ ⊢
      exact ChromGate.left_transport d _ _ _ _ _ _ _ _ e₁ e₂ d₁ d₂ phase
    · have e₁ := u₁.2 a (by simp) hab
      have e₂ := u₂.2 a (by simp) hab
      have d₁ := v₁.1
      have d₂ := v₂.1
      simp only [ChromGate.word_get] at d₁ d₂ ⊢
      exact ChromGate.right_transport d _ _ _ _ _ _ _ _ e₁ e₂ d₁ d₂ phase
  · simpa only [moved, ite_eq_right hc] using phase

lemma criticalPair_noCollapse {k : Nat} {target g a b z : BitVec width}
    {U : Finset (BitVec width)} (hz : z ∈ basicOps a b)
    (run : live basicOps g k (insert z U)) (hg : g = target ∨ g = ~~~target)
    (ha : a ∉ U) (hb : b ∉ U)
    (h : criticalPair target (insert a (insert b U)) a b) : False := by
  obtain ⟨_, _, hab, p, q, ra, rb, sa, sb, hp, hq, hra, hrb, hsa, hsb,
    u₁, u₂, u₃, u₄, phase₁, phase₂⟩ := h
  have v₁ : z[p.val] ≠ z[ra.val] := by
    simpa using (uniqueSep_step hz run hg (by simp [hp, hra])
      (fun _ => ha) (fun _ => hb) u₁).1
  have v₂ : z[p.val] ≠ z[rb.val] := by
    simpa using (uniqueSep_step hz run hg (by simp [hp, hrb])
      (fun _ => ha) (fun _ => hb) u₂).1
  have v₃ : z[sa.val] ≠ z[q.val] := by
    simpa using (uniqueSep_step hz run hg (by simp [hsa, hq])
      (fun _ => ha) (fun _ => hb) u₃).1
  have v₄ : z[sb.val] ≠ z[q.val] := by
    simpa using (uniqueSep_step hz run hg (by simp [hsb, hq])
      (fun _ => ha) (fun _ => hb) u₄).1
  have ara : a[ra.val] = a[q.val] := bool_other_eq u₁.1 (phase₁ ▸ u₃.1)
  have brb : b[rb.val] = b[q.val] := bool_other_eq u₂.1 (phase₂ ▸ u₄.1)
  have bra := u₁.2 b (by simp) hab.symm
  have arb := u₂.2 a (by simp) hab
  have bsa := u₃.2 b (by simp) hab.symm
  have asb := u₄.2 a (by simp) hab
  obtain ⟨d, hzword⟩ := ChromGate.of_basicOps hz
  have d₁ : ChromGate.eval d a[p.val] b[p.val] ≠ ChromGate.eval d a[q.val] b[p.val] := by
    simpa only [hzword, ChromGate.word_get, ara, ← bra] using v₁
  have d₂ : ChromGate.eval d a[p.val] b[p.val] ≠ ChromGate.eval d a[p.val] b[q.val] := by
    simpa only [hzword, ChromGate.word_get, brb, ← arb] using v₂
  have d₃ : ChromGate.eval d a[q.val] b[q.val] ≠ ChromGate.eval d a[p.val] b[q.val] := by
    simpa only [hzword, ChromGate.word_get, ← phase₁, bsa] using v₃.symm
  have d₄ : ChromGate.eval d a[q.val] b[q.val] ≠ ChromGate.eval d a[q.val] b[p.val] := by
    simpa only [hzword, ChromGate.word_get, ← phase₂, asb] using v₄.symm
  exact ChromGate.rectangle_false d _ _ _ _ d₁ d₂ d₃ d₄

lemma criticalPair_step {k : Nat} {target g a b z c d : BitVec width}
    {U : Finset (BitVec width)} (hab : a ≠ b) (hz : z ∈ basicOps a b)
    (fresh : z ∉ insert a (insert b U))
    (run : live basicOps g k (insert z U)) (hg : g = target ∨ g = ~~~target)
    (hca : c = a → a ∉ U) (hcb : c = b → b ∉ U)
    (hda : d = a → a ∉ U) (hdb : d = b → b ∉ U)
    (h : criticalPair target (insert a (insert b U)) c d) :
    criticalPair target (insert z U)
      (if c = a ∨ c = b then z else c) (if d = a ∨ d = b then z else d) := by
  have notboth : ¬ ((c = a ∨ c = b) ∧ (d = a ∨ d = b)) := by
    rintro ⟨hc, hd⟩
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
    · exact h.2.2.1 rfl
    · exact criticalPair_noCollapse hz run hg (hca rfl) (hdb rfl) h
    · exact criticalPair_noCollapse hz run hg (hda rfl) (hcb rfl) (criticalPair_symm h)
    · exact h.2.2.1 rfl
  obtain ⟨hc, hd, hcd, p, q, ra, rb, sa, sb, hp, hq, hra, hrb, hsa, hsb,
    u₁, u₂, u₃, u₄, phase₁, phase₂⟩ := h
  have v₁ := uniqueSep_step hz run hg (by simp [hp, hra]) hca hcb u₁
  have v₂ := uniqueSep_step hz run hg (by simp [hp, hrb]) hda hdb u₂
  have v₃ := uniqueSep_step hz run hg (by simp [hsa, hq]) hca hcb u₃
  have v₄ := uniqueSep_step hz run hg (by simp [hsb, hq]) hda hdb u₄
  change criticalPair target (insert z U) (moved a b z c) (moved a b z d)
  exact ⟨moved_mem hc, moved_mem hd, moved_ne hc hd fresh hcd notboth,
    p, q, ra, rb, sa, sb, hp, hq, hra, hrb, hsa, hsb, v₁, v₂, v₃, v₄,
    moved_phase hab hz u₁ u₃ v₁ v₃ phase₁,
    moved_phase hab hz u₂ u₄ v₂ v₄ phase₂⟩

end ChromRelation

lemma live_criticalPair_coloring {width k : Nat} {target g : BitVec width}
    {S : Finset (BitVec width)} (run : live basicOps g k S)
    (hg : g = target ∨ g = ~~~target) :
    ∃ color : BitVec width → Nat,
      (∀ a ∈ S, color a < k + 2 - S.card) ∧
      ∀ a b, criticalPair target S a b → color a ≠ color b := by
  have irrefl : ∀ U c, ¬ criticalPair target U c c := by
    intro U c h
    exact h.2.2.1 rfl
  obtain ⟨x, color, hcard, hbound, hproper⟩ :=
    ChromGeneric.live_coloring (criticalPair target) irrefl
      (by
        intro n a b z U hab fresh hz tail c hc d hd edge hca hcb hda hdb
        exact ChromRelation.criticalPair_step hab hz fresh tail hg
          hca hcb hda hdb edge) run
  refine ⟨color, ?_, ?_⟩
  · intro a ha
    have := hbound a ha
    omega
  · intro a b edge
    exact hproper a edge.1 b edge.2.1 edge

open PEqualNP.CircuitLowerBounds

def holds (av : Finset (BitVec width)) (z : (BitVec width)) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

lemma holds_insert {av : Finset (BitVec width)} {z a : (BitVec width)} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

lemma holds_not {av : Finset (BitVec width)} {z : (BitVec width)} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset (BitVec width)) (z : (BitVec width)) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

lemma reachable_not {av : Finset (BitVec width)} {z : (BitVec width)} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
lemma and_reach {av : Finset (BitVec width)} {x y : (BitVec width)} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : (BitVec width)) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : (BitVec width)) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · have he : (~~~(0 : BitVec width)) &&& y = y := by
      apply BitVec.eq_of_getLsbD_eq
      intro i
      simp
    rw [he]
    exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : (BitVec width)) = 0 from BitVec.and_zero]; exact .inl const
  · have he : x &&& ~~~(0 : BitVec width) = x := by
      apply BitVec.eq_of_getLsbD_eq
      intro i
      simp
    rw [he]
    exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : (BitVec width)) (hw : w ∈ basicOps a b) (z : (BitVec width)) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

lemma or_reach {av : Finset (BitVec width)} {x y : (BitVec width)} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin width) (z : (BitVec width)) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma read_bit (w : List (BitVec width)) (i : ℕ) (k : Fin width) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List (BitVec width)) (g : Gate) : (BitVec width) := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

lemma evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
lemma evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
lemma evalNot (xs : List Bool) : GateOp.not.eval xs = !(xs.headD false) := rfl

set_option maxRecDepth 5000 in
lemma action_spec (w : List (BitVec width)) (g : Gate) (hg : legal g) (k : Fin width) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : (BitVec width))[k.val] = false := by change (0 : BitVec width)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, evalAnd, evalOr, evalNot, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      BitVec.getElem_zero,bit0,Bool.not_false] <;> rfl

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

lemma available_read {av : Finset (BitVec width)} {w : List (BitVec width)} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
lemma gate_reach (w : List (BitVec width)) (av : Finset (BitVec width)) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : (BitVec width), x ||| (0 : (BitVec width)) = x from fun x => BitVec.or_zero,
    show ∀ x : (BitVec width), x &&& ~~~0 = x from fun x => by simp]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
lemma compile {goal : BitVec width} (nonzero : goal ≠ 0) (nonones : goal ≠ ~~~0) (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List (BitVec width)) (av : Finset (BitVec width)) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim (nonzero zero)
    · exact False.elim (nonones ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset (BitVec width)) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

lemma bound_from_samples {inputCount budget : Nat} {goal : BitVec width}
    (nonzero : goal ≠ 0) (nonones : goal ≠ ~~~0)
    (target : (Fin inputCount → Bool) → Bool) (ins : List (BitVec width))
    (roots : Finset (BitVec width)) (represented : ∀ u ∈ ins, holds roots u)
    (inputLength : ins.length = inputCount)
    (row : ∀ j : Fin width,
      target (fun i => (ins.getD i.val 0)[j.val]) = goal[j.val])
    (rejection : ∀ z, z = goal ∨ z = ~~~goal →
      ¬ build basicOps z budget roots)
    (gs : List Gate) (out : Nat) (legalGates : ∀ g ∈ gs, legal g)
    (computes : ∀ x : Fin inputCount → Bool,
      Circuit.eval ⟨gs, out⟩ (List.ofFn x) = target x) :
    budget < binaryCost gs := by
  by_contra! low
  have evaluate (k : Fin width) :
      (gs.foldl step (ins.map (bit k))).getD out false = bit k goal := by
    let x (i : Fin inputCount) : Bool := bit k (ins.getD i.val 0)
    have same : List.ofFn x = ins.map (bit k) := by
      apply List.ext_getElem
      · simp [inputLength]
      · intro i hi hj
        have hlt : i < ins.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, out⟩ (ins.map (bit k)) = bit k goal
    rw [← same, computes]
    exact row k
  obtain ⟨z, hz, run⟩ := compile nonzero nonones gs out legalGates ins roots
    represented evaluate
  have lift {a b : Nat} (h : a ≤ b) (hr : build basicOps z a roots) :
      build basicOps z b roots := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact rejection z hz (lift low run)

lemma replace_from_samples {inputCount replacementSize : Nat} {goal : BitVec width}
    (nonzero : goal ≠ 0) (nonones : goal ≠ ~~~0)
    (target : (Fin inputCount → Bool) → Bool) (ins : List (BitVec width))
    (roots : Finset (BitVec width)) (represented : ∀ u ∈ ins, holds roots u)
    (inputLength : ins.length = inputCount)
    (row : ∀ j : Fin width,
      target (fun i => (ins.getD i.val 0)[j.val]) = goal[j.val])
    (rejection : ∀ z, z = goal ∨ z = ~~~goal →
      ¬ build basicOps z (replacementSize - 2) roots)
    (upper : ∃ (gs : List Gate) (out : Nat),
      (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs.length = replacementSize ∧
      ∀ x : Fin inputCount → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) = target x)
    (gs : List Gate) (out : Nat) (legalGates : ∀ g ∈ gs, legal g)
    (computes : ∀ x : Fin inputCount → Bool,
      Circuit.eval ⟨gs, out⟩ (List.ofFn x) = target x) :
    ∃ (ds : List Gate) (newOut : Nat),
      (∀ g ∈ ds, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      ds.length ≤ gs.length ∧
      ∀ x : Fin inputCount → Bool, Circuit.eval ⟨ds, newOut⟩ (List.ofFn x) = target x := by
  by_cases present : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g, member, op⟩ := present
    have cut : binaryCost gs < gs.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, member, by simp [isBinary, op]⟩
    have lower := bound_from_samples nonzero nonones target ins roots represented inputLength row rejection
      gs out legalGates computes
    obtain ⟨ds, newOut, ok, size, evaluates⟩ := upper
    exact ⟨ds, newOut, ok, by omega, evaluates⟩
  · refine ⟨gs, out, ?_, le_rfl, computes⟩
    intro g member
    obtain ⟨op, arity⟩ := legalGates g member
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr
      (fun eq => (present ⟨g, member, eq⟩).elim)), arity⟩

end PEqualNP.Outside.L_meta_10760

namespace PEqualNP.Outside.L_meta_10760

lemma live_zero_free {width k : Nat} {g : BitVec width} {S : Finset (BitVec width)}
    (hg : g ≠ 0) (run : live basicOps g k S) : (0 : BitVec width) ∉ S := by
  induction k generalizing S with
  | zero =>
    change S = {g} at run
    intro hz
    rw [run, Finset.mem_singleton] at hz
    exact hg hz.symm
  | succ k ih =>
    rcases run with skip | ⟨a, ha, b, hb, hab, z, hz, fresh, rest, rfl, tail⟩
    · exact ih skip
    · have hrest : (0 : BitVec width) ∉ rest := by
        intro h
        exact ih tail (Finset.mem_insert_of_mem h)
      intro h
      simp only [Finset.mem_insert] at h
      rcases h with h | h | h
      · subst a
        simp only [basicOps, ops, List.mem_toFinset, List.mem_cons,
          List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl <;> exact fresh (by simp)
      · subst b
        simp only [basicOps, ops, List.mem_toFinset, List.mem_cons,
          List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl <;> exact fresh (by simp)
      · exact hrest h

end PEqualNP.Outside.L_meta_10760


namespace PEqualNP.Outside.L_meta_10760

open PEqualNP.CircuitLowerBounds

def edgeFunction (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6)

def monotoneWitness : List Gate :=
  [
    ⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [3, 5]⟩,
    ⟨GateOp.or, [7, 8]⟩,
    ⟨GateOp.and, [6, 9]⟩,
    ⟨GateOp.or, [1, 5]⟩,
    ⟨GateOp.and, [3, 11]⟩,
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [13, 14]⟩,
    ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.and, [2, 16]⟩,
    ⟨GateOp.or, [10, 12]⟩,
    ⟨GateOp.or, [15, 17]⟩,
    ⟨GateOp.or, [18, 19]⟩
  ]

lemma witness_size : monotoneWitness.length = 14 := rfl

lemma witness_allowed : ∀ g ∈ monotoneWitness,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [monotoneWitness]

set_option maxHeartbeats 2000000 in
lemma witness_eval : ∀ x : Fin 7 → Bool,
    Circuit.eval ⟨monotoneWitness, 20⟩ (List.ofFn x) = edgeFunction x := by
  decide +kernel

set_option maxHeartbeats 2000000 in
lemma edgeFunction_posted : ∀ x : Fin 7 → Bool,
    decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) = edgeFunction x := by
  decide +kernel


def pairInput (i j : Fin 7) : Fin 7 → Bool :=
  fun k => decide (k = i ∨ k = j)

set_option maxHeartbeats 8000000 in
lemma positive_pair : ∀ x : Fin 7 → Bool, edgeFunction x = true →
    ∃ i j : Fin 7, i ≠ j ∧ pairInput i j ≤ x ∧ edgeFunction (pairInput i j) = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
lemma negative_pair : ∀ x : Fin 7 → Bool, edgeFunction x = false →
    ∃ i j : Fin 7, i ≠ j ∧ x ≤ pairInput i j ∧ edgeFunction (pairInput i j) = false := by
  decide +kernel

lemma pair_table_suffices (g : (Fin 7 → Bool) → Bool) (hg : Monotone g)
    (hpair : ∀ i j : Fin 7, i ≠ j → g (pairInput i j) = edgeFunction (pairInput i j)) :
    ∀ x : Fin 7 → Bool, g x = edgeFunction x := by
  intro x
  cases hx : edgeFunction x with
  | false =>
    obtain ⟨i, j, hij, hle, hf⟩ := negative_pair x hx
    have h := hg hle
    rw [hpair i j hij, hf] at h
    exact Bool.eq_false_of_le_false h
  | true =>
    obtain ⟨i, j, hij, hle, hf⟩ := positive_pair x hx
    have h := hg hle
    rw [hpair i j hij, hf] at h
    exact Bool.eq_true_of_true_le h

end PEqualNP.Outside.L_meta_10760

namespace PEqualNP.Outside.L_meta_10760

open PEqualNP.CircuitLowerBounds

def sampleInputs : List (BitVec 128) := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000]

def sampleGoal : BitVec 128 := 0xfffffffffffefffafffeffeefefeeca0

def signedRoots : Finset (BitVec 128) := (sampleInputs.map (fun w => ~~~w)).toFinset

lemma sample_represented : ∀ u ∈ sampleInputs, holds signedRoots u := by
  intro u hu
  refine Or.inr (Or.inr ⟨~~~u, ?_, Or.inr ?_⟩)
  · exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨u, hu, rfl⟩)
  · exact BitVec.not_not.symm

set_option maxHeartbeats 2000000 in
lemma sample_rows : ∀ j : Fin 128,
    edgeFunction (fun i => (sampleInputs.getD i.val 0)[j.val]) = sampleGoal[j.val] := by
  decide +kernel

set_option maxHeartbeats 2000000 in
lemma gap_of_rejection
    (reject : ∀ z, z = sampleGoal ∨ z = ~~~sampleGoal →
      ¬ build basicOps z 12 signedRoots) :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hg _ hf
  obtain ⟨ds, out, ok, len, ev⟩ := replace_from_samples
    (replacementSize := 14) (goal := sampleGoal)
    (by decide +kernel) (by decide +kernel) edgeFunction sampleInputs signedRoots
    sample_represented rfl sample_rows reject
    ⟨monotoneWitness, 20, witness_allowed, witness_size, witness_eval⟩
    gates o hg (fun x => (hf x).trans (edgeFunction_posted x))
  exact ⟨ds, out, ok, len, fun x => (ev x).trans (edgeFunction_posted x).symm⟩

end PEqualNP.Outside.L_meta_10760


namespace PEqualNP.Outside.L_meta_10760

def firstRoot (i : Fin 7) : BitVec 128 := ~~~(sampleInputs.getD i.val 0)

def firstOp (i j : Fin 7) (o : Fin 4) : BitVec 128 :=
  (ops (firstRoot i) (firstRoot j)).getD o.val 0

def collisionData : List Nat := [0, 0, 0, 0, 775, 517, 517, 775, 517, 2065, 2065, 517, 1549, 517, 517, 1549, 2065, 517, 517, 2065, 4129, 517, 517, 4129, 8257, 517, 517, 8257, 1163, 1034, 1034, 1163, 0, 0, 0, 0, 1550, 1034, 1034, 1550, 1034, 2066, 2066, 1034, 2066, 1034, 1034, 2066, 4130, 1034, 1034, 4130, 10322, 1034, 1034, 10322, 133, 2068, 2068, 133, 391, 133, 133, 391, 0, 0, 0, 0, 1165, 133, 133, 1165, 2068, 133, 133, 2068, 6196, 133, 133, 6196, 8260, 133, 133, 8260, 395, 266, 266, 395, 266, 4136, 4136, 266, 782, 266, 266, 782, 0, 0, 0, 0, 6200, 266, 266, 6200, 4136, 266, 266, 4136, 8264, 266, 266, 8264, 145, 274, 274, 145, 274, 145, 145, 274, 532, 145, 145, 532, 1177, 145, 145, 1177, 0, 0, 0, 0, 4660, 145, 145, 4660, 8530, 145, 145, 8530, 161, 290, 290, 161, 290, 161, 161, 290, 806, 161, 161, 806, 1064, 161, 161, 1064, 3128, 161, 161, 3128, 0, 0, 0, 0, 8288, 161, 161, 8288, 193, 580, 580, 193, 451, 193, 193, 451, 580, 193, 193, 580, 1096, 193, 193, 1096, 3160, 193, 193, 3160, 4192, 193, 193, 4192, 0, 0, 0, 0]

def collisionPos (i j : Fin 7) (o : Fin 4) : Fin 128 :=
  ⟨(collisionData.getD ((i.val * 7 + j.val) * 4 + o.val) 0) % 128, Nat.mod_lt _ (by decide)⟩

def collisionNeg (i j : Fin 7) (o : Fin 4) : Fin 128 :=
  ⟨(collisionData.getD ((i.val * 7 + j.val) * 4 + o.val) 0 / 128) % 128, Nat.mod_lt _ (by decide)⟩

set_option maxHeartbeats 8000000 in
lemma first_collision : ∀ i j : Fin 7, ∀ o : Fin 4, i ≠ j →
    sampleGoal[(collisionPos i j o).val] ≠ sampleGoal[(collisionNeg i j o).val] ∧
    (firstOp i j o)[(collisionPos i j o).val] = (firstOp i j o)[(collisionNeg i j o).val] ∧
    ∀ k : Fin 7, k ≠ i →
      (firstRoot k)[(collisionPos i j o).val] = (firstRoot k)[(collisionNeg i j o).val] := by
  decide +kernel

lemma first_roots_eq : signedRoots = Finset.univ.image firstRoot := by
  decide +kernel

lemma first_mem {u : BitVec 128} (hu : u ∈ signedRoots) : ∃ i : Fin 7, u = firstRoot i := by
  rw [first_roots_eq] at hu
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hu
  exact ⟨i, hi.symm⟩

lemma first_op_mem {i j : Fin 7} {z : BitVec 128}
    (hz : z ∈ basicOps (firstRoot i) (firstRoot j)) : ∃ o : Fin 4, z = firstOp i j o := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

lemma first_bit_congr {width : Nat} {a b z : BitVec width} (i j : Fin width)
    (hz : z ∈ basicOps a b) (ha : a[i.val] = a[j.val]) (hb : b[i.val] = b[j.val]) :
    z[i.val] = z[j.val] := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, ha, hb]

lemma first_live_separates {width : Nat} {goal : BitVec width} {k : Nat}
    {s : Finset (BitVec width)} (i j : Fin width) (hd : goal[i.val] ≠ goal[j.val])
    (hl : live basicOps goal k s) : ∃ w ∈ s, w[i.val] ≠ w[j.val] := by
  apply live_separates (fun w => w[i.val] ≠ w[j.val]) hd _ hl
  intro a b z hz hne
  by_contra hn
  simp only [not_or, not_not] at hn
  exact hne (first_bit_congr i j hz hn.1 hn.2)

lemma first_drop_collision {a b z : BitVec 128}
    (ha : a ∈ signedRoots) (hb : b ∈ signedRoots) (hne : a ≠ b)
    (hz : z ∈ basicOps a b) :
    ∃ i j : Fin 128, sampleGoal[i.val] ≠ sampleGoal[j.val] ∧
      ∀ w ∈ insert z (signedRoots.erase a), w[i.val] = w[j.val] := by
  obtain ⟨i, rfl⟩ := first_mem ha
  obtain ⟨j, rfl⟩ := first_mem hb
  obtain ⟨o, rfl⟩ := first_op_mem hz
  obtain ⟨hg, ho, hw⟩ := first_collision i j o (fun h => hne (congrArg firstRoot h))
  refine ⟨collisionPos i j o, collisionNeg i j o, hg, ?_⟩
  intro w hmem
  rcases Finset.mem_insert.mp hmem with rfl | hmem
  · exact ho
  · obtain ⟨hneq, hroot⟩ := Finset.mem_erase.mp hmem
    obtain ⟨k, rfl⟩ := first_mem hroot
    exact hw k (fun h => hneq (congrArg firstRoot h))

def essentialPos (i : Fin 7) : Fin 128 :=
  ⟨(([5, 10, 5, 10, 17, 33, 65] : List Nat).getD i.val 0) % 128, Nat.mod_lt _ (by decide)⟩

def essentialNeg (i : Fin 7) : Fin 128 :=
  ⟨(([4, 8, 1, 2, 1, 1, 1] : List Nat).getD i.val 0) % 128, Nat.mod_lt _ (by decide)⟩

lemma first_essential : ∀ i : Fin 7,
    sampleGoal[(essentialPos i).val] ≠ sampleGoal[(essentialNeg i).val] ∧
    ∀ j : Fin 7, j ≠ i →
      (firstRoot j)[(essentialPos i).val] = (firstRoot j)[(essentialNeg i).val] := by
  decide +kernel

lemma first_goal_diff {goal : BitVec 128} (hgoal : goal = sampleGoal ∨ goal = ~~~sampleGoal)
    {i j : Fin 128} (hd : sampleGoal[i.val] ≠ sampleGoal[j.val]) : goal[i.val] ≠ goal[j.val] := by
  rcases hgoal with rfl | rfl
  · exact hd
  · intro h
    apply hd
    have hh := congrArg Bool.not h
    simpa only [BitVec.getElem_not, Bool.not_not] using hh

lemma firstRootsComplete {goal : BitVec 128} {k : Nat} {s : Finset (BitVec 128)}
    (hgoal : goal = sampleGoal ∨ goal = ~~~sampleGoal)
    (hsub : s ⊆ signedRoots) (hl : live basicOps goal k s) : s = signedRoots := by
  apply Finset.Subset.antisymm hsub
  intro a ha
  obtain ⟨i, rfl⟩ := first_mem ha
  by_contra hn
  obtain ⟨hd, hw⟩ := first_essential i
  obtain ⟨w, hws, hne⟩ := first_live_separates (essentialPos i) (essentialNeg i)
    (first_goal_diff hgoal hd) hl
  obtain ⟨j, rfl⟩ := first_mem (hsub hws)
  exact hne (hw j (fun h => hn (by simpa [h] using hws)))

lemma first_keeps_left {goal a b z : BitVec 128} {k : Nat} {rest : Finset (BitVec 128)}
    (hgoal : goal = sampleGoal ∨ goal = ~~~sampleGoal)
    (ha : a ∈ signedRoots) (hb : b ∈ signedRoots) (hne : a ≠ b)
    (hz : z ∈ basicOps a b) (hsub : rest ⊆ signedRoots)
    (hl : live basicOps goal k (insert z rest)) : a ∈ rest := by
  by_contra haout
  obtain ⟨i, j, hd, hc⟩ := first_drop_collision ha hb hne hz
  obtain ⟨w, hw, hbad⟩ := first_live_separates i j (first_goal_diff hgoal hd) hl
  apply hbad
  apply hc
  rcases Finset.mem_insert.mp hw with rfl | hw
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun h => haout (h ▸ hw), hsub hw⟩)

lemma first_ops_comm (a b : BitVec 128) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false,
    BitVec.and_comm, BitVec.or_comm]
  tauto

lemma first_rest_complete {goal a b z : BitVec 128} {k : Nat} {rest : Finset (BitVec 128)}
    (hgoal : goal = sampleGoal ∨ goal = ~~~sampleGoal)
    (ha : a ∈ signedRoots) (hb : b ∈ signedRoots) (hne : a ≠ b)
    (hz : z ∈ basicOps a b) (hs : signedRoots = insert a (insert b rest))
    (hl : live basicOps goal k (insert z rest)) : rest = signedRoots := by
  have hsub : rest ⊆ signedRoots := by
    intro w hw
    rw [hs]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw)
  have hleft := first_keeps_left hgoal ha hb hne hz hsub hl
  have hright := first_keeps_left hgoal hb ha hne.symm
    (by simpa only [first_ops_comm] using hz) hsub hl
  rw [Finset.insert_eq_of_mem hright, Finset.insert_eq_of_mem hleft] at hs
  exact hs.symm

lemma first_roots_card : signedRoots.card = 7 := by decide +kernel

lemma first_split_live {goal : BitVec 128} {k : Nat}
    (hgoal : goal = sampleGoal ∨ goal = ~~~sampleGoal)
    (hl : live basicOps goal (k + 1) signedRoots) :
    ∃ a ∈ signedRoots, ∃ b ∈ signedRoots, a ≠ b ∧
      ∃ z ∈ basicOps a b, z ∉ signedRoots ∧ live basicOps goal k (insert z signedRoots) := by
  rcases first_live hl with hs | ⟨a, ha, b, hb, hne, z, hz, hout, rest, hs, ht⟩
  · have hc := first_roots_card
    rw [hs, Finset.card_singleton] at hc
    omega
  · have hrest := first_rest_complete hgoal ha hb hne hz hs ht
    rw [hrest] at ht
    exact ⟨a, ha, b, hb, hne, z, hz, hout, ht⟩

lemma first_split_build {goal : BitVec 128} {k : Nat}
    (hgoal : goal = sampleGoal ∨ goal = ~~~sampleGoal)
    (hb : build basicOps goal (k + 1) signedRoots) :
    ∃ a ∈ signedRoots, ∃ b ∈ signedRoots, a ≠ b ∧
      ∃ z ∈ basicOps a b, z ∉ signedRoots ∧ live basicOps goal k (insert z signedRoots) := by
  obtain ⟨s, hs, hl⟩ := compress hb
  have he := firstRootsComplete hgoal hs hl
  rw [he] at hl
  exact first_split_live hgoal hl

lemma rejection_from_first {goal : BitVec 128} {k : Nat}
    (hgoal : goal = sampleGoal ∨ goal = ~~~sampleGoal)
    (reject : ∀ a ∈ signedRoots, ∀ b ∈ signedRoots, a ≠ b →
      ∀ z ∈ basicOps a b, z ∉ signedRoots → ¬ live basicOps goal k (insert z signedRoots)) :
    ¬ build basicOps goal (k + 1) signedRoots := by
  intro hb
  obtain ⟨a, ha, b, hb, hne, z, hz, hout, hl⟩ := first_split_build hgoal hb
  exact reject a ha b hb hne z hz hout hl

lemma rejection_from_indexed {goal : BitVec 128} {k : Nat}
    (hgoal : goal = sampleGoal ∨ goal = ~~~sampleGoal)
    (reject : ∀ i j : Fin 7, j < i → ∀ o : Fin 4,
      ¬ live basicOps goal k (insert (firstOp i j o) signedRoots)) :
    ¬ build basicOps goal (k + 1) signedRoots := by
  apply rejection_from_first hgoal
  intro a ha b hb hne z hz _
  obtain ⟨i, rfl⟩ := first_mem ha
  obtain ⟨j, rfl⟩ := first_mem hb
  have hij : i ≠ j := fun h => hne (congrArg firstRoot h)
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hz' : z ∈ basicOps (firstRoot j) (firstRoot i) := by
      rwa [first_ops_comm]
    obtain ⟨o, rfl⟩ := first_op_mem hz'
    exact reject j i hij o
  · obtain ⟨o, rfl⟩ := first_op_mem hz
    exact reject i j hji o

lemma first_ops_zero {width : Nat} {a b z : BitVec width} (i : Fin width)
    (hz : z ∈ basicOps a b) (ha : a[i.val] = false) (hb : b[i.val] = false) :
    z[i.val] = false := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, ha, hb,
      Bool.false_and, Bool.false_or]

lemma first_build_zero {width : Nat} {goal : BitVec width} (i : Fin width)
    (k : Nat) (s : Finset (BitVec width)) (hs : ∀ w ∈ s, w[i.val] = false)
    (hb : build basicOps goal k s) : goal[i.val] = false := by
  induction k generalizing s with
  | zero => exact hs goal hb
  | succ k ih =>
    rcases hb with skip | ⟨a, ha, b, hb, _, z, hz, tail⟩
    · exact ih s hs skip
    · apply ih (insert z s) _ tail
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact first_ops_zero i hz (hs a ha) (hs b hb)
      · exact hs w hw

lemma first_roots_zero : ∀ w ∈ signedRoots, w[127] = false := by
  intro w hw
  obtain ⟨i, rfl⟩ := first_mem hw
  have all : ∀ j : Fin 7, (firstRoot j)[127] = false := by decide +kernel
  exact all i

lemma reject_positive_goal (k : Nat) : ¬ build basicOps sampleGoal k signedRoots := by
  intro hb
  have hz := first_build_zero (goal := sampleGoal) ⟨127, by decide⟩ k signedRoots first_roots_zero hb
  have ho : sampleGoal[127] = true := by decide +kernel
  exact Bool.noConfusion (ho.symm.trans hz)

lemma rejection_from_84
    (reject : ∀ i j : Fin 7, j < i → ∀ o : Fin 4,
      ¬ live basicOps (~~~sampleGoal) 11 (insert (firstOp i j o) signedRoots)) :
    ∀ z, z = sampleGoal ∨ z = ~~~sampleGoal → ¬ build basicOps z 12 signedRoots := by
  intro z hz
  rcases hz with rfl | rfl
  · exact reject_positive_goal 12
  · exact rejection_from_indexed (Or.inr rfl) reject

end PEqualNP.Outside.L_meta_10760

namespace PEqualNP.Outside.L_meta_10760

open PEqualNP.CircuitLowerBounds

def canonical64 (w : BitVec 64) : BitVec 64 :=
  if w.toNat ≤ (~~~w).toNat then w else ~~~w

def sampleInputs64 : List (BitVec 64) := [0x844a844a8952aaa, 0x1089308931264ccc, 0x2111c111c23870f0, 0x421e021e03c07f00, 0x83e003e003ff8000, 0xfc0003fffc000000, 0xfffffc0000000000]

def sampleGoal64 : BitVec 64 := 0xffdfebdfbbbf6ca0

def signedRoots64 : Finset (BitVec 64) := (sampleInputs64.map canonical64).toFinset

lemma sample_represented64 : ∀ u ∈ sampleInputs64, holds signedRoots64 u := by
  intro u hu
  refine Or.inr (Or.inr ⟨canonical64 u,
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨u, hu, rfl⟩), ?_⟩)
  unfold canonical64
  split
  · exact Or.inl rfl
  · exact Or.inr BitVec.not_not.symm

set_option maxHeartbeats 2000000 in
lemma sample_rows64 : ∀ j : Fin 64,
    edgeFunction (fun i => (sampleInputs64.getD i.val 0)[j.val]) = sampleGoal64[j.val] := by
  decide +kernel

set_option maxHeartbeats 2000000 in
lemma gap_of_rejection64
    (reject : ∀ z, z = sampleGoal64 ∨ z = ~~~sampleGoal64 →
      ¬ build basicOps z 12 signedRoots64) :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hg _ hf
  obtain ⟨ds, out, ok, len, ev⟩ := replace_from_samples
    (replacementSize := 14) (goal := sampleGoal64)
    (by decide +kernel) (by decide +kernel) edgeFunction sampleInputs64 signedRoots64
    sample_represented64 rfl sample_rows64 reject
    ⟨monotoneWitness, 20, witness_allowed, witness_size, witness_eval⟩
    gates o hg (fun x => (hf x).trans (edgeFunction_posted x))
  exact ⟨ds, out, ok, len, fun x => (ev x).trans (edgeFunction_posted x).symm⟩

end PEqualNP.Outside.L_meta_10760


namespace PEqualNP.Outside.L_meta_10760.S64

def firstRoot (i : Fin 7) : BitVec 64 :=
  min (sampleInputs64.getD i.val 0) (~~~(sampleInputs64.getD i.val 0))

def firstOp (i j : Fin 7) (o : Fin 4) : BitVec 64 :=
  (ops (firstRoot i) (firstRoot j)).getD o.val 0

def collisionData : List Nat := [0, 0, 0, 0, 261, 391, 391, 261, 976, 261, 261, 976, 261, 781, 781, 261, 976, 261, 261, 976, 1691, 261, 261, 1691, 2731, 261, 261, 2731, 522, 587, 587, 522, 0, 0, 0, 0, 522, 782, 782, 522, 977, 522, 522, 977, 977, 522, 522, 977, 1692, 522, 522, 1692, 3447, 522, 522, 3447, 979, 69, 69, 979, 69, 199, 199, 69, 0, 0, 0, 0, 69, 589, 589, 69, 979, 69, 69, 979, 2408, 69, 69, 2408, 2734, 69, 69, 2734, 138, 203, 203, 138, 1697, 138, 138, 1697, 138, 398, 398, 138, 0, 0, 0, 0, 2409, 138, 138, 2409, 1697, 138, 138, 1697, 2737, 138, 138, 2737, 145, 80, 80, 145, 80, 145, 145, 80, 80, 275, 275, 80, 80, 599, 599, 80, 0, 0, 0, 0, 1960, 80, 80, 1960, 2871, 80, 80, 2871, 156, 91, 91, 156, 91, 156, 156, 91, 91, 416, 416, 91, 91, 545, 545, 91, 1449, 91, 91, 1449, 0, 0, 0, 0, 2746, 91, 91, 2746, 302, 107, 107, 302, 107, 237, 237, 107, 107, 302, 302, 107, 107, 561, 561, 107, 1465, 107, 107, 1465, 1722, 107, 107, 1722, 0, 0, 0, 0]

def collisionPos (i j : Fin 7) (o : Fin 4) : Fin 64 :=
  ⟨(collisionData.getD ((i.val * 7 + j.val) * 4 + o.val) 0) % 64, Nat.mod_lt _ (by decide)⟩

def collisionNeg (i j : Fin 7) (o : Fin 4) : Fin 64 :=
  ⟨(collisionData.getD ((i.val * 7 + j.val) * 4 + o.val) 0 / 64) % 64, Nat.mod_lt _ (by decide)⟩

set_option maxHeartbeats 8000000 in
lemma first_collision : ∀ i j : Fin 7, ∀ o : Fin 4, i ≠ j →
    sampleGoal64[(collisionPos i j o).val] ≠ sampleGoal64[(collisionNeg i j o).val] ∧
    (firstOp i j o)[(collisionPos i j o).val] = (firstOp i j o)[(collisionNeg i j o).val] ∧
    ∀ k : Fin 7, k ≠ i →
      (firstRoot k)[(collisionPos i j o).val] = (firstRoot k)[(collisionNeg i j o).val] := by
  decide +kernel

lemma first_roots_eq : signedRoots64 = Finset.univ.image firstRoot := by
  decide +kernel

lemma first_mem {u : BitVec 64} (hu : u ∈ signedRoots64) : ∃ i : Fin 7, u = firstRoot i := by
  rw [first_roots_eq] at hu
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hu
  exact ⟨i, hi.symm⟩

lemma first_op_mem {i j : Fin 7} {z : BitVec 64}
    (hz : z ∈ basicOps (firstRoot i) (firstRoot j)) : ∃ o : Fin 4, z = firstOp i j o := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

lemma first_bit_congr {width : Nat} {a b z : BitVec width} (i j : Fin width)
    (hz : z ∈ basicOps a b) (ha : a[i.val] = a[j.val]) (hb : b[i.val] = b[j.val]) :
    z[i.val] = z[j.val] := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, ha, hb]

lemma first_live_separates {width : Nat} {goal : BitVec width} {k : Nat}
    {s : Finset (BitVec width)} (i j : Fin width) (hd : goal[i.val] ≠ goal[j.val])
    (hl : live basicOps goal k s) : ∃ w ∈ s, w[i.val] ≠ w[j.val] := by
  apply live_separates (fun w => w[i.val] ≠ w[j.val]) hd _ hl
  intro a b z hz hne
  by_contra hn
  simp only [not_or, not_not] at hn
  exact hne (first_bit_congr i j hz hn.1 hn.2)

lemma first_drop_collision {a b z : BitVec 64}
    (ha : a ∈ signedRoots64) (hb : b ∈ signedRoots64) (hne : a ≠ b)
    (hz : z ∈ basicOps a b) :
    ∃ i j : Fin 64, sampleGoal64[i.val] ≠ sampleGoal64[j.val] ∧
      ∀ w ∈ insert z (signedRoots64.erase a), w[i.val] = w[j.val] := by
  obtain ⟨i, rfl⟩ := first_mem ha
  obtain ⟨j, rfl⟩ := first_mem hb
  obtain ⟨o, rfl⟩ := first_op_mem hz
  obtain ⟨hg, ho, hw⟩ := first_collision i j o (fun h => hne (congrArg firstRoot h))
  refine ⟨collisionPos i j o, collisionNeg i j o, hg, ?_⟩
  intro w hmem
  rcases Finset.mem_insert.mp hmem with rfl | hmem
  · exact ho
  · obtain ⟨hneq, hroot⟩ := Finset.mem_erase.mp hmem
    obtain ⟨k, rfl⟩ := first_mem hroot
    exact hw k (fun h => hneq (congrArg firstRoot h))

def essentialPos (i : Fin 7) : Fin 64 :=
  ⟨(([5, 10, 5, 10, 16, 27, 43] : List Nat).getD i.val 0) % 64, Nat.mod_lt _ (by decide)⟩

def essentialNeg (i : Fin 7) : Fin 64 :=
  ⟨(([4, 8, 1, 2, 1, 1, 1] : List Nat).getD i.val 0) % 64, Nat.mod_lt _ (by decide)⟩

lemma first_essential : ∀ i : Fin 7,
    sampleGoal64[(essentialPos i).val] ≠ sampleGoal64[(essentialNeg i).val] ∧
    ∀ j : Fin 7, j ≠ i →
      (firstRoot j)[(essentialPos i).val] = (firstRoot j)[(essentialNeg i).val] := by
  decide +kernel

lemma first_goal_diff {goal : BitVec 64} (hgoal : goal = sampleGoal64 ∨ goal = ~~~sampleGoal64)
    {i j : Fin 64} (hd : sampleGoal64[i.val] ≠ sampleGoal64[j.val]) : goal[i.val] ≠ goal[j.val] := by
  rcases hgoal with rfl | rfl
  · exact hd
  · intro h
    apply hd
    have hh := congrArg Bool.not h
    simpa only [BitVec.getElem_not, Bool.not_not] using hh

lemma firstRootsComplete {goal : BitVec 64} {k : Nat} {s : Finset (BitVec 64)}
    (hgoal : goal = sampleGoal64 ∨ goal = ~~~sampleGoal64)
    (hsub : s ⊆ signedRoots64) (hl : live basicOps goal k s) : s = signedRoots64 := by
  apply Finset.Subset.antisymm hsub
  intro a ha
  obtain ⟨i, rfl⟩ := first_mem ha
  by_contra hn
  obtain ⟨hd, hw⟩ := first_essential i
  obtain ⟨w, hws, hne⟩ := first_live_separates (essentialPos i) (essentialNeg i)
    (first_goal_diff hgoal hd) hl
  obtain ⟨j, rfl⟩ := first_mem (hsub hws)
  exact hne (hw j (fun h => hn (by simpa [h] using hws)))

lemma first_keeps_left {goal a b z : BitVec 64} {k : Nat} {rest : Finset (BitVec 64)}
    (hgoal : goal = sampleGoal64 ∨ goal = ~~~sampleGoal64)
    (ha : a ∈ signedRoots64) (hb : b ∈ signedRoots64) (hne : a ≠ b)
    (hz : z ∈ basicOps a b) (hsub : rest ⊆ signedRoots64)
    (hl : live basicOps goal k (insert z rest)) : a ∈ rest := by
  by_contra haout
  obtain ⟨i, j, hd, hc⟩ := first_drop_collision ha hb hne hz
  obtain ⟨w, hw, hbad⟩ := first_live_separates i j (first_goal_diff hgoal hd) hl
  apply hbad
  apply hc
  rcases Finset.mem_insert.mp hw with rfl | hw
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun h => haout (h ▸ hw), hsub hw⟩)

lemma first_ops_comm (a b : BitVec 64) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false,
    BitVec.and_comm, BitVec.or_comm]
  tauto

lemma first_rest_complete {goal a b z : BitVec 64} {k : Nat} {rest : Finset (BitVec 64)}
    (hgoal : goal = sampleGoal64 ∨ goal = ~~~sampleGoal64)
    (ha : a ∈ signedRoots64) (hb : b ∈ signedRoots64) (hne : a ≠ b)
    (hz : z ∈ basicOps a b) (hs : signedRoots64 = insert a (insert b rest))
    (hl : live basicOps goal k (insert z rest)) : rest = signedRoots64 := by
  have hsub : rest ⊆ signedRoots64 := by
    intro w hw
    rw [hs]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw)
  have hleft := first_keeps_left hgoal ha hb hne hz hsub hl
  have hright := first_keeps_left hgoal hb ha hne.symm
    (by simpa only [first_ops_comm] using hz) hsub hl
  rw [Finset.insert_eq_of_mem hright, Finset.insert_eq_of_mem hleft] at hs
  exact hs.symm

lemma first_roots_card : signedRoots64.card = 7 := by decide +kernel

lemma first_split_live {goal : BitVec 64} {k : Nat}
    (hgoal : goal = sampleGoal64 ∨ goal = ~~~sampleGoal64)
    (hl : live basicOps goal (k + 1) signedRoots64) :
    ∃ a ∈ signedRoots64, ∃ b ∈ signedRoots64, a ≠ b ∧
      ∃ z ∈ basicOps a b, z ∉ signedRoots64 ∧ live basicOps goal k (insert z signedRoots64) := by
  rcases first_live hl with hs | ⟨a, ha, b, hb, hne, z, hz, hout, rest, hs, ht⟩
  · have hc := first_roots_card
    rw [hs, Finset.card_singleton] at hc
    omega
  · have hrest := first_rest_complete hgoal ha hb hne hz hs ht
    rw [hrest] at ht
    exact ⟨a, ha, b, hb, hne, z, hz, hout, ht⟩

lemma first_split_build {goal : BitVec 64} {k : Nat}
    (hgoal : goal = sampleGoal64 ∨ goal = ~~~sampleGoal64)
    (hb : build basicOps goal (k + 1) signedRoots64) :
    ∃ a ∈ signedRoots64, ∃ b ∈ signedRoots64, a ≠ b ∧
      ∃ z ∈ basicOps a b, z ∉ signedRoots64 ∧ live basicOps goal k (insert z signedRoots64) := by
  obtain ⟨s, hs, hl⟩ := compress hb
  have he := firstRootsComplete hgoal hs hl
  rw [he] at hl
  exact first_split_live hgoal hl

lemma rejection_from_first {goal : BitVec 64} {k : Nat}
    (hgoal : goal = sampleGoal64 ∨ goal = ~~~sampleGoal64)
    (reject : ∀ a ∈ signedRoots64, ∀ b ∈ signedRoots64, a ≠ b →
      ∀ z ∈ basicOps a b, z ∉ signedRoots64 → ¬ live basicOps goal k (insert z signedRoots64)) :
    ¬ build basicOps goal (k + 1) signedRoots64 := by
  intro hb
  obtain ⟨a, ha, b, hb, hne, z, hz, hout, hl⟩ := first_split_build hgoal hb
  exact reject a ha b hb hne z hz hout hl

lemma rejection_from_indexed {goal : BitVec 64} {k : Nat}
    (hgoal : goal = sampleGoal64 ∨ goal = ~~~sampleGoal64)
    (reject : ∀ i j : Fin 7, j < i → ∀ o : Fin 4,
      ¬ live basicOps goal k (insert (firstOp i j o) signedRoots64)) :
    ¬ build basicOps goal (k + 1) signedRoots64 := by
  apply rejection_from_first hgoal
  intro a ha b hb hne z hz _
  obtain ⟨i, rfl⟩ := first_mem ha
  obtain ⟨j, rfl⟩ := first_mem hb
  have hij : i ≠ j := fun h => hne (congrArg firstRoot h)
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hz' : z ∈ basicOps (firstRoot j) (firstRoot i) := by
      rwa [first_ops_comm]
    obtain ⟨o, rfl⟩ := first_op_mem hz'
    exact reject j i hij o
  · obtain ⟨o, rfl⟩ := first_op_mem hz
    exact reject i j hji o

lemma first_ops_zero {width : Nat} {a b z : BitVec width} (i : Fin width)
    (hz : z ∈ basicOps a b) (ha : a[i.val] = false) (hb : b[i.val] = false) :
    z[i.val] = false := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, ha, hb,
      Bool.false_and, Bool.false_or]

lemma first_build_zero {width : Nat} {goal : BitVec width} (i : Fin width)
    (k : Nat) (s : Finset (BitVec width)) (hs : ∀ w ∈ s, w[i.val] = false)
    (hb : build basicOps goal k s) : goal[i.val] = false := by
  induction k generalizing s with
  | zero => exact hs goal hb
  | succ k ih =>
    rcases hb with skip | ⟨a, ha, b, hb, _, z, hz, tail⟩
    · exact ih s hs skip
    · apply ih (insert z s) _ tail
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact first_ops_zero i hz (hs a ha) (hs b hb)
      · exact hs w hw

lemma first_roots_zero : ∀ w ∈ signedRoots64, w[63] = false := by
  intro w hw
  obtain ⟨i, rfl⟩ := first_mem hw
  have all : ∀ j : Fin 7, (firstRoot j)[63] = false := by decide +kernel
  exact all i

lemma reject_positive_goal (k : Nat) : ¬ build basicOps sampleGoal64 k signedRoots64 := by
  intro hb
  have hz := first_build_zero (goal := sampleGoal64) ⟨63, by decide⟩ k signedRoots64 first_roots_zero hb
  have ho : sampleGoal64[63] = true := by decide +kernel
  exact Bool.noConfusion (ho.symm.trans hz)

lemma rejection_from_84_64
    (reject : ∀ i j : Fin 7, j < i → ∀ o : Fin 4,
      ¬ live basicOps (~~~sampleGoal64) 11 (insert (firstOp i j o) signedRoots64)) :
    ∀ z, z = sampleGoal64 ∨ z = ~~~sampleGoal64 → ¬ build basicOps z 12 signedRoots64 := by
  intro z hz
  rcases hz with rfl | rfl
  · exact reject_positive_goal 12
  · exact rejection_from_indexed (Or.inr rfl) reject

end PEqualNP.Outside.L_meta_10760.S64

namespace PEqualNP.Outside.L_meta_10760

namespace SearchKernel

open PEqualNP.Outside.L_meta_10760

variable {width : Nat}

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
lemma pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

set_option maxRecDepth 100000 in
lemma pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

lemma ops_swap (a b : (BitVec width)) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : (BitVec width)) (r : List (BitVec width)) : List (List (BitVec width)) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 100000 in
lemma recover_kept {ws r : List (BitVec width)} {a b : (BitVec width)} {needed : Finset (BitVec width)}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

set_option maxRecDepth 100000 in
lemma singleton_list {goal : (BitVec width)} {ws : List (BitVec width)} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def rowClass (j : Fin width) (w : BitVec width) : BitVec width :=
  if w[j.val] then w else ~~~w

def survivors (goal : BitVec width) (j : Fin width) (ws : List (BitVec width)) : BitVec width :=
  ws.foldr (fun w r => rowClass j w &&& r) goal

def separates (goal : BitVec width) (rows : List (Fin width))
    (ws : List (BitVec width)) : Bool :=
  rows.all (fun j => goal[j.val] || (survivors goal j ws == 0))

lemma rowClass_bit (i j : Fin width) (w : BitVec width) :
    (rowClass j w)[i.val] = true ↔ w[i.val] = w[j.val] := by
  unfold rowClass
  split <;> simp_all

lemma survivors_bit (goal : BitVec width) (i j : Fin width) (ws : List (BitVec width)) :
    (survivors goal j ws)[i.val] = true ↔
      goal[i.val] = true ∧ ∀ w ∈ ws, w[i.val] = w[j.val] := by
  induction ws with
  | nil => simp [survivors]
  | cons w ws ih =>
    simp only [survivors, List.foldr_cons, BitVec.getElem_and, Bool.and_eq_true]
    change (rowClass j w)[i.val] = true ∧ (survivors goal j ws)[i.val] = true ↔ _
    rw [rowClass_bit, ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

lemma ops_separate (i j : Fin width) (a b z : BitVec width) (hz : z ∈ basicOps a b)
    (hd : z[i.val] ≠ z[j.val]) : a[i.val] ≠ a[j.val] ∨ b[i.val] ≠ b[j.val] := by
  by_contra h
  push Not at h
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> apply hd <;>
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, h.1, h.2]

lemma separates_complete {goal g : BitVec width} (hg : g = goal ∨ g = ~~~goal)
    (rows : List (Fin width))
    {k : Nat} {ws : List (BitVec width)} (h : live basicOps g k ws.toFinset) :
    separates goal rows ws = true := by
  rw [separates, List.all_eq_true]
  intro j hj
  cases he : goal[j.val] with
  | true => simp [he]
  | false =>
    simp only [he, Bool.false_or, beq_iff_eq]
    apply BitVec.eq_of_getElem_eq
    intro i hi
    have zi : (0 : BitVec width)[i] = false := by simp
    rw [zi]
    cases hs : (survivors goal j ws)[i] with
    | false => rfl
    | true =>
      obtain ⟨hgoal, hagree⟩ := (survivors_bit goal ⟨i,hi⟩ j ws).mp hs
      have diff : g[i] ≠ g[j.val] := by
        rcases hg with rfl | rfl <;> simp [hgoal, he]
      obtain ⟨w, hw, hd⟩ := live_separates (fun w : BitVec width => w[i] ≠ w[j.val])
        diff (ops_separate ⟨i,hi⟩ j) h
      exact False.elim (hd (hagree w (List.mem_toFinset.mp hw)))


def dispatch (goal : BitVec width) (rows : List (Fin width)) (extra : Nat)
    (next : Nat → List (BitVec width) → Bool) (a b : BitVec width)
    (r : List (BitVec width)) : Bool :=
  (ops a b).any fun z => !(a :: b :: r).contains z &&
    (keepChoices a b r).any fun kept =>
    decide (kept.length ≤ extra + r.length) && separates goal rows (z :: kept) &&
      next (extra + r.length - kept.length) (z :: kept)

def optimized (goal : BitVec width) (rows : List (Fin width)) : Nat → Nat → List (BitVec width) → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch goal rows extra (optimized goal rows k) a b r)

lemma dispatch_complete {goal : BitVec width} {rows : List (Fin width)} {k extra : Nat} {a b z : BitVec width}
    {r kept : List (BitVec width)} (next : Nat → List (BitVec width) → Bool)
    (hz : z ∈ basicOps a b) (hnew : z ∉ a :: b :: r) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : separates goal rows (z :: kept) = true)
    (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch goal rows extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨by simpa using hnew, ?_⟩
  apply List.any_eq_true.mpr
  refine ⟨kept, hk, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨by omega, hc⟩, by simpa only [he] using ht⟩

set_option maxRecDepth 100000 in
lemma optimized_complete {goal g : (BitVec width)} (hg : g = goal ∨ g = ~~~goal) (rows : List (Fin width)) (n : ℕ) (ws : List (BitVec width)) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized goal rows n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : (BitVec width)} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch goal rows extra (optimized goal rows k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized goal rows k) hop (by
          intro hz
          exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hz))) hk (by omega) (by omega) (separates_complete hg rows hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def falseRows (goal : BitVec width) : List (Fin width) :=
  (List.finRange width).filter (fun j => !goal[j.val])

def search (goal : BitVec width) (n : ℕ) (inputs : List (BitVec width)) : Bool :=
  let rows := falseRows goal
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && separates goal rows ws && optimized goal rows n (n+1-ws.length) ws

set_option maxRecDepth 100000 in
lemma search_complete {goal g : (BitVec width)} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List (BitVec width))
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search goal n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, separates_complete hg (falseRows goal) hl', optimized_complete hg (falseRows goal) n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

lemma no_build {goal g : BitVec width} (hg : g = goal ∨ g = ~~~goal)
    (n : Nat) (inputs : List (BitVec width)) (hn : inputs.Nodup)
    (rejected : search goal n inputs = false) :
    ¬ build basicOps g n inputs.toFinset := by
  intro h
  have found := search_complete hg n inputs hn h
  rw [rejected] at found
  contradiction

end SearchKernel


namespace PackedKeyWide

def packWords {w : Nat} : List (BitVec w) → Nat
  | [] => 1
  | a :: xs => packWords xs * 2 ^ (w + 1) + a.toNat

lemma packWords_pos {w : Nat} (xs : List (BitVec w)) : 0 < packWords xs := by
  induction xs with
  | nil => simp [packWords]
  | cons a xs ih =>
    have h := Nat.mul_pos ih (Nat.two_pow_pos (w + 1))
    simp only [packWords]
    omega

lemma base_ge_two (w : Nat) : 2 ≤ 2 ^ (w + 1) := by
  have h := Nat.two_pow_pos w
  simp only [pow_succ]
  omega

lemma packWords_cons_gt_one {w : Nat} (a : BitVec w) (xs : List (BitVec w)) :
    1 < packWords (a :: xs) := by
  have h := packWords_pos xs
  have hb := base_ge_two w
  have hm := Nat.mul_le_mul_right (2 ^ (w + 1)) h
  simp only [packWords, Nat.one_mul] at *
  omega

lemma packWords_inj {w : Nat} {xs ys : List (BitVec w)}
    (h : packWords xs = packWords ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons a ys =>
      have hc := packWords_cons_gt_one a ys
      change 1 = packWords (a :: ys) at h
      omega
  | cons a xs ih =>
    cases ys with
    | nil =>
      have hc := packWords_cons_gt_one a xs
      change packWords (a :: xs) = 1 at h
      omega
    | cons b ys =>
      have ha0 := a.isLt
      have ha : a.toNat < 2 ^ (w + 1) := by rw [pow_succ]; omega
      have hb0 := b.isLt
      have hb : b.toNat < 2 ^ (w + 1) := by rw [pow_succ]; omega
      have hd := congrArg (fun v => v % 2 ^ (w + 1)) h
      simp only [packWords, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add,
        Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hd
      have hab : a = b := BitVec.eq_of_toNat_eq hd
      subst b
      have ht : packWords xs * 2 ^ (w + 1) = packWords ys * 2 ^ (w + 1) := by
        simp only [packWords] at h
        omega
      have he : packWords xs = packWords ys := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos (w + 1)) ht
      exact congrArg (a :: ·) (ih he)

def packBudget : Nat → Nat → Nat
  | 0, p => 2 * p + 1
  | k + 1, p => 2 * packBudget k p

lemma packBudget_inj {k j p q : Nat} (h : packBudget k p = packBudget j q) : k = j ∧ p = q := by
  induction k generalizing j with
  | zero =>
    cases j with
    | zero => simp only [packBudget] at h; exact ⟨rfl, by omega⟩
    | succ j => simp only [packBudget] at h; omega
  | succ k ih =>
    cases j with
    | zero => simp only [packBudget] at h; omega
    | succ j =>
      have he : packBudget k p = packBudget j q := by simpa only [packBudget, Nat.mul_right_inj (by decide : 2 ≠ 0)] using h
      obtain ⟨rfl, rfl⟩ := ih he
      exact ⟨rfl, rfl⟩

def key {w : Nat} (k : Nat) (xs : List (BitVec w)) : Nat := packBudget k (packWords xs)

lemma key_inj {w : Nat} {k j : Nat} {xs ys : List (BitVec w)}
    (h : key k xs = key j ys) : k = j ∧ xs = ys := by
  obtain ⟨hkj, hxy⟩ := packBudget_inj h
  exact ⟨hkj, packWords_inj hxy⟩

end PackedKeyWide


namespace RawLaws

lemma empty_wf : (∅ : Std.TreeSet.Raw Nat compare).WF :=
  ⟨⟨⟨(∅ : Std.TreeSet Nat compare).inner.inner.wf⟩⟩⟩

lemma insert_wf {t : Std.TreeSet.Raw Nat compare} (h : t.WF) (a : Nat) : (t.insert a).WF :=
  ⟨⟨⟨h.out.out.out.insertIfNew!⟩⟩⟩

lemma contains_insert {t : Std.TreeSet.Raw Nat compare} (h : t.WF) (k a : Nat) :
    (t.insert k).contains a = (compare k a == .eq || t.contains a) := by
  exact Std.DTreeMap.Internal.Impl.contains_insertIfNew! h.out.out.out

end RawLaws


namespace MemoPruned

variable {α κ : Type}

def plain (admissible : Nat → α → Bool) (done : α → Bool) (children : Nat → α → List α) : Nat → α → Bool
  | 0, x => if admissible 0 x then done x else false
  | k + 1, x => if admissible (k+1) x then done x || (children k x).any (plain admissible done children k) else false

def scan (next : α → κ → Bool × κ) : List α → κ → Bool × κ
  | [], cache => (false, cache)
  | x :: xs, cache =>
    match next x cache with
    | (true, cache') => (true, cache')
    | (false, cache') => scan next xs cache'

lemma scan_correct (Good : κ → Prop)
    (f : α → Bool) (next : α → κ → Bool × κ)
    (hnext : ∀ x cache, Good cache →
      (next x cache).1 = f x ∧ Good (next x cache).2)
    (xs : List α) (cache : κ) (hc : Good cache) :
    (scan next xs cache).1 = xs.any f ∧ Good (scan next xs cache).2 := by
  induction xs generalizing cache with
  | nil => exact ⟨rfl, hc⟩
  | cons x xs ih =>
    have hs := hnext x cache hc
    cases he : next x cache with
    | mk b cache' =>
      simp only [he] at hs
      cases b with
      | false =>
        have ht := ih cache' hs.2
        simpa only [scan, he, hs.1.symm, List.any_cons, Bool.false_or] using ht
      | true =>
        simp only [scan, he, hs.1.symm, List.any_cons, Bool.true_or]
        exact ⟨trivial, hs.2⟩

def search (hit : Nat → α → κ → Bool) (put : Nat → α → κ → κ) (admissible : Nat → α → Bool) (done : α → Bool) (children : Nat → α → List α) :
    Nat → α → κ → Bool × κ
  | 0, x, cache =>
    if hit 0 x cache then (false, cache)
    else if !admissible 0 x then (false, cache)
    else if done x then (true, cache)
    else (false, put 0 x cache)
  | k+1, x, cache =>
    if hit (k+1) x cache then (false, cache)
    else if !admissible (k+1) x then (false, cache)
    else if done x then (true, cache)
    else match scan (search hit put admissible done children k) (children k x) cache with
    | (true, cache') => (true, cache')
    | (false, cache') => (false, put (k+1) x cache')

lemma search_correct (hit : Nat → α → κ → Bool) (put : Nat → α → κ → κ)
    (admissible : Nat → α → Bool) (done : α → Bool) (children : Nat → α → List α) (Good : κ → Prop)
    (hit_sound : ∀ k x cache, Good cache → hit k x cache = true → plain admissible done children k x = false)
    (put_good : ∀ k x cache, Good cache → plain admissible done children k x = false → Good (put k x cache))
    (k : Nat) (x : α) (cache : κ) (hc : Good cache) :
    (search hit put admissible done children k x cache).1 = plain admissible done children k x ∧
      Good (search hit put admissible done children k x cache).2 := by
  induction k generalizing x cache with
  | zero =>
    by_cases hh : hit 0 x cache = true
    · simp only [search, hh, Bool.true_eq, ite_true, Prod.fst, Prod.snd]
      exact ⟨(hit_sound 0 x cache hc hh).symm, hc⟩
    · have hh' : hit 0 x cache = false := Bool.eq_false_iff.mpr hh
      by_cases ha : admissible 0 x = true
      · by_cases hd : done x = true
        · simp [search, hh', ha, hd, plain, hc]
        · have hd' : done x = false := Bool.eq_false_iff.mpr hd
          have hx : plain admissible done children 0 x = false := by simp [plain, ha, hd']
          simpa only [search, hh', Bool.false_eq_true, ite_false, ha, Bool.not_true,
            hd', Prod.fst, Prod.snd] using And.intro hx.symm (put_good 0 x cache hc hx)
      · have ha' : admissible 0 x = false := Bool.eq_false_iff.mpr ha
        simp [search, hh', ha', plain, hc]
  | succ k ih =>
    by_cases hh : hit (k+1) x cache = true
    · simp only [search, hh, Bool.true_eq, ite_true, Prod.fst, Prod.snd]
      exact ⟨(hit_sound (k+1) x cache hc hh).symm, hc⟩
    · have hh' : hit (k+1) x cache = false := Bool.eq_false_iff.mpr hh
      by_cases ha : admissible (k+1) x = true
      · by_cases hd : done x = true
        · simp [search, hh', ha, hd, plain, hc]
        · have hd' : done x = false := Bool.eq_false_iff.mpr hd
          have hs := scan_correct Good (plain admissible done children k) (search hit put admissible done children k)
            (fun y c h => ih y c h) (children k x) cache hc
          cases he : scan (search hit put admissible done children k) (children k x) cache with
          | mk b cache' =>
            simp only [he] at hs
            cases b with
            | false =>
              have hx : plain admissible done children (k+1) x = false := by
                simp only [plain, ha, Bool.true_eq, ite_true, hd', Bool.false_or]
                exact hs.1.symm
              simp only [search, hh', Bool.false_eq_true, ite_false, ha, Bool.not_true,
                hd', he, Prod.fst, Prod.snd]
              exact ⟨hx.symm, put_good (k+1) x cache' hs.2 hx⟩
            | true =>
              simp only [search, hh', Bool.false_eq_true, ite_false, ha, Bool.not_true,
                hd', he, Prod.fst, Prod.snd]
              constructor
              · simp only [plain, ha, Bool.true_eq, ite_true, hd', Bool.false_or]
                exact hs.1.symm
              · exact hs.2
      · have ha' : admissible (k+1) x = false := Bool.eq_false_iff.mpr ha
        simp [search, hh', ha', plain, hc]

lemma search_run (hit : Nat → α → κ → Bool) (put : Nat → α → κ → κ)
    (admissible : Nat → α → Bool) (done : α → Bool) (children : Nat → α → List α) (Good : κ → Prop)
    (hit_sound : ∀ k x cache, Good cache → hit k x cache = true → plain admissible done children k x = false)
    (put_good : ∀ k x cache, Good cache → plain admissible done children k x = false → Good (put k x cache))
    (k : Nat) (x : α) (cache : κ) (hc : Good cache) :
    (search hit put admissible done children k x cache).1 = plain admissible done children k x :=
  (search_correct hit put admissible done children Good hit_sound put_good k x cache hc).1


variable {width : Nat}

abbrev States (width : Nat) := List (BitVec width)
abbrev TreeCache := Std.TreeSet.Raw Nat

def key (k : Nat) (ws : States width) : Nat :=
  PackedKeyWide.key k ws

def forceNat {β : Type} (n : Nat) (f : Nat → β) : β :=
  Nat.rec (f 0) (fun k _ => f (k+1)) n

lemma forceNat_eq {β : Type} (n : Nat) (f : Nat → β) : forceNat n f = f n := by
  cases n <;> rfl

def treeHit (k : Nat) (ws : States width) (cache : TreeCache) : Bool := forceNat (key k ws) (fun q => cache.contains q)
def treePut (k : Nat) (ws : States width) (cache : TreeCache) : TreeCache := forceNat (key k ws) (fun q => cache.insert q)

lemma key_inj {k j : Nat} {ws vs : States width} (h : key k ws = key j vs) : k = j ∧ ws = vs :=
  PackedKeyWide.key_inj h

def TreeGood (admissible : Nat → States width → Bool) (done : States width → Bool) (children : Nat → States width → List (States width)) (cache : TreeCache) : Prop :=
  cache.WF ∧ ∀ k ws, treeHit k ws cache = true → plain admissible done children k ws = false

lemma tree_good_empty (admissible : Nat → States width → Bool) (done : States width → Bool) (children : Nat → States width → List (States width)) :
    TreeGood admissible done children ∅ := by
  refine ⟨RawLaws.empty_wf, ?_⟩
  intro k ws h
  simp only [treeHit, forceNat_eq] at h
  change false = true at h
  contradiction

lemma tree_put_good {admissible : Nat → States width → Bool} {done : States width → Bool} {children : Nat → States width → List (States width)}
    (k : Nat) (ws : States width) (cache : TreeCache) (hc : TreeGood admissible done children cache)
    (h : plain admissible done children k ws = false) : TreeGood admissible done children (treePut k ws cache) := by
  simp only [treePut, forceNat_eq]
  refine ⟨RawLaws.insert_wf hc.1 _, ?_⟩
  intro j vs hh
  simp only [treeHit, forceNat_eq, RawLaws.contains_insert hc.1, Bool.or_eq_true] at hh
  rcases hh with he | hold
  · have heq : key k ws = key j vs := Std.LawfulEqCmp.eq_of_compare (beq_iff_eq.mp he)
    obtain ⟨rfl, rfl⟩ := key_inj heq
    exact h
  · exact hc.2 j vs (by simpa only [treeHit, forceNat_eq] using hold)

def run (admissible : Nat → States width → Bool) (done : States width → Bool) (children : Nat → States width → List (States width)) (k : Nat) (ws : States width) : Bool :=
  (search treeHit treePut admissible done children k ws ∅).1

lemma run_correct (admissible : Nat → States width → Bool) (done : States width → Bool) (children : Nat → States width → List (States width)) (k : Nat) (ws : States width) :
    run admissible done children k ws = plain admissible done children k ws := by
  exact search_run treeHit treePut admissible done children (TreeGood admissible done children)
    (fun k ws cache hc hh => hc.2 k ws hh)
    (fun k ws cache hc hh => tree_put_good k ws cache hc hh)
    k ws ∅ (tree_good_empty admissible done children)


lemma plain_complete (admissible : Nat → α → Bool) (done : α → Bool) (children : Nat → α → List α)
    (Sol : Nat → α → Prop)
    (admissible_complete : ∀ k x, Sol k x → admissible k x = true)
    (base : ∀ x, Sol 0 x → done x = true)
    (step : ∀ k x, Sol (k+1) x → done x = true ∨ ∃ y ∈ children k x, Sol k y)
    (k : Nat) (x : α) (h : Sol k x) : plain admissible done children k x = true := by
  induction k generalizing x with
  | zero => simp only [plain, admissible_complete 0 x h, Bool.true_eq, ite_true, base x h]
  | succ k ih =>
    simp only [plain, admissible_complete (k+1) x h, Bool.true_eq, ite_true]
    rcases step k x h with hd | ⟨y, hy, hs⟩
    · simp only [hd, Bool.true_or]
    · simp only [Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨y, hy, ih y hs⟩

lemma run_reject (admissible : Nat → States width → Bool) (done : States width → Bool)
    (children : Nat → States width → List (States width)) (Sol : Nat → States width → Prop)
    (admissible_complete : ∀ k x, Sol k x → admissible k x = true)
    (base : ∀ x, Sol 0 x → done x = true)
    (step : ∀ k x, Sol (k+1) x → done x = true ∨ ∃ y ∈ children k x, Sol k y)
    (k : Nat) (ws : States width) (h : run admissible done children k ws = false) : ¬ Sol k ws := by
  intro hs
  have ht := plain_complete admissible done children Sol admissible_complete base step k ws hs
  rw [← run_correct, h] at ht
  contradiction


def treeHitFrom (threshold k : Nat) (ws : States width) (cache : TreeCache) : Bool :=
  decide (threshold ≤ k) && treeHit k ws cache

lemma tree_hitFrom_sound {admissible : Nat → States width → Bool} {done : States width → Bool} {children : Nat → States width → List (States width)}
    (threshold k : Nat) (ws : States width) (cache : TreeCache) (hc : TreeGood admissible done children cache)
    (h : treeHitFrom threshold k ws cache = true) : plain admissible done children k ws = false := by
  simp only [treeHitFrom, Bool.and_eq_true] at h
  exact hc.2 k ws h.2

def treePutFrom (threshold k : Nat) (ws : States width) (cache : TreeCache) : TreeCache :=
  if threshold ≤ k then treePut k ws cache else cache

lemma tree_putFrom_good {admissible : Nat → States width → Bool} {done : States width → Bool} {children : Nat → States width → List (States width)}
    (threshold k : Nat) (ws : States width) (cache : TreeCache) (hc : TreeGood admissible done children cache)
    (h : plain admissible done children k ws = false) : TreeGood admissible done children (treePutFrom threshold k ws cache) := by
  unfold treePutFrom
  split_ifs
  · exact tree_put_good k ws cache hc h
  · exact hc

def runFrom (threshold : Nat) (admissible : Nat → States width → Bool) (done : States width → Bool) (children : Nat → States width → List (States width))
    (k : Nat) (ws : States width) : Bool :=
  (search (treeHitFrom threshold) (treePutFrom threshold) admissible done children k ws ∅).1

lemma runFrom_correct (threshold : Nat) (admissible : Nat → States width → Bool) (done : States width → Bool) (children : Nat → States width → List (States width))
    (k : Nat) (ws : States width) : runFrom threshold admissible done children k ws = plain admissible done children k ws := by
  exact search_run (treeHitFrom threshold) (treePutFrom threshold) admissible done children (TreeGood admissible done children)
    (fun k ws cache hc hh => tree_hitFrom_sound threshold k ws cache hc hh)
    (fun k ws cache hc hh => tree_putFrom_good threshold k ws cache hc hh)
    k ws ∅ (tree_good_empty admissible done children)

end MemoPruned


namespace MemoActualPruned

open SearchKernel
variable {width : Nat}

abbrev State := List (BitVec width)

def insertW (v : BitVec width) : List (BitVec width) → List (BitVec width)
  | [] => [v]
  | x :: xs => if v ≤ x then v :: x :: xs else x :: insertW v xs

def ordered (ws : List (BitVec width)) := ws.foldr insertW []

lemma insertW_perm (v : BitVec width) (ws : List (BitVec width)) :
    (insertW v ws).Perm (v :: ws) := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insertW]
    split
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

lemma ordered_perm (ws : List (BitVec width)) : (ordered ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih => exact (insertW_perm x (ordered xs)).trans (ih.cons x)

lemma perm_set {u v : List (BitVec width)} (p : u.Perm v) : u.toFinset = v.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (p.mem_iff : a ∈ u ↔ a ∈ v)

def done (goal : BitVec width) (ws : List (BitVec width)) : Bool :=
  ws == [goal] || ws == [~~~goal]

def children (goal : BitVec width) (rows : List (Fin width)) (k : Nat)
    (ws : List (BitVec width)) : List (List (BitVec width)) :=
  (pairs ws).flatMap fun (a,b,r) =>
    (ops a b).flatMap fun z =>
      if z ∈ a :: b :: r then [] else
        (keepChoices a b r).filterMap fun kept =>
          if kept.length ≤ k ∧ separates goal rows (z :: kept) = true
          then some (ordered (z :: kept)) else none

lemma base_complete {goal g : BitVec width} (hg : g = goal ∨ g = ~~~goal)
    (ws : List (BitVec width)) (h : ws.Nodup ∧ live basicOps g 0 ws.toFinset) :
    done goal ws = true := by
  have he := singleton_list h.1 h.2
  rcases hg with rfl | rfl <;> simp [done, he]

lemma step_complete {goal g : BitVec width} (hg : g = goal ∨ g = ~~~goal)
    (rows : List (Fin width)) (k : Nat) (ws : List (BitVec width))
    (h : ws.Nodup ∧ live basicOps g (k+1) ws.toFinset) :
    done goal ws = true ∨ ∃ child ∈ children goal rows k ws,
      child.Nodup ∧ live basicOps g k child.toFinset := by
  obtain ⟨hn, hlive⟩ := h
  rcases first_live hlive with hend | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · left
    have he := singleton_list hn hend
    rcases hg with rfl | rfl <;> simp [done, he]
  · right
    obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : BitVec width} (perm : ws.Perm (a :: b :: r))
        (hmem : (a,b,r) ∈ pairs ws)
        (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
        ∃ child ∈ children goal rows k ws,
          child.Nodup ∧ live basicOps g k child.toFinset := by
      obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
      have hznew : z ∉ kept := by
        intro hu
        apply hout
        rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hl : live basicOps g k (z :: kept).toFinset := by simpa [hfin] using tail
      have hc := live_card hl
      rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
      have fresh : z ∉ a :: b :: r := by
        intro hzmem
        exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hzmem))
      refine ⟨ordered (z :: kept), ?_, (ordered_perm _).nodup_iff.mpr hnd, ?_⟩
      · apply List.mem_flatMap.mpr
        refine ⟨(a,b,r), hmem, List.mem_flatMap.mpr ⟨z, List.mem_toFinset.mp hop, ?_⟩⟩
        simp only [if_neg fresh]
        exact List.mem_filterMap.mpr ⟨kept, hk, by simp [show kept.length ≤ k by omega,
          separates_complete hg rows hl]⟩
      · rwa [perm_set (ordered_perm _)]
    rcases hm with direct | swap
    · exact go hp direct hs hz
    · exact go (hp.trans (.swap _ _ _)) swap (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)

lemma run_complete {goal g : BitVec width} (hg : g = goal ∨ g = ~~~goal)
    (admissible : Nat → List (BitVec width) → Bool)
    (admissible_complete : ∀ k ws, ws.Nodup → live basicOps g k ws.toFinset → admissible k ws = true)
    (rows : List (Fin width)) (threshold k : Nat) (ws : List (BitVec width))
    (hn : ws.Nodup) (h : live basicOps g k ws.toFinset) :
    MemoPruned.runFrom threshold admissible (done goal) (children goal rows) k ws = true := by
  rw [MemoPruned.runFrom_correct]
  exact MemoPruned.plain_complete admissible (done goal) (children goal rows)
    (fun k ws => ws.Nodup ∧ live basicOps g k ws.toFinset)
    (fun k ws h => admissible_complete k ws h.1 h.2)
    (base_complete hg) (step_complete hg rows) k ws ⟨hn,h⟩

def search (goal : BitVec width) (admissible : Nat → List (BitVec width) → Bool)
    (threshold n : Nat) (inputs : List (BitVec width)) : Bool :=
  let rows := falseRows goal
  inputs.sublists.any fun ws => decide (ws.length ≤ n+1) && separates goal rows ws &&
    MemoPruned.runFrom threshold admissible (done goal) (children goal rows) n ws

lemma search_complete {goal g : BitVec width} (hg : g = goal ∨ g = ~~~goal)
    (admissible : Nat → List (BitVec width) → Bool)
    (admissible_complete : ∀ k ws, ws.Nodup → live basicOps g k ws.toFinset → admissible k ws = true)
    (threshold n : Nat) (inputs : List (BitVec width)) (hn : inputs.Nodup)
    (h : build basicOps g n inputs.toFinset) : search goal admissible threshold n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, separates_complete hg (falseRows goal) hl',
      run_complete hg admissible admissible_complete (falseRows goal) threshold n ws hnd hl']⟩

lemma no_build {goal g : BitVec width} (hg : g = goal ∨ g = ~~~goal)
    (admissible : Nat → List (BitVec width) → Bool)
    (admissible_complete : ∀ k ws, ws.Nodup → live basicOps g k ws.toFinset → admissible k ws = true)
    (threshold n : Nat) (inputs : List (BitVec width)) (hn : inputs.Nodup)
    (rejected : search goal admissible threshold n inputs = false) : ¬ build basicOps g n inputs.toFinset := by
  intro h
  have found := search_complete hg admissible admissible_complete threshold n inputs hn h
  rw [rejected] at found
  contradiction

end MemoActualPruned


def graphEdge (graph : List ℕ) (i j : ℕ) : Bool :=
  (graph.getD i 0).testBit j || (graph.getD j 0).testBit i

def colorPrefix (f : ℕ → ℕ) (n : ℕ) : List ℕ := (List.range n).map f

lemma colorPrefix_length (f : ℕ → ℕ) (n : ℕ) : (colorPrefix f n).length = n := by
  simp [colorPrefix]

lemma colorPrefix_get (f : ℕ → ℕ) (n i : ℕ) (hi : i < n) :
    (colorPrefix f n).getD i 0 = f i := by
  simp [colorPrefix, List.getD_eq_getElem?_getD, hi]

lemma colorPrefix_succ (f : ℕ → ℕ) (n : ℕ) :
    colorPrefix f (n + 1) = colorPrefix f n ++ [f n] := by
  simp [colorPrefix, List.range_succ]

def fitsColor (graph assigned : List ℕ) (c : ℕ) : Bool :=
  !(graphEdge graph assigned.length assigned.length) &&
    (List.range assigned.length).all (fun i =>
      !(graphEdge graph assigned.length i) || assigned.getD i 0 != c)

def colorSearch (graph : List ℕ) (colors : ℕ) : ℕ → List ℕ → Bool
  | 0, _ => true
  | k + 1, assigned => (List.range colors).any (fun c =>
      fitsColor graph assigned c && colorSearch graph colors k (assigned ++ [c]))

def graphColorable (graph : List ℕ) (colors : ℕ) : Prop :=
  ∃ f : ℕ → ℕ, (∀ i < graph.length, f i < colors) ∧
    ∀ i < graph.length, ∀ j < graph.length,
      (graph.getD i 0).testBit j = true → f i ≠ f j

def graphColorCheck (graph : List ℕ) (colors : ℕ) : Bool :=
  colorSearch graph colors graph.length []

lemma graphEdge_colors {graph : List ℕ} {f : ℕ → ℕ}
    (hproper : ∀ i < graph.length, ∀ j < graph.length,
      (graph.getD i 0).testBit j = true → f i ≠ f j)
    {i j : ℕ} (hi : i < graph.length) (hj : j < graph.length)
    (h : graphEdge graph i j = true) : f i ≠ f j := by
  simp only [graphEdge, Bool.or_eq_true] at h
  rcases h with h | h
  · exact hproper i hi j hj h
  · exact Ne.symm (hproper j hj i hi h)

lemma fitsColor_prefix {graph : List ℕ} {f : ℕ → ℕ}
    (hproper : ∀ i < graph.length, ∀ j < graph.length,
      (graph.getD i 0).testBit j = true → f i ≠ f j)
    {n : ℕ} (hn : n < graph.length) :
    fitsColor graph (colorPrefix f n) (f n) = true := by
  have hself : graphEdge graph n n = false := by
    cases he : graphEdge graph n n with
    | false => rfl
    | true => exact False.elim ((graphEdge_colors hproper hn hn he) rfl)
  simp only [fitsColor, colorPrefix_length, hself, Bool.not_false, Bool.true_and]
  apply List.all_eq_true.mpr
  intro i hi
  have hin : i < n := List.mem_range.mp hi
  rw [colorPrefix_get f n i hin]
  cases he : graphEdge graph n i with
  | false => simp
  | true =>
    have hh : f i ≠ f n := Ne.symm (graphEdge_colors hproper hn (by omega) he)
    simp [hh]

lemma colorSearch_complete {graph : List ℕ} {colors : ℕ} {f : ℕ → ℕ}
    (hbound : ∀ i < graph.length, f i < colors)
    (hproper : ∀ i < graph.length, ∀ j < graph.length,
      (graph.getD i 0).testBit j = true → f i ≠ f j)
    (k n : ℕ) (hsize : n + k ≤ graph.length) :
    colorSearch graph colors k (colorPrefix f n) = true := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    have hn : n < graph.length := by omega
    apply List.any_eq_true.mpr
    refine ⟨f n, List.mem_range.mpr (hbound n hn), ?_⟩
    simp only [Bool.and_eq_true]
    constructor
    · exact fitsColor_prefix hproper hn
    · simpa only [colorPrefix_succ] using ih (n + 1) (by omega)

lemma graphColorCheck_complete {graph : List ℕ} {colors : ℕ}
    (h : graphColorable graph colors) : graphColorCheck graph colors = true := by
  obtain ⟨f, hbound, hproper⟩ := h
  simpa [graphColorCheck, colorPrefix] using
    colorSearch_complete hbound hproper graph.length 0 (by omega)

lemma not_graphColorable_of_check {graph : List ℕ} {colors : ℕ}
    (h : graphColorCheck graph colors = false) : ¬ graphColorable graph colors := by
  intro hc
  have hh := graphColorCheck_complete hc
  rw [h] at hh
  cases hh

def graphEmptyCheck (graph : List ℕ) : Bool :=
  graph.all (fun row => decide (BitVec.ofNat graph.length row = 0))

lemma graphEmptyCheck_complete {graph : List ℕ} (h : graphColorable graph 1) :
    graphEmptyCheck graph = true := by
  obtain ⟨f, hbound, hproper⟩ := h
  apply List.all_eq_true.mpr
  intro row hrow
  obtain ⟨i, hin, hroweq⟩ := List.mem_iff_getElem.mp hrow
  have hr : graph.getD i 0 = row := by
    simp [List.getD_eq_getElem?_getD, hin, hroweq]
  apply decide_eq_true
  rw [← hr]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro j hj
  have hfalse : (graph.getD i 0).testBit j = false := by
    cases he : (graph.getD i 0).testBit j with
    | false => rfl
    | true =>
      have hh := hproper i hin j hj he
      have hb1 := hbound i hin
      have hb2 := hbound j hj
      omega
  simp only [BitVec.getLsbD_ofNat, hj, decide_true, Bool.true_and, hfalse]
  change false = (BitVec.ofNat graph.length 0).getLsbD j
  simp [BitVec.getLsbD_ofNat]

def graphColorFast (graph : List ℕ) (colors : ℕ) : Bool :=
  if colors = 1 then graphEmptyCheck graph else graphColorCheck graph colors

lemma graphColorFast_complete {graph : List ℕ} {colors : ℕ}
    (h : graphColorable graph colors) : graphColorFast graph colors = true := by
  unfold graphColorFast
  split
  next hc => subst colors; exact graphEmptyCheck_complete h
  next hc => exact graphColorCheck_complete h

lemma not_graphColorable_of_fast {graph : List ℕ} {colors : ℕ}
    (h : graphColorFast graph colors = false) : ¬ graphColorable graph colors := by
  intro hc
  have hh := graphColorFast_complete hc
  rw [h] at hh
  cases hh

lemma graphColorable_of_fin {graph : List ℕ} {colors : ℕ}
    (f : Fin graph.length → Fin colors)
    (hproper : ∀ i j, (graph.getD i.val 0).testBit j.val = true → f i ≠ f j) :
    graphColorable graph colors := by
  let g : ℕ → ℕ := fun i => if hi : i < graph.length then (f ⟨i, hi⟩).val else 0
  refine ⟨g, ?_, ?_⟩
  · intro i hi
    simp [g, hi]
  · intro i hi j hj he
    have hh := hproper ⟨i, hi⟩ ⟨j, hj⟩ he
    simp only [g, hi, hj, dite_true]
    intro eq
    apply hh
    exact Fin.ext eq

lemma not_fin_coloring_of_fast {graph : List ℕ} {colors : ℕ}
    (h : graphColorFast graph colors = false)
    (f : Fin graph.length → Fin colors)
    (hproper : ∀ i j, (graph.getD i.val 0).testBit j.val = true → f i ≠ f j) : False :=
  not_graphColorable_of_fast h (graphColorable_of_fin f hproper)


end PEqualNP.Outside.L_meta_10760

namespace PEqualNP.Outside.L_meta_10760

def inducedGraph (graph chosen : List ℕ) : List ℕ :=
  chosen.map fun v => (BitVec.ofBoolListLE (chosen.map fun u => graphEdge graph v u)).toNat

lemma inducedGraph_length (graph chosen : List ℕ) :
    (inducedGraph graph chosen).length = chosen.length := by
  simp only [inducedGraph, List.length_map]

lemma inducedGraph_bit (graph chosen : List ℕ) (i j : ℕ)
    (hi : i < chosen.length) (hj : j < chosen.length) :
    ((inducedGraph graph chosen).getD i 0).testBit j =
      graphEdge graph (chosen.getD i 0) (chosen.getD j 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa only [inducedGraph_length] using hi)]
  simp only [inducedGraph, List.getElem_map, BitVec.testBit_toNat,
    BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hj),
    List.getElem_map, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]

lemma graphColorable_induced {graph chosen : List ℕ} {colors : ℕ}
    (hc : graphColorable graph colors)
    (hchosen : ∀ v ∈ chosen, v < graph.length) :
    graphColorable (inducedGraph graph chosen) colors := by
  obtain ⟨f, hbound, hproper⟩ := hc
  have hv (i : ℕ) (hi : i < chosen.length) : chosen.getD i 0 < graph.length := by
    rw [List.getD_eq_getElem _ _ hi]
    exact hchosen _ (List.getElem_mem hi)
  refine ⟨fun i => f (chosen.getD i 0), ?_, ?_⟩
  · intro i hi
    rw [inducedGraph_length] at hi
    exact hbound _ (hv i hi)
  · intro i hi j hj he
    rw [inducedGraph_length] at hi hj
    rw [inducedGraph_bit graph chosen i j hi hj] at he
    exact graphEdge_colors hproper (hv i hi) (hv j hj) he

def graphDegree (graph : List ℕ) (v : ℕ) : ℕ :=
  ((List.range graph.length).filter fun u => graphEdge graph v u).length

def degreeInsert (a : ℕ × ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [a]
  | b :: rest => if b.1 ≤ a.1 then a :: b :: rest else b :: degreeInsert a rest

def degreeSort : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | a :: rest => degreeInsert a (degreeSort rest)

def graphOrder (graph : List ℕ) : List ℕ :=
  (degreeSort (((List.range graph.length).map fun v => (graphDegree graph v, v)).filter
    fun entry => 0 < entry.1)).map Prod.snd

lemma mem_degreeInsert (a entry : ℕ × ℕ) (entries : List (ℕ × ℕ)) :
    entry ∈ degreeInsert a entries ↔ entry = a ∨ entry ∈ entries := by
  induction entries with
  | nil => simp [degreeInsert]
  | cons b rest ih =>
    simp only [degreeInsert]
    split
    · simp only [List.mem_cons]
    · simp only [List.mem_cons, ih]
      tauto

lemma mem_degreeSort (entry : ℕ × ℕ) (entries : List (ℕ × ℕ)) :
    entry ∈ degreeSort entries ↔ entry ∈ entries := by
  induction entries with
  | nil => rfl
  | cons a rest ih =>
    simp only [degreeSort, mem_degreeInsert, ih, List.mem_cons]

lemma graphOrder_valid (graph : List ℕ) :
    ∀ v ∈ graphOrder graph, v < graph.length := by
  intro v hv
  simp only [graphOrder, List.mem_map] at hv
  obtain ⟨entry, he, hvalue⟩ := hv
  rw [mem_degreeSort] at he
  have hentry := (List.mem_filter.mp he).1
  obtain ⟨u, hu, hue⟩ := List.mem_map.mp hentry
  have hlt : u < graph.length := List.mem_range.mp hu
  subst entry
  change u = v at hvalue
  simpa only [hvalue] using hlt

def graphOrderedCheck (graph : List ℕ) (colors : ℕ) : Bool :=
  graphColorCheck (inducedGraph graph (graphOrder graph)) colors

lemma graphOrderedCheck_complete {graph : List ℕ} {colors : ℕ}
    (hc : graphColorable graph colors) : graphOrderedCheck graph colors = true := by
  exact graphColorCheck_complete (graphColorable_induced hc (graphOrder_valid graph))

lemma not_graphColorable_of_ordered {graph : List ℕ} {colors : ℕ}
    (h : graphOrderedCheck graph colors = false) : ¬ graphColorable graph colors := by
  intro hc
  have hh := graphOrderedCheck_complete hc
  rw [h] at hh
  cases hh

def graphColorDegreeFast (graph : List ℕ) (colors : ℕ) : Bool :=
  if colors = 1 then graphEmptyCheck graph
  else if 1 < colors then graphOrderedCheck graph colors
  else graphColorCheck graph colors

lemma graphColorDegreeFast_complete {graph : List ℕ} {colors : ℕ}
    (hc : graphColorable graph colors) : graphColorDegreeFast graph colors = true := by
  unfold graphColorDegreeFast
  split
  · next h => subst colors; exact graphEmptyCheck_complete hc
  · split
    · exact graphOrderedCheck_complete hc
    · exact graphColorCheck_complete hc

lemma not_graphColorable_of_degreeFast {graph : List ℕ} {colors : ℕ}
    (h : graphColorDegreeFast graph colors = false) : ¬ graphColorable graph colors := by
  intro hc
  have hh := graphColorDegreeFast_complete hc
  rw [h] at hh
  cases hh



section RowTransport

variable {α β : Type} [DecidableEq α] [DecidableEq β]

lemma build_map_on (ops : α → α → Finset α) (ops' : β → β → Finset β)
    (D : α → Prop) (f : α → β)
    (closed : ∀ a b, D a → D b → ∀ z ∈ ops a b, D z)
    (injectiveOn : ∀ a b, D a → D b → f a = f b → a = b)
    (respects : ∀ a b, D a → D b → ∀ z ∈ ops a b, f z ∈ ops' (f a) (f b))
    {goal : α} {budget : ℕ} {available : Finset α}
    (initial : ∀ a ∈ available, D a) (run : build ops goal budget available) :
    build ops' (f goal) budget (available.image f) := by
  induction budget generalizing available with
  | zero =>
    exact Finset.mem_image.mpr ⟨goal, run, rfl⟩
  | succ budget ih =>
    rcases run with skip | ⟨a, ha, b, hb, distinct, z, hz, tail⟩
    · exact Or.inl (ih initial skip)
    · have da : D a := initial a ha
      have db : D b := initial b hb
      have next : ∀ u ∈ insert z available, D u := by
        intro u hu
        rcases Finset.mem_insert.mp hu with he | hu
        · rw [he]
          exact closed a b da db z hz
        · exact initial u hu
      refine Or.inr ⟨f a, Finset.mem_image.mpr ⟨a, ha, rfl⟩,
        f b, Finset.mem_image.mpr ⟨b, hb, rfl⟩,
        fun he => distinct (injectiveOn a b da db he),
        f z, respects a b da db z hz, ?_⟩
      simpa only [Finset.image_insert] using ih next tail

lemma live_map_on (ops : α → α → Finset α) (ops' : β → β → Finset β)
    (D : α → Prop) (f : α → β)
    (closed : ∀ a b, D a → D b → ∀ z ∈ ops a b, D z)
    (injectiveOn : ∀ a b, D a → D b → f a = f b → a = b)
    (respects : ∀ a b, D a → D b → ∀ z ∈ ops a b, f z ∈ ops' (f a) (f b))
    {goal : α} {budget : ℕ} {available : Finset α}
    (initial : ∀ a ∈ available, D a) (run : live ops goal budget available) :
    live ops' (f goal) budget (available.image f) := by
  induction budget generalizing available with
  | zero =>
    change available = {goal} at run
    simp only [live, run, Finset.image_singleton]
  | succ budget ih =>
    rcases run with skip | ⟨a, ha, b, hb, distinct, z, hz, fresh, rest, hs, tail⟩
    · exact Or.inl (ih initial skip)
    · have da : D a := initial a ha
      have db : D b := initial b hb
      have dz : D z := closed a b da db z hz
      have restIn : rest ⊆ available := by
        intro u hu
        rw [hs]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)
      have next : ∀ u ∈ insert z rest, D u := by
        intro u hu
        rcases Finset.mem_insert.mp hu with he | hu
        · simpa only [he] using dz
        · exact initial u (restIn hu)
      have freshImage : f z ∉ available.image f := by
        intro hmem
        obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hmem
        exact fresh ((injectiveOn u z (initial u hu) dz he) ▸ hu)
      refine Or.inr ⟨f a, Finset.mem_image.mpr ⟨a, ha, rfl⟩,
        f b, Finset.mem_image.mpr ⟨b, hb, rfl⟩,
        fun he => distinct (injectiveOn a b da db he),
        f z, respects a b da db z hz, freshImage,
        rest.image f, ?_, ?_⟩
      · rw [hs, Finset.image_insert, Finset.image_insert]
      · simpa only [Finset.image_insert] using ih next tail

end RowTransport

def pullback {m n : ℕ} (ρ : Fin n → Fin m) (w : BitVec m) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun j => w[(ρ j).val]))).cast (by simp)

lemma pullback_bit {m n : ℕ} (ρ : Fin n → Fin m) (w : BitVec m) (j : Fin n) :
    (pullback ρ w)[j.val] = w[(ρ j).val] := by
  simp [pullback, ← BitVec.getLsbD_eq_getElem]

lemma pullback_zero {m n : ℕ} (ρ : Fin n → Fin m) : pullback ρ 0 = 0 := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simpa using pullback_bit ρ 0 ⟨i, hi⟩

lemma pullback_not {m n : ℕ} (ρ : Fin n → Fin m) (w : BitVec m) :
    pullback ρ (~~~w) = ~~~(pullback ρ w) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simpa only [BitVec.getElem_not, pullback_bit ρ w ⟨i, hi⟩] using
    pullback_bit ρ (~~~w) ⟨i, hi⟩

lemma pullback_and {m n : ℕ} (ρ : Fin n → Fin m) (u w : BitVec m) :
    pullback ρ (u &&& w) = pullback ρ u &&& pullback ρ w := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simpa only [BitVec.getElem_and, pullback_bit ρ u ⟨i, hi⟩,
    pullback_bit ρ w ⟨i, hi⟩] using pullback_bit ρ (u &&& w) ⟨i, hi⟩

lemma pullback_or {m n : ℕ} (ρ : Fin n → Fin m) (u w : BitVec m) :
    pullback ρ (u ||| w) = pullback ρ u ||| pullback ρ w := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simpa only [BitVec.getElem_or, pullback_bit ρ u ⟨i, hi⟩,
    pullback_bit ρ w ⟨i, hi⟩] using pullback_bit ρ (u ||| w) ⟨i, hi⟩



lemma pullback_ops {m n : ℕ} (ρ : Fin n → Fin m) (u w z : BitVec m)
    (hz : z ∈ basicOps u w) : pullback ρ z ∈ basicOps (pullback ρ u) (pullback ρ w) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil,
    or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp [basicOps, ops, pullback_and, pullback_or, pullback_not]



def canonicalAt {m : ℕ} (ref : Fin m) (w : BitVec m) : BitVec m :=
  if w[ref.val] then ~~~w else w

lemma canonicalAt_bit {m : ℕ} (ref : Fin m) (w : BitVec m) :
    (canonicalAt ref w)[ref.val] = false := by
  cases h : w[ref.val] <;> simp [canonicalAt, h]

lemma canonicalAt_of_false {m : ℕ} (ref : Fin m) (w : BitVec m)
    (h : w[ref.val] = false) : canonicalAt ref w = w := by
  simp only [canonicalAt, h, Bool.false_eq_true, ite_false]

lemma canonicalAt_not {m : ℕ} (ref : Fin m) (w : BitVec m) :
    canonicalAt ref (~~~w) = canonicalAt ref w := by
  cases h : w[ref.val] <;> simp [canonicalAt, h]

lemma canonicalAt_eq_iff {m : ℕ} (ref : Fin m) (u w : BitVec m) :
    canonicalAt ref u = canonicalAt ref w ↔ u = w ∨ u = ~~~w := by
  constructor
  · intro h
    cases hu : u[ref.val] <;> cases hw : w[ref.val] <;>
      simp only [canonicalAt, hu, hw, Bool.false_eq_true,
        ite_false, ite_true] at h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr (by simpa only [BitVec.not_not] using congrArg (fun z => ~~~z) h)
    · exact Or.inl (by simpa only [BitVec.not_not] using congrArg (fun z => ~~~z) h)
  · rintro (rfl | rfl)
    · rfl
    · exact canonicalAt_not ref w

lemma canonicalAt_ops {m : ℕ} (ref : Fin m) (u w z : BitVec m)
    (hz : z ∈ basicOps u w) :
    canonicalAt ref z ∈ basicOps (canonicalAt ref u) (canonicalAt ref w) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil,
    or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  all_goals cases hu : u[ref.val] <;> cases hw : w[ref.val] <;>
    simp [canonicalAt, basicOps, ops, hu, hw, BitVec.not_and, BitVec.not_or,
      BitVec.and_comm, BitVec.or_comm]

lemma zeroAt_ops {m : ℕ} (ref : Fin m) (u w : BitVec m)
    (hu : u[ref.val] = false) (hw : w[ref.val] = false)
    (z : BitVec m) (hz : z ∈ basicOps u w) : z[ref.val] = false := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil,
    or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> simp [hu, hw]

lemma pullback_rowEquiv_injective {m n : ℕ} (e : Fin n ≃ Fin m) :
    Function.Injective (pullback e) := by
  intro u w he
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hb := congrArg (fun z : BitVec n => z[(e.symm ⟨i, hi⟩).val]) he
  simpa only [pullback_bit, Equiv.apply_symm_apply] using hb

def canonicalTransport {m n : ℕ} (e : Fin n ≃ Fin m) (ref : Fin n)
    (w : BitVec m) : BitVec n := canonicalAt ref (pullback e w)

lemma canonicalTransport_injective_zero {m n : ℕ}
    (e : Fin n ≃ Fin m) (src : Fin m) (dst : Fin n)
    (u w : BitVec m) (hu : u[src.val] = false) (hw : w[src.val] = false)
    (he : canonicalTransport e dst u = canonicalTransport e dst w) : u = w := by
  rcases (canonicalAt_eq_iff dst _ _).mp he with same | opposite
  · exact pullback_rowEquiv_injective e same
  · have inv : u = ~~~w := pullback_rowEquiv_injective e (by
      simpa only [pullback_not] using opposite)
    have bad := congrArg (fun z : BitVec m => z[src.val]) inv
    simp only [BitVec.getElem_not, hu, hw, Bool.not_false] at bad
    contradiction

lemma canonicalTransport_ops {m n : ℕ} (e : Fin n ≃ Fin m) (ref : Fin n)
    (u w z : BitVec m) (hz : z ∈ basicOps u w) :
    canonicalTransport e ref z ∈
      basicOps (canonicalTransport e ref u) (canonicalTransport e ref w) :=
  canonicalAt_ops ref _ _ _ (pullback_ops e u w z hz)

lemma build_canonicalTransport {m n budget : ℕ}
    {roots : Finset (BitVec m)} {goal : BitVec m}
    (e : Fin n ≃ Fin m) (src : Fin m) (dst : Fin n)
    (initial : ∀ w ∈ roots, w[src.val] = false)
    (run : build basicOps goal budget roots) :
    build basicOps (canonicalTransport e dst goal) budget
      (roots.image (canonicalTransport e dst)) := by
  exact build_map_on basicOps basicOps (fun w => w[src.val] = false)
    (canonicalTransport e dst) (zeroAt_ops src)
    (canonicalTransport_injective_zero e src dst)
    (fun a b _ _ z hz => canonicalTransport_ops e dst a b z hz) initial run

lemma live_canonicalTransport {m n budget : ℕ}
    {roots : Finset (BitVec m)} {goal : BitVec m}
    (e : Fin n ≃ Fin m) (src : Fin m) (dst : Fin n)
    (initial : ∀ w ∈ roots, w[src.val] = false)
    (run : live basicOps goal budget roots) :
    live basicOps (canonicalTransport e dst goal) budget
      (roots.image (canonicalTransport e dst)) := by
  exact live_map_on basicOps basicOps (fun w => w[src.val] = false)
    (canonicalTransport e dst) (zeroAt_ops src)
    (canonicalTransport_injective_zero e src dst)
    (fun a b _ _ z hz => canonicalTransport_ops e dst a b z hz) initial run

lemma pullback_rowEquiv_inverse {m n : ℕ} (e : Fin n ≃ Fin m) (w : BitVec m) :
    pullback e.symm (pullback e w) = w := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [pullback_bit e.symm (pullback e w) ⟨i, hi⟩,
    pullback_bit e w (e.symm ⟨i, hi⟩)]
  simp only [Equiv.apply_symm_apply]

lemma canonicalTransport_roundtrip {m n : ℕ}
    (e : Fin n ≃ Fin m) (src : Fin m) (dst : Fin n) (w : BitVec m) :
    canonicalTransport e.symm src (canonicalTransport e dst w) = canonicalAt src w := by
  change canonicalAt src (pullback e.symm (canonicalAt dst (pullback e w))) = _
  by_cases phase : (pullback e w)[dst.val] = true
  · have hc : canonicalAt dst (pullback e w) = ~~~(pullback e w) := by
      simp only [canonicalAt, phase, ite_true]
    rw [hc, pullback_not, pullback_rowEquiv_inverse, canonicalAt_not]
  · have hc : canonicalAt dst (pullback e w) = pullback e w := by
      simp [canonicalAt, phase]
    rw [hc, pullback_rowEquiv_inverse]

lemma canonicalTransport_roots_zero {m n : ℕ}
    (e : Fin n ≃ Fin m) (dst : Fin n) (roots : Finset (BitVec m)) :
    ∀ w ∈ roots.image (canonicalTransport e dst), w[dst.val] = false := by
  intro w hw
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw
  exact canonicalAt_bit dst (pullback e u)

lemma canonicalTransport_roots_inverse {m n : ℕ}
    (e : Fin n ≃ Fin m) (src : Fin m) (dst : Fin n) (roots : Finset (BitVec m))
    (initial : ∀ w ∈ roots, w[src.val] = false) :
    (roots.image (canonicalTransport e dst)).image (canonicalTransport e.symm src) = roots := by
  rw [Finset.image_image]
  have inv : ∀ w ∈ roots,
      canonicalTransport e.symm src (canonicalTransport e dst w) = w := by
    intro w hw
    rw [canonicalTransport_roundtrip, canonicalAt_of_false src w (initial w hw)]
  ext w
  constructor
  · intro h
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp h
    change canonicalTransport e.symm src (canonicalTransport e dst u) = w at he
    rw [inv u hu] at he
    exact he ▸ hu
  · intro hw
    exact Finset.mem_image.mpr ⟨w, hw, inv w hw⟩

lemma build_iff_canonicalTransport {m n budget : ℕ}
    (roots : Finset (BitVec m)) (goal : BitVec m)
    (e : Fin n ≃ Fin m) (src : Fin m) (dst : Fin n)
    (initial : ∀ w ∈ roots, w[src.val] = false) (targetZero : goal[src.val] = false) :
    build basicOps goal budget roots ↔
      build basicOps (canonicalTransport e dst goal) budget
        (roots.image (canonicalTransport e dst)) := by
  constructor
  · exact build_canonicalTransport e src dst initial
  · intro run
    have back := build_canonicalTransport e.symm dst src
      (canonicalTransport_roots_zero e dst roots) run
    simpa only [canonicalTransport_roundtrip, canonicalAt_of_false src goal targetZero,
      canonicalTransport_roots_inverse e src dst roots initial] using back

lemma live_iff_canonicalTransport {m n budget : ℕ}
    (roots : Finset (BitVec m)) (goal : BitVec m)
    (e : Fin n ≃ Fin m) (src : Fin m) (dst : Fin n)
    (initial : ∀ w ∈ roots, w[src.val] = false) (targetZero : goal[src.val] = false) :
    live basicOps goal budget roots ↔
      live basicOps (canonicalTransport e dst goal) budget
        (roots.image (canonicalTransport e dst)) := by
  constructor
  · exact live_canonicalTransport e src dst initial
  · intro run
    have back := live_canonicalTransport e.symm dst src
      (canonicalTransport_roots_zero e dst roots) run
    simpa only [canonicalTransport_roundtrip, canonicalAt_of_false src goal targetZero,
      canonicalTransport_roots_inverse e src dst roots initial] using back

lemma build_iff_canonicalAutomorphism {m budget : ℕ}
    (roots : Finset (BitVec m)) (goal : BitVec m)
    (e : Equiv.Perm (Fin m)) (ref : Fin m)
    (initial : ∀ w ∈ roots, w[ref.val] = false) (targetZero : goal[ref.val] = false)
    (goalFixed : canonicalTransport e ref goal = goal) :
    build basicOps goal budget roots ↔
      build basicOps goal budget (roots.image (canonicalTransport e ref)) := by
  simpa only [goalFixed] using build_iff_canonicalTransport roots goal e ref ref initial targetZero

lemma live_iff_canonicalAutomorphism {m budget : ℕ}
    (roots : Finset (BitVec m)) (goal : BitVec m)
    (e : Equiv.Perm (Fin m)) (ref : Fin m)
    (initial : ∀ w ∈ roots, w[ref.val] = false) (targetZero : goal[ref.val] = false)
    (goalFixed : canonicalTransport e ref goal = goal) :
    live basicOps goal budget roots ↔
      live basicOps goal budget (roots.image (canonicalTransport e ref)) := by
  simpa only [goalFixed] using live_iff_canonicalTransport roots goal e ref ref initial targetZero



namespace S64

def symRowData : List Nat := [0, 26, 15, 37, 8, 33, 22, 41, 4, 30, 19, 40, 12, 36, 25, 2, 28, 17, 39, 10, 35, 24, 6, 32, 21, 14, 1, 27, 16, 38, 9, 34, 23, 5, 31, 20, 13, 3, 29, 18, 11, 7, 42, 58, 53, 63, 49, 62, 57, 46, 61, 56, 52, 44, 60, 55, 51, 48, 43, 59, 54, 50, 47, 45]

def symRow (i : Fin 64) : Fin 64 :=
  ⟨symRowData.getD i.val 0 % 64, Nat.mod_lt _ (by decide)⟩

lemma symRow_involutive : Function.Involutive symRow := by
  change ∀ i : Fin 64, symRow (symRow i) = i
  decide +kernel

def symEquiv : Equiv.Perm (Fin 64) :=
  ⟨symRow, symRow, symRow_involutive, symRow_involutive⟩

abbrev symWord (w : BitVec 64) : BitVec 64 :=
  canonicalTransport symEquiv ⟨63, by decide⟩ w

def caseData : List (Fin 7 × Fin 7 × Fin 4) := [(1, 0, 0), (1, 0, 1), (1, 0, 2), (1, 0, 3), (2, 0, 0), (2, 0, 1), (2, 0, 2), (2, 0, 3), (2, 1, 0), (2, 1, 1), (2, 1, 2), (2, 1, 3), (3, 0, 0), (3, 0, 1), (3, 0, 2), (3, 0, 3), (3, 1, 0), (3, 1, 1), (3, 1, 2), (3, 1, 3), (3, 2, 0), (3, 2, 1), (3, 2, 2), (3, 2, 3), (4, 0, 0), (4, 0, 1), (4, 0, 2), (4, 0, 3), (4, 1, 0), (4, 1, 1), (4, 1, 2), (4, 1, 3), (4, 2, 0), (4, 2, 1), (4, 2, 2), (4, 2, 3), (4, 3, 0), (4, 3, 1), (4, 3, 2), (4, 3, 3), (5, 0, 0), (5, 0, 1), (5, 0, 2), (5, 0, 3), (5, 1, 0), (5, 1, 1), (5, 1, 2), (5, 1, 3), (5, 2, 0), (5, 2, 1), (5, 2, 2), (5, 2, 3), (5, 3, 0), (5, 3, 1), (5, 3, 2), (5, 3, 3), (5, 4, 0), (5, 4, 1), (5, 4, 2), (5, 4, 3), (6, 0, 0), (6, 0, 1), (6, 0, 2), (6, 0, 3), (6, 1, 0), (6, 1, 1), (6, 1, 2), (6, 1, 3), (6, 2, 0), (6, 2, 1), (6, 2, 2), (6, 2, 3), (6, 3, 0), (6, 3, 1), (6, 3, 2), (6, 3, 3), (6, 4, 0), (6, 4, 1), (6, 4, 2), (6, 4, 3), (6, 5, 0), (6, 5, 1), (6, 5, 2), (6, 5, 3)]

def caseWord (c : Fin 84) : BitVec 64 :=
  let t := caseData.getD c.val (0, 0, 0)
  firstOp t.1 t.2.1 t.2.2

def symCaseData : List Nat := [57, 56, 58, 59, 55, 54, 52, 53, 39, 38, 36, 37, 51, 50, 48, 49, 35, 34, 32, 33, 20, 21, 23, 22, 45, 44, 46, 47, 29, 28, 30, 31, 18, 19, 17, 16, 10, 11, 9, 8, 41, 40, 42, 43, 25, 24, 26, 27, 14, 15, 13, 12, 6, 7, 5, 4, 1, 0, 2, 3, 82, 83, 80, 81, 78, 79, 76, 77, 72, 73, 74, 75, 68, 69, 70, 71, 66, 67, 64, 65, 62, 63, 60, 61]

def symCase (c : Fin 84) : Fin 84 :=
  ⟨symCaseData.getD c.val 0 % 84, Nat.mod_lt _ (by decide)⟩

def representativeData : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 30, 31, 40, 42, 43, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71]

def representative (r : Fin 45) : Fin 84 :=
  ⟨representativeData.getD r.val 0 % 84, Nat.mod_lt _ (by decide)⟩

def caseIndex (i j : Fin 7) (o : Fin 4) : Fin 84 :=
  ⟨(2 * i.val * (i.val - 1) + 4 * j.val + o.val) % 84, Nat.mod_lt _ (by decide)⟩

set_option maxHeartbeats 8000000 in
lemma caseIndex_correct : ∀ i j : Fin 7, ∀ o : Fin 4, j < i →
    caseWord (caseIndex i j o) = firstOp i j o := by decide +kernel

lemma symGoal_fixed : symWord (~~~sampleGoal64) = ~~~sampleGoal64 := by decide +kernel

lemma symRoots_fixed : signedRoots64.image symWord = signedRoots64 := by decide +kernel

set_option maxHeartbeats 8000000 in
lemma symCases_correct : ∀ c : Fin 84, symWord (caseWord c) = caseWord (symCase c) := by
  decide +kernel

lemma symCase_involutive : Function.Involutive symCase := by
  change ∀ c : Fin 84, symCase (symCase c) = c
  decide +kernel

lemma representatives_cover : ∀ c : Fin 84, ∃ r : Fin 45,
    c = representative r ∨ symCase c = representative r := by decide +kernel

lemma symRoots_zero : ∀ w ∈ signedRoots64, w[63] = false := by
  intro w hw
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
  simp only [sampleInputs64, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

lemma caseWords_zero : ∀ c : Fin 84, (caseWord c)[63] = false := by decide +kernel

lemma live_case_symmetry (c : Fin 84) (budget : ℕ) :
    live basicOps (~~~sampleGoal64) budget (insert (caseWord c) signedRoots64) ↔
      live basicOps (~~~sampleGoal64) budget (insert (caseWord (symCase c)) signedRoots64) := by
  have initial : ∀ w ∈ insert (caseWord c) signedRoots64, w[63] = false := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact caseWords_zero c
    · exact symRoots_zero w hw
  have h := live_iff_canonicalAutomorphism (budget := budget) (insert (caseWord c) signedRoots64)
    (~~~sampleGoal64) symEquiv ⟨63, by decide⟩ initial (by decide +kernel) symGoal_fixed
  change live basicOps (~~~sampleGoal64) budget (insert (caseWord c) signedRoots64) ↔
    live basicOps (~~~sampleGoal64) budget
      ((insert (caseWord c) signedRoots64).image symWord) at h
  simpa only [Finset.image_insert, symCases_correct, symRoots_fixed] using h

lemma reject84_of_reject45 (budget : ℕ)
    (reject : ∀ r : Fin 45, ¬ live basicOps (~~~sampleGoal64) budget
      (insert (caseWord (representative r)) signedRoots64)) :
    ∀ c : Fin 84, ¬ live basicOps (~~~sampleGoal64) budget
      (insert (caseWord c) signedRoots64) := by
  intro c run
  obtain ⟨r, same | mapped⟩ := representatives_cover c
  · exact reject r (same ▸ run)
  · exact reject r (mapped ▸ (live_case_symmetry c budget).mp run)

lemma rejection_from_45_64 (budget : ℕ)
    (reject : ∀ r : Fin 45, ¬ live basicOps (~~~sampleGoal64) budget
      (insert (caseWord (representative r)) signedRoots64)) :
    ∀ i j : Fin 7, j < i → ∀ o : Fin 4,
      ¬ live basicOps (~~~sampleGoal64) budget (insert (firstOp i j o) signedRoots64) := by
  intro i j hji o
  have h := reject84_of_reject45 budget reject (caseIndex i j o)
  rwa [caseIndex_correct i j o hji] at h

end S64
end PEqualNP.Outside.L_meta_10760

namespace PEqualNP.Outside.L_meta_10760.KernelNat64


def mask : Nat := 0xffffffffffffffff
def goal : Nat := 0xffdfebdfbbbf6ca0
def roots : List Nat := [0x844a844a8952aaa, 0x1089308931264ccc, 0x2111c111c23870f0, 0x421e021e03c07f00, 0x7c1ffc1ffc007fff, 0x3fffc0003ffffff, 0x3ffffffffff]
def rows : List Nat := [0, 1, 2, 3, 4, 6, 8, 9, 12, 15, 22, 26, 30, 37, 42, 44, 53]
def ops (a b : Nat) : List Nat :=
  [a &&& b, a ||| b, a &&& (b ^^^ mask), b &&& (a ^^^ mask)]

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rowClass (j w : Nat) : Nat :=
  if (w >>> j) &&& 1 == 1 then w else w ^^^ mask

def survivors (j : Nat) (ws : List Nat) : Nat :=
  ws.foldr (fun w r => rowClass j w &&& r) goal

def collisions (ws : List Nat) : List (Nat × Nat) :=
  rows.filterMap fun j =>
    let bits := survivors j ws
    if bits == 0 then none else some (j, bits)

def separatesNew (cs : List (Nat × Nat)) (ws : List Nat) : Bool :=
  cs.all fun (j, bits) => ws.foldr (fun w r => rowClass j w &&& r) bits == 0

def cmpWords : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => match compare a b with
    | .eq => cmpWords as bs
    | o => o

def insertWord (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs => if a <= b then a :: b :: bs else b :: insertWord a bs

def sortWords : List Nat → List Nat
  | [] => []
  | a :: as => insertWord a (sortWords as)


def rowPattern (row : Nat) : List Nat → Nat
  | [] => 0
  | w :: ws => ((w >>> row) &&& 1) ||| (rowPattern row ws <<< 1)

def labelledPatterns (ws : List Nat) : List (Nat × Bool) :=
  (List.range 64).map fun row => (rowPattern row ws, (goal >>> row) &&& 1 == 1)

def patternSets (ps : List (Nat × Bool)) : Nat × Nat :=
  ps.foldl (fun (positive, negative) (p, label) =>
    if label then (positive ||| (1 <<< p), negative)
    else (positive, negative ||| (1 <<< p))) (0, 0)

def bitTest (w j : Nat) : Bool := (w >>> j) &&& 1 == 1

def phaseMasks (ps : List (Nat × Bool)) (positive negative i j : Nat) : Nat × Nat :=
  let bi := 1 <<< i
  let bj := 1 <<< j
  ps.foldl (fun (pf, nf) (p, label) =>
    let opposite := if label then negative else positive
    if bitTest opposite (p ^^^ bi) && bitTest opposite (p ^^^ bj) then
      let phase := ((p >>> i) &&& 1) ||| (((p >>> j) &&& 1) <<< 1)
      if label then (pf ||| (1 <<< phase), nf)
      else (pf, nf ||| (1 <<< (phase ^^^ 3)))
    else (pf, nf)) (0, 0)

def criticalEdges (ws : List Nat) : List (Nat × Nat) :=
  let ps := labelledPatterns ws
  let (positive, negative) := patternSets ps
  (pairs (List.range ws.length)).filterMap fun (i, j, _) =>
    let (pf, nf) := phaseMasks ps positive negative i j
    if pf &&& nf == 0 then none else some (i, j)

def criticalGraph (ws : List Nat) : List (Nat × Nat) :=
  let es := criticalEdges ws
  (List.range ws.length).map fun i =>
    (i, es.foldl (fun mask (a,b) =>
      if a == i then mask ||| (1 <<< b)
      else if b == i then mask ||| (1 <<< a) else mask) 0)

lemma adj_bitTest (w i : Nat) : bitTest w i = w.testBit i := by
  apply Bool.eq_iff_iff.mpr
  simp only [bitTest, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow,
    Nat.testBit_eq_decide_div_mod_eq, beq_iff_eq, decide_eq_true_eq]

def adj_bitmapStep (acc : Nat × Nat) (item : Nat × Bool) : Nat × Nat :=
  if item.2 then (acc.1 ||| (1 <<< item.1), acc.2)
  else (acc.1, acc.2 ||| (1 <<< item.1))

lemma adj_bitmap_step_pos (acc : Nat × Nat) (item : Nat × Bool) (t : Nat) :
    (adj_bitmapStep acc item).1.testBit t =
      (acc.1.testBit t || (item.2 && decide (item.1 = t))) := by
  rcases acc with ⟨a,b⟩
  rcases item with ⟨p,label⟩
  cases label <;> simp [adj_bitmapStep, Nat.testBit_or, Nat.shiftLeft_eq, Nat.testBit_two_pow]

lemma adj_bitmap_step_neg (acc : Nat × Nat) (item : Nat × Bool) (t : Nat) :
    (adj_bitmapStep acc item).2.testBit t =
      (acc.2.testBit t || (!item.2 && decide (item.1 = t))) := by
  rcases acc with ⟨a,b⟩
  rcases item with ⟨p,label⟩
  cases label <;> simp [adj_bitmapStep, Nat.testBit_or, Nat.shiftLeft_eq, Nat.testBit_two_pow]

lemma adj_bitmap_fold_pos (ps : List (Nat × Bool)) (acc : Nat × Nat) (t : Nat) :
    (ps.foldl adj_bitmapStep acc).1.testBit t =
      (acc.1.testBit t || ps.any (fun item => item.2 && decide (item.1 = t))) := by
  induction ps generalizing acc with
  | nil => simp
  | cons a ps ih =>
    rw [List.foldl_cons, ih, adj_bitmap_step_pos]
    simp only [List.any_cons, Bool.or_assoc]

lemma adj_bitmap_fold_neg (ps : List (Nat × Bool)) (acc : Nat × Nat) (t : Nat) :
    (ps.foldl adj_bitmapStep acc).2.testBit t =
      (acc.2.testBit t || ps.any (fun item => !item.2 && decide (item.1 = t))) := by
  induction ps generalizing acc with
  | nil => simp
  | cons a ps ih =>
    rw [List.foldl_cons, ih, adj_bitmap_step_neg]
    simp only [List.any_cons, Bool.or_assoc]

lemma adj_patternSets_eq (ps : List (Nat × Bool)) :
    patternSets ps = ps.foldl adj_bitmapStep (0,0) := rfl

lemma adj_patternSets_pos (ps : List (Nat × Bool)) (t : Nat) :
    (patternSets ps).1.testBit t = true ↔ (t,true) ∈ ps := by
  rw [adj_patternSets_eq, adj_bitmap_fold_pos]
  simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨p,label⟩, hm, hl, hp⟩
    cases hl
    cases hp
    exact hm
  · intro h
    exact ⟨(t,true),h,rfl,rfl⟩

lemma adj_patternSets_neg (ps : List (Nat × Bool)) (t : Nat) :
    (patternSets ps).2.testBit t = true ↔ (t,false) ∈ ps := by
  rw [adj_patternSets_eq, adj_bitmap_fold_neg]
  simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨p,label⟩, hm, hl, hp⟩
    cases label with
    | false => cases hp; exact hm
    | true => simp at hl
  · intro h
    exact ⟨(t,false),h,rfl,rfl⟩

def adj_phase (p i j : Nat) : Nat :=
  ((p >>> i) &&& 1) ||| (((p >>> j) &&& 1) <<< 1)

def adj_phaseEntry (positive negative i j : Nat) (item : Nat × Bool) : Option (Nat × Bool) :=
  let p := item.1
  let label := item.2
  let opposite := if label then negative else positive
  if bitTest opposite (p ^^^ (1 <<< i)) && bitTest opposite (p ^^^ (1 <<< j)) then
    some (if label then adj_phase p i j else adj_phase p i j ^^^ 3, label)
  else none

def adj_phaseRows (ps : List (Nat × Bool)) (positive negative i j : Nat) : List (Nat × Bool) :=
  ps.filterMap (adj_phaseEntry positive negative i j)

lemma adj_phaseMasks_eq (ps : List (Nat × Bool)) (positive negative i j : Nat) :
    phaseMasks ps positive negative i j = patternSets (adj_phaseRows ps positive negative i j) := by
  unfold phaseMasks patternSets adj_phaseRows
  rw [List.foldl_filterMap]
  change ps.foldl _ (0,0) = ps.foldl _ (0,0)
  apply congrArg (fun f => ps.foldl f (0,0))
  funext acc item
  rcases acc with ⟨pf,nf⟩
  rcases item with ⟨p,label⟩
  cases label <;> simp [adj_phaseEntry, adj_phase] <;> split_ifs <;> rfl

lemma adj_phase_pos {ps : List (Nat × Bool)} {positive negative i j t : Nat}
    (hm : (t,true) ∈ adj_phaseRows ps positive negative i j) :
    ∃ p, (p,true) ∈ ps ∧ bitTest negative (p ^^^ (1 <<< i)) = true ∧
      bitTest negative (p ^^^ (1 <<< j)) = true ∧ adj_phase p i j = t := by
  obtain ⟨⟨p,label⟩, hp, he⟩ := List.mem_filterMap.mp hm
  cases label with
  | false =>
    dsimp [adj_phaseEntry] at he
    split at he <;> simp_all
  | true =>
    dsimp [adj_phaseEntry] at he
    split at he
    · rename_i hc
      have ht : adj_phase p i j = t := congrArg Prod.fst (Option.some.inj he)
      exact ⟨p,hp,(Bool.and_eq_true_iff.mp hc).1,(Bool.and_eq_true_iff.mp hc).2,ht⟩
    · simp at he

lemma adj_phase_neg {ps : List (Nat × Bool)} {positive negative i j t : Nat}
    (hm : (t,false) ∈ adj_phaseRows ps positive negative i j) :
    ∃ q, (q,false) ∈ ps ∧ bitTest positive (q ^^^ (1 <<< i)) = true ∧
      bitTest positive (q ^^^ (1 <<< j)) = true ∧ (adj_phase q i j ^^^ 3) = t := by
  obtain ⟨⟨q,label⟩, hq, he⟩ := List.mem_filterMap.mp hm
  cases label with
  | false =>
    dsimp [adj_phaseEntry] at he
    split at he
    · rename_i hc
      have ht : (adj_phase q i j ^^^ 3) = t := congrArg Prod.fst (Option.some.inj he)
      exact ⟨q,hq,(Bool.and_eq_true_iff.mp hc).1,(Bool.and_eq_true_iff.mp hc).2,ht⟩
    · simp at he
  | true =>
    dsimp [adj_phaseEntry] at he
    split at he <;> simp_all

def adj_patternWitness (ps : List (Nat × Bool)) (i j : Nat) : Prop :=
  ∃ p q, (p,true) ∈ ps ∧ (q,false) ∈ ps ∧
    (p ^^^ (1 <<< i),false) ∈ ps ∧ (p ^^^ (1 <<< j),false) ∈ ps ∧
    (q ^^^ (1 <<< i),true) ∈ ps ∧ (q ^^^ (1 <<< j),true) ∈ ps ∧
    adj_phase p i j = (adj_phase q i j ^^^ 3)

lemma adj_overlap {ps : List (Nat × Bool)} {i j : Nat}
    (hn : (phaseMasks ps (patternSets ps).1 (patternSets ps).2 i j).1 &&&
      (phaseMasks ps (patternSets ps).1 (patternSets ps).2 i j).2 ≠ 0) :
    adj_patternWitness ps i j := by
  obtain ⟨t,ht⟩ := Nat.exists_testBit_of_ne_zero hn
  rw [Nat.testBit_and] at ht
  obtain ⟨hp,hn⟩ := Bool.and_eq_true_iff.mp ht
  rw [adj_phaseMasks_eq] at hp hn
  have hpm := (adj_patternSets_pos _ t).mp hp
  have hnm := (adj_patternSets_neg _ t).mp hn
  obtain ⟨p,hp,hpi,hpj,hpt⟩ := adj_phase_pos hpm
  obtain ⟨q,hq,hqi,hqj,hqt⟩ := adj_phase_neg hnm
  rw [adj_bitTest] at hpi hpj hqi hqj
  exact ⟨p,q,hp,hq,(adj_patternSets_neg _ _).mp hpi,(adj_patternSets_neg _ _).mp hpj,
    (adj_patternSets_pos _ _).mp hqi,(adj_patternSets_pos _ _).mp hqj,hpt.trans hqt.symm⟩

lemma adj_phase_zero (p i j : Nat) : (adj_phase p i j).testBit 0 = p.testBit i := by
  simp [adj_phase]

lemma adj_phase_one (p i j : Nat) : (adj_phase p i j).testBit 1 = p.testBit j := by
  have h1 : (1 : Nat).testBit 1 = false := by decide
  rw [adj_phase, Nat.testBit_or, Nat.testBit_and, h1]
  simp [Nat.testBit_shiftLeft, Nat.testBit_shiftRight]

lemma adj_opposite_phase {p q i j : Nat} (he : adj_phase p i j = (adj_phase q i j ^^^ 3)) :
    p.testBit i ≠ q.testBit i ∧ p.testBit j ≠ q.testBit j := by
  have h0 := congrArg (fun n : Nat => n.testBit 0) he
  have h1 := congrArg (fun n : Nat => n.testBit 1) he
  rw [adj_phase_zero, Nat.testBit_xor, adj_phase_zero] at h0
  rw [adj_phase_one, Nat.testBit_xor, adj_phase_one] at h1
  have ht0 : (3 : Nat).testBit 0 = true := by decide
  have ht1 : (3 : Nat).testBit 1 = true := by decide
  rw [ht0] at h0
  rw [ht1] at h1
  constructor
  · cases hp : p.testBit i <;> cases hq : q.testBit i <;> simp_all
  · cases hp : p.testBit j <;> cases hq : q.testBit j <;> simp_all

lemma singles_mem {a : Nat} {rest ws : List Nat}
    (h : (a, rest) ∈ singles ws) : a ∈ ws ∧ ∀ x ∈ rest, x ∈ ws := by
  induction ws generalizing rest with
  | nil => simp [singles] at h
  | cons b bs ih =>
    simp only [singles, List.mem_cons, List.mem_map] at h
    rcases h with h | ⟨⟨c, cs⟩, hc, he⟩
    · cases h
      exact ⟨by simp, fun x hx => by simp [hx]⟩
    · cases he
      obtain ⟨ha, hr⟩ := ih hc
      refine ⟨by simp [ha], ?_⟩
      intro x hx
      simp only [List.mem_cons] at hx ⊢
      exact hx.imp_right (hr x)

lemma pairs_mem_bounds {a b : Nat} {rest ws : List Nat} (hw : ws.Nodup)
    (h : (a, b, rest) ∈ pairs ws) : a ∈ ws ∧ b ∈ ws ∧ a ≠ b := by
  induction ws generalizing a b rest with
  | nil => simp [pairs] at h
  | cons c cs ih =>
    simp only [List.nodup_cons] at hw
    simp only [pairs, List.mem_append, List.mem_map] at h
    rcases h with ⟨⟨d, ds⟩, hd, he⟩ | ⟨⟨d, e, ds⟩, hd, he⟩
    · cases he
      obtain ⟨hdmem, _⟩ := singles_mem hd
      refine ⟨by simp, by simp [hdmem], ?_⟩
      intro he
      exact hw.1 (he ▸ hdmem)
    · cases he
      obtain ⟨ha, hb, hab⟩ := ih hw.2 hd
      exact ⟨by simp [ha], by simp [hb], hab⟩

lemma pairs_range_bounds {n i j : Nat} {rest : List Nat}
    (h : (i, j, rest) ∈ pairs (List.range n)) : i < n ∧ j < n ∧ i ≠ j := by
  simpa using pairs_mem_bounds (List.nodup_range) h

lemma rowPattern_bit (row i : Nat) (ws : List Nat) :
    (rowPattern row ws).testBit i = (ws.getD i 0).testBit row := by
  induction ws generalizing i with
  | nil => simp [rowPattern]
  | cons w ws ih =>
    cases i with
    | zero => simp [rowPattern]
    | succ i =>
      have h1 : (1 : Nat).testBit (i + 1) = false := by
        rw [show (1 : Nat) = 2 ^ 0 by rfl, Nat.testBit_two_pow]
        simp
      rw [rowPattern, Nat.testBit_or, Nat.testBit_and, h1]
      simpa using ih i

lemma rowPattern_flip {p q i : Nat} {ws : List Nat}
    (h : rowPattern q ws = rowPattern p ws ^^^ (1 <<< i)) (j : Nat) :
    (ws.getD j 0).testBit q = xor ((ws.getD j 0).testBit p) (decide (i = j)) := by
  have hb := congrArg (fun w : Nat => w.testBit j) h
  rw [rowPattern_bit, Nat.testBit_xor, rowPattern_bit] at hb
  simpa [Nat.shiftLeft_eq, Nat.testBit_two_pow] using hb


lemma adj_labelled {ws : List Nat} {pattern : Nat} {label : Bool}
    (hm : (pattern,label) ∈ labelledPatterns ws) :
    ∃ r : Fin 64, rowPattern r.val ws = pattern ∧ goal.testBit r.val = label := by
  obtain ⟨r,hr,he⟩ := List.mem_map.mp hm
  have hr' : r < 64 := List.mem_range.mp hr
  refine ⟨⟨r,hr'⟩,congrArg Prod.fst he,?_⟩
  have hl := congrArg Prod.snd he
  change bitTest goal r = label at hl
  rwa [adj_bitTest] at hl

lemma adj_ofNat_bit (w : Nat) (r : Fin 64) :
    (BitVec.ofNat 64 w)[r.val] = w.testBit r.val := by
  rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat]
  simp only [r.isLt, decide_true, Bool.true_and]

def adj_frontier (ws : List Nat) : Finset (BitVec 64) :=
  (ws.map (BitVec.ofNat 64)).toFinset

def adj_word (ws : List Nat) (i : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (ws.getD i 0)

lemma adj_word_bit (ws : List Nat) (i : Nat) (r : Fin 64) :
    (adj_word ws i)[r.val] = (ws.getD i 0).testBit r.val := adj_ofNat_bit _ _

lemma adj_word_mem {ws : List Nat} {i : Nat} (hi : i < ws.length) :
    adj_word ws i ∈ adj_frontier ws := by
  simp only [adj_word, adj_frontier, List.mem_toFinset, List.mem_map]
  exact ⟨ws.getD i 0, by rw [List.getD_eq_getElem ws 0 hi]; exact List.getElem_mem hi, rfl⟩

lemma adj_mem_word {ws : List Nat} {w : BitVec 64} (hw : w ∈ adj_frontier ws) :
    ∃ k, k < ws.length ∧ adj_word ws k = w := by
  simp only [adj_frontier, List.mem_toFinset, List.mem_map] at hw
  obtain ⟨v,hv,he⟩ := hw
  obtain ⟨k,hk,hv⟩ := List.mem_iff_getElem.mp hv
  exact ⟨k,hk,by rw [adj_word, List.getD_eq_getElem ws 0 hk, hv]; exact he⟩

lemma adj_flip_unique {ws : List Nat} {i : Nat} {p q : Fin 64}
    (hf : rowPattern q.val ws = rowPattern p.val ws ^^^ (1 <<< i)) :
    uniqueSep (adj_frontier ws) (adj_word ws i) p q := by
  constructor
  · have hb := rowPattern_flip hf i
    simp only [decide_true, Bool.xor_true] at hb
    simp only [adj_word_bit]
    rw [hb]
    exact Bool.ne_not.mpr rfl
  · intro w hw hne
    obtain ⟨k,hk,rfl⟩ := adj_mem_word hw
    have hki : i ≠ k := by
      intro he
      exact hne (congrArg (adj_word ws) he.symm)
    have hb := rowPattern_flip hf k
    simpa only [adj_word_bit, hki, decide_false, Bool.xor_false] using hb.symm

lemma adj_unique_symm {S : Finset (BitVec 64)} {a : BitVec 64} {p q : Fin 64}
    (h : uniqueSep S a p q) : uniqueSep S a q p := by
  exact ⟨Ne.symm h.1,fun w hw hne => (h.2 w hw hne).symm⟩


def adj_patternCorners (ps : List (Nat × Bool)) (i j : Nat) : Prop :=
  ∃ p q, (p,true) ∈ ps ∧ (q,false) ∈ ps ∧
    (p ^^^ (1 <<< i),false) ∈ ps ∧ (p ^^^ (1 <<< j),false) ∈ ps ∧
    (q ^^^ (1 <<< i),true) ∈ ps ∧ (q ^^^ (1 <<< j),true) ∈ ps ∧
    p.testBit i ≠ q.testBit i ∧ p.testBit j ≠ q.testBit j

lemma adj_corner_rows {ws : List Nat} {i j : Nat}
    (hi : i < ws.length) (hj : j < ws.length) (hij : i ≠ j)
    (hc : adj_patternCorners (labelledPatterns ws) i j) :
    criticalPair (BitVec.ofNat 64 goal) (adj_frontier ws) (adj_word ws i) (adj_word ws j) := by
  obtain ⟨x,y,hx,hy,hxi,hxj,hyi,hyj,hpi,hpj⟩ := hc
  obtain ⟨p,hp,hpt⟩ := adj_labelled hx
  obtain ⟨q,hq,hqt⟩ := adj_labelled hy
  obtain ⟨ra,hra,hrat⟩ := adj_labelled hxi
  obtain ⟨rb,hrb,hrbt⟩ := adj_labelled hxj
  obtain ⟨sa,hsa,hsat⟩ := adj_labelled hyi
  obtain ⟨sb,hsb,hsbt⟩ := adj_labelled hyj
  have hfra : rowPattern ra.val ws = rowPattern p.val ws ^^^ (1 <<< i) := by rwa [hp]
  have hfrb : rowPattern rb.val ws = rowPattern p.val ws ^^^ (1 <<< j) := by rwa [hp]
  have hfsa : rowPattern sa.val ws = rowPattern q.val ws ^^^ (1 <<< i) := by rwa [hq]
  have hfsb : rowPattern sb.val ws = rowPattern q.val ws ^^^ (1 <<< j) := by rwa [hq]
  have ua := adj_flip_unique hfra
  have ub := adj_flip_unique hfrb
  have usa := adj_unique_symm (adj_flip_unique hfsa)
  have usb := adj_unique_symm (adj_flip_unique hfsb)
  have hne : adj_word ws i ≠ adj_word ws j := by
    have hb := rowPattern_flip hfra j
    simp only [hij, decide_false, Bool.xor_false] at hb
    have hbe : (adj_word ws j)[p.val] = (adj_word ws j)[ra.val] := by
      simpa only [adj_word_bit] using hb.symm
    intro he
    exact ua.1 (by rw [he]; exact hbe)
  have hip : (adj_word ws i)[p.val] ≠ (adj_word ws i)[q.val] := by
    simpa only [adj_word_bit, ← rowPattern_bit, hp, hq] using hpi
  have hjp : (adj_word ws j)[p.val] ≠ (adj_word ws j)[q.val] := by
    simpa only [adj_word_bit, ← rowPattern_bit, hp, hq] using hpj
  have his : (adj_word ws i)[sa.val] = !(adj_word ws i)[q.val] := by
    have hb := rowPattern_flip hfsa i
    simpa only [adj_word_bit, decide_true, Bool.xor_true] using hb
  have hjs : (adj_word ws j)[sb.val] = !(adj_word ws j)[q.val] := by
    have hb := rowPattern_flip hfsb j
    simpa only [adj_word_bit, decide_true, Bool.xor_true] using hb
  have hipa : (adj_word ws i)[p.val] = (adj_word ws i)[sa.val] := by
    rw [his]
    exact Bool.eq_not.mpr hip
  have hjpb : (adj_word ws j)[p.val] = (adj_word ws j)[sb.val] := by
    rw [hjs]
    exact Bool.eq_not.mpr hjp
  refine ⟨adj_word_mem hi, adj_word_mem hj, hne, p,q,ra,rb,sa,sb,?_,?_,?_,?_,?_,?_,ua,ub,usa,usb,hipa,hjpb⟩
  all_goals rwa [adj_ofNat_bit]

lemma adj_witness_rows {ws : List Nat} {i j : Nat}
    (hi : i < ws.length) (hj : j < ws.length) (hij : i ≠ j)
    (hc : adj_patternWitness (labelledPatterns ws) i j) :
    criticalPair (BitVec.ofNat 64 goal) (adj_frontier ws) (adj_word ws i) (adj_word ws j) := by
  apply adj_corner_rows hi hj hij
  obtain ⟨p,q,hp,hq,hpi,hpj,hqi,hqj,he⟩ := hc
  exact ⟨p,q,hp,hq,hpi,hpj,hqi,hqj,adj_opposite_phase he⟩



def lowMasks : List Nat := [0x5555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555, 0x3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff]

def flipPatternBits (i x : Nat) : Nat :=
  ((x &&& lowMasks[i]!) <<< (1 <<< i)) |||
    ((x >>> (1 <<< i)) &&& lowMasks[i]!)

def flipIndexLaw (i p : Nat) : Prop :=
  let d := 1 <<< i
  let mask := lowMasks[i]!
  (mask.testBit p = true ∧
    (decide (p ≥ d) && mask.testBit (p-d)) = false ∧
    p+d = p ^^^ d) ∨
  (mask.testBit p = false ∧
    (decide (p ≥ d) && mask.testBit (p-d)) = true ∧
    p-d = p ^^^ d)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma flipIndexLaw_checked (i : Fin 10) (p : Fin 1024) :
    flipIndexLaw i p := by
  unfold flipIndexLaw
  decide +kernel +revert

lemma flipPatternBits_bit {i p : Nat} (hi : i < 10) (hp : p < 1024) (x : Nat) :
    (flipPatternBits i x).testBit p = x.testBit (p ^^^ (1 <<< i)) := by
  obtain (⟨hm, hf, he⟩ | ⟨hm, hf, he⟩) :=
    flipIndexLaw_checked ⟨i, hi⟩ ⟨p, hp⟩ <;>
    change lowMasks[i]!.testBit p = _ at hm <;>
    change (decide (p ≥ (1 <<< i)) && lowMasks[i]!.testBit (p-(1 <<< i))) = _ at hf
  all_goals
    rw [flipPatternBits, Nat.testBit_or, Nat.testBit_shiftLeft,
      Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight]
    have regroup :
        (decide (p ≥ (1 <<< i)) &&
          (x.testBit (p-(1 <<< i)) && lowMasks[i]!.testBit (p-(1 <<< i)))) =
        ((decide (p ≥ (1 <<< i)) && lowMasks[i]!.testBit (p-(1 <<< i))) &&
          x.testBit (p-(1 <<< i))) := by
      cases decide (p ≥ (1 <<< i)) <;>
        cases x.testBit (p-(1 <<< i)) <;>
        cases lowMasks[i]!.testBit (p-(1 <<< i)) <;> rfl
    rw [regroup, hf, hm]
    simp only [Bool.false_and, Bool.true_and, Bool.and_true,
      Bool.and_false, Bool.false_or, Bool.or_false, Nat.add_comm (1 <<< i) p, he]



set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem lowMask_bit_checked : ∀ (i : Fin 10) (p : Fin 1024),
    (lowMasks[i.val]!).testBit p.val = !(p.val.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem highMask_bit_checked : ∀ (i : Fin 10) (p : Fin 1024),
    ((lowMasks[i.val]!) <<< (1 <<< i.val)).testBit p.val = p.val.testBit i.val := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem lowMask_lt_checked : ∀ (i : Fin 10), lowMasks[i.val]! < 2 ^ 1024 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem highMask_lt_checked : ∀ (i : Fin 10),
    ((lowMasks[i.val]!) <<< (1 <<< i.val)) < 2 ^ 1024 := by decide +kernel

lemma fastForkPhaseWitness {positive negative fi fj li lj i j : Nat} {a b : Bool}
    (hfi : ∀ p < 1024, fi.testBit p = negative.testBit (p ^^^ (1 <<< i)))
    (hfj : ∀ p < 1024, fj.testBit p = negative.testBit (p ^^^ (1 <<< j)))
    (hli : ∀ p, li.testBit p = (decide (p < 1024) && (p.testBit i == a)))
    (hlj : ∀ p, lj.testBit p = (decide (p < 1024) && (p.testBit j == b)))
    (hn : (positive &&& fi) &&& (positive &&& fj) &&& li &&& lj ≠ 0) :
    ∃ p < 1024, positive.testBit p = true ∧
      negative.testBit (p ^^^ (1 <<< i)) = true ∧
      negative.testBit (p ^^^ (1 <<< j)) = true ∧
      p.testBit i = a ∧ p.testBit j = b := by
  obtain ⟨p, hp⟩ := Nat.exists_testBit_of_ne_zero hn
  simp only [Nat.testBit_and, Bool.and_eq_true] at hp
  obtain ⟨⟨⟨⟨hpos, hflipI⟩, ⟨_, hflipJ⟩⟩, hmaskI⟩, hmaskJ⟩ := hp
  rw [hli] at hmaskI
  rw [hlj] at hmaskJ
  have hmaskI : p < 1024 ∧ p.testBit i = a := by simpa using hmaskI
  have hmaskJ : p < 1024 ∧ p.testBit j = b := by simpa using hmaskJ
  rw [hfi p hmaskI.1] at hflipI
  rw [hfj p hmaskI.1] at hflipJ
  exact ⟨p, hmaskI.1, hpos, hflipI, hflipJ, hmaskI.2, hmaskJ.2⟩

lemma boundedMask_bits {mask dim : Nat}
    (hlt : mask < 2 ^ dim) (bit : Nat → Bool)
    (hbit : ∀ p < dim, mask.testBit p = bit p) (p : Nat) :
    mask.testBit p = (decide (p < dim) && bit p) := by
  by_cases hp : p < dim
  · simp [hp, hbit p hp]
  · have hpow : 2 ^ dim ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) (by omega)
    have hzero := Nat.testBit_lt_two_pow (hlt.trans_le hpow)
    simp [hp, hzero]


lemma fastOppositeCorners {positive negative fi fj gi gj li lj mi mj i j : Nat}
    {a b : Bool}
    (hfi : ∀ p < 1024, fi.testBit p = negative.testBit (p ^^^ (1 <<< i)))
    (hfj : ∀ p < 1024, fj.testBit p = negative.testBit (p ^^^ (1 <<< j)))
    (hgi : ∀ p < 1024, gi.testBit p = positive.testBit (p ^^^ (1 <<< i)))
    (hgj : ∀ p < 1024, gj.testBit p = positive.testBit (p ^^^ (1 <<< j)))
    (hli : ∀ p, li.testBit p = (decide (p < 1024) && (p.testBit i == a)))
    (hlj : ∀ p, lj.testBit p = (decide (p < 1024) && (p.testBit j == b)))
    (hmi : ∀ p, mi.testBit p = (decide (p < 1024) && (p.testBit i == !a)))
    (hmj : ∀ p, mj.testBit p = (decide (p < 1024) && (p.testBit j == !b)))
    (hpos : (positive &&& fi) &&& (positive &&& fj) &&& li &&& lj ≠ 0)
    (hneg : (negative &&& gi) &&& (negative &&& gj) &&& mi &&& mj ≠ 0) :
    ∃ p q, p < 1024 ∧ q < 1024 ∧
      positive.testBit p = true ∧ negative.testBit q = true ∧
      negative.testBit (p ^^^ (1 <<< i)) = true ∧
      negative.testBit (p ^^^ (1 <<< j)) = true ∧
      positive.testBit (q ^^^ (1 <<< i)) = true ∧
      positive.testBit (q ^^^ (1 <<< j)) = true ∧
      p.testBit i ≠ q.testBit i ∧ p.testBit j ≠ q.testBit j := by
  obtain ⟨p, hp, hP, hPi, hPj, hia, hjb⟩ :=
    fastForkPhaseWitness hfi hfj hli hlj hpos
  obtain ⟨q, hq, hQ, hQi, hQj, hni, hnj⟩ :=
    fastForkPhaseWitness hgi hgj hmi hmj hneg
  refine ⟨p, q, hp, hq, hP, hQ, hPi, hPj, hQi, hQj, ?_, ?_⟩
  · rw [hia, hni]
    cases a <;> decide
  · rw [hjb, hnj]
    cases b <;> decide

lemma lowMask_bit {i : Nat} (hi : i < 10) (p : Nat) :
    lowMasks[i]!.testBit p = (decide (p < 1024) && !(p.testBit i)) := by
  apply boundedMask_bits (lowMask_lt_checked ⟨i, hi⟩)
  intro q hq
  exact lowMask_bit_checked ⟨i, hi⟩ ⟨q, hq⟩

lemma highMask_bit {i : Nat} (hi : i < 10) (p : Nat) :
    (lowMasks[i]! <<< (1 <<< i)).testBit p =
      (decide (p < 1024) && p.testBit i) := by
  apply boundedMask_bits (highMask_lt_checked ⟨i, hi⟩)
  intro q hq
  exact highMask_bit_checked ⟨i, hi⟩ ⟨q, hq⟩

def inspectNat {α : Sort u} (n : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k 0) (fun p _ => k (Nat.succ p)) n

lemma inspectNat_eq {α : Sort u} (n : Nat) (k : Nat → α) : inspectNat n k = k n := by
  cases n <;> rfl

def fastVertices (n positive negative : Nat) : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range n).map fun i =>
    let low := lowMasks[i]!
    let high := low <<< (1 <<< i)
    let forkP := positive &&& flipPatternBits i negative
    let forkN := negative &&& flipPatternBits i positive
    inspectNat forkP fun forkP =>
      inspectNat forkN fun forkN => (i,low,high,forkP,forkN)

def edgeBoolFast (vi vj : Nat × Nat × Nat × Nat × Nat) : Bool :=
  let (_,li,hi,pi,ni) := vi
  let (_,lj,hj,pj,nj) := vj
  let cp := pi &&& pj
  let cn := ni &&& nj
  (!(cp &&& li &&& lj == 0) && !(cn &&& hi &&& hj == 0)) ||
  (!(cp &&& hi &&& lj == 0) && !(cn &&& li &&& hj == 0)) ||
  (!(cp &&& li &&& hj == 0) && !(cn &&& hi &&& lj == 0)) ||
  (!(cp &&& hi &&& hj == 0) && !(cn &&& li &&& lj == 0))

def criticalEdgesFast (ws : List Nat) : List (Nat × Nat) :=
  let (positive, negative) := patternSets (labelledPatterns ws)
  inspectNat positive fun positive =>
    inspectNat negative fun negative =>
      (pairs (fastVertices ws.length positive negative)).filterMap fun (vi,vj,_) =>
        if edgeBoolFast vi vj then some (vi.1,vj.1) else none

def hasCriticalEdgeFast (ws : List Nat) : Bool :=
  let (positive, negative) := patternSets (labelledPatterns ws)
  inspectNat positive fun positive =>
    inspectNat negative fun negative =>
      (pairs (fastVertices ws.length positive negative)).any fun (vi,vj,_) =>
        edgeBoolFast vi vj


def adj_phaseMask (i : Nat) (a : Bool) : Nat :=
  if a then lowMasks[i]! <<< (1 <<< i) else lowMasks[i]!

lemma adj_phaseMask_bit {i : Nat} (hi : i < 10) (a : Bool) (p : Nat) :
    (adj_phaseMask i a).testBit p = (decide (p < 1024) && (p.testBit i == a)) := by
  cases a with
  | false =>
    change lowMasks[i]!.testBit p = _
    rw [lowMask_bit hi]
    cases p.testBit i <;> rfl
  | true =>
    change (lowMasks[i]! <<< (1 <<< i)).testBit p = _
    rw [highMask_bit hi]
    cases p.testBit i <;> rfl

def adj_corner (positive negative i j : Nat) (a b : Bool) : Nat :=
  (positive &&& flipPatternBits i negative) &&&
    (positive &&& flipPatternBits j negative) &&& adj_phaseMask i a &&& adj_phaseMask j b

lemma adj_fast_corner {ps : List (Nat × Bool)} {i j : Nat} (hi : i < 10) (hj : j < 10)
    {a b : Bool}
    (hp : adj_corner (patternSets ps).1 (patternSets ps).2 i j a b ≠ 0)
    (hn : adj_corner (patternSets ps).2 (patternSets ps).1 i j (!a) (!b) ≠ 0) :
    adj_patternCorners ps i j := by
  obtain ⟨p,q,_,_,hP,hN,hPi,hPj,hNi,hNj,hij,hij'⟩ :=
    fastOppositeCorners
      (fun p hp => flipPatternBits_bit hi hp _)
      (fun p hp => flipPatternBits_bit hj hp _)
      (fun p hp => flipPatternBits_bit hi hp _)
      (fun p hp => flipPatternBits_bit hj hp _)
      (adj_phaseMask_bit hi a) (adj_phaseMask_bit hj b)
      (adj_phaseMask_bit hi (!a)) (adj_phaseMask_bit hj (!b)) hp hn
  exact ⟨p,q,(adj_patternSets_pos ps p).mp hP,(adj_patternSets_neg ps q).mp hN,
    (adj_patternSets_neg ps _).mp hPi,(adj_patternSets_neg ps _).mp hPj,
    (adj_patternSets_pos ps _).mp hNi,(adj_patternSets_pos ps _).mp hNj,hij,hij'⟩

lemma adj_singles_map {α β : Type} (f : α → β) (ws : List α) :
    singles (ws.map f) = (singles ws).map (fun (a,rest) => (f a,rest.map f)) := by
  induction ws with
  | nil => rfl
  | cons a ws ih => simp [singles, ih, List.map_map, Function.comp_def]

lemma adj_pairs_map {α β : Type} (f : α → β) (ws : List α) :
    pairs (ws.map f) = (pairs ws).map (fun (a,b,rest) => (f a,f b,rest.map f)) := by
  induction ws with
  | nil => rfl
  | cons a ws ih => simp [pairs, adj_singles_map, ih, List.map_map, Function.comp_def]

def adj_vertex (positive negative i : Nat) : Nat × Nat × Nat × Nat × Nat :=
  (i,lowMasks[i]!,lowMasks[i]! <<< (1 <<< i),
    positive &&& flipPatternBits i negative,negative &&& flipPatternBits i positive)

def adj_edge (positive negative i j : Nat) : Bool :=
  (!(adj_corner positive negative i j false false == 0) &&
     !(adj_corner negative positive i j true true == 0)) ||
  (!(adj_corner positive negative i j true false == 0) &&
     !(adj_corner negative positive i j false true == 0)) ||
  (!(adj_corner positive negative i j false true == 0) &&
     !(adj_corner negative positive i j true false == 0)) ||
  (!(adj_corner positive negative i j true true == 0) &&
     !(adj_corner negative positive i j false false == 0))

lemma adj_edge_sound {ps : List (Nat × Bool)} {i j : Nat} (hi : i < 10) (hj : j < 10)
    (he : adj_edge (patternSets ps).1 (patternSets ps).2 i j = true) :
    adj_patternCorners ps i j := by
  simp only [adj_edge, Bool.or_eq_true, Bool.and_eq_true] at he
  rcases he with ((h | h) | h) | h
  · exact adj_fast_corner hi hj (a := false) (b := false) (by simpa using h.1) (by simpa using h.2)
  · exact adj_fast_corner hi hj (a := true) (b := false) (by simpa using h.1) (by simpa using h.2)
  · exact adj_fast_corner hi hj (a := false) (b := true) (by simpa using h.1) (by simpa using h.2)
  · exact adj_fast_corner hi hj (a := true) (b := true) (by simpa using h.1) (by simpa using h.2)

lemma adj_criticalEdgesFast_eq (ws : List Nat) :
    criticalEdgesFast ws = (pairs (List.range ws.length)).filterMap (fun (i,j,_) =>
      if adj_edge (patternSets (labelledPatterns ws)).1 (patternSets (labelledPatterns ws)).2 i j
        then some (i,j) else none) := by
  unfold criticalEdgesFast
  simp only [inspectNat_eq, fastVertices]
  change (pairs ((List.range ws.length).map (adj_vertex _ _))).filterMap _ = _
  rw [adj_pairs_map, List.filterMap_map]
  rfl

lemma criticalEdgesFast_sound {ws : List Nat} {i j : Nat} (hw : ws.length ≤ 10)
    (he : (i,j) ∈ criticalEdgesFast ws) :
    criticalPair (BitVec.ofNat 64 goal) (adj_frontier ws) (adj_word ws i) (adj_word ws j) := by
  rw [adj_criticalEdgesFast_eq] at he
  obtain ⟨⟨a,b,rest⟩,hab,he⟩ := List.mem_filterMap.mp he
  change (if adj_edge (patternSets (labelledPatterns ws)).1
    (patternSets (labelledPatterns ws)).2 a b then some (a,b) else none) = some (i,j) at he
  split at he
  · rename_i hc
    have heq : (a,b) = (i,j) := Option.some.inj he
    cases heq
    obtain ⟨ha,hb,hne⟩ := pairs_range_bounds hab
    exact adj_corner_rows ha hb hne (adj_edge_sound (ha.trans_le hw) (hb.trans_le hw) hc)
  · simp at he




def criticalGraphFast (ws : List Nat) : List (Nat × Nat) :=
  let es := criticalEdgesFast ws
  (List.range ws.length).map fun i =>
    (i, es.foldl (fun mask (a,b) =>
      if a == i then mask ||| (1 <<< b)
      else if b == i then mask ||| (1 <<< a) else mask) 0)

lemma criticalPair_symm {width : Nat} {target : BitVec width}
    {S : Finset (BitVec width)} {a b : BitVec width}
    (h : criticalPair target S a b) : criticalPair target S b a := by
  obtain ⟨ha,hb,hne,p,q,ra,rb,sa,sb,hp,hq,hra,hrb,hsa,hsb,ua,ub,usa,usb,hpa,hpb⟩ := h
  exact ⟨hb,ha,Ne.symm hne,p,q,rb,ra,sb,sa,hp,hq,hrb,hra,hsb,hsa,ub,ua,usb,usa,hpb,hpa⟩

def adj_neighborStep (i acc : Nat) (e : Nat × Nat) : Nat :=
  if e.1 == i then acc ||| (1 <<< e.2)
  else if e.2 == i then acc ||| (1 <<< e.1) else acc

lemma adj_neighbor_bit (i acc j : Nat) (e : Nat × Nat) :
    (adj_neighborStep i acc e).testBit j =
      (acc.testBit j || decide ((e.1 = i ∧ e.2 = j) ∨ (e.2 = i ∧ e.1 = j))) := by
  obtain ⟨a,b⟩ := e
  by_cases ha : a = i <;> by_cases hb : b = i <;>
    simp [adj_neighborStep, ha, hb, Nat.testBit_or, Nat.shiftLeft_eq, Nat.testBit_two_pow]

lemma adj_neighbor_fold (es : List (Nat × Nat)) (i acc j : Nat) :
    (es.foldl (adj_neighborStep i) acc).testBit j =
      (acc.testBit j || es.any (fun (a,b) => decide ((a=i ∧ b=j) ∨ (b=i ∧ a=j)))) := by
  induction es generalizing acc with
  | nil => simp
  | cons e es ih =>
    rw [List.foldl_cons, ih, adj_neighbor_bit]
    simp only [List.any_cons, Bool.or_assoc]

lemma adj_neighbor_sound {es : List (Nat × Nat)} {i j : Nat}
    (h : (es.foldl (adj_neighborStep i) 0).testBit j = true) :
    (i,j) ∈ es ∨ (j,i) ∈ es := by
  rw [adj_neighbor_fold] at h
  simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨a,b⟩,he,(⟨ha,hb⟩ | ⟨hb,ha⟩)⟩ := h
  · dsimp at ha hb; subst a; subst b; exact Or.inl he
  · dsimp at ha hb; subst a; subst b; exact Or.inr he

lemma criticalGraphFast_sound {ws : List Nat} {i adj j : Nat} (hw : ws.length ≤ 10)
    (hi : (i,adj) ∈ criticalGraphFast ws) (hb : adj.testBit j = true) :
    criticalPair (BitVec.ofNat 64 goal) (adj_frontier ws) (adj_word ws i) (adj_word ws j) := by
  obtain ⟨k,_,he⟩ := List.mem_map.mp hi
  have he1 : k = i := congrArg Prod.fst he
  subst k
  have he2 := congrArg Prod.snd he
  change (criticalEdgesFast ws).foldl (adj_neighborStep i) 0 = adj at he2
  rw [← he2] at hb
  rcases adj_neighbor_sound hb with he | he
  · exact criticalEdgesFast_sound hw he
  · exact criticalPair_symm (criticalEdgesFast_sound hw he)

lemma criticalEdgesFast_exists {ws : List Nat} (hw : ws.length ≤ 10)
    (he : (criticalEdgesFast ws).isEmpty = false) :
    ∃ i j, criticalPair (BitVec.ofNat 64 goal) (adj_frontier ws) (adj_word ws i) (adj_word ws j) := by
  have hn : criticalEdgesFast ws ≠ [] := by simpa using he
  obtain ⟨⟨i,j⟩,hm⟩ := List.exists_mem_of_ne_nil _ hn
  exact ⟨i,j,criticalEdgesFast_sound hw hm⟩


lemma hasCriticalEdgeFast_edges {ws : List Nat} (h : hasCriticalEdgeFast ws = true) :
    ∃ i j, (i,j) ∈ criticalEdgesFast ws := by
  unfold hasCriticalEdgeFast at h
  simp only [inspectNat_eq] at h
  obtain ⟨⟨vi,vj,rest⟩,hm,he⟩ := List.any_eq_true.mp h
  refine ⟨vi.1,vj.1,?_⟩
  unfold criticalEdgesFast
  simp only [inspectNat_eq]
  refine List.mem_filterMap.mpr ⟨(vi,vj,rest),hm,?_⟩
  change (if edgeBoolFast vi vj then some (vi.1,vj.1) else none) = some (vi.1,vj.1)
  rw [he]
  rfl

lemma hasCriticalEdgeFast_sound {ws : List Nat} (hw : ws.length ≤ 10)
    (h : hasCriticalEdgeFast ws = true) :
    ∃ i j, criticalPair (BitVec.ofNat 64 goal) (adj_frontier ws) (adj_word ws i) (adj_word ws j) := by
  obtain ⟨i,j,he⟩ := hasCriticalEdgeFast_edges h
  exact ⟨i,j,criticalEdgesFast_sound hw he⟩


end PEqualNP.Outside.L_meta_10760.KernelNat64

namespace PEqualNP.Outside.L_meta_10760

def sampledGraph (ws : List (BitVec 64)) : List Nat :=
  (KernelNat64.criticalGraphFast (ws.map BitVec.toNat)).map Prod.snd

lemma sampledGraph_length (ws : List (BitVec 64)) :
    (sampledGraph ws).length = ws.length := by
  simp [sampledGraph, KernelNat64.criticalGraphFast]

lemma sampled_frontier (ws : List (BitVec 64)) :
    KernelNat64.adj_frontier (ws.map BitVec.toNat) = ws.toFinset := by
  simp [KernelNat64.adj_frontier, List.map_map, Function.comp_def]

lemma sampledGraph_row (ws : List (BitVec 64)) (i : Nat) (hi : i < ws.length) :
    (i, (sampledGraph ws).getD i 0) ∈
      KernelNat64.criticalGraphFast (ws.map BitVec.toNat) := by
  unfold sampledGraph KernelNat64.criticalGraphFast
  simp only [List.map_map, Function.comp_def, List.length_map]
  apply List.mem_map.mpr
  refine ⟨i, List.mem_range.mpr hi, ?_⟩
  simp [List.getD_eq_getElem?_getD, hi]

def sampledAdmissible (k : Nat) (ws : List (BitVec 64)) : Bool :=
  if ws.length ≤ 10 then
    let colors := k + 2 - ws.length
    if 4 ≤ colors then true
    else if colors = 1 then !KernelNat64.hasCriticalEdgeFast (ws.map BitVec.toNat)
    else graphColorDegreeFast (sampledGraph ws) colors
  else true

lemma sampledAdmissible_complete {g : BitVec 64}
    (hg : g = sampleGoal64 ∨ g = ~~~sampleGoal64)
    (k : Nat) (ws : List (BitVec 64)) (hn : ws.Nodup)
    (run : live basicOps g k ws.toFinset) : sampledAdmissible k ws = true := by
  obtain ⟨color, bound, proper⟩ := live_criticalPair_coloring run hg
  have card : ws.toFinset.card = ws.length := List.toFinset_card_of_nodup hn
  rw [card] at bound
  unfold sampledAdmissible
  split
  next hsize =>
    dsimp only
    split
    · rfl
    · split
      next hone =>
        cases he : KernelNat64.hasCriticalEdgeFast (ws.map BitVec.toNat) with
        | false => rfl
        | true =>
          obtain ⟨i, j, hedge⟩ := KernelNat64.hasCriticalEdgeFast_sound
            (by simpa using hsize) he
          change criticalPair sampleGoal64
            (KernelNat64.adj_frontier (ws.map BitVec.toNat)) _ _ at hedge
          rw [sampled_frontier] at hedge
          have hb1 := bound _ hedge.1
          have hb2 := bound _ hedge.2.1
          have hne := proper _ _ hedge
          omega
      next hnotone =>
        apply graphColorDegreeFast_complete
        refine ⟨fun i => color (KernelNat64.adj_word (ws.map BitVec.toNat) i), ?_, ?_⟩
        · intro i hi
          rw [sampledGraph_length] at hi
          apply bound
          rw [← sampled_frontier]
          exact KernelNat64.adj_word_mem (by simpa using hi)
        · intro i hi j hj he
          rw [sampledGraph_length] at hi hj
          have hedge := KernelNat64.criticalGraphFast_sound
            (by simpa using hsize) (sampledGraph_row ws i hi) he
          change criticalPair sampleGoal64
            (KernelNat64.adj_frontier (ws.map BitVec.toNat)) _ _ at hedge
          rw [sampled_frontier] at hedge
          exact proper _ _ hedge
  next hsize => rfl

def checkedAdmissible (k : Nat) (ws : List (BitVec 64)) : Bool :=
  decide ((0 : BitVec 64) ∉ ws) && sampledAdmissible k ws

lemma checkedAdmissible_complete {g : BitVec 64}
    (hg : g = sampleGoal64 ∨ g = ~~~sampleGoal64)
    (k : Nat) (ws : List (BitVec 64)) (hn : ws.Nodup)
    (run : live basicOps g k ws.toFinset) : checkedAdmissible k ws = true := by
  have hnonzero : g ≠ 0 := by
    rcases hg with rfl | rfl <;> decide +kernel
  have hz : (0 : BitVec 64) ∉ ws := by
    simpa using live_zero_free hnonzero run
  simpa only [checkedAdmissible, Bool.and_eq_true, decide_eq_true_eq] using
    And.intro hz (sampledAdmissible_complete hg k ws hn run)

def representativeInputs (r : Fin 45) : List (BitVec 64) :=
  MemoActualPruned.ordered
    (S64.caseWord (S64.representative r) :: sampleInputs64.map canonical64)

lemma representativeInputs_set (r : Fin 45) :
    (representativeInputs r).toFinset =
      insert (S64.caseWord (S64.representative r)) signedRoots64 := by
  rw [representativeInputs, MemoActualPruned.perm_set (MemoActualPruned.ordered_perm _)]
  simp [signedRoots64]

set_option maxHeartbeats 8000000 in
lemma representativeInputs_nodup : ∀ r : Fin 45, (representativeInputs r).Nodup := by
  decide +kernel

def selectedFalseRows : List (Fin 64) :=
  [0, 1, 2, 3, 4, 6, 8, 9, 12, 15, 22, 26, 30, 37, 42, 44, 53]

def representativeCheck (r : Fin 45) : Bool :=
  MemoPruned.runFrom 0 checkedAdmissible (MemoActualPruned.done sampleGoal64)
    (MemoActualPruned.children sampleGoal64 selectedFalseRows) 11 (representativeInputs r)

lemma representative_rejection (r : Fin 45) (h : representativeCheck r = false) :
    ¬ live basicOps (~~~sampleGoal64) 11
      (insert (S64.caseWord (S64.representative r)) signedRoots64) := by
  intro run
  rw [← representativeInputs_set r] at run
  have found := MemoActualPruned.run_complete (Or.inr rfl)
    checkedAdmissible (checkedAdmissible_complete (Or.inr rfl))
    selectedFalseRows 0 11 (representativeInputs r) (representativeInputs_nodup r) run
  change representativeCheck r = true at found
  rw [h] at found
  contradiction

end PEqualNP.Outside.L_meta_10760


namespace PEqualNP.Outside.L_meta_10760.PNInitial

def frontier (r : Fin 45) : List (BitVec 64) :=
  sampleInputs64.map canonical64 ++ [S64.caseWord (S64.representative r)]

lemma frontier_set (r : Fin 45) : (frontier r).toFinset =
    insert (S64.caseWord (S64.representative r)) signedRoots64 := by
  simp [frontier, signedRoots64, Finset.union_comm]

set_option maxHeartbeats 8000000 in
lemma frontier_facts : ∀ r : Fin 45,
    (frontier r).length = 8 ∧ (frontier r).Nodup ∧
      (frontier r).all (fun w => !w[63]) = true := by decide +kernel

def data : List (Nat × Nat) := [
  (0x880000800080000000800000000000064201676176601161772011601170001, 0x8000000000000000000000000000013570101001100010005000100000000),
  (0x6ca0066e066e0006066a00060006000000001010110001101110011001110001, 0x24e000000000000000400000000000011110101001100010001000100000000),
  (0x4400044404440004044000040004000028a0123a132a0112133a011201130001, 0x440000000000000004000000000000131b0101001100010001000100000000),
  (0x202002220222000202220002000200004c80145c154c01141558011401150001, 0x2020000000000000000000000000000115d0101001100010005000100000000),
  (0x20a000200020000000200000000000004c00165e174e0116175a011601170001, 0x135f0101001100010005000100000000),
  (0x68a0127a126a0012127a00120012000004000404050401040500010401050001, 0x125a000000100000000000000000000001050101000100010005000100000000),
  (0x400010501040001010500010001000002ca0062e072e0106072a010601070001, 0x10500000001000000000000000000000030f0101000100010005000100000000),
  (0x800020a020a0002020a00020002000064a01474156401141570011401150001, 0x20a000000000000000000000000000011550101001100010005000100000000),
  (0x408000400040000000400000000000002c20163e172e0116173a011601170001, 0x400000000000000000000000000000131f0101001100010005000100000000),
  (0x6ca0147c146c0014147800140014000000000202030201020302010201030001, 0x105c000000100000000400000000000003030101000100010001000100000000),
  (0x202010301020001010300010001000004c80064e074e0106074a010601070001, 0x10100000001000000000000000000000034f0101000100010005000100000000),
  (0xc00040c040c0004040800040004000060a01272136201121372011201130001, 0xc000000000000000400000000000013530101001100010001000100000000),
  (0x2800020002000000020000000000000044a0147e156e0116157a011601170001, 0x2000000000000000000000000000000115f0101001100010005000100000000),
  (0x6ca0162a172a0102172a01020102000000000054004400140050001400150001, 0x130a010000000000000000000000000000550001001100010005000100000000),
  (0x4400140015000100150001000100000028a0027e026e0016027a001600170001, 0x11000100000000000000000000000000025f0001001100010005000100000000),
  (0xa0002a002a0002002a0002000200006c001654174401141750011401150001, 0xa000000000000000000000000000013550101001100010005000100000000),
  (0x4c00040004000000040000000000000020a0127e136e0116137a011601170001, 0x135f0101001100010005000100000000),
  (0x6c80164c174c0104174801040104000000200032002200120032001200130001, 0x134c010000000000000400000000000000130001001100010001000100000000),
  (0x200012001300010013000100010000004ca0047e046e0016047a001600170001, 0x13000100000000000000000000000000005f0001001100010005000100000000),
  (0x80004c004c000400480004000400006c201632172201121732011201130001, 0x4c000000000000000400000000000013130101001100010001000100000000),
  (0x600010001000000010000000000000000ca0067e076e0116077a011601170001, 0x10000000000000000000000000000000035f0101001100010005000100000000),
  (0x6ca016701760011017700110011000000000000e000e0006000a000600070001, 0x13500100001000000000000000000000000f0001000100010005000100000000),
  (0xc00060007000100070001000100000060a0107e106e0016107a001600170001, 0x3000100000000000000000000000000105f0001001100010005000100000000),
  (0x28a00000022a0000022a0000000200004400167e154401161550011601150001, 0x20a000000000000000000000000000011550101001100010005000100000000),
  (0x6ca0022a176e0002177a00020117000000001454000001140000011400000001, 0x135f000000110000000500000000000000000101000000010000000100000000),
  (0x4400000015440000155000000115000028a0167e022a0116022a011600020001, 0x11550000001100000005000000000000020a0101000000010000000100000000),
  (0x22a0000000200000002000000006ca01454176e0114177a011401170001, 0x135f0101001100010005000100000000),
  (0x4c800000044c000004480000000400002020167e132201161332011601130001, 0x4c000000000000000400000000000013130101001100010001000100000000),
  (0x202000001322000013320000011300004c80167e044c01160448011600040001, 0x13130000001100000001000000000000004c0101000000010004000100000000),
  (0x44c0000000400000004000000006ca01232176e0112177a011201170001, 0x135f0101001100010005000100000000),
  (0x28a0022a00000000022a00020000000044001454176e01161550011401170001, 0x20a000000000000000000000000000011550101001100010005000100000000),
  (0x4400145400000000155001140000000028a0022a176e0116022a000201170001, 0x11550101000000000005000100000000020a0000001100010000000000000000),
  (0x22a000200000000000200006ca0167e15440114177a011601150001, 0x135f0101001100010005000100000000),
  (0x28a0022a022a000200000000000000004400145415440114177a011601170001, 0x20a000000000000000000000000000011550101001100010005000100000000),
  (0x6ca0167e176e0116022a00020002000000000000000000001550011401150001, 0x135f010100110001000000000000000000000000000000000005000100000000),
  (0x4400145415440114000000000000000028a0022a022a0002177a011601170001, 0x11550101001100010000000000000000020a0000000000000005000100000000),
  (0x22a0002000200006ca0167e176e01161550011401150001, 0x135f0101001100010005000100000000),
  (0x4c80044c044c000400000000000000002020123213220112177a011601170001, 0x4c000000000000000000000000000013130101001100010005000100000000),
  (0x6ca0167e176e0116044800040004000000000000000000001332011201130001, 0x135f010100110001000400000000000000000000000000000001000100000000),
  (0x202012321322011200000000000000004c80044c044c0004177a011601170001, 0x13130101001100010000000000000000004c0000000000000005000100000000),
  (0x4480004000400006ca0167e176e01161332011201130001, 0x4000000000000135f0101001100010001000100000000),
  (0x60a010701060001000000000000000000c00060e070e0106177a011601170001, 0x10500000001000000000000000000000030f0101000100010005000100000000),
  (0x6ca0167e176e011610700010001000000000000000000000070a010601070001, 0x135f010100110001000000000000000000000000000000000005000100000000),
  (0xc00060e070e0106000000000000000060a0107010600010177a011601170001, 0x30f010100010001000000000000000010500000001000000005000100000000),
  (0x10700010001000006ca0167e176e0116070a010601070001, 0x135f0101001100010005000100000000)]

def positive (r : Fin 45) : Nat := (data.getD r.val (0, 0)).1

def negative (r : Fin 45) : Nat := (data.getD r.val (0, 0)).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma data_correct : ∀ r : Fin 45,
    KernelNat64.patternSets (KernelNat64.labelledPatterns ((frontier r).map BitVec.toNat)) =
      (positive r, negative r) := by decide +kernel

end PEqualNP.Outside.L_meta_10760.PNInitial

namespace PEqualNP.Outside.L_meta_10760

namespace PNMasks

def lowMasks : List Nat := [
  59923104495410530257643506359634157787265899298076885757810027052577558601833654377569492440802512007040037959957131119219596589604805540830949143546491374792589297808288495092100739867082031373151027650695001922946050227447487627157971036846942412387783503561528766079982415312826572101611785443208074712405,
  35953862697246318154586103815780494672359539578846131454686016231546535161100192626541695464481507204224022775974278671531757953762883324498569486127894824875553578684973097055260443920249218823890616590417001153767630136468492576294782622108165447432670102136917259647989449187695943260967071265924844827443,
  10574665499190093574878265828170733727164570464366509251378240068101922106205939007806381018965149177712947875286552550450517045224377448381932201802322007316339287848521499133900130564779182007026651938357941515814008863667203698910230182972989837480197088863799194014114543878734100959107962137036719066895,
  699491492164325255925799685131916238761858746670158199507510043415302240488330595847114697752558505918755306925569623959761827894219519931878783776807292312753960674804924067222965835024303868169078143782431929061627045456585458682777872025450689638767900819784382483423919244896808234649164810621105930495,
  2743020179230535281946541939345750848555742525508196244463891865018732560317087494586393599377565894397365059124943060525486210366883083181910179450378780297812958991483673120165741788626975511839923752263378027203536180819116878732226270817108308850929253867045887029310881577406346282326553799069597695,
  41855804958468253215416862131907979778454107725009450118155365586182407620204276291770907358880301160328046586258184810029483623519757063820280685745923183539846145986816692000600865017772938381340388341514537443249396336985068988168808660090905282896115730467361995897392102061092763730264872452095,
  9745314011399999079825087856739523064552525976596965881551925397018201298194122315297074087275581256833590487601395744005744951780045343217449061696331431509203394542567385587901876228620663761300800549174547043425925390537456083938846363324592488964804017437595582105683670264434074320895,
  528294531135665246352339784916516606517294807943820813192811729538211400001472535897918181471736777028254044331895631613250787768007518677792952317086889741124906620767309129894662251090542585738100845990744019557890744873615362666431441255911497635040213580733791338495,
  1552518092300708935148979488462502555256886017116696611139052038026050952686363478522948466231546903925489524851003593840350987650737090830000565511011107708019742339038878425693560262461319812044393910951468561638530421117939613695,
  13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084095]

def lowMask (i : Nat) : Nat := lowMasks[i]?.getD 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma lowMask_bits : ∀ (i : Fin 10) (x : Fin 1024),
    (lowMask i.val).testBit x.val = !(x.val.testBit i.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
lemma lowMask_bound : ∀ i : Fin 10, lowMask i.val < 2^1024 := by
  decide

end PNMasks

namespace PnProjection

def delBit (i x : Nat) : Nat :=
  x % 2^i + (x / 2^(i+1)) * 2^i

def insBit (i : Nat) (b : Bool) (y : Nat) : Nat :=
  y % 2^i + (if b then 2^i else 0) + (y / 2^i) * 2^(i+1)

lemma testBit_delBit (i x j : Nat) :
    (delBit i x).testBit j = x.testBit (if j < i then j else j+1) := by
  have form : delBit i x = 2^i * (x / 2^(i+1)) + x % 2^i := by
    simp [delBit, Nat.add_comm, Nat.mul_comm]
  rw [form, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _))]
  by_cases h : j < i
  · simp [h]
  · simp only [h, ite_false, Nat.testBit_div_two_pow]
    congr 1
    omega

lemma testBit_cons (b : Bool) (x j : Nat) :
    (2*x + b.toNat).testBit j = if j = 0 then b else x.testBit (j-1) := by
  have hb : b.toNat < 2^1 := by cases b <;> decide
  change (2^1*x + b.toNat).testBit j = _
  rw [Nat.testBit_two_pow_mul_add _ hb]
  by_cases h : j = 0
  · subst j
    cases b <;> simp
  · have hj : ¬ j < 1 := by omega
    simp [h, hj]

lemma insBit_form (i : Nat) (b : Bool) (y : Nat) :
    insBit i b y = 2^i * (2*(y / 2^i) + b.toNat) + y % 2^i := by
  cases b <;> simp [insBit, Nat.pow_succ] <;> ring

lemma testBit_insBit (i : Nat) (b : Bool) (y j : Nat) :
    (insBit i b y).testBit j =
      if j < i then y.testBit j else if j = i then b else y.testBit (j-1) := by
  rw [insBit_form, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _))]
  by_cases h : j < i
  · simp [h]
  · simp only [h, ite_false, testBit_cons, Nat.testBit_div_two_pow]
    by_cases e : j = i
    · subst j
      simp
    · have he : j-i ≠ 0 := by omega
      simp only [e, he, ite_false]
      congr 1
      omega

lemma delBit_insBit (i : Nat) (b : Bool) (y : Nat) :
    delBit i (insBit i b y) = y := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_delBit]
  by_cases h : j < i
  · simp [h, testBit_insBit]
  · have hlt : ¬ j+1 < i := by omega
    have hne : j+1 ≠ i := by omega
    simp [h, testBit_insBit, hlt, hne]

lemma insBit_delBit (i x : Nat) :
    insBit i (x.testBit i) (delBit i x) = x := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_insBit]
  by_cases h : j < i
  · simp [h, testBit_delBit]
  · by_cases e : j = i
    · simp [h, e]
    · have hlt : ¬ j-1 < i := by omega
      have back : j-1+1 = j := by omega
      simp [h, e, testBit_delBit, hlt, back]

lemma delBit_eq_iff (i x y : Nat) :
    delBit i x = y ↔ x = insBit i false y ∨ x = insBit i true y := by
  constructor
  · intro h
    have inverse := insBit_delBit i x
    rw [h] at inverse
    cases bit : x.testBit i
    · exact Or.inl (by simpa [bit] using inverse.symm)
    · exact Or.inr (by simpa [bit] using inverse.symm)
  · rintro (rfl | rfl) <;> exact delBit_insBit ..

lemma insBit_false_ne_true (i y : Nat) : insBit i false y ≠ insBit i true y := by
  intro h
  have bit := congrArg (fun x : Nat => x.testBit i) h
  simpa [testBit_insBit] using bit

lemma delBit_lt {i x m : Nat} (hi : i < m) (hx : x < 2^m) :
    delBit i x < 2^(m-1) := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [testBit_delBit, if_neg (by omega : ¬ (j < i))]
  apply Nat.testBit_lt_two_pow
  exact lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega))

lemma insBit_lt {i y m : Nat} (hi : i ≤ m) (hy : y < 2^m) (b : Bool) :
    insBit i b y < 2^(m+1) := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [testBit_insBit, if_neg (by omega : ¬ (j < i)), if_neg (by omega : j ≠ i)]
  apply Nat.testBit_lt_two_pow
  exact lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) (by omega))

end PnProjection

namespace PnProjection

lemma insBit_adjacent (i : Nat) (b c : Bool) (y : Nat) :
    insBit (i+1) c (insBit i b y) = insBit i b (insBit i c y) := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases h : j < i
  · have h' : j < i+1 := by omega
    simp [testBit_insBit, h, h']
  · by_cases e : j = i
    · subst j
      simp [testBit_insBit]
    · by_cases e' : j = i+1
      · subst j
        simp [testBit_insBit]
      · have h' : ¬ (j < i+1) := by omega
        have hs : ¬ (j-1 < i) := by omega
        have hse : j-1 ≠ i := by omega
        simp [testBit_insBit, h, h', e, e', hs, hse]

lemma insBit_true_add_false (i y : Nat) :
    insBit i true y = insBit i false y + 2^i := by
  simp [insBit]
  omega

lemma hole_swap_insert (i : Nat) (b : Bool) (y : Nat) :
    insBit i false (insBit i b y) =
      insBit (i+1) false (insBit i b y) + (if b then 2^i else 0) := by
  cases b
  · simpa using (insBit_adjacent i false false y).symm
  · simp only [Bool.true_eq, ite_true]
    calc
      insBit i false (insBit i true y) = insBit (i+1) true (insBit i false y) :=
        (insBit_adjacent i false true y).symm
      _ = insBit (i+1) false (insBit i false y) + 2^(i+1) := insBit_true_add_false ..
      _ = insBit i false (insBit i false y) + 2^(i+1) := by rw [insBit_adjacent]
      _ = (insBit i false (insBit i false y) + 2^i) + 2^i := by rw [Nat.pow_succ]; omega
      _ = insBit i true (insBit i false y) + 2^i := by rw [insBit_true_add_false]
      _ = insBit (i+1) false (insBit i true y) + 2^i := by rw [insBit_adjacent]

lemma hole_swap (i y : Nat) :
    insBit i false y = insBit (i+1) false y + (if y.testBit i then 2^i else 0) := by
  have h := hole_swap_insert i (y.testBit i) (delBit i y)
  simpa only [insBit_delBit] using h

lemma hole_move {i x : Nat} (hole : x.testBit (i+1) = false) :
    insBit i false (delBit (i+1) x) = x + (if x.testBit i then 2^i else 0) := by
  have back : insBit (i+1) false (delBit (i+1) x) = x := by
    simpa [hole] using insBit_delBit (i+1) x
  have bit : (delBit (i+1) x).testBit i = x.testBit i := by simp [testBit_delBit]
  rw [hole_swap, back, bit]

lemma hole_move_false {i x : Nat} (hole : x.testBit (i+1) = false)
    (bit : x.testBit i = false) : delBit i x = delBit (i+1) x := by
  have move := hole_move hole
  simp only [bit, Bool.false_eq_true, ite_false, Nat.add_zero] at move
  calc
    delBit i x = delBit i (insBit i false (delBit (i+1) x)) := congrArg (delBit i) move.symm
    _ = delBit (i+1) x := delBit_insBit ..

lemma hole_move_true {i x : Nat} (hole : x.testBit (i+1) = false)
    (bit : x.testBit i = true) : delBit i (x+2^i) = delBit (i+1) x := by
  have move := hole_move hole
  simp only [bit, ite_true] at move
  rw [← move, delBit_insBit]

lemma add_pow_bit_false {i x : Nat} (bit : x.testBit i = false) :
    (x+2^i).testBit i = true := by
  rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, bit]
  rfl

lemma add_pow_bit_true {i x : Nat} (bit : x.testBit i = true) :
    (x+2^i).testBit i = false := by
  rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, bit]
  rfl

lemma hole_move_add {i x : Nat} (hole : x.testBit (i+1) = false) :
    x+2^i = insBit i (!(x.testBit i)) (delBit (i+1) x) := by
  have move := hole_move hole
  cases bit : x.testBit i
  · simp only [bit, Bool.false_eq_true, ite_false, Nat.add_zero] at move
    simp only [Bool.not_false]
    rw [insBit_true_add_false, move]
  · simp only [bit, ite_true] at move
    exact move.symm

lemma hole_add_lt {i x m : Nat} (hi : i+1 < m) (hx : x < 2^m)
    (hole : x.testBit (i+1) = false) : x+2^i < 2^m := by
  rw [hole_move_add hole]
  have bound := insBit_lt (by omega : i ≤ m-1) (delBit_lt hi hx) (!(x.testBit i))
  simpa only [show m-1+1 = m by omega] using bound

lemma hole_move_1024 (j : Nat) (hj : j < 9) (x : Nat) (hx : x < 1024)
    (hole : x.testBit (j+1) = false) :
    x+2^j < 1024 ∧
    (x+2^j).testBit j = !(x.testBit j) ∧
    (if x.testBit j then delBit j (x+2^j) else delBit j x) = delBit (j+1) x := by
  refine ⟨hole_add_lt (m := 10) (by omega) hx hole, ?_, ?_⟩
  · simpa only [Nat.add_comm] using Nat.testBit_two_pow_add_eq x j
  · cases bit : x.testBit j
    · simpa only [Bool.false_eq_true, ite_false] using hole_move_false hole bit
    · simpa only [ite_true] using hole_move_true hole bit

end PnProjection

namespace PnProjection

def bitmapStage (mask shift S : Nat) : Nat :=
  (S ||| (S >>> shift)) &&& mask

lemma testBit_bitmapStage (mask shift S y : Nat) :
    (bitmapStage mask shift S).testBit y =
      ((S.testBit y || S.testBit (y + shift)) && mask.testBit y) := by
  simp [bitmapStage, Nat.testBit_shiftRight, Nat.add_comm]

def packBits : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n + 1, f => 2 * packBits n (fun y => f (y + 1)) + (f 0).toNat

lemma testBit_packBits (n : Nat) (f : Nat → Bool) (y : Nat) :
    (packBits n f).testBit y = if y < n then f y else false := by
  induction n generalizing f y with
  | zero => simp [packBits]
  | succ n ih =>
    rw [packBits]
    have hb : (f 0).toNat < 2^1 := by cases f 0 <;> decide
    change (2^1 * packBits n (fun y => f (y+1)) + (f 0).toNat).testBit y = _
    rw [Nat.testBit_two_pow_mul_add _ hb]
    cases y with
    | zero => cases h : f 0 <;> simp [h]
    | succ y => simpa [ih]

lemma packBits_lt (n : Nat) (f : Nat → Bool) : packBits n f < 2^n := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  simp [testBit_packBits, Nat.not_lt.mpr hj]

def dropBitmapSimple (m i S : Nat) : Nat :=
  packBits (2^(m-1)) (fun y =>
    S.testBit (insBit i false y) || S.testBit (insBit i true y))

lemma testBit_dropBitmapSimple (m i S y : Nat) :
    (dropBitmapSimple m i S).testBit y =
      if y < 2^(m-1) then
        S.testBit (insBit i false y) || S.testBit (insBit i true y)
      else false := by
  exact testBit_packBits ..

lemma dropBitmapSimple_lt (m i S : Nat) : dropBitmapSimple m i S < 2^(2^(m-1)) :=
  packBits_lt ..

lemma testBit_dropBitmapSimple_iff (m i S y : Nat) :
    (dropBitmapSimple m i S).testBit y = true ↔
      y < 2^(m-1) ∧ ∃ x, S.testBit x = true ∧ delBit i x = y := by
  rw [testBit_dropBitmapSimple]
  by_cases hy : y < 2^(m-1)
  · simp only [hy, if_pos, true_and, Bool.or_eq_true]
    constructor
    · rintro (hf | ht)
      · exact ⟨insBit i false y, hf, delBit_insBit ..⟩
      · exact ⟨insBit i true y, ht, delBit_insBit ..⟩
    · rintro ⟨x, hx, hxy⟩
      rcases (delBit_eq_iff i x y).mp hxy with rfl | rfl
      · exact Or.inl hx
      · exact Or.inr hx
  · simp [hy]

lemma testBit_dropBitmapSimple_image {m i S : Nat} (hi : i < m)
    (hS : S < 2^(2^m)) (y : Nat) :
    (dropBitmapSimple m i S).testBit y = true ↔
      ∃ x, S.testBit x = true ∧ delBit i x = y := by
  rw [testBit_dropBitmapSimple_iff]
  constructor
  · exact And.right
  · rintro ⟨x, hx, rfl⟩
    refine ⟨delBit_lt hi ?_, x, hx, rfl⟩
    by_contra hn
    have hz : S.testBit x = false := Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hS (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hx] at hz

def deletePattern (i S y : Nat) : Bool :=
  S.testBit (insBit i false y) || S.testBit (insBit i true y)

def MaskSpec (j mask : Nat) : Prop :=
  ∀ x, mask.testBit x = if x < 1024 then !(x.testBit j) else false

def HoleSpec (j T : Nat) (f : Nat → Bool) : Prop :=
  ∀ x, T.testBit x =
    if x < 1024 then if x.testBit j then false else f (delBit j x) else false

lemma lowMask_spec {j : Nat} (hj : j < 10) :
    MaskSpec j (PNMasks.lowMask j) := by
  intro x
  by_cases hx : x < 1024
  · exact (PNMasks.lowMask_bits ⟨j, hj⟩ ⟨x, hx⟩).trans (by simp [hx])
  · simp only [hx, if_false]
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le
      (PNMasks.lowMask_bound ⟨j, hj⟩)
      (Nat.pow_le_pow_right (by decide) (by omega)))

lemma insBit_true_eq_false_add (i y : Nat) :
    insBit i true y = insBit i false y + 2^i := by
  simp only [insBit, Bool.false_eq_true, if_false, if_true]
  omega

lemma bitmapStage_first (i S mask : Nat) (hm : MaskSpec i mask) :
    HoleSpec i (bitmapStage mask (2^i) S) (deletePattern i S) := by
  intro x
  rw [testBit_bitmapStage, hm]
  by_cases hx : x < 1024
  · simp only [hx, if_pos]
    cases hb : x.testBit i with
    | true => simp [hb]
    | false =>
      have he : insBit i false (delBit i x) = x := by
        simpa [hb] using insBit_delBit i x
      simp [hb, deletePattern, insBit_true_eq_false_add, he]
  · simp [hx]

lemma bitmapStage_move_aux (j T mask : Nat) (f : Nat → Bool)
    (hm : MaskSpec (j+1) mask) (hT : HoleSpec j T f)
    (move : ∀ x, x < 1024 → x.testBit (j+1) = false →
      x + 2^j < 1024 ∧
      (x + 2^j).testBit j = !(x.testBit j) ∧
      (if x.testBit j then delBit j (x + 2^j) else delBit j x) = delBit (j+1) x) :
    HoleSpec (j+1) (bitmapStage mask (2^j) T) f := by
  intro x
  rw [testBit_bitmapStage, hm]
  by_cases hx : x < 1024
  · simp only [hx, if_pos]
    cases hh : x.testBit (j+1) with
    | true => simp [hh]
    | false =>
      rcases move x hx hh with ⟨hxshift, hflip, hdel⟩
      rw [hT x, hT (x + 2^j)]
      cases hb : x.testBit j <;> simp_all
  · simp [hx]

def compressHoles (mask : Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, _, T => T
  | n+1, j, T => compressHoles mask n (j+1) (bitmapStage (mask (j+1)) (2^j) T)

lemma compressHoles_spec_aux (mask : Nat → Nat) (f : Nat → Bool)
    (step : ∀ j T, j < 9 → HoleSpec j T f →
      HoleSpec (j+1) (bitmapStage (mask (j+1)) (2^j) T) f)
    (n j T : Nat) (hj : j + n ≤ 9) (hT : HoleSpec j T f) :
    HoleSpec (j+n) (compressHoles mask n j T) f := by
  induction n generalizing j T with
  | zero => simpa [compressHoles] using hT
  | succ n ih =>
    have hnext := step j T (by omega) hT
    have hrest := ih (j+1) _ (by omega) hnext
    simpa [compressHoles, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest

lemma holeSpec_final {T : Nat} {f : Nat → Bool} (h : HoleSpec 9 T f) :
    T = packBits 512 f := by
  apply Nat.eq_of_testBit_eq
  intro x
  rw [h, testBit_packBits]
  by_cases hx : x < 512
  · have hbit : x.testBit 9 = false := Nat.testBit_lt_two_pow (by omega)
    have hdel : delBit 9 x = x := by
      simp [delBit, Nat.mod_eq_of_lt hx, Nat.div_eq_of_lt (show x < 1024 by omega)]
    simp [hx, show x < 1024 by omega, hbit, hdel]
  · by_cases hxx : x < 1024
    · have hbit : x.testBit 9 = true :=
        Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (by omega) (by omega)
      simp [hx, hxx, hbit]
    · simp [hx, hxx]

def dropBitmap (i S : Nat) : Nat :=
  compressHoles PNMasks.lowMask (9-i) i
    (bitmapStage (PNMasks.lowMask i) (2^i) S)

lemma dropBitmap_eq_simple_aux {i : Nat} (hi : i < 10) (S : Nat)
    (move : ∀ j x, j < 9 → x < 1024 → x.testBit (j+1) = false →
      x + 2^j < 1024 ∧
      (x + 2^j).testBit j = !(x.testBit j) ∧
      (if x.testBit j then delBit j (x + 2^j) else delBit j x) = delBit (j+1) x) :
    dropBitmap i S = dropBitmapSimple 10 i S := by
  have hfirst := bitmapStage_first i S (PNMasks.lowMask i) (lowMask_spec hi)
  have hfull := compressHoles_spec_aux PNMasks.lowMask (deletePattern i S)
    (fun j T hj hT => bitmapStage_move_aux j T _ _ (lowMask_spec (by omega)) hT
      (fun x hx hh => move j x hj hx hh))
    (9-i) i _ (by omega) hfirst
  have hi9 : i + (9-i) = 9 := by omega
  rw [hi9] at hfull
  exact holeSpec_final hfull

lemma dropBitmap_eq_simple {i : Nat} (hi : i < 10) (S : Nat) :
    dropBitmap i S = dropBitmapSimple 10 i S := by
  exact dropBitmap_eq_simple_aux hi S (fun j x hj hx hh => hole_move_1024 j hj x hx hh)

lemma testBit_dropBitmap {i : Nat} (hi : i < 10) (S y : Nat) :
    (dropBitmap i S).testBit y =
      if y < 512 then
        S.testBit (insBit i false y) || S.testBit (insBit i true y)
      else false := by
  rw [dropBitmap_eq_simple hi S]
  exact testBit_dropBitmapSimple 10 i S y

lemma testBit_dropBitmap_image {i S : Nat} (hi : i < 10) (hS : S < 2^1024) (y : Nat) :
    (dropBitmap i S).testBit y = true ↔
      ∃ x, S.testBit x = true ∧ delBit i x = y := by
  rw [dropBitmap_eq_simple hi S]
  exact testBit_dropBitmapSimple_image hi hS y

lemma dropBitmap_lt {m i S : Nat} (hi : i < m) (hm : m ≤ 10) (hS : S < 2^(2^m)) :
    dropBitmap i S < 2^(2^(m-1)) := by
  have hi10 : i < 10 := by omega
  have hS1024 : S < 2^1024 := lt_of_lt_of_le hS
    (Nat.pow_le_pow_right (by decide) (by exact Nat.pow_le_pow_right (by decide) hm))
  apply Nat.lt_pow_two_of_testBit
  intro y hy
  cases hb : (dropBitmap i S).testBit y with
  | false => rfl
  | true =>
    rcases (testBit_dropBitmap_image hi10 hS1024 y).mp hb with ⟨x, hx, hxy⟩
    have hxb : x < 2^m := by
      by_contra hn
      have hz : S.testBit x = false := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hS (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hx] at hz
    have hlt := delBit_lt hi hxb
    omega

end PnProjection

namespace PnProjection

lemma compressHoles_eq_foldl (mask : Nat → Nat) (n j S : Nat) :
    compressHoles mask n j S =
      (List.range n).foldl (fun T offset =>
        bitmapStage (mask (j + offset + 1)) (2^(j + offset)) T) S := by
  induction n generalizing j S with
  | zero => rfl
  | succ n ih =>
    rw [compressHoles, ih, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def projectPatternBits (i S : Nat) : Nat :=
  let d := 1 <<< i
  let T := (S &&& PNMasks.lowMask i) ||| ((S >>> d) &&& PNMasks.lowMask i)
  (List.range (9-i)).foldl (fun T offset =>
    let j := i + 1 + offset
    (T ||| (T >>> (1 <<< (j-1)))) &&& PNMasks.lowMask j) T

lemma mask_distribute (S d mask : Nat) :
    (S &&& mask) ||| ((S >>> d) &&& mask) = bitmapStage mask d S := by
  apply Nat.eq_of_testBit_eq
  intro x
  simp only [bitmapStage, Nat.testBit_or, Nat.testBit_and]
  cases S.testBit x <;> cases (S >>> d).testBit x <;> cases mask.testBit x <;> rfl

lemma projectPatternBits_eq_dropBitmap (i S : Nat) :
    projectPatternBits i S = dropBitmap i S := by
  unfold projectPatternBits dropBitmap
  rw [compressHoles_eq_foldl]
  simp only [Nat.one_shiftLeft, mask_distribute]
  congr 1
  funext T offset
  dsimp only [bitmapStage]
  rw [show i + 1 + offset - 1 = i + offset by omega,
    show i + 1 + offset = i + offset + 1 by omega]

lemma lowMask_getBang : ∀ i : Fin 10,
    PNMasks.lowMask i.val = PNMasks.lowMasks[i.val]! := by
  decide

end PnProjection

namespace PNPlanes

def allPatterns : Nat := 2^1024 - 1

def highMask (i : Nat) : Nat := PNMasks.lowMask i <<< (1 <<< i)

set_option maxRecDepth 10000 in
lemma highMask_eq : ∀ i : Fin 10,
    highMask i.val = allPatterns ^^^ PNMasks.lowMask i.val := by
  decide +kernel

lemma highMask_bits (i : Fin 10) (x : Fin 1024) :
    (highMask i.val).testBit x.val = x.val.testBit i.val := by
  rw [highMask_eq i]
  simp [Nat.testBit_xor, allPatterns, x.isLt, PNMasks.lowMask_bits]

def gateMask (i j : Nat) (d : Fin 4) : Nat :=
  match d.val with
  | 0 => highMask i &&& highMask j
  | 1 => highMask i ||| highMask j
  | 2 => highMask i &&& PNMasks.lowMask j
  | _ => highMask j &&& PNMasks.lowMask i

lemma gateMask_bits (i j : Fin 10) (d : Fin 4) (x : Fin 1024) :
    (gateMask i.val j.val d).testBit x.val =
      ChromGate.eval d (x.val.testBit i.val) (x.val.testBit j.val) := by
  fin_cases d <;> simp [gateMask, ChromGate.eval, Nat.testBit_and, Nat.testBit_or,
    highMask_bits, PNMasks.lowMask_bits]

def planeOne (s gate : Nat) : Nat := s &&& gate
def planeZero (s gate : Nat) : Nat := s &&& (allPatterns ^^^ gate)

lemma planeOne_le (s gate : Nat) : planeOne s gate ≤ s := Nat.and_le_left
lemma planeZero_le (s gate : Nat) : planeZero s gate ≤ s := Nat.and_le_left

lemma testBit_planeOne (s gate x : Nat) :
    (planeOne s gate).testBit x = (s.testBit x && gate.testBit x) := by
  simp [planeOne, Nat.testBit_and]

lemma testBit_planeZero {s : Nat} (hs : s < 2^1024) (gate x : Nat) :
    (planeZero s gate).testBit x = (s.testBit x && !(gate.testBit x)) := by
  by_cases hx : x < 1024
  · simp [planeZero, allPatterns, Nat.testBit_and, Nat.testBit_xor, hx]
  · have powle : 2^1024 ≤ 2^x := Nat.pow_le_pow_of_le (by decide) (by omega)
    have no : s.testBit x = false := Nat.testBit_lt_two_pow (hs.trans_le powle)
    simp [planeZero, Nat.testBit_and, no]

lemma planeZero_eq_xor {s : Nat} (hs : s < 2^1024) (gate : Nat) :
    planeZero s gate = s ^^^ (s &&& gate) := by
  apply Nat.eq_of_testBit_eq
  intro x
  rw [testBit_planeZero hs, Nat.testBit_xor, Nat.testBit_and]
  cases s.testBit x <;> cases gate.testBit x <;> rfl

end PNPlanes

namespace PnProjection

def joinPlanes (q a b : Nat) : Nat := a ||| (b <<< q)

def appendPlanes (n a b : Nat) : Nat := joinPlanes (2^n) a b

lemma bitIndex_lt {x q y : Nat} (bound : x < 2^q) (bit : x.testBit y = true) : y < q := by
  by_contra! h
  have zero := Nat.testBit_lt_two_pow (lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) h))
  rw [zero] at bit
  contradiction

lemma testBit_joinPlanes (q a b x : Nat) :
    (joinPlanes q a b).testBit x = (a.testBit x || (decide (q ≤ x) && b.testBit (x-q))) := by
  simp [joinPlanes, Nat.testBit_shiftLeft]

lemma joinPlanes_image {q a b x : Nat} (ha : a < 2^q) (hb : b < 2^q) :
    (joinPlanes q a b).testBit x = true ↔
      (∃ y < q, a.testBit y = true ∧ x = y) ∨
      (∃ y < q, b.testBit y = true ∧ x = y+q) := by
  rw [testBit_joinPlanes, Bool.or_eq_true]
  constructor
  · rintro (h | h)
    · exact Or.inl ⟨x, bitIndex_lt ha h, h, rfl⟩
    · have h' : q ≤ x ∧ b.testBit (x-q) = true := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using h
      obtain ⟨hle', hbit⟩ := h'
      exact Or.inr ⟨x-q, bitIndex_lt hb hbit, hbit, by omega⟩
  · rintro (⟨y, hy, hbit, rfl⟩ | ⟨y, hy, hbit, rfl⟩)
    · exact Or.inl hbit
    · exact Or.inr (by simp [hbit])

lemma joinPlanes_lt {q a b : Nat} (ha : a < 2^q) (hb : b < 2^q) :
    joinPlanes q a b < 2^(2*q) := by
  apply Nat.lt_pow_two_of_testBit
  intro x hx
  rw [testBit_joinPlanes]
  have za : a.testBit x = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))
  have zb : b.testBit (x-q) = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega)))
  simp [za, zb]

lemma insBit_top (n : Nat) (flag : Bool) {y : Nat} (hy : y < 2^n) :
    insBit n flag y = y + (if flag then 2^n else 0) := by
  simp [insBit, Nat.mod_eq_of_lt hy, Nat.div_eq_of_lt hy]

lemma appendPlanes_image {n a b x : Nat} (ha : a < 2^(2^n)) (hb : b < 2^(2^n)) :
    (appendPlanes n a b).testBit x = true ↔
      ∃ (flag : Bool) (y : Nat), y < 2^n ∧
        (if flag then b else a).testBit y = true ∧ x = insBit n flag y := by
  rw [appendPlanes, joinPlanes_image ha hb]
  constructor
  · rintro (⟨y, hy, hbit, eq⟩ | ⟨y, hy, hbit, eq⟩)
    · exact ⟨false, y, hy, hbit, by simpa [insBit_top n false hy] using eq⟩
    · exact ⟨true, y, hy, hbit, by simpa [insBit_top n true hy] using eq⟩
  · rintro ⟨flag, y, hy, hbit, eq⟩
    cases flag
    · exact Or.inl ⟨y, hy, hbit, by simpa [insBit_top n false hy] using eq⟩
    · exact Or.inr ⟨y, hy, hbit, by simpa [insBit_top n true hy] using eq⟩

lemma appendPlanes_image_unbounded {n a b x : Nat}
    (ha : a < 2^(2^n)) (hb : b < 2^(2^n)) :
    (appendPlanes n a b).testBit x = true ↔
      ∃ (flag : Bool) (y : Nat),
        (if flag then b else a).testBit y = true ∧ x = insBit n flag y := by
  rw [appendPlanes_image ha hb]
  constructor
  · rintro ⟨flag, y, hy, hbit, eq⟩
    exact ⟨flag, y, hbit, eq⟩
  · rintro ⟨flag, y, hbit, eq⟩
    refine ⟨flag, y, ?_, hbit, eq⟩
    cases flag
    · exact bitIndex_lt ha hbit
    · exact bitIndex_lt hb hbit

lemma appendPlanes_image_sum {n a b x : Nat}
    (ha : a < 2^(2^n)) (hb : b < 2^(2^n)) :
    (appendPlanes n a b).testBit x = true ↔
      ∃ (flag : Bool) (y : Nat), y < 2^n ∧
        (if flag then b else a).testBit y = true ∧ x = y + (if flag then 2^n else 0) := by
  rw [appendPlanes_image ha hb]
  constructor
  · rintro ⟨flag, y, hy, hbit, eq⟩
    exact ⟨flag, y, hy, hbit, by simpa only [insBit_top n flag hy] using eq⟩
  · rintro ⟨flag, y, hy, hbit, eq⟩
    exact ⟨flag, y, hy, hbit, by simpa only [insBit_top n flag hy] using eq⟩

lemma appendPlanes_lt {n a b : Nat} (ha : a < 2^(2^n)) (hb : b < 2^(2^n)) :
    appendPlanes n a b < 2^(2^(n+1)) := by
  simpa only [appendPlanes, Nat.pow_succ, Nat.mul_comm (2^n) 2] using joinPlanes_lt ha hb

end PnProjection

namespace PnTransition

open PnProjection
open PNPlanes

def keepSize (keep : Fin 4) : Nat :=
  if keep.val == 0 then 0 else if keep.val == 3 then 2 else 1

def dropPattern (i j : Nat) (keep : Fin 4) (x : Nat) : Nat :=
  let x := if keep.val &&& 2 == 0 then delBit j x else x
  if keep.val &&& 1 == 0 then delBit i x else x

def projectDropped (i j : Nat) (keep : Fin 4) (S : Nat) : Nat :=
  let S := if keep.val &&& 2 == 0 then dropBitmap j S else S
  if keep.val &&& 1 == 0 then dropBitmap i S else S

lemma bound_1024 {m S : Nat} (hm : m ≤ 10) (hS : S < 2^(2^m)) : S < 2^1024 :=
  lt_of_lt_of_le hS (Nat.pow_le_pow_right (by decide)
    (by exact Nat.pow_le_pow_right (by decide) hm))

lemma projectDropped_image {m i j S : Nat} (hij : i < j) (hj : j < m) (hm : m ≤ 10)
    (hS : S < 2^(2^m)) (keep : Fin 4) (y : Nat) :
    (projectDropped i j keep S).testBit y = true ↔
      ∃ x, S.testBit x = true ∧ dropPattern i j keep x = y := by
  have hS1024 := bound_1024 hm hS
  have hi10 : i < 10 := by omega
  have hj10 : j < 10 := by omega
  have hdrop := dropBitmap_lt hj hm hS
  have hdrop1024 := bound_1024 (by omega : m-1 ≤ 10) hdrop
  fin_cases keep
  · simp only [projectDropped, dropPattern, Fin.val_zero, Nat.zero_and, beq_self_eq_true, ite_true]
    rw [testBit_dropBitmap_image hi10 hdrop1024]
    simp only [testBit_dropBitmap_image hj10 hS1024]
    constructor
    · rintro ⟨u, ⟨x, hx, hxu⟩, huy⟩
      exact ⟨x, hx, by simpa [hxu] using huy⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨delBit j x, ⟨x, hx, rfl⟩, hxy⟩
  · simpa [projectDropped, dropPattern] using testBit_dropBitmap_image hj10 hS1024 y
  · simpa [projectDropped, dropPattern] using testBit_dropBitmap_image hi10 hS1024 y
  · simp [projectDropped, dropPattern]

lemma projectDropped_lt {m i j S : Nat} (hij : i < j) (hj : j < m) (hm : m ≤ 10)
    (hS : S < 2^(2^m)) (keep : Fin 4) :
    projectDropped i j keep S < 2^(2^(m-2+keepSize keep)) := by
  have htwo : 2 ≤ m := by omega
  have hm1 : m-2+1 = m-1 := by omega
  have hm2 : m-2+2 = m := by omega
  fin_cases keep
  · simpa [projectDropped, keepSize, Nat.sub_sub] using
      dropBitmap_lt (by omega : i < m-1) (by omega : m-1 ≤ 10) (dropBitmap_lt hj hm hS)
  · simpa [projectDropped, keepSize, hm1] using dropBitmap_lt hj hm hS
  · simpa [projectDropped, keepSize, hm1] using dropBitmap_lt (by omega : i < m) hm hS
  · simpa [projectDropped, keepSize, hm2] using hS

lemma dropPattern_lt {m i j x : Nat} (hij : i < j) (hj : j < m)
    (hx : x < 2^m) (keep : Fin 4) :
    dropPattern i j keep x < 2^(m-2+keepSize keep) := by
  have htwo : 2 ≤ m := by omega
  have hm1 : m-2+1 = m-1 := by omega
  have hm2 : m-2+2 = m := by omega
  fin_cases keep
  · simpa [dropPattern, keepSize, Nat.sub_sub] using
      delBit_lt (by omega : i < m-1) (delBit_lt hj hx)
  · simpa [dropPattern, keepSize, hm1] using delBit_lt hj hx
  · simpa [dropPattern, keepSize, hm1] using delBit_lt (by omega : i < m) hx
  · simpa [dropPattern, keepSize, hm2] using hx

def transitionSet (m i j : Nat) (keep : Fin 4) (gate S : Nat) : Nat :=
  let zero := projectDropped i j keep (planeZero S gate)
  let one := projectDropped i j keep (planeOne S gate)
  zero ||| (one <<< (1 <<< (m-2+keepSize keep)))

lemma transitionSet_eq_appendPlanes (m i j : Nat) (keep : Fin 4) (gate S : Nat) :
    transitionSet m i j keep gate S =
      appendPlanes (m-2+keepSize keep)
        (projectDropped i j keep (planeZero S gate))
        (projectDropped i j keep (planeOne S gate)) := by
  simp [transitionSet, appendPlanes, joinPlanes, Nat.shiftLeft_eq]

lemma transitionSet_image {m i j S : Nat} (hij : i < j) (hj : j < m) (hm : m ≤ 10)
    (hS : S < 2^(2^m)) (keep : Fin 4) (gate y : Nat) :
    (transitionSet m i j keep gate S).testBit y = true ↔
      ∃ x, S.testBit x = true ∧
        y = dropPattern i j keep x + (if gate.testBit x then 2^(m-2+keepSize keep) else 0) := by
  have hS1024 := bound_1024 hm hS
  have hzero : planeZero S gate < 2^(2^m) := lt_of_le_of_lt (planeZero_le S gate) hS
  have hone : planeOne S gate < 2^(2^m) := lt_of_le_of_lt (planeOne_le S gate) hS
  rw [transitionSet_eq_appendPlanes, appendPlanes,
    joinPlanes_image (projectDropped_lt hij hj hm hzero keep) (projectDropped_lt hij hj hm hone keep)]
  constructor
  · rintro (⟨u, hu, hbit, hy⟩ | ⟨u, hu, hbit, hy⟩)
    · rcases (projectDropped_image hij hj hm hzero keep u).mp hbit with ⟨x, hx, hxu⟩
      rw [testBit_planeZero hS1024] at hx
      have hpair : S.testBit x = true ∧ gate.testBit x = false := by
        simpa using hx
      obtain ⟨hxS, hg⟩ := hpair
      exact ⟨x, hxS, by simpa [hg, hxu] using hy⟩
    · rcases (projectDropped_image hij hj hm hone keep u).mp hbit with ⟨x, hx, hxu⟩
      rw [testBit_planeOne] at hx
      have hpair : S.testBit x = true ∧ gate.testBit x = true := by
        simpa only [Bool.and_eq_true] using hx
      obtain ⟨hxS, hxgate⟩ := hpair
      exact ⟨x, hxS, by simpa [hxgate, hxu] using hy⟩
  · rintro ⟨x, hxS, hy⟩
    have hxb := bitIndex_lt hS hxS
    have hdrop := dropPattern_lt hij hj hxb keep
    cases hg : gate.testBit x with
    | false =>
      have hbit : (planeZero S gate).testBit x = true := by
        simp [testBit_planeZero hS1024, hxS, hg]
      exact Or.inl ⟨dropPattern i j keep x, hdrop,
        (projectDropped_image hij hj hm hzero keep _).mpr ⟨x, hbit, rfl⟩,
        by simpa [hg] using hy⟩
    | true =>
      have hbit : (planeOne S gate).testBit x = true := by
        simp [testBit_planeOne, hxS, hg]
      exact Or.inr ⟨dropPattern i j keep x, hdrop,
        (projectDropped_image hij hj hm hone keep _).mpr ⟨x, hbit, rfl⟩,
        by simpa [hg] using hy⟩

lemma transitionSet_lt {m i j S : Nat} (hij : i < j) (hj : j < m) (hm : m ≤ 10)
    (hS : S < 2^(2^m)) (keep : Fin 4) (gate : Nat) :
    transitionSet m i j keep gate S < 2^(2^(m-1+keepSize keep)) := by
  have hzero : planeZero S gate < 2^(2^m) := lt_of_le_of_lt (planeZero_le S gate) hS
  have hone : planeOne S gate < 2^(2^m) := lt_of_le_of_lt (planeOne_le S gate) hS
  rw [transitionSet_eq_appendPlanes]
  have h := appendPlanes_lt (projectDropped_lt hij hj hm hzero keep)
    (projectDropped_lt hij hj hm hone keep)
  have he : m-2+keepSize keep+1 = m-1+keepSize keep := by omega
  simpa [he] using h

lemma transitionSet_gate_image {m i j S : Nat} (hij : i < j) (hj : j < m) (hm : m ≤ 10)
    (hS : S < 2^(2^m)) (keep d : Fin 4) (y : Nat) :
    (transitionSet m i j keep (gateMask i j d) S).testBit y = true ↔
      ∃ x, S.testBit x = true ∧ y = dropPattern i j keep x +
        (if ChromGate.eval d (x.testBit i) (x.testBit j) then 2^(m-2+keepSize keep) else 0) := by
  rw [transitionSet_image hij hj hm hS]
  have hS1024 := bound_1024 hm hS
  constructor <;> rintro ⟨x, hx, hy⟩
  · have hg := gateMask_bits ⟨i, by omega⟩ ⟨j, by omega⟩ d ⟨x, bitIndex_lt hS1024 hx⟩
    exact ⟨x, hx, by simpa only [hg] using hy⟩
  · have hg := gateMask_bits ⟨i, by omega⟩ ⟨j, by omega⟩ d ⟨x, bitIndex_lt hS1024 hx⟩
    exact ⟨x, hx, by simpa only [hg] using hy⟩

end PnTransition

namespace PNQuotient

variable {Q : Type} {width : Nat}

def liveState (rep : Nat → Q → List (BitVec width) → Prop) (goal : BitVec width)
    (k : Nat) (s : Q) : Prop :=
  ∃ ws, ws.Nodup ∧ rep k s ws ∧ live basicOps goal k ws.toFinset

def search (done : Q → Bool) (admissible : Nat → Q → Bool)
    (children : Nat → Q → List Q) : Nat → Q → Bool
  | 0, s => done s
  | k + 1, s => done s ||
      (admissible (k + 1) s && (children (k + 1) s).any (search done admissible children k))

lemma kept_front {a b : BitVec width} {r kept : List (BitVec width)}
    (hk : kept ∈ SearchKernel.keepChoices a b r) :
    ∃ front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width))),
      kept = front ++ r := by
  simp only [SearchKernel.keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact ⟨[], by simp, rfl⟩
  · exact ⟨[a], by simp, rfl⟩
  · exact ⟨[b], by simp, rfl⟩
  · exact ⟨[a,b], by simp, rfl⟩

lemma liveState_step {rep : Nat → Q → List (BitVec width) → Prop} {goal : BitVec width}
    {done : Q → Bool} {children : Nat → Q → List Q}
    (finish : ∀ k s, rep k s [goal] → done s = true)
    (cover : ∀ (k : Nat) (s : Q) (ws : List (BitVec width))
      (a b z : BitVec width) (r front : List (BitVec width)),
      ws.Nodup → rep (k + 1) s ws → (a, b, r) ∈ SearchKernel.pairs ws →
      front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width))) →
      z ∈ basicOps a b → z ∉ ws.toFinset →
      live basicOps goal k (z :: (front ++ r)).toFinset →
      ∃ t ∈ children (k + 1) s, ∃ ys, rep k t ys ∧ ys.Perm (z :: (front ++ r)))
    {k : Nat} {s : Q} (hs : liveState rep goal (k + 1) s) :
    done s = true ∨ ∃ t ∈ children (k + 1) s, liveState rep goal k t := by
  obtain ⟨ws, hn, hrep, hrun⟩ := hs
  rcases first_live hrun with hstop | ⟨a, ha, b, hb, hab, z, hz, hnew, U, hset, tail⟩
  · left
    exact finish (k + 1) s ((SearchKernel.singleton_list hn hstop) ▸ hrep)
  · right
    obtain ⟨r, hm, hp⟩ := SearchKernel.pick_two
      (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : BitVec width} (hpair : (a, b, r) ∈ SearchKernel.pairs ws)
        (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b U)) (hop : z ∈ basicOps a b) :
        ∃ t ∈ children (k + 1) s, liveState rep goal k t := by
      obtain ⟨kept, hk, hnk, hfin⟩ := SearchKernel.recover_kept perm hn hset
      have hzkept : z ∉ kept := by
        intro hzmem
        apply hnew
        rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (hfin ▸ List.mem_toFinset.mpr hzmem))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hzkept, hnk⟩
      have hl : live basicOps goal k (z :: kept).toFinset := by
        simpa only [List.toFinset_cons, hfin] using tail
      obtain ⟨front, hfront, rfl⟩ := kept_front hk
      obtain ⟨t, ht, ys, htrep, hperm⟩ := cover k s ws a b z r front hn hrep hpair hfront hop hnew hl
      have heq : ys.toFinset = (z :: (front ++ r)).toFinset := by
        ext w
        simp only [List.mem_toFinset]
        exact hperm.mem_iff
      exact ⟨t, ht, ys, hperm.nodup_iff.mpr hnd, htrep, heq.symm ▸ hl⟩
    rcases hm with direct | swap
    · exact go direct hp hset hz
    · exact go swap (hp.trans (.swap _ _ _)) (by rw [hset, Finset.insert_comm])
        (SearchKernel.ops_swap a b ▸ hz)

lemma search_complete {rep : Nat → Q → List (BitVec width) → Prop} {goal : BitVec width}
    {done : Q → Bool} {admissible : Nat → Q → Bool} {children : Nat → Q → List Q}
    (finish : ∀ k s, rep k s [goal] → done s = true)
    (step : ∀ k s, liveState rep goal (k + 1) s →
      done s = true ∨ ∃ t ∈ children (k + 1) s, liveState rep goal k t)
    (allowed : ∀ k s, liveState rep goal (k + 1) s → admissible (k + 1) s = true)
    {k : Nat} {s : Q} (hs : liveState rep goal k s) :
    search done admissible children k s = true := by
  induction k generalizing s with
  | zero =>
    obtain ⟨ws, hn, hrep, hrun⟩ := hs
    exact finish 0 s ((SearchKernel.singleton_list hn hrun) ▸ hrep)
  | succ k ih =>
    rcases step k s hs with hdone | ⟨t, ht, htail⟩
    · simp only [search, hdone, Bool.true_or]
    · simp only [search, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true]
      exact Or.inr ⟨allowed k s hs, t, ht, ih htail⟩

lemma rejected_no_liveState {rep : Nat → Q → List (BitVec width) → Prop} {goal : BitVec width}
    {done : Q → Bool} {admissible : Nat → Q → Bool} {children : Nat → Q → List Q}
    (finish : ∀ k s, rep k s [goal] → done s = true)
    (step : ∀ k s, liveState rep goal (k + 1) s →
      done s = true ∨ ∃ t ∈ children (k + 1) s, liveState rep goal k t)
    (allowed : ∀ k s, liveState rep goal (k + 1) s → admissible (k + 1) s = true)
    {k : Nat} {s : Q} (rejected : search done admissible children k s = false) :
    ¬ liveState rep goal k s := by
  intro hs
  have found := search_complete finish step allowed hs
  rw [rejected] at found
  contradiction

lemma build_represented_sublist {rep : Nat → Q → List (BitVec width) → Prop}
    {goal : BitVec width} {k : Nat} {inputs : List (BitVec width)}
    (hn : inputs.Nodup)
    (represented : ∀ ws, ws.Sublist inputs → ∃ s, rep k s ws)
    (run : build basicOps goal k inputs.toFinset) :
    ∃ s, liveState rep goal k s := by
  classical
  obtain ⟨S, hS, hlive⟩ := compress run
  let ws := inputs.filter (· ∈ S)
  have hfin : ws.toFinset = S := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq,
      and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hS hw)
  obtain ⟨s, hs⟩ := represented ws (List.filter_sublist ..)
  exact ⟨s, ws, hn.filter _, hs, hfin.symm ▸ hlive⟩

lemma live_length_cap {goal : BitVec width} {k cap : Nat} {ws : List (BitVec width)}
    (hn : ws.Nodup) (run : live basicOps goal k ws.toFinset)
    (room : ws.length + k < 2 * cap) : ws.length ≤ cap := by
  have hc := live_card run
  rw [List.toFinset_card_of_nodup hn] at hc
  omega

lemma child_length_budget {a b z : BitVec width} {ws r front : List (BitVec width)}
    {k bound : Nat} (hp : ws.Perm (a :: b :: r))
    (hf : front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width))))
    (room : ws.length + (k + 1) ≤ bound) :
    (z :: (front ++ r)).length + k ≤ bound := by
  have plen := hp.length_eq
  have flen : front.length ≤ 2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl <;> simp
  simp only [List.length_cons, List.length_append] at plen ⊢
  omega

lemma build_represented_roots {rep : Nat → Q → List (BitVec width) → Prop}
    {goal : BitVec width} {k : Nat} {inputs : List (BitVec width)} {roots : List Q}
    (hn : inputs.Nodup)
    (represented : ∀ ws, ws.Sublist inputs → ws.Nodup →
      live basicOps goal k ws.toFinset →
      ∃ s ∈ roots, ∃ ys, rep k s ys ∧ ys.Perm ws)
    (run : build basicOps goal k inputs.toFinset) :
    ∃ s ∈ roots, liveState rep goal k s := by
  classical
  obtain ⟨S, hS, hlive⟩ := compress run
  let ws := inputs.filter (· ∈ S)
  have hfin : ws.toFinset = S := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq,
      and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hS hw)
  have hnd : ws.Nodup := hn.filter _
  have hrun : live basicOps goal k ws.toFinset := hfin.symm ▸ hlive
  obtain ⟨s, hs, ys, hrep, hp⟩ := represented ws (List.filter_sublist ..) hnd hrun
  have heq : ys.toFinset = ws.toFinset := by
    ext w
    simp only [List.mem_toFinset]
    exact hp.mem_iff
  exact ⟨s, hs, ys, hp.nodup_iff.mpr hnd, hrep, heq.symm ▸ hrun⟩

lemma rejected_roots_no_build {rep : Nat → Q → List (BitVec width) → Prop}
    {goal : BitVec width} {k : Nat} {inputs : List (BitVec width)} {roots : List Q}
    {done : Q → Bool} {admissible : Nat → Q → Bool} {children : Nat → Q → List Q}
    (hn : inputs.Nodup)
    (finish : ∀ k s, rep k s [goal] → done s = true)
    (step : ∀ k s, liveState rep goal (k + 1) s →
      done s = true ∨ ∃ t ∈ children (k + 1) s, liveState rep goal k t)
    (allowed : ∀ k s, liveState rep goal (k + 1) s → admissible (k + 1) s = true)
    (represented : ∀ ws, ws.Sublist inputs → ws.Nodup →
      live basicOps goal k ws.toFinset →
      ∃ s ∈ roots, ∃ ys, rep k s ys ∧ ys.Perm ws)
    (rejected : ∀ s ∈ roots, search done admissible children k s = false) :
    ¬ build basicOps goal k inputs.toFinset := by
  intro run
  obtain ⟨s, hs, hlive⟩ := build_represented_roots hn represented run
  exact rejected_no_liveState finish step allowed (rejected s hs) hlive

end PNQuotient

end PEqualNP.Outside.L_meta_10760
