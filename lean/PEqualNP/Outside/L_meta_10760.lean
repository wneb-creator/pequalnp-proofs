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

def canonical (w : BitVec width) : BitVec width :=
  if w.toNat ≤ (~~~w).toNat then w else ~~~w

lemma canonical_of_msb_false {w : BitVec width} (h : w.msb = false) :
    canonical w = w := by
  have bound := BitVec.msb_eq_false_iff_two_mul_lt.mp h
  have order : w.toNat ≤ (~~~w).toNat := by
    rw [BitVec.toNat_not]
    omega
  simp only [canonical, if_pos order]

lemma canonical_msb_false (w : BitVec width) : (canonical w).msb = false := by
  unfold canonical
  split_ifs with order
  · apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    rw [BitVec.toNat_not] at order
    have bound := w.isLt
    omega
  · apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    rw [BitVec.toNat_not] at order ⊢
    have bound := w.isLt
    omega

lemma ops_msb_false {a b w : BitVec width} (ha : a.msb = false)
    (hb : b.msb = false) (hw : w ∈ ops a b) : w.msb = false := by
  simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> simp [ha, hb]

lemma canonical_ops {a b : BitVec width} (ha : a.msb = false)
    (hb : b.msb = false) : (ops a b).map canonical = ops a b := by
  have one (w : BitVec width) (hw : w ∈ ops a b) : canonical w = w :=
    canonical_of_msb_false (ops_msb_false ha hb hw)
  simpa only [List.map_id'] using List.map_congr_left one

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


lemma signedRootsTransport {width n : Nat} {g : BitVec width}
    (nonzero : g ≠ 0) (nonones : g ≠ ~~~0)
    {s t : Finset (BitVec width)}
    (represented : ∀ x ∈ s, holds t x)
    (run : build basicOps g n s) :
    ∃ g', (g' = g ∨ g' = ~~~g) ∧ build basicOps g' n t := by
  induction n generalizing s t with
  | zero =>
    have hg : holds t g := represented g run
    rcases hg with hzero | hones | ⟨a, ha, h | h⟩
    · exact False.elim (nonzero hzero)
    · exact False.elim (nonones hones)
    · exact ⟨a, .inl h.symm, ha⟩
    · exact ⟨a, .inr (by rw [h, BitVec.not_not]), ha⟩
  | succ n ih =>
    rcases run with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨g', he, hg'⟩ := ih represented skip
      exact ⟨g', he, Or.inl hg'⟩
    · have za : holds t a := represented a ha
      have zb : holds t b := represented b hb
      have reach : reachable t z := by
        simp only [basicOps, ops, List.mem_toFinset, List.mem_cons,
          List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact and_reach za zb
        · exact or_reach za zb
        · exact and_reach za (holds_not zb)
        · exact and_reach zb (holds_not za)
      rcases reach with old | ⟨a', ha', b', hb', ne, w, hw, added⟩
      · have rep : ∀ x ∈ insert z s, holds t x := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact old
          · exact represented x hx
        obtain ⟨g', he, hg'⟩ := ih rep tail
        exact ⟨g', he, Or.inl hg'⟩
      · have rep : ∀ x ∈ insert z s, holds (insert w t) x := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact added
          · exact holds_insert (represented x hx)
        obtain ⟨g', he, hg'⟩ := ih rep tail
        exact ⟨g', he, Or.inr ⟨a', ha', b', hb', ne, w, hw, hg'⟩⟩


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



namespace PNFrontier

open PnProjection PnTransition

variable {width : Nat}

def rowCode (ws : List (BitVec width)) (r : Fin width) : Nat :=
  (BitVec.ofBoolListLE (ws.map fun w => w[r.val])).toNat

lemma testBit_rowCode (ws : List (BitVec width)) (r : Fin width) (i : Nat) :
    (rowCode ws r).testBit i = ((ws[i]?).map fun w => w[r.val]).getD false := by
  change (BitVec.ofBoolListLE (ws.map fun w => w[r.val])).getLsbD i = _
  rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_map]

lemma rowCode_testBit (ws : List (BitVec width)) (r : Fin width) (i : Nat)
    (hi : i < ws.length) : (rowCode ws r).testBit i = ws[i][r.val] := by
  simp [testBit_rowCode, hi]

lemma rowCode_lt (ws : List (BitVec width)) (r : Fin width) : rowCode ws r < 2^ws.length := by
  simpa only [rowCode, List.length_map] using
    (BitVec.ofBoolListLE (ws.map fun w => w[r.val])).isLt

lemma rowCode_eraseIdx (ws : List (BitVec width)) (r : Fin width) (i : Nat) :
    rowCode (ws.eraseIdx i) r = delBit i (rowCode ws r) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_rowCode, testBit_delBit, testBit_rowCode, List.getElem?_eraseIdx]
  by_cases h : j < i <;> simp [h]

lemma rowCode_append_insBit (ws : List (BitVec width)) (z : BitVec width) (r : Fin width) :
    rowCode (ws ++ [z]) r = insBit ws.length z[r.val] (rowCode ws r) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_rowCode, testBit_insBit, List.getElem?_append]
  by_cases h : j < ws.length
  · simp [h, testBit_rowCode]
  · by_cases e : j = ws.length
    · simp [e]
    · have hs : ws.length ≤ j-1 := by omega
      have hz : j-ws.length ≠ 0 := by omega
      simp [h, e, testBit_rowCode, List.getElem?_eq_none hs, hz]

lemma rowCode_append_singleton (ws : List (BitVec width)) (z : BitVec width) (r : Fin width) :
    rowCode (ws ++ [z]) r = rowCode ws r + (if z[r.val] then 2^ws.length else 0) := by
  rw [rowCode_append_insBit, insBit_top _ _ (rowCode_lt ws r)]

def keptFront (i j : Nat) (keep : Fin 4) (ws : List (BitVec width)) : List (BitVec width) :=
  let ws := if keep.val &&& 2 == 0 then ws.eraseIdx j else ws
  if keep.val &&& 1 == 0 then ws.eraseIdx i else ws

lemma rowCode_keptFront (i j : Nat) (keep : Fin 4) (ws : List (BitVec width)) (r : Fin width) :
    rowCode (keptFront i j keep ws) r = dropPattern i j keep (rowCode ws r) := by
  unfold keptFront dropPattern
  split_ifs <;> simp only [rowCode_eraseIdx]

lemma keptFront_length {i j : Nat} (keep : Fin 4) (ws : List (BitVec width))
    (hij : i < j) (hj : j < ws.length) :
    (keptFront i j keep ws).length = ws.length-2+keepSize keep := by
  have hi : i < ws.length := by omega
  have hi' : i < (ws.eraseIdx j).length := by
    rw [List.length_eraseIdx_of_lt hj]
    omega
  fin_cases keep <;>
    simp [keptFront, keepSize, List.length_eraseIdx_of_lt hj,
      List.length_eraseIdx_of_lt hi, List.length_eraseIdx_of_lt hi'] <;> omega

lemma keptFront_sublist (i j : Nat) (keep : Fin 4) (ws : List (BitVec width)) :
    (keptFront i j keep ws).Sublist ws := by
  unfold keptFront
  split_ifs <;>
    first
    | exact (List.eraseIdx_sublist _ _).trans (List.eraseIdx_sublist _ _)
    | exact List.eraseIdx_sublist _ _
    | exact List.Sublist.refl _

lemma keptFront_mem {i j : Nat} {keep : Fin 4} {ws : List (BitVec width)} {w : BitVec width}
    (hw : w ∈ keptFront i j keep ws) : w ∈ ws := by
  unfold keptFront at hw
  split_ifs at hw <;>
    first
    | exact List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx hw)
    | exact List.mem_of_mem_eraseIdx hw
    | exact hw

end PNFrontier

namespace PNSelectors

lemma singles_index {α : Type} {ws r : List α} {a : α}
    (h : (a,r) ∈ SearchKernel.singles ws) :
    ∃ i, i < ws.length ∧ ws[i]? = some a ∧ r = ws.eraseIdx i ∧
      ws.Perm (a :: r) := by
  induction ws generalizing a r with
  | nil => simp [SearchKernel.singles] at h
  | cons x xs ih =>
    simp only [SearchKernel.singles, List.mem_cons, List.mem_map] at h
    rcases h with he | ⟨⟨a,r⟩, hm, he⟩
    · cases he
      exact ⟨0, by simp, rfl, rfl, .refl _⟩
    · cases he
      obtain ⟨i, hi, hv, hr, hp⟩ := ih hm
      refine ⟨i+1, by simpa using hi, by simpa using hv, ?_, ?_⟩
      · simp [hr]
      · exact (hp.cons x).trans (.swap _ _ _)

lemma pairs_indices {α : Type} {ws r : List α} {a b : α}
    (h : (a,b,r) ∈ SearchKernel.pairs ws) :
    ∃ i j, i < j ∧ j < ws.length ∧ ws[i]? = some a ∧ ws[j]? = some b ∧
      r = (ws.eraseIdx j).eraseIdx i ∧ ws.Perm (a :: b :: r) := by
  induction ws generalizing a b r with
  | nil => simp [SearchKernel.pairs] at h
  | cons x xs ih =>
    simp only [SearchKernel.pairs, List.mem_append, List.mem_map] at h
    rcases h with ⟨⟨b,r⟩, hm, he⟩ | ⟨⟨a,b,r⟩, hm, he⟩
    · cases he
      obtain ⟨j, hj, hv, hr, hp⟩ := singles_index hm
      refine ⟨0, j+1, by omega, by simpa using hj, rfl,
        by simpa using hv, ?_, hp.cons x⟩
      simp [hr]
    · cases he
      obtain ⟨i, j, hij, hj, hiVal, hjVal, hr, hp⟩ := ih hm
      refine ⟨i+1, j+1, by omega, by simpa using hj,
        by simpa using hiVal, by simpa using hjVal, ?_, ?_⟩
      · simp [hr]
      · exact (hp.cons x).trans ((List.Perm.swap _ _ _).trans
          ((List.Perm.swap _ _ _).cons a))

lemma perm_cons_eraseIdx {α : Type} {ws : List α} {i : Nat} {a : α}
    (h : ws[i]? = some a) : ws.Perm (a :: ws.eraseIdx i) := by
  induction ws generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst x
      exact .refl _
    | succ i =>
      have hp := ih (by simpa using h)
      simpa using (hp.cons x).trans (.swap _ _ _)

lemma pairs_retention_indices {α : Type} {ws r : List α} {a b : α}
    (h : (a,b,r) ∈ SearchKernel.pairs ws) :
    ∃ i j, i < j ∧ j < ws.length ∧ ws[i]? = some a ∧ ws[j]? = some b ∧
      (ws.eraseIdx j).eraseIdx i = r ∧
      (ws.eraseIdx j).Perm (a :: r) ∧
      (ws.eraseIdx i).Perm (b :: r) ∧ ws.Perm (a :: b :: r) := by
  obtain ⟨i, j, hij, hj, hiVal, hjVal, hr, hp⟩ := pairs_indices h
  refine ⟨i, j, hij, hj, hiVal, hjVal, hr.symm, ?_, ?_, hp⟩
  · have hb := perm_cons_eraseIdx hjVal
    have hab : ws.Perm (b :: a :: r) := hp.trans (.swap _ _ _)
    exact (List.perm_cons b).mp (hb.symm.trans hab)
  · have ha := perm_cons_eraseIdx hiVal
    exact (List.perm_cons a).mp (ha.symm.trans hp)

lemma pairs_keptFront_indices {width : Nat}
    {ws r front : List (BitVec width)} {a b : BitVec width}
    (h : (a,b,r) ∈ SearchKernel.pairs ws)
    (hf : front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width)))) :
    ∃ i j, ∃ keep : Fin 4,
      i < j ∧ j < ws.length ∧ ws[i]? = some a ∧ ws[j]? = some b ∧
      (PNFrontier.keptFront i j keep ws).Perm (front ++ r) := by
  obtain ⟨i, j, hij, hj, ha, hb, hnone, honlyA, honlyB, hboth⟩ := pairs_retention_indices h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · refine ⟨i, j, 0, hij, hj, ha, hb, ?_⟩
    simpa [PNFrontier.keptFront, hnone] using (List.Perm.refl r)
  · refine ⟨i, j, 1, hij, hj, ha, hb, ?_⟩
    simpa [PNFrontier.keptFront] using honlyA
  · refine ⟨i, j, 2, hij, hj, ha, hb, ?_⟩
    simpa [PNFrontier.keptFront] using honlyB
  · refine ⟨i, j, 3, hij, hj, ha, hb, ?_⟩
    simpa [PNFrontier.keptFront] using hboth

end PNSelectors

namespace PNConcrete

open PnTransition PNPlanes


def Rep {width : Nat} (target : BitVec width) (anchor : Fin width)
    (k : Nat) (state : Nat × Nat × Nat) (ws : List (BitVec width)) : Prop :=
  ws.length = state.1 ∧ state.1 + k ≤ 19 ∧ state.1 ≤ 10 ∧
    (∀ w ∈ ws, w[anchor.val] = false) ∧
    ∀ value : Bool, ∀ x : Nat,
      (if value then state.2.1 else state.2.2).testBit x = true ↔
        ∃ r : Fin width, target[r.val] = value ∧ PNFrontier.rowCode ws r = x

lemma bitmap_bound {ρ : Type} {m S : Nat} {code : ρ → Nat} {label : ρ → Prop}
    (bounded : ∀ r, code r < 2^m)
    (represented : ∀ x, S.testBit x = true ↔ ∃ r, label r ∧ code r = x) :
    S < 2^(2^m) := by
  apply Nat.lt_pow_two_of_testBit
  intro x hx
  cases hb : S.testBit x with
  | false => rfl
  | true =>
    obtain ⟨r, hr, he⟩ := (represented x).mp hb
    have hc := bounded r
    omega

lemma transitionSet_exact {ρ : Type} {m i j S : Nat}
    (hij : i < j) (hj : j < m) (hm : m ≤ 10) (hS : S < 2^(2^m))
    (keep gate : Fin 4) {code childCode : ρ → Nat} {label : ρ → Prop}
    (represented : ∀ x, S.testBit x = true ↔ ∃ r, label r ∧ code r = x)
    (rows : ∀ r, childCode r = dropPattern i j keep (code r) +
      (if ChromGate.eval gate ((code r).testBit i) ((code r).testBit j)
        then 2^(m-2+keepSize keep) else 0)) :
    ∀ y, (transitionSet m i j keep (gateMask i j gate) S).testBit y = true ↔
      ∃ r, label r ∧ childCode r = y := by
  intro y
  rw [transitionSet_gate_image hij hj hm hS]
  constructor
  · rintro ⟨x, hx, hy⟩
    obtain ⟨r, hr, hcode⟩ := (represented x).mp hx
    subst x
    exact ⟨r, hr, (rows r).trans hy.symm⟩
  · rintro ⟨r, hr, hy⟩
    refine ⟨code r, (represented (code r)).mpr ⟨r, hr, rfl⟩, ?_⟩
    exact hy.symm.trans (rows r)

def childState (m P N i j : Nat) (keep gate : Fin 4) : Nat × Nat × Nat :=
  (m - 1 + keepSize keep,
    transitionSet m i j keep (gateMask i j gate) P,
    transitionSet m i j keep (gateMask i j gate) N)

def childFront {width : Nat} (ws : List (BitVec width)) (i j : Nat)
    (keep gate : Fin 4) (a b : BitVec width) : List (BitVec width) :=
  PNFrontier.keptFront i j keep ws ++ [ChromGate.word gate a b]

lemma childFront_rows {width : Nat} (ws : List (BitVec width)) (i j : Nat)
    (keep gate : Fin 4) (a b : BitVec width)
    (hij : i < j) (hj : j < ws.length)
    (ha : ws[i]? = some a) (hb : ws[j]? = some b) (r : Fin width) :
    PNFrontier.rowCode (childFront ws i j keep gate a b) r =
      dropPattern i j keep (PNFrontier.rowCode ws r) +
        (if ChromGate.eval gate ((PNFrontier.rowCode ws r).testBit i)
          ((PNFrontier.rowCode ws r).testBit j)
          then 2^(ws.length-2+keepSize keep) else 0) := by
  rw [childFront, PNFrontier.rowCode_append_singleton,
    PNFrontier.rowCode_keptFront, PNFrontier.keptFront_length keep ws hij hj,
    ChromGate.word_get, PNFrontier.testBit_rowCode, PNFrontier.testBit_rowCode,
    ha, hb]
  rfl

lemma childFront_nodup {width : Nat} {ws : List (BitVec width)} {i j : Nat}
    {keep gate : Fin 4} {a b : BitVec width} (hn : ws.Nodup)
    (fresh : ChromGate.word gate a b ∉ ws.toFinset) :
    (childFront ws i j keep gate a b).Nodup := by
  rw [childFront, List.nodup_append]
  refine ⟨hn.sublist (PNFrontier.keptFront_sublist i j keep ws), by simp, ?_⟩
  intro w hw v hv hwv
  have he := List.mem_singleton.mp hv
  subst v
  subst w
  exact fresh (List.mem_toFinset.mpr (PNFrontier.keptFront_mem hw))

lemma rep_transition {width k m P N i j : Nat}
    {target goal a b : BitVec width} {anchor : Fin width} {ws : List (BitVec width)}
    (keep gate : Fin 4) (hn : ws.Nodup) (rep : Rep target anchor (k + 1) (m,P,N) ws)
    (hij : i < j) (hj : j < m) (ha : ws[i]? = some a) (hb : ws[j]? = some b)
    (hamem : a ∈ ws) (hbmem : b ∈ ws)
    (fresh : ChromGate.word gate a b ∉ ws.toFinset)
    (tail : live basicOps goal k (childFront ws i j keep gate a b).toFinset) :
    Rep target anchor k (childState m P N i j keep gate)
      (childFront ws i j keep gate a b) := by
  obtain ⟨hlen, hroom, hcap, hzero, hexact⟩ := rep
  have hjw : j < ws.length := by omega
  have hm2 : 2 ≤ m := by omega
  have hsize : keepSize keep ≤ 2 := by
    fin_cases keep <;> decide
  have childlen : (childFront ws i j keep gate a b).length = m-1+keepSize keep := by
    simp only [childFront, List.length_append, List.length_singleton,
      PNFrontier.keptFront_length keep ws hij hjw, hlen]
    omega
  have childroom : (m-1+keepSize keep) + k ≤ 19 := by omega
  have childcap : m-1+keepSize keep ≤ 10 := by
    have hc := live_card tail
    rw [List.toFinset_card_of_nodup (childFront_nodup hn fresh), childlen] at hc
    omega
  refine ⟨childlen, childroom, childcap, ?_, ?_⟩
  · intro w hw
    rcases List.mem_append.mp hw with hold | hnew
    · exact hzero w (PNFrontier.keptFront_mem hold)
    · have he := List.mem_singleton.mp hnew
      subst w
      rw [ChromGate.word_get, hzero a hamem, hzero b hbmem]
      fin_cases gate <;> rfl
  · intro value y
    have bound : (if value then P else N) < 2^(2^m) := by
      apply bitmap_bound (code := PNFrontier.rowCode ws) (label := fun r => target[r.val] = value)
      · intro r
        simpa only [hlen] using PNFrontier.rowCode_lt ws r
      · exact hexact value
    have he := transitionSet_exact hij hj hcap bound keep gate
      (represented := hexact value)
      (rows := fun r => by
        simpa only [hlen] using childFront_rows ws i j keep gate a b hij hjw ha hb r) y
    cases value <;> exact he

end PNConcrete

namespace PNConcrete

lemma transitionCover {width k m P N : Nat}
    {target goal a b z : BitVec width} {anchor : Fin width}
    {ws r front : List (BitVec width)}
    (hn : ws.Nodup) (rep : Rep target anchor (k+1) (m,P,N) ws)
    (hpair : (a,b,r) ∈ SearchKernel.pairs ws)
    (hfront : front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width))))
    (hz : z ∈ basicOps a b) (fresh : z ∉ ws.toFinset)
    (tail : live basicOps goal k (z :: (front ++ r)).toFinset) :
    ∃ i j, ∃ keep gate : Fin 4, i < j ∧ j < m ∧
      ∃ ys, Rep target anchor k (childState m P N i j keep gate) ys ∧
        ys.Perm (z :: (front ++ r)) := by
  obtain ⟨i, j, keep, hij, hj, ha, hb, hp⟩ := PNSelectors.pairs_keptFront_indices hpair hfront
  obtain ⟨gate, rfl⟩ := ChromGate.of_basicOps hz
  have hperm : (childFront ws i j keep gate a b).Perm
      (ChromGate.word gate a b :: (front ++ r)) := by
    change (PNFrontier.keptFront i j keep ws ++ [ChromGate.word gate a b]).Perm _
    exact List.perm_append_comm.trans (hp.cons _)
  have heq : (childFront ws i j keep gate a b).toFinset =
      (ChromGate.word gate a b :: (front ++ r)).toFinset := by
    ext w
    simp only [List.mem_toFinset]
    exact hperm.mem_iff
  have htail : live basicOps goal k (childFront ws i j keep gate a b).toFinset :=
    heq.symm ▸ tail
  have hamem : a ∈ ws := (PNSelectors.perm_cons_eraseIdx ha).mem_iff.mpr (by simp)
  have hbmem : b ∈ ws := (PNSelectors.perm_cons_eraseIdx hb).mem_iff.mpr (by simp)
  have hjm : j < m := by have hlen := rep.1; omega
  exact ⟨i, j, keep, gate, hij, hjm, childFront ws i j keep gate a b,
    rep_transition keep gate hn rep hij hjm ha hb hamem hbmem fresh htail, hperm⟩

def coordinateChildren (state : Nat × Nat × Nat) : List (Nat × Nat × Nat) :=
  (List.range state.1).flatMap fun j =>
    (List.range j).flatMap fun i =>
      (List.finRange 4).flatMap fun gate =>
        (List.finRange 4).map fun keep =>
          childState state.1 state.2.1 state.2.2 i j keep gate

lemma childState_mem {m P N i j : Nat} (keep gate : Fin 4)
    (hij : i < j) (hj : j < m) :
    childState m P N i j keep gate ∈ coordinateChildren (m,P,N) := by
  simp only [coordinateChildren, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨j, hj, i, hij, gate, by simp, keep, by simp, rfl⟩

lemma coordinateCover {width k : Nat}
    {target goal a b z : BitVec width} {anchor : Fin width}
    {state : Nat × Nat × Nat} {ws r front : List (BitVec width)}
    (hn : ws.Nodup) (rep : Rep target anchor (k+1) state ws)
    (hpair : (a,b,r) ∈ SearchKernel.pairs ws)
    (hfront : front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width))))
    (hz : z ∈ basicOps a b) (fresh : z ∉ ws.toFinset)
    (tail : live basicOps goal k (z :: (front ++ r)).toFinset) :
    ∃ child ∈ coordinateChildren state,
      ∃ ys, Rep target anchor k child ys ∧ ys.Perm (z :: (front ++ r)) := by
  obtain ⟨m, P, N⟩ := state
  obtain ⟨i, j, keep, gate, hij, hj, ys, hrep, hp⟩ :=
    transitionCover hn rep hpair hfront hz fresh tail
  exact ⟨childState m P N i j keep gate, childState_mem keep gate hij hj, ys, hrep, hp⟩

lemma coordinate_liveState_step {width : Nat} {target goal : BitVec width}
    {anchor : Fin width} {done : (Nat × Nat × Nat) → Bool}
    (finish : ∀ k s, Rep target anchor k s [goal] → done s = true)
    (k : Nat) (s : Nat × Nat × Nat)
    (run : PNQuotient.liveState (Rep target anchor) goal (k+1) s) :
    done s = true ∨ ∃ t ∈ coordinateChildren s,
      PNQuotient.liveState (Rep target anchor) goal k t := by
  apply PNQuotient.liveState_step (children := fun _ => coordinateChildren) finish ?_ run
  intro k s ws a b z r front hn hrep hpair hfront hz fresh tail
  exact coordinateCover hn hrep hpair hfront hz fresh tail

lemma coordinate_search_complete {width : Nat} {target goal : BitVec width}
    {anchor : Fin width} {done : (Nat × Nat × Nat) → Bool}
    {admissible : Nat → (Nat × Nat × Nat) → Bool}
    (finish : ∀ k s, Rep target anchor k s [goal] → done s = true)
    (allowed : ∀ k s, PNQuotient.liveState (Rep target anchor) goal (k+1) s →
      admissible (k+1) s = true)
    {k : Nat} {s : Nat × Nat × Nat}
    (run : PNQuotient.liveState (Rep target anchor) goal k s) :
    PNQuotient.search done admissible (fun _ => coordinateChildren) k s = true :=
  PNQuotient.search_complete finish (coordinate_liveState_step finish) allowed run

end PNConcrete

namespace PNConcrete

lemma rowCode_singleton {width : Nat} (w : BitVec width) (r : Fin width) :
    PNFrontier.rowCode [w] r = if w[r.val] then 1 else 0 := by
  change (BitVec.ofBoolListLE [w[r.val]]).toNat = if w[r.val] then 1 else 0
  cases w[r.val] <;> rfl

lemma mask_empty_of_rows {ρ : Type} {S mask : Nat} {code : ρ → Nat} {label : ρ → Prop}
    (represented : ∀ x, S.testBit x = true ↔ ∃ r, label r ∧ code r = x)
    (excluded : ∀ r, label r → mask.testBit (code r) = false) : S &&& mask = 0 := by
  apply Nat.eq_of_testBit_eq
  intro x
  rw [Nat.testBit_and, show (0 : Nat).testBit x = false by simp]
  cases hx : S.testBit x with
  | false => rfl
  | true =>
    change mask.testBit x = false
    obtain ⟨r, hr, he⟩ := (represented x).mp hx
    rw [← he]
    exact excluded r hr

def solved (n positive negative : Nat) : Bool :=
  (List.range n).any fun i =>
    ((positive &&& PNMasks.lowMask i == 0) && (negative &&& PNPlanes.highMask i == 0)) ||
      ((positive &&& PNPlanes.highMask i == 0) && (negative &&& PNMasks.lowMask i == 0))

lemma solved_singleton {width k : Nat} {target goal : BitVec width} {anchor : Fin width}
    {state : Nat × Nat × Nat} (goal_eq : goal = target ∨ goal = ~~~target)
    (rep : Rep target anchor k state [goal]) :
    solved state.1 state.2.1 state.2.2 = true := by
  obtain ⟨m, P, N⟩ := state
  obtain ⟨hlen, hroom, hcap, hzero, hexact⟩ := rep
  have hm : m = 1 := by simpa using hlen.symm
  subst m
  unfold solved
  apply List.any_eq_true.mpr
  refine ⟨0, by simp, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  have low1 : (PNMasks.lowMask 0).testBit 1 = false := by
    simpa using PNMasks.lowMask_bits (0 : Fin 10) (1 : Fin 1024)
  have high0 : (PNPlanes.highMask 0).testBit 0 = false := by
    simpa using PNPlanes.highMask_bits (0 : Fin 10) (0 : Fin 1024)
  rcases goal_eq with rfl | rfl
  · left
    constructor
    · apply mask_empty_of_rows (hexact true)
      intro r hr
      rw [rowCode_singleton, hr]
      exact low1
    · apply mask_empty_of_rows (hexact false)
      intro r hr
      rw [rowCode_singleton, hr]
      exact high0
  · right
    constructor
    · apply mask_empty_of_rows (hexact true)
      intro r hr
      rw [rowCode_singleton, BitVec.getElem_not, hr]
      exact high0
    · apply mask_empty_of_rows (hexact false)
      intro r hr
      rw [rowCode_singleton, BitVec.getElem_not, hr]
      exact low1

end PNConcrete

namespace PNGuards

open PNConcrete PNFrontier PNPlanes

lemma rep_active {width k m P N : Nat} {target : BitVec width} {anchor : Fin width}
    {ws : List (BitVec width)} (rep : Rep target anchor k (m,P,N) ws) (r : Fin width) :
    (P ||| N).testBit (rowCode ws r) = true := by
  have represented := rep.2.2.2.2 (target[r.val]) (rowCode ws r)
  have hbit := represented.mpr ⟨r, rfl, rfl⟩
  rw [Nat.testBit_or]
  cases h : target[r.val] with
  | false =>
    have hn : N.testBit (rowCode ws r) = true := by simpa [h] using hbit
    simp [hn]
  | true =>
    have hp : P.testBit (rowCode ws r) = true := by simpa [h] using hbit
    simp [hp]

lemma rowCode_eq_bits {width : Nat} {ws : List (BitVec width)} {p q : Fin width}
    (he : rowCode ws p = rowCode ws q) {w : BitVec width} (hw : w ∈ ws) :
    w[p.val] = w[q.val] := by
  obtain ⟨i, hi, hwi⟩ := List.getElem_of_mem hw
  have hb := congrArg (fun x : Nat => x.testBit i) he
  simpa only [rowCode_testBit ws p i hi, rowCode_testBit ws q i hi, hwi] using hb

lemma rep_disjoint {width k m P N : Nat} {target g : BitVec width} {anchor : Fin width}
    {ws : List (BitVec width)} (rep : Rep target anchor k (m,P,N) ws)
    (run : live basicOps g k ws.toFinset) (hg : g = target ∨ g = ~~~target) :
    P &&& N = 0 := by
  apply Nat.eq_of_testBit_eq
  intro x
  rw [Nat.testBit_and, Nat.zero_testBit]
  cases hp : P.testBit x with
  | false => simp
  | true =>
    cases hn : N.testBit x with
    | false => simp
    | true =>
      obtain ⟨p, htp, hcp⟩ := (rep.2.2.2.2 true x).mp hp
      obtain ⟨q, htq, hcq⟩ := (rep.2.2.2.2 false x).mp hn
      have htarget : target[p.val] ≠ target[q.val] := by simp [htp, htq]
      obtain ⟨w, hw, hdiff⟩ := live_target_separates run hg htarget
      exact False.elim (hdiff (rowCode_eq_bits (hcp.trans hcq.symm) (List.mem_toFinset.mp hw)))

def redundant (n active gate : Nat) : Bool :=
  (List.range n).any fun i =>
    active &&& (gate ^^^ (PNMasks.lowMasks[i]! <<< (1 <<< i))) == 0

lemma redundant_eq_true {m active gate : Nat} :
    redundant m active gate = true ↔
      ∃ i, i < m ∧ active &&& (gate ^^^ (PNMasks.lowMasks[i]! <<< (1 <<< i))) = 0 := by
  simp [redundant, List.any_eq_true]

lemma lookup_bound {α : Type} {ws : List α} {i : Nat} {a : α}
    (ha : ws[i]? = some a) : i < ws.length := by
  by_contra hi
  have hn : ws[i]? = none := List.getElem?_eq_none (by omega)
  rw [hn] at ha
  contradiction

lemma rep_fresh_nonredundant {width k m P N i j : Nat}
    {target a b : BitVec width} {anchor : Fin width} {ws : List (BitVec width)}
    (rep : Rep target anchor k (m,P,N) ws) (op : Fin 4)
    (ha : ws[i]? = some a) (hb : ws[j]? = some b)
    (fresh : ChromGate.word op a b ∉ ws.toFinset) :
    redundant m (P ||| N) (gateMask i j op) = false := by
  apply Bool.eq_false_iff.mpr
  intro hred
  obtain ⟨v, hv, hzero⟩ := redundant_eq_true.mp hred
  have hlen := rep.1
  have hcap := rep.2.2.1
  have hi : i < 10 := by have := lookup_bound ha; omega
  have hj : j < 10 := by have := lookup_bound hb; omega
  have hv10 : v < 10 := by omega
  have hvw : v < ws.length := by omega
  let w := ws[v]'hvw
  have hword : ChromGate.word op a b = w := by
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    let row : Fin width := ⟨r, hr⟩
    have hcode : rowCode ws row < 1024 := lt_of_lt_of_le (rowCode_lt ws row)
      (by simpa only [hlen] using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hcap)
    have heq := congrArg (fun x : Nat => x.testBit (rowCode ws row)) hzero
    have hlookup : PNMasks.lowMasks[v]! <<< (1 <<< v) = highMask v := by
      rw [← PnProjection.lowMask_getBang ⟨v, hv10⟩]
      rfl
    rw [hlookup, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit,
      rep_active rep row, gateMask_bits ⟨i, hi⟩ ⟨j, hj⟩ op ⟨rowCode ws row, hcode⟩,
      highMask_bits ⟨v, hv10⟩ ⟨rowCode ws row, hcode⟩] at heq
    have hgate : ChromGate.eval op ((rowCode ws row).testBit i) ((rowCode ws row).testBit j) =
        (rowCode ws row).testBit v := by
      simpa using heq
    change (ChromGate.word op a b)[row.val] = w[row.val]
    rw [ChromGate.word_get]
    simpa [testBit_rowCode, ha, hb, w, hvw] using hgate
  apply fresh
  rw [hword]
  exact List.mem_toFinset.mpr (List.getElem_mem hvw)

end PNGuards

namespace PNConcrete

open PnTransition

lemma keepSize_le_of_live_length {width k m : Nat} {keep : Fin 4}
    {goal : BitVec width} {ys : List (BitVec width)}
    (hn : ys.Nodup) (hlen : ys.length = m - 1 + keepSize keep)
    (run : live basicOps goal k ys.toFinset) :
    keepSize keep ≤ k + 2 - m := by
  have hc := live_card run
  rw [List.toFinset_card_of_nodup hn, hlen] at hc
  omega

lemma represented_child_keepSize_le {width k m P N i j : Nat} {keep gate : Fin 4}
    {target goal : BitVec width} {anchor : Fin width} {ys : List (BitVec width)}
    (hn : ys.Nodup) (rep : Rep target anchor k (childState m P N i j keep gate) ys)
    (run : live basicOps goal k ys.toFinset) :
    keepSize keep ≤ k + 2 - m :=
  keepSize_le_of_live_length hn rep.1 run

lemma selected_child_nodup {width : Nat} {ws r front : List (BitVec width)}
    {a b z : BitVec width} (hn : ws.Nodup)
    (hpair : (a,b,r) ∈ SearchKernel.pairs ws)
    (hfront : front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width))))
    (fresh : z ∉ ws.toFinset) : (z :: (front ++ r)).Nodup := by
  obtain ⟨i,j,keep,_,_,_,_,hp⟩ := PNSelectors.pairs_keptFront_indices hpair hfront
  have hkept := hn.sublist (PNFrontier.keptFront_sublist i j keep ws)
  refine List.nodup_cons.mpr ⟨?_, hp.nodup_iff.mp hkept⟩
  intro hz
  exact fresh (List.mem_toFinset.mpr (PNFrontier.keptFront_mem (hp.mem_iff.mpr hz)))

lemma transitionCover_sizeBound {width k m P N : Nat}
    {target goal a b z : BitVec width} {anchor : Fin width}
    {ws r front : List (BitVec width)}
    (hn : ws.Nodup) (rep : Rep target anchor (k+1) (m,P,N) ws)
    (hpair : (a,b,r) ∈ SearchKernel.pairs ws)
    (hfront : front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width))))
    (hz : z ∈ basicOps a b) (fresh : z ∉ ws.toFinset)
    (tail : live basicOps goal k (z :: (front ++ r)).toFinset) :
    ∃ i j, ∃ keep gate : Fin 4, i < j ∧ j < m ∧ keepSize keep ≤ k+2-m ∧
      ∃ ys, Rep target anchor k (childState m P N i j keep gate) ys ∧
        ys.Perm (z :: (front ++ r)) := by
  obtain ⟨i,j,keep,gate,hij,hj,ys,hrep,hp⟩ :=
    transitionCover hn rep hpair hfront hz fresh tail
  have hny : ys.Nodup := hp.nodup_iff.mpr (selected_child_nodup hn hpair hfront fresh)
  have heq : ys.toFinset = (z :: (front ++ r)).toFinset := by
    ext w
    simp only [List.mem_toFinset]
    exact hp.mem_iff
  have hrun : live basicOps goal k ys.toFinset := heq.symm ▸ tail
  exact ⟨i,j,keep,gate,hij,hj,represented_child_keepSize_le hny hrep hrun,ys,hrep,hp⟩

def sizeCoordinateChildren (budget : Nat) (state : Nat × Nat × Nat) :
    List (Nat × Nat × Nat) :=
  (List.range state.1).flatMap fun j =>
    (List.range j).flatMap fun i =>
      (List.finRange 4).flatMap fun gate =>
        ((List.finRange 4).filter fun keep => decide (keepSize keep ≤ budget+1-state.1)).map
          fun keep => childState state.1 state.2.1 state.2.2 i j keep gate

lemma childState_mem_size {budget m P N i j : Nat} (keep gate : Fin 4)
    (hij : i < j) (hj : j < m) (hkeep : keepSize keep ≤ budget+1-m) :
    childState m P N i j keep gate ∈ sizeCoordinateChildren budget (m,P,N) := by
  simp only [sizeCoordinateChildren, List.mem_flatMap, List.mem_map,
    List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨j,hj,i,hij,gate,by simp,keep,⟨by simp,hkeep⟩,rfl⟩

lemma sizeCoordinateCover {width k : Nat}
    {target goal a b z : BitVec width} {anchor : Fin width}
    {state : Nat × Nat × Nat} {ws r front : List (BitVec width)}
    (hn : ws.Nodup) (rep : Rep target anchor (k+1) state ws)
    (hpair : (a,b,r) ∈ SearchKernel.pairs ws)
    (hfront : front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width))))
    (hz : z ∈ basicOps a b) (fresh : z ∉ ws.toFinset)
    (tail : live basicOps goal k (z :: (front ++ r)).toFinset) :
    ∃ child ∈ sizeCoordinateChildren (k+1) state,
      ∃ ys, Rep target anchor k child ys ∧ ys.Perm (z :: (front ++ r)) := by
  obtain ⟨m,P,N⟩ := state
  obtain ⟨i,j,keep,gate,hij,hj,hkeep,ys,hrep,hp⟩ :=
    transitionCover_sizeBound hn rep hpair hfront hz fresh tail
  exact ⟨childState m P N i j keep gate,
    childState_mem_size keep gate hij hj (by simpa [Nat.add_assoc] using hkeep),ys,hrep,hp⟩

end PNConcrete


namespace PNGraphEdges

def phaseMask (i : Nat) (b : Bool) : Nat :=
  if b then PNPlanes.highMask i else PNMasks.lowMask i

lemma phaseMask_bits (i : Fin 10) (x : Fin 1024) (b : Bool) :
    (phaseMask i.val b).testBit x.val = (x.val.testBit i.val == b) := by
  cases b <;> simp [phaseMask, PNPlanes.highMask_bits, PNMasks.lowMask_bits]

lemma bit_bound {S x : Nat} (hS : S < 2^1024) (hbit : S.testBit x = true) :
    x < 1024 := by
  by_contra h
  have hp : 2^1024 ≤ 2^x := Nat.pow_le_pow_right (by decide) (by omega)
  have hf := Nat.testBit_lt_two_pow (show S < 2^x by omega)
  simp only [hbit] at hf
  exact Bool.noConfusion hf

def maskWitness (P N : Nat) (flip : Nat → Nat → Nat) (i j : Nat) : Prop :=
  ∃ p q,
    (P &&& flip i N).testBit p = true ∧ (P &&& flip j N).testBit p = true ∧
    (N &&& flip i P).testBit q = true ∧ (N &&& flip j P).testBit q = true ∧
    p.testBit i ≠ q.testBit i ∧ p.testBit j ≠ q.testBit j

lemma quadrant_witness (P N : Nat) (flip : Nat → Nat → Nat) (i j : Fin 10)
    (hP : P < 2^1024) (hN : N < 2^1024) (a b : Bool)
    (hp : ((P &&& flip i.val N) &&& (P &&& flip j.val N)) &&&
      phaseMask i.val a &&& phaseMask j.val b ≠ 0)
    (hq : ((N &&& flip i.val P) &&& (N &&& flip j.val P)) &&&
      phaseMask i.val (!a) &&& phaseMask j.val (!b) ≠ 0) :
    maskWitness P N flip i.val j.val := by
  obtain ⟨p, hp⟩ := Nat.exists_testBit_of_ne_zero hp
  obtain ⟨q, hq⟩ := Nat.exists_testBit_of_ne_zero hq
  simp only [Nat.testBit_and, Bool.and_eq_true] at hp hq
  have pb := bit_bound hP hp.1.1.1.1
  have qb := bit_bound hN hq.1.1.1.1
  have pa := hp.1.2
  have pbb := hp.2
  have qa := hq.1.2
  have qbb := hq.2
  rw [phaseMask_bits i ⟨p,pb⟩ a] at pa
  rw [phaseMask_bits j ⟨p,pb⟩ b] at pbb
  rw [phaseMask_bits i ⟨q,qb⟩ (!a)] at qa
  rw [phaseMask_bits j ⟨q,qb⟩ (!b)] at qbb
  simp only [beq_iff_eq] at pa pbb qa qbb
  refine ⟨p,q,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.testBit_and, Bool.and_eq_true] using hp.1.1.1
  · simpa only [Nat.testBit_and, Bool.and_eq_true] using hp.1.1.2
  · simpa only [Nat.testBit_and, Bool.and_eq_true] using hq.1.1.1
  · simpa only [Nat.testBit_and, Bool.and_eq_true] using hq.1.1.2
  · rw [pa, qa]; cases a <;> decide
  · rw [pbb, qbb]; cases b <;> decide

def vertex (P N : Nat) (flip : Nat → Nat → Nat) (i : Nat) :
    Nat × Nat × Nat × Nat × Nat :=
  (i,PNMasks.lowMask i,PNPlanes.highMask i,P &&& flip i N,N &&& flip i P)

def edgeBoolFast (vi vj : Nat × Nat × Nat × Nat × Nat) : Bool :=
  let (_,li,hi,pi,ni) := vi
  let (_,lj,hj,pj,nj) := vj
  let cp := pi &&& pj
  let cn := ni &&& nj
  (!(cp &&& li &&& lj == 0) && !(cn &&& hi &&& hj == 0)) ||
  (!(cp &&& hi &&& lj == 0) && !(cn &&& li &&& hj == 0)) ||
  (!(cp &&& li &&& hj == 0) && !(cn &&& hi &&& lj == 0)) ||
  (!(cp &&& hi &&& hj == 0) && !(cn &&& li &&& lj == 0))

lemma edgeBoolFast_witness (P N : Nat) (flip : Nat → Nat → Nat) (i j : Fin 10)
    (hP : P < 2^1024) (hN : N < 2^1024)
    (h : edgeBoolFast (vertex P N flip i.val) (vertex P N flip j.val) = true) :
    maskWitness P N flip i.val j.val := by
  simp only [edgeBoolFast, vertex, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', beq_eq_false_iff_ne] at h
  rcases h with ((⟨hp,hq⟩ | ⟨hp,hq⟩) | ⟨hp,hq⟩) | ⟨hp,hq⟩
  · exact quadrant_witness P N flip i j hP hN false false hp hq
  · exact quadrant_witness P N flip i j hP hN true false hp hq
  · exact quadrant_witness P N flip i j hP hN false true hp hq
  · exact quadrant_witness P N flip i j hP hN true true hp hq

end PNGraphEdges


namespace PNConcrete

open PnTransition PNPlanes

lemma transitionCover_guards {width k m P N : Nat}
    {target goal a b z : BitVec width} {anchor : Fin width}
    {ws r front : List (BitVec width)}
    (hg : goal = target ∨ goal = ~~~target)
    (hn : ws.Nodup) (rep : Rep target anchor (k+1) (m,P,N) ws)
    (hpair : (a,b,r) ∈ SearchKernel.pairs ws)
    (hfront : front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width))))
    (hz : z ∈ basicOps a b) (fresh : z ∉ ws.toFinset)
    (tail : live basicOps goal k (z :: (front ++ r)).toFinset) :
    ∃ i j, ∃ keep gate : Fin 4, i < j ∧ j < m ∧
      PNGuards.redundant m (P ||| N) (gateMask i j gate) = false ∧
      keepSize keep ≤ k+2-m ∧
      (childState m P N i j keep gate).2.1 &&&
        (childState m P N i j keep gate).2.2 = 0 ∧
      ∃ ys, Rep target anchor k (childState m P N i j keep gate) ys ∧
        ys.Perm (z :: (front ++ r)) := by
  obtain ⟨i,j,keep,hij,hj,ha,hb,hp⟩ := PNSelectors.pairs_keptFront_indices hpair hfront
  obtain ⟨gate,rfl⟩ := ChromGate.of_basicOps hz
  have hperm : (childFront ws i j keep gate a b).Perm
      (ChromGate.word gate a b :: (front ++ r)) := by
    change (PNFrontier.keptFront i j keep ws ++ [ChromGate.word gate a b]).Perm _
    exact List.perm_append_comm.trans (hp.cons _)
  have heq : (childFront ws i j keep gate a b).toFinset =
      (ChromGate.word gate a b :: (front ++ r)).toFinset := by
    ext w
    simp only [List.mem_toFinset]
    exact hperm.mem_iff
  have htail : live basicOps goal k (childFront ws i j keep gate a b).toFinset :=
    heq.symm ▸ tail
  have hamem : a ∈ ws := (PNSelectors.perm_cons_eraseIdx ha).mem_iff.mpr (by simp)
  have hbmem : b ∈ ws := (PNSelectors.perm_cons_eraseIdx hb).mem_iff.mpr (by simp)
  have hjm : j < m := by have hlen := rep.1; omega
  have hrep := rep_transition keep gate hn rep hij hjm ha hb hamem hbmem fresh htail
  have hkeep := represented_child_keepSize_le (childFront_nodup hn fresh) hrep htail
  have hdisjoint := PNGuards.rep_disjoint hrep htail hg
  exact ⟨i,j,keep,gate,hij,hjm,PNGuards.rep_fresh_nonredundant rep gate ha hb fresh,
    hkeep,hdisjoint,childFront ws i j keep gate a b,hrep,hperm⟩

def filteredChildren (budget : Nat) (state : Nat × Nat × Nat) : List (Nat × Nat × Nat) :=
  (List.range state.1).flatMap fun j =>
    (List.range j).flatMap fun i =>
      (List.finRange 4).flatMap fun gate =>
        if PNGuards.redundant state.1 (state.2.1 ||| state.2.2) (gateMask i j gate) then [] else
          (((List.finRange 4).filter fun keep => decide (keepSize keep ≤ budget+1-state.1)).map
            fun keep => childState state.1 state.2.1 state.2.2 i j keep gate).filter
              fun child => child.2.1 &&& child.2.2 == 0

lemma childState_mem_filtered {budget m P N i j : Nat} (keep gate : Fin 4)
    (hij : i < j) (hj : j < m)
    (hred : PNGuards.redundant m (P ||| N) (gateMask i j gate) = false)
    (hkeep : keepSize keep ≤ budget+1-m)
    (hdisjoint : (childState m P N i j keep gate).2.1 &&&
      (childState m P N i j keep gate).2.2 = 0) :
    childState m P N i j keep gate ∈ filteredChildren budget (m,P,N) := by
  apply List.mem_flatMap.mpr
  refine ⟨j, by simp [hj], List.mem_flatMap.mpr ?_⟩
  refine ⟨i, by simp [hij], List.mem_flatMap.mpr ?_⟩
  refine ⟨gate, by simp, ?_⟩
  simp only [hred, Bool.false_eq_true, ite_false, List.mem_filter, List.mem_map,
    decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨keep,⟨by simp,hkeep⟩,rfl⟩,hdisjoint⟩

lemma filteredCoordinateCover {width k : Nat}
    {target goal a b z : BitVec width} {anchor : Fin width}
    {state : Nat × Nat × Nat} {ws r front : List (BitVec width)}
    (hg : goal = target ∨ goal = ~~~target)
    (hn : ws.Nodup) (rep : Rep target anchor (k+1) state ws)
    (hpair : (a,b,r) ∈ SearchKernel.pairs ws)
    (hfront : front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width))))
    (hz : z ∈ basicOps a b) (fresh : z ∉ ws.toFinset)
    (tail : live basicOps goal k (z :: (front ++ r)).toFinset) :
    ∃ child ∈ filteredChildren (k+1) state,
      ∃ ys, Rep target anchor k child ys ∧ ys.Perm (z :: (front ++ r)) := by
  obtain ⟨m,P,N⟩ := state
  obtain ⟨i,j,keep,gate,hij,hj,hred,hkeep,hdisjoint,ys,hrep,hp⟩ :=
    transitionCover_guards hg hn rep hpair hfront hz fresh tail
  exact ⟨childState m P N i j keep gate,
    childState_mem_filtered keep gate hij hj hred
      (by simpa [Nat.add_assoc] using hkeep) hdisjoint,ys,hrep,hp⟩

lemma filtered_liveState_step {width : Nat} {target goal : BitVec width}
    {anchor : Fin width} (hg : goal = target ∨ goal = ~~~target)
    (k : Nat) (s : Nat × Nat × Nat)
    (run : PNQuotient.liveState (Rep target anchor) goal (k+1) s) :
    solved s.1 s.2.1 s.2.2 = true ∨ ∃ t ∈ filteredChildren (k+1) s,
      PNQuotient.liveState (Rep target anchor) goal k t := by
  apply PNQuotient.liveState_step (children := filteredChildren)
    (fun _ _ hrep => solved_singleton hg hrep) ?_ run
  intro k s ws a b z r front hn hrep hpair hfront hz fresh tail
  exact filteredCoordinateCover hg hn hrep hpair hfront hz fresh tail

lemma filtered_search_complete {width : Nat} {target goal : BitVec width}
    {anchor : Fin width} {admissible : Nat → (Nat × Nat × Nat) → Bool}
    (hg : goal = target ∨ goal = ~~~target)
    (allowed : ∀ k s, PNQuotient.liveState (Rep target anchor) goal (k+1) s →
      admissible (k+1) s = true)
    {k : Nat} {s : Nat × Nat × Nat}
    (run : PNQuotient.liveState (Rep target anchor) goal k s) :
    PNQuotient.search (fun state => solved state.1 state.2.1 state.2.2)
      admissible filteredChildren k s = true :=
  PNQuotient.search_complete (fun _ _ hrep => solved_singleton hg hrep)
    (filtered_liveState_step hg) allowed run

end PNConcrete


namespace NatFlip

lemma xor_pow_of_testBit_false {r i : Nat} (hr : r.testBit i = false) :
    r ^^^ 2 ^ i = r + 2 ^ i := by
  have hpow : 0 < 2 ^ i := Nat.two_pow_pos i
  have hbit : (r / 2 ^ i).testBit 0 = false := by
    simpa only [Nat.testBit_div_two_pow, Nat.zero_add] using hr
  have heven : Even (r / 2 ^ i) :=
    Nat.even_iff.mpr (Nat.mod_two_eq_zero_iff_testBit_zero.mpr hbit)
  have hdiv : (r ^^^ 2 ^ i) / 2 ^ i = r / 2 ^ i + 1 := by
    rw [Nat.xor_div_two_pow, Nat.div_self hpow, Nat.xor_one_of_even heven]
  have hmod : (r ^^^ 2 ^ i) % 2 ^ i = r % 2 ^ i := by
    rw [Nat.xor_mod_two_pow, Nat.mod_self, Nat.xor_zero]
  calc
    r ^^^ 2 ^ i = (r ^^^ 2 ^ i) % 2 ^ i + 2 ^ i * ((r ^^^ 2 ^ i) / 2 ^ i) :=
      (Nat.mod_add_div _ _).symm
    _ = r % 2 ^ i + 2 ^ i * (r / 2 ^ i + 1) := by rw [hmod, hdiv]
    _ = r + 2 ^ i := by
      rw [Nat.mul_add, Nat.mul_one, ← Nat.add_assoc, Nat.mod_add_div]

lemma xor_pow_of_testBit_true {r i : Nat} (hr : r.testBit i = true) :
    r ^^^ 2 ^ i = r - 2 ^ i := by
  have hbit : (r ^^^ 2 ^ i).testBit i = false := by
    simp [Nat.testBit_xor, hr]
  have h := xor_pow_of_testBit_false hbit
  rw [Nat.xor_xor_cancel_right] at h
  omega

lemma testBit_sub_pow {r i : Nat} (h : 2 ^ i ≤ r) :
    (r - 2 ^ i).testBit i = !r.testBit i := by
  have hflip := Nat.testBit_two_pow_add_eq (r - 2 ^ i) i
  rw [Nat.add_sub_of_le h] at hflip
  simpa using (congrArg Bool.not hflip).symm

def flipCoordinate (B mask i : Nat) : Nat :=
  ((B &&& mask) <<< (2 ^ i)) ||| ((B >>> (2 ^ i)) &&& mask)

lemma flipCoordinate_testBit (B mask i N r : Nat)
    (hmask : ∀ t < N, mask.testBit t = !t.testBit i)
    (hr : r < N) :
    (flipCoordinate B mask i).testBit r = B.testBit (r ^^^ 2 ^ i) := by
  simp only [flipCoordinate, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, Nat.testBit_and]
  have hm := hmask r hr
  cases hbit : r.testBit i with
  | false =>
    rw [xor_pow_of_testBit_false hbit]
    by_cases hle : 2 ^ i ≤ r
    · have hs : r - 2 ^ i < N := (Nat.sub_le r _).trans_lt hr
      have hms := hmask (r - 2 ^ i) hs
      have hsub := testBit_sub_pow hle
      simp [hle, hm, hms, hsub, hbit, Nat.add_comm]
    · simp [hle, hm, hbit, Nat.add_comm]
  | true =>
    rw [xor_pow_of_testBit_true hbit]
    have hle : 2 ^ i ≤ r := Nat.ge_two_pow_of_testBit hbit
    have hs : r - 2 ^ i < N := (Nat.sub_le r _).trans_lt hr
    have hms := hmask (r - 2 ^ i) hs
    have hsub := testBit_sub_pow hle
    simp [hle, hm, hms, hsub, hbit]

lemma flipCoordinate_testBit_of_mask (B mask m i r : Nat)
    (hmask : ∀ t, mask.testBit t = decide (t < 2 ^ m ∧ t.testBit i = false))
    (hr : r < 2 ^ m) :
    (flipCoordinate B mask i).testBit r = B.testBit (r ^^^ 2 ^ i) := by
  apply flipCoordinate_testBit B mask i (2 ^ m) r ?_ hr
  intro t ht
  simp [hmask, ht]

end NatFlip

namespace PNFlip

def flipPatternBits (i B : Nat) : Nat :=
  let mask := PNMasks.lowMasks[i]!
  let shift := 1 <<< i
  ((B &&& mask) <<< shift) ||| ((B >>> shift) &&& mask)

lemma flipPatternBits_testBit (i : Fin 10) (r : Fin 1024) (B : Nat) :
    (flipPatternBits i.val B).testBit r.val = B.testBit (r.val ^^^ 2^i.val) := by
  unfold flipPatternBits
  rw [← PnProjection.lowMask_getBang i, Nat.one_shiftLeft]
  apply NatFlip.flipCoordinate_testBit B (PNMasks.lowMask i.val) i.val 1024 r.val ?_ r.isLt
  intro t ht
  exact PNMasks.lowMask_bits i ⟨t,ht⟩

lemma flipPatternBits_testBit_bounded {m i r : Nat} (hm : m ≤ 10) (hi : i < m)
    (hr : r < 2^m) (B : Nat) :
    (flipPatternBits i B).testBit r = B.testBit (r ^^^ 2^i) := by
  have hi10 : i < 10 := by omega
  have hr1024 : r < 1024 := lt_of_lt_of_le hr
    (by exact Nat.pow_le_pow_right (by decide) hm)
  exact flipPatternBits_testBit ⟨i,hi10⟩ ⟨r,hr1024⟩ B

end PNFlip



namespace BitmapCollision

def collisionMask (flip : Nat → Nat) (domainBits P N G : Nat) : Nat :=
  (P &&& flip N) &&& (domainBits ^^^ (G ^^^ flip G))

lemma collisionMask_testBit (flip delta : Nat → Nat) (domainBits P N G p : Nat)
    (hflip : ∀ B, (flip B).testBit p = B.testBit (delta p))
    (hdomain : domainBits.testBit p = true) :
    (collisionMask flip domainBits P N G).testBit p = true ↔
      P.testBit p = true ∧ N.testBit (delta p) = true ∧
        G.testBit p = G.testBit (delta p) := by
  simp only [collisionMask, Nat.testBit_and, Nat.testBit_xor, hflip, hdomain]
  cases P.testBit p <;> cases N.testBit (delta p) <;>
    cases G.testBit p <;> cases G.testBit (delta p) <;> decide

lemma collisionMask_ne_zero_iff (flip delta : Nat → Nat) (domainBits P N G : Nat)
    (hflip : ∀ B q, P.testBit q = true → (flip B).testBit q = B.testBit (delta q))
    (hsupport : ∀ p, P.testBit p = true → domainBits.testBit p = true) :
    collisionMask flip domainBits P N G ≠ 0 ↔
      ∃ p, P.testBit p = true ∧ N.testBit (delta p) = true ∧
        G.testBit p = G.testBit (delta p) := by
  constructor
  · intro hnonzero
    obtain ⟨p, hp⟩ := Nat.exists_testBit_of_ne_zero hnonzero
    have hP : P.testBit p = true := by
      have h := hp
      simp only [collisionMask, Nat.testBit_and, Bool.and_eq_true] at h
      exact h.1.1
    exact ⟨p, (collisionMask_testBit flip delta domainBits P N G p
      (fun B => hflip B p hP) (hsupport p hP)).mp hp⟩
  · rintro ⟨p, hp, hn, hg⟩ hzero
    have h := (collisionMask_testBit flip delta domainBits P N G p
      (fun B => hflip B p hp) (hsupport p hp)).mpr ⟨hp, hn, hg⟩
    simp only [hzero, Nat.zero_testBit, Bool.false_eq_true] at h

lemma selfMask_ne_zero_iff (flip delta : Nat → Nat) (P N G : Nat)
    (hflip : ∀ B q, P.testBit q = true → (flip B).testBit q = B.testBit (delta q)) :
    collisionMask flip P P N G ≠ 0 ↔
      ∃ p, P.testBit p = true ∧ N.testBit (delta p) = true ∧
        G.testBit p = G.testBit (delta p) :=
  collisionMask_ne_zero_iff flip delta P P N G hflip (fun _ hp => hp)

lemma projected_overlap_of_collision
    (flip delta f : Nat → Nat) (domainBits P N G projectedP projectedN : Nat)
    (hflip : ∀ B q, P.testBit q = true → (flip B).testBit q = B.testBit (delta q))
    (hsupport : ∀ p, P.testBit p = true → domainBits.testBit p = true)
    (himageP : ∀ q, projectedP.testBit q = true ↔
      ∃ p, P.testBit p = true ∧ f p = q)
    (himageN : ∀ q, projectedN.testBit q = true ↔
      ∃ p, N.testBit p = true ∧ f p = q)
    (hmap : ∀ p, P.testBit p = true → N.testBit (delta p) = true →
      G.testBit p = G.testBit (delta p) → f p = f (delta p))
    (hnonzero : collisionMask flip domainBits P N G ≠ 0) :
    projectedP &&& projectedN ≠ 0 := by
  obtain ⟨p, hp, hn, hg⟩ :=
    (collisionMask_ne_zero_iff flip delta domainBits P N G hflip hsupport).mp hnonzero
  have hP : projectedP.testBit (f p) = true :=
    (himageP (f p)).mpr ⟨p, hp, rfl⟩
  have hN : projectedN.testBit (f p) = true :=
    (himageN (f p)).mpr ⟨delta p, hn, (hmap p hp hn hg).symm⟩
  intro hzero
  have hbit : (projectedP &&& projectedN).testBit (f p) = true := by
    simp only [Nat.testBit_and, hP, hN, Bool.and_self]
  simp only [hzero, Nat.zero_testBit, Bool.false_eq_true] at hbit

lemma projected_overlap_of_selfMask
    (flip delta f : Nat → Nat) (P N G projectedP projectedN : Nat)
    (hflip : ∀ B q, P.testBit q = true → (flip B).testBit q = B.testBit (delta q))
    (himageP : ∀ q, projectedP.testBit q = true ↔
      ∃ p, P.testBit p = true ∧ f p = q)
    (himageN : ∀ q, projectedN.testBit q = true ↔
      ∃ p, N.testBit p = true ∧ f p = q)
    (hmap : ∀ p, P.testBit p = true → N.testBit (delta p) = true →
      G.testBit p = G.testBit (delta p) → f p = f (delta p))
    (hnonzero : collisionMask flip P P N G ≠ 0) :
    projectedP &&& projectedN ≠ 0 :=
  projected_overlap_of_collision flip delta f P P N G projectedP projectedN
    hflip (fun _ hp => hp) himageP himageN hmap hnonzero

end BitmapCollision

namespace PNDropFlip

open PnProjection PnTransition

lemma delBit_xor_self (i x : Nat) : delBit i (x ^^^ 2^i) = delBit i x := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_delBit, Nat.testBit_xor, testBit_delBit, Nat.testBit_two_pow]
  have hne : i ≠ (if k < i then k else k+1) := by
    split_ifs <;> omega
  simp [hne]

lemma delBit_xor_below {i j : Nat} (hij : i < j) (x : Nat) :
    delBit j (x ^^^ 2^i) = (delBit j x) ^^^ 2^i := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [testBit_delBit, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hk : k < j
  · simp [hk]
  · have hne : i ≠ k := by omega
    have hne' : i ≠ k+1 := by omega
    simp [hk, hne, hne']

lemma dropPattern_xor_left {i j : Nat} (hij : i < j) (keep : Fin 4)
    (hdrop : keep.val &&& 1 = 0) (x : Nat) :
    dropPattern i j keep (x ^^^ 2^i) = dropPattern i j keep x := by
  by_cases hk : keep.val &&& 2 = 0
  · simp [dropPattern, hdrop, hk, delBit_xor_below hij, delBit_xor_self]
  · simp [dropPattern, hdrop, hk, delBit_xor_self]

lemma dropPattern_xor_right (i j : Nat) (keep : Fin 4)
    (hdrop : keep.val &&& 2 = 0) (x : Nat) :
    dropPattern i j keep (x ^^^ 2^j) = dropPattern i j keep x := by
  simp [dropPattern, hdrop, delBit_xor_self]

lemma dropPattern_xor_both {i j : Nat} (hij : i < j) (x : Nat) :
    dropPattern i j (0 : Fin 4) ((x ^^^ 2^i) ^^^ 2^j) = dropPattern i j 0 x := by
  rw [dropPattern_xor_right i j 0 (by decide), dropPattern_xor_left hij 0 (by decide)]

lemma dropPattern_xor_both_mask {i j : Nat} (hij : i < j) (x : Nat) :
    dropPattern i j (0 : Fin 4) (x ^^^ (2^i ^^^ 2^j)) = dropPattern i j 0 x := by
  rw [← Nat.xor_assoc]
  exact dropPattern_xor_both hij x

end PNDropFlip

namespace PNFlipRows

lemma xor_power_bound {m i r : Nat} (hi : i < m) (hr : r < 2^m) :
    r ^^^ 2^i < 2^m :=
  Nat.xor_lt_two_pow hr (Nat.pow_lt_pow_right (by decide) hi)

lemma flipPatternBits_twice_testBit {m i j r : Nat} (hm : m ≤ 10)
    (hi : i < m) (hj : j < m) (hr : r < 2^m) (B : Nat) :
    (PNFlip.flipPatternBits i (PNFlip.flipPatternBits j B)).testBit r =
      B.testBit ((r ^^^ 2^i) ^^^ 2^j) := by
  rw [PNFlip.flipPatternBits_testBit_bounded hm hi hr,
    PNFlip.flipPatternBits_testBit_bounded hm hj (xor_power_bound hi hr)]

lemma gateMask_testBit_bounded {m i j r : Nat} (hm : m ≤ 10)
    (hi : i < m) (hj : j < m) (hr : r < 2^m) (op : Fin 4) :
    (PNPlanes.gateMask i j op).testBit r =
      ChromGate.eval op (r.testBit i) (r.testBit j) := by
  have hr1024 : r < 1024 := lt_of_lt_of_le hr
    (by exact Nat.pow_le_pow_right (by decide) hm)
  exact PNPlanes.gateMask_bits ⟨i, by omega⟩ ⟨j, by omega⟩ op ⟨r, hr1024⟩

lemma gateMask_xor_left {m i j r : Nat} (hm : m ≤ 10)
    (hij : i < j) (hj : j < m) (hr : r < 2^m) (op : Fin 4) :
    (PNPlanes.gateMask i j op).testBit (r ^^^ 2^i) =
      ChromGate.eval op (!(r.testBit i)) (r.testBit j) := by
  rw [gateMask_testBit_bounded hm (by omega) hj (xor_power_bound (by omega) hr)]
  simp [Nat.testBit_xor, Nat.ne_of_lt hij]

lemma gateMask_xor_right {m i j r : Nat} (hm : m ≤ 10)
    (hij : i < j) (hj : j < m) (hr : r < 2^m) (op : Fin 4) :
    (PNPlanes.gateMask i j op).testBit (r ^^^ 2^j) =
      ChromGate.eval op (r.testBit i) (!(r.testBit j)) := by
  rw [gateMask_testBit_bounded hm (by omega) hj (xor_power_bound hj hr)]
  simp [Nat.testBit_xor, Nat.ne_of_gt hij]

lemma gateMask_xor_both {m i j r : Nat} (hm : m ≤ 10)
    (hij : i < j) (hj : j < m) (hr : r < 2^m) (op : Fin 4) :
    (PNPlanes.gateMask i j op).testBit ((r ^^^ 2^i) ^^^ 2^j) =
      ChromGate.eval op (!(r.testBit i)) (!(r.testBit j)) := by
  rw [gateMask_testBit_bounded hm (by omega) hj
    (xor_power_bound hj (xor_power_bound (by omega) hr))]
  simp [Nat.testBit_xor, Nat.ne_of_lt hij, Nat.ne_of_gt hij]

lemma gateMask_xor_both_mask {m i j r : Nat} (hm : m ≤ 10)
    (hij : i < j) (hj : j < m) (hr : r < 2^m) (op : Fin 4) :
    (PNPlanes.gateMask i j op).testBit (r ^^^ (2^i ^^^ 2^j)) =
      ChromGate.eval op (!(r.testBit i)) (!(r.testBit j)) := by
  rw [← Nat.xor_assoc]
  exact gateMask_xor_both hm hij hj hr op

end PNFlipRows

namespace PNGateSpecs

open PNPlanes

def gateSpec (i j : Nat) (d : Fin 4) : Nat × Nat × Nat × Nat :=
  let li := PNMasks.lowMask i
  let lj := PNMasks.lowMask j
  let hi := highMask i
  let hj := highMask j
  let different := hi ^^^ hj
  let same := allPatterns ^^^ different
  match d.val with
  | 0 => (hi &&& hj, lj, li, different)
  | 1 => (hi ||| hj, hj, hi, different)
  | 2 => (hi &&& lj, hj, li, same)
  | _ => (hj &&& li, lj, hi, same)

lemma gateSpec_gate (i j : Nat) (d : Fin 4) :
    (gateSpec i j d).1 = gateMask i j d := by
  fin_cases d <;> rfl

lemma allPatterns_bits (x : Fin 1024) : allPatterns.testBit x.val = true := by
  simp [allPatterns, x.isLt]

lemma gateSpec_samei_bits (i j : Fin 10) (x : Fin 1024) (d : Fin 4) :
    (gateSpec i.val j.val d).2.1.testBit x.val =
      decide (ChromGate.eval d (x.val.testBit i.val) (x.val.testBit j.val) =
        ChromGate.eval d (!(x.val.testBit i.val)) (x.val.testBit j.val)) := by
  fin_cases d <;>
    simp only [gateSpec, ChromGate.eval, highMask_bits, PNMasks.lowMask_bits] <;>
    cases x.val.testBit i.val <;> cases x.val.testBit j.val <;> rfl

lemma gateSpec_samej_bits (i j : Fin 10) (x : Fin 1024) (d : Fin 4) :
    (gateSpec i.val j.val d).2.2.1.testBit x.val =
      decide (ChromGate.eval d (x.val.testBit i.val) (x.val.testBit j.val) =
        ChromGate.eval d (x.val.testBit i.val) (!(x.val.testBit j.val))) := by
  fin_cases d <;>
    simp only [gateSpec, ChromGate.eval, highMask_bits, PNMasks.lowMask_bits] <;>
    cases x.val.testBit i.val <;> cases x.val.testBit j.val <;> rfl

lemma gateSpec_sameij_bits (i j : Fin 10) (x : Fin 1024) (d : Fin 4) :
    (gateSpec i.val j.val d).2.2.2.testBit x.val =
      decide (ChromGate.eval d (x.val.testBit i.val) (x.val.testBit j.val) =
        ChromGate.eval d (!(x.val.testBit i.val)) (!(x.val.testBit j.val))) := by
  fin_cases d <;>
    simp only [gateSpec, ChromGate.eval, Nat.testBit_xor, highMask_bits, allPatterns_bits] <;>
    cases x.val.testBit i.val <;> cases x.val.testBit j.val <;> rfl

end PNGateSpecs

namespace PNKeepLogic

def validKeep (keep ci cj cij samei samej sameij : Nat) : Bool :=
  if keep == 3 then true
  else if keep == 1 then cj &&& samej == 0
  else if keep == 2 then ci &&& samei == 0
  else ci &&& samei == 0 && cj &&& samej == 0 && cij &&& sameij == 0

lemma validKeep_of_checks (keep : Fin 4) (ci cj cij samei samej sameij : Nat)
    (hleft : keep.val &&& 1 = 0 → ci &&& samei = 0)
    (hright : keep.val &&& 2 = 0 → cj &&& samej = 0)
    (hboth : keep.val = 0 → cij &&& sameij = 0) :
    validKeep keep.val ci cj cij samei samej sameij = true := by
  fin_cases keep <;> simp_all [validKeep]

end PNKeepLogic

namespace PNPreCollision

open PnTransition

lemma transition_overlap_of_collision {m i j P N : Nat}
    (hij : i < j) (hj : j < m) (hm : m ≤ 10)
    (hP : P < 2^(2^m)) (hN : N < 2^(2^m)) (keep : Fin 4) (G domainBits : Nat)
    (flip delta : Nat → Nat)
    (hflip : ∀ B p, P.testBit p = true → (flip B).testBit p = B.testBit (delta p))
    (hsupport : ∀ p, P.testBit p = true → domainBits.testBit p = true)
    (hdrop : ∀ p, P.testBit p = true → N.testBit (delta p) = true →
      G.testBit p = G.testBit (delta p) →
      dropPattern i j keep p = dropPattern i j keep (delta p))
    (hbad : BitmapCollision.collisionMask flip domainBits P N G ≠ 0) :
    transitionSet m i j keep G P &&& transitionSet m i j keep G N ≠ 0 := by
  apply BitmapCollision.projected_overlap_of_collision flip delta
    (fun p => dropPattern i j keep p + (if G.testBit p then 2^(m-2+keepSize keep) else 0))
    domainBits P N G _ _ hflip hsupport ?_ ?_ ?_ hbad
  · intro y
    rw [transitionSet_image hij hj hm hP]
    apply exists_congr
    intro p
    exact and_congr_right (fun _ => eq_comm)
  · intro y
    rw [transitionSet_image hij hj hm hN]
    apply exists_congr
    intro p
    exact and_congr_right (fun _ => eq_comm)
  · intro p hp hn hg
    rw [hdrop p hp hn hg, hg]

lemma transition_overlap_of_selfMask {m i j P N : Nat}
    (hij : i < j) (hj : j < m) (hm : m ≤ 10)
    (hP : P < 2^(2^m)) (hN : N < 2^(2^m)) (keep : Fin 4) (G : Nat)
    (flip delta : Nat → Nat)
    (hflip : ∀ B p, P.testBit p = true → (flip B).testBit p = B.testBit (delta p))
    (hdrop : ∀ p, dropPattern i j keep p = dropPattern i j keep (delta p))
    (hbad : BitmapCollision.collisionMask flip P P N G ≠ 0) :
    transitionSet m i j keep G P &&& transitionSet m i j keep G N ≠ 0 :=
  transition_overlap_of_collision hij hj hm hP hN keep G P flip delta hflip
    (fun _ hp => hp) (fun p _ _ _ => hdrop p) hbad

lemma sameMask_zero_of_disjoint {m i j P N : Nat}
    (hij : i < j) (hj : j < m) (hm : m ≤ 10)
    (hP : P < 2^(2^m)) (hN : N < 2^(2^m)) (keep : Fin 4) (G sameMask : Nat)
    (flip delta : Nat → Nat)
    (hflip : ∀ B p, P.testBit p = true → (flip B).testBit p = B.testBit (delta p))
    (hsame : ∀ p, P.testBit p = true → sameMask.testBit p = true →
      G.testBit p = G.testBit (delta p))
    (hdrop : ∀ p, dropPattern i j keep p = dropPattern i j keep (delta p))
    (hdisjoint : transitionSet m i j keep G P &&& transitionSet m i j keep G N = 0) :
    (P &&& flip N) &&& sameMask = 0 := by
  by_contra hbad
  obtain ⟨p, hp⟩ := Nat.exists_testBit_of_ne_zero hbad
  simp only [Nat.testBit_and, Bool.and_eq_true] at hp
  have hNbit : N.testBit (delta p) = true := by
    rw [← hflip N p hp.1.1]
    exact hp.1.2
  have hcollision : BitmapCollision.collisionMask flip P P N G ≠ 0 :=
    (BitmapCollision.selfMask_ne_zero_iff flip delta P N G hflip).mpr
      ⟨p, hp.1.1, hNbit, hsame p hp.1.1 hp.2⟩
  exact transition_overlap_of_selfMask hij hj hm hP hN keep G flip delta hflip hdrop
    hcollision hdisjoint

end PNPreCollision

namespace PNPrecheck

open PnTransition PNPlanes PNFlip PNFlipRows PNGateSpecs

def precheck (i j : Nat) (keep op : Fin 4) (P N : Nat) : Bool :=
  let spec := gateSpec i j op
  let fi := flipPatternBits i N
  let fj := flipPatternBits j N
  PNKeepLogic.validKeep keep.val (P &&& fi) (P &&& fj)
    (P &&& flipPatternBits i fj) spec.2.1 spec.2.2.1 spec.2.2.2

lemma validKeep_of_disjoint {m i j P N : Nat}
    (hij : i < j) (hj : j < m) (hm : m ≤ 10)
    (hP : P < 2^(2^m)) (hN : N < 2^(2^m)) (keep op : Fin 4)
    (hdisjoint : transitionSet m i j keep (gateMask i j op) P &&&
      transitionSet m i j keep (gateMask i j op) N = 0) :
    precheck i j keep op P N = true := by
  have hi : i < m := by omega
  have hi10 : i < 10 := by omega
  have hj10 : j < 10 := by omega
  have pbound (p : Nat) (hp : P.testBit p = true) : p < 2^m :=
    PnProjection.bitIndex_lt hP hp
  have p1024 (p : Nat) (hp : P.testBit p = true) : p < 1024 :=
    lt_of_lt_of_le (pbound p hp) (by exact Nat.pow_le_pow_right (by decide) hm)
  unfold precheck
  apply PNKeepLogic.validKeep_of_checks
  · intro hdrop
    apply PNPreCollision.sameMask_zero_of_disjoint hij hj hm hP hN keep
      (gateMask i j op) (gateSpec i j op).2.1 (flipPatternBits i)
      (fun p => p ^^^ 2^i) ?_ ?_ ?_ hdisjoint
    · intro B p hp
      exact flipPatternBits_testBit_bounded hm hi (pbound p hp) B
    · intro p hp hs
      rw [gateSpec_samei_bits ⟨i,hi10⟩ ⟨j,hj10⟩ ⟨p,p1024 p hp⟩ op] at hs
      rw [gateMask_testBit_bounded hm hi hj (pbound p hp),
        gateMask_xor_left hm hij hj (pbound p hp)]
      exact of_decide_eq_true hs
    · intro p
      exact (PNDropFlip.dropPattern_xor_left hij keep hdrop p).symm
  · intro hdrop
    apply PNPreCollision.sameMask_zero_of_disjoint hij hj hm hP hN keep
      (gateMask i j op) (gateSpec i j op).2.2.1 (flipPatternBits j)
      (fun p => p ^^^ 2^j) ?_ ?_ ?_ hdisjoint
    · intro B p hp
      exact flipPatternBits_testBit_bounded hm hj (pbound p hp) B
    · intro p hp hs
      rw [gateSpec_samej_bits ⟨i,hi10⟩ ⟨j,hj10⟩ ⟨p,p1024 p hp⟩ op] at hs
      rw [gateMask_testBit_bounded hm hi hj (pbound p hp),
        gateMask_xor_right hm hij hj (pbound p hp)]
      exact of_decide_eq_true hs
    · intro p
      exact (PNDropFlip.dropPattern_xor_right i j keep hdrop p).symm
  · intro hzero
    have he : keep = (0 : Fin 4) := Fin.ext hzero
    subst keep
    apply PNPreCollision.sameMask_zero_of_disjoint hij hj hm hP hN 0
      (gateMask i j op) (gateSpec i j op).2.2.2
      (fun B => flipPatternBits i (flipPatternBits j B))
      (fun p => (p ^^^ 2^i) ^^^ 2^j) ?_ ?_ ?_ hdisjoint
    · intro B p hp
      exact flipPatternBits_twice_testBit hm hi hj (pbound p hp) B
    · intro p hp hs
      rw [gateSpec_sameij_bits ⟨i,hi10⟩ ⟨j,hj10⟩ ⟨p,p1024 p hp⟩ op] at hs
      rw [gateMask_testBit_bounded hm hi hj (pbound p hp),
        gateMask_xor_both hm hij hj (pbound p hp)]
      exact of_decide_eq_true hs
    · intro p
      exact (PNDropFlip.dropPattern_xor_both hij p).symm

end PNPrecheck

namespace PNConcrete

open PnTransition PNPlanes PNFlip PNKeepLogic PNGateSpecs

def keepCheck (i j P N : Nat) (keep gate : Fin 4) : Bool :=
  let spec := gateSpec i j gate
  validKeep keep.val (P &&& flipPatternBits i N) (P &&& flipPatternBits j N)
    (P &&& flipPatternBits i (flipPatternBits j N)) spec.2.1 spec.2.2.1 spec.2.2.2

def precheckedChildren (budget : Nat) (state : Nat × Nat × Nat) : List (Nat × Nat × Nat) :=
  (List.range state.1).flatMap fun j =>
    (List.range j).flatMap fun i =>
      let fi := flipPatternBits i state.2.2
      let fj := flipPatternBits j state.2.2
      let ci := state.2.1 &&& fi
      let cj := state.2.1 &&& fj
      let cij := state.2.1 &&& flipPatternBits i fj
      (List.finRange 4).flatMap fun gate =>
        let spec := gateSpec i j gate
        if PNGuards.redundant state.1 (state.2.1 ||| state.2.2) (gateMask i j gate) then [] else
          (((List.finRange 4).filter fun keep =>
            decide (keepSize keep ≤ budget+1-state.1) &&
              validKeep keep.val ci cj cij spec.2.1 spec.2.2.1 spec.2.2.2).map
            fun keep => childState state.1 state.2.1 state.2.2 i j keep gate).filter
              fun child => child.2.1 &&& child.2.2 == 0

lemma childState_mem_prechecked {budget m P N i j : Nat} (keep gate : Fin 4)
    (hij : i < j) (hj : j < m)
    (hred : PNGuards.redundant m (P ||| N) (gateMask i j gate) = false)
    (hkeep : keepSize keep ≤ budget+1-m)
    (hpre : keepCheck i j P N keep gate = true)
    (hdisjoint : (childState m P N i j keep gate).2.1 &&&
      (childState m P N i j keep gate).2.2 = 0) :
    childState m P N i j keep gate ∈ precheckedChildren budget (m,P,N) := by
  apply List.mem_flatMap.mpr
  refine ⟨j, by simp [hj], List.mem_flatMap.mpr ?_⟩
  refine ⟨i, by simp [hij], List.mem_flatMap.mpr ?_⟩
  refine ⟨gate, by simp, ?_⟩
  simp only [hred, Bool.false_eq_true, ite_false, List.mem_filter, List.mem_map,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨keep,⟨by simp,⟨hkeep,hpre⟩⟩,rfl⟩,hdisjoint⟩

lemma rep_bitmap_bound {width k m P N : Nat} {target : BitVec width} {anchor : Fin width}
    {ws : List (BitVec width)} (rep : Rep target anchor k (m,P,N) ws) (value : Bool) :
    (if value then P else N) < 2^(2^m) := by
  apply bitmap_bound (code := PNFrontier.rowCode ws) (label := fun r => target[r.val] = value)
  · intro r
    simpa only [rep.1] using PNFrontier.rowCode_lt ws r
  · exact rep.2.2.2.2 value

lemma precheckedCoordinateCover {width k : Nat}
    {target goal a b z : BitVec width} {anchor : Fin width}
    {state : Nat × Nat × Nat} {ws r front : List (BitVec width)}
    (hg : goal = target ∨ goal = ~~~target)
    (hn : ws.Nodup) (rep : Rep target anchor (k+1) state ws)
    (hpair : (a,b,r) ∈ SearchKernel.pairs ws)
    (hfront : front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width))))
    (hz : z ∈ basicOps a b) (fresh : z ∉ ws.toFinset)
    (tail : live basicOps goal k (z :: (front ++ r)).toFinset) :
    ∃ child ∈ precheckedChildren (k+1) state,
      ∃ ys, Rep target anchor k child ys ∧ ys.Perm (z :: (front ++ r)) := by
  obtain ⟨m,P,N⟩ := state
  obtain ⟨i,j,keep,gate,hij,hj,hred,hkeep,hdisjoint,ys,hrep,hp⟩ :=
    transitionCover_guards hg hn rep hpair hfront hz fresh tail
  have hpre := PNPrecheck.validKeep_of_disjoint hij hj rep.2.2.1
    (rep_bitmap_bound rep true) (rep_bitmap_bound rep false) keep gate hdisjoint
  exact ⟨childState m P N i j keep gate,
    childState_mem_prechecked keep gate hij hj hred
      (by simpa [Nat.add_assoc] using hkeep) hpre hdisjoint,ys,hrep,hp⟩

lemma prechecked_liveState_step {width : Nat} {target goal : BitVec width}
    {anchor : Fin width} (hg : goal = target ∨ goal = ~~~target)
    (k : Nat) (s : Nat × Nat × Nat)
    (run : PNQuotient.liveState (Rep target anchor) goal (k+1) s) :
    solved s.1 s.2.1 s.2.2 = true ∨ ∃ t ∈ precheckedChildren (k+1) s,
      PNQuotient.liveState (Rep target anchor) goal k t := by
  apply PNQuotient.liveState_step (children := precheckedChildren)
    (fun _ _ hrep => solved_singleton hg hrep) ?_ run
  intro k s ws a b z r front hn hrep hpair hfront hz fresh tail
  exact precheckedCoordinateCover hg hn hrep hpair hfront hz fresh tail

lemma prechecked_search_complete {width : Nat} {target goal : BitVec width}
    {anchor : Fin width} {admissible : Nat → (Nat × Nat × Nat) → Bool}
    (hg : goal = target ∨ goal = ~~~target)
    (allowed : ∀ k s, PNQuotient.liveState (Rep target anchor) goal (k+1) s →
      admissible (k+1) s = true)
    {k : Nat} {s : Nat × Nat × Nat}
    (run : PNQuotient.liveState (Rep target anchor) goal k s) :
    PNQuotient.search (fun state => solved state.1 state.2.1 state.2.2)
      admissible precheckedChildren k s = true :=
  PNQuotient.search_complete (fun _ _ hrep => solved_singleton hg hrep)
    (prechecked_liveState_step hg) allowed run

end PNConcrete

end PEqualNP.Outside.L_meta_10760
