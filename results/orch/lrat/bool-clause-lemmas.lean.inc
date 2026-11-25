theorem sat_and_left (a b z : Bool) (h : z = (a && b)) :
    z = true → (¬ a = true) → False := by
  cases a <;> cases b <;> cases z <;> simp_all

theorem sat_and_right (a b z : Bool) (h : z = (a && b)) :
    z = true → (¬ b = true) → False := by
  cases a <;> cases b <;> cases z <;> simp_all

theorem sat_and_out (a b z : Bool) (h : z = (a && b)) :
    (¬ z = true) → a = true → b = true → False := by
  cases a <;> cases b <;> cases z <;> simp_all

theorem sat_or_left (a b z : Bool) (h : z = (a || b)) :
    (¬ z = true) → a = true → False := by
  cases a <;> cases b <;> cases z <;> simp_all

theorem sat_or_right (a b z : Bool) (h : z = (a || b)) :
    (¬ z = true) → b = true → False := by
  cases a <;> cases b <;> cases z <;> simp_all

theorem sat_or_out (a b z : Bool) (h : z = (a || b)) :
    z = true → (¬ a = true) → (¬ b = true) → False := by
  cases a <;> cases b <;> cases z <;> simp_all

theorem sat_xor_left (a b : Bool) (h : a ≠ b) :
    (¬ a = true) → (¬ b = true) → False := by
  cases a <;> cases b <;> simp_all

theorem sat_xor_right (a b : Bool) (h : a ≠ b) :
    a = true → b = true → False := by
  cases a <;> cases b <;> simp_all

