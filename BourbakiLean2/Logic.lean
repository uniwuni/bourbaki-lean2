
variable {p q : Prop}
theorem imp_iff_not_imp_not : (p → q) ↔ (¬ q → ¬ p) := by
  constructor
  · exact fun h h' h'' => h' (h h'')
  · intro h h'
    by_cases h'' : q
    · exact h''
    · exact (h h'' h').elim
attribute [simp] Subtype.eq_iff
