
variable {p q : Prop}
theorem imp_iff_not_imp_not : (p → q) ↔ (¬ q → ¬ p) := by
  constructor
  · exact fun h h' h'' => h' (h h'')
  · intro h h'
    by_cases h'' : q
    · exact h''
    · exact (h h'' h').elim

universe u v
theorem func_subsingleton_iff_to_empty {α : Type u} {β : Type v} (h : α → Empty) : Subsingleton (α → β) := by
  constructor
  intro a b
  ext c
  rcases h c

attribute [simp] Subtype.eq_iff
