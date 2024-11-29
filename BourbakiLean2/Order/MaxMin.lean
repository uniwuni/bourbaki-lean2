import BourbakiLean2.Order.Monotone
variable {α β : Type*} [PartialOrder α] [PartialOrder β]

@[simp] def Minimal (a : α) := ∀ b, b ≤ a → b = a
@[simp] def Maximal (a : α) := ∀ b, a ≤ b → b = a

theorem minimal_iff_no_lt {a : α} : Minimal a ↔ ∀ b, ¬ b < a := by
  simp only [Minimal, le_iff_lt_or_eq]
  apply forall_congr'
  intro b
  constructor
  · exact fun h h' => ne_of_lt h' (h $ Or.inl h')
  · rintro h (h'|rfl)
    · exact (h h').elim
    · rfl

theorem maximal_iff_no_lt {a : α} : Maximal a ↔ ∀ b, ¬ a < b := by
  simp only [Maximal, le_iff_lt_or_eq]
  apply forall_congr'
  intro b
  constructor
  · exact fun h h' => ne_of_lt h' (h $ Or.inl h').symm
  · rintro h (h'|rfl)
    · exact (h h').elim
    · rfl

theorem maximal_toOp_iff_minimal {a : α} : Maximal (toOp a) ↔ Minimal a := Iff.rfl
theorem minimal_toOp_iff_maximal {a : α} : Minimal (toOp a) ↔ Maximal a := Iff.rfl

theorem preimage_maximal_strictMono {a : α} {f : α → β} (mono : StrictMonotone f) (h : Maximal (f a)) : Maximal a := by
  rw[maximal_iff_no_lt] at *
  intro b h'
  apply h _ $ mono h'

theorem preimage_minimal_strictMono {a : α} {f : α → β} (mono : StrictMonotone f) (h : Minimal (f a)) : Minimal a := by
  rw[minimal_iff_no_lt] at *
  intro b h'
  apply h _ $ mono h'

theorem preimage_maximal_strictAnti {a : α} {f : α → β} (mono : StrictAntitone f) (h : Maximal (f a)) : Minimal a := by
  rw[maximal_iff_no_lt, minimal_iff_no_lt] at *
  intro b h'
  apply h _ $ mono h'

theorem preimage_minimal_strictAnti {a : α} {f : α → β} (mono : StrictAntitone f) (h : Minimal (f a)) : Maximal a := by
  rw[maximal_iff_no_lt, minimal_iff_no_lt] at *
  intro b h'
  apply h _ $ mono h'
