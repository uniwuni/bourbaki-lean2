import BourbakiLean2.Order.Monotone
variable {α β : Type*} [PartialOrder α] [PartialOrder β]

/-! maximal and minimal elements -/

@[simp] def Minimal (a : α) := ∀ b, b ≤ a → b = a
@[simp] def Maximal (a : α) := ∀ b, a ≤ b → b = a
variable {a : α}
theorem minimal_iff_no_lt : Minimal a ↔ ∀ b, ¬ b < a := by
  simp only [Minimal, le_iff_lt_or_eq]
  apply forall_congr'
  intro b
  constructor
  · exact fun h h' => ne_of_lt h' (h $ Or.inl h')
  · rintro h (h'|rfl)
    · exact (h h').elim
    · rfl

theorem maximal_iff_no_lt : Maximal a ↔ ∀ b, ¬ a < b := by
  simp only [Maximal, le_iff_lt_or_eq]
  apply forall_congr'
  intro b
  constructor
  · exact fun h h' => ne_of_lt h' (h $ Or.inl h').symm
  · rintro h (h'|rfl)
    · exact (h h').elim
    · rfl

theorem maximal_toOp_iff_minimal : Maximal (toOp a) ↔ Minimal a := Iff.rfl
theorem minimal_toOp_iff_maximal : Minimal (toOp a) ↔ Maximal a := Iff.rfl

theorem preimage_maximal_strictMono {f : α → β} (mono : StrictMonotone f) (h : Maximal (f a)) : Maximal a := by
  rw[maximal_iff_no_lt] at *
  intro b h'
  apply h _ $ mono h'

theorem preimage_minimal_strictMono {f : α → β} (mono : StrictMonotone f) (h : Minimal (f a)) : Minimal a := by
  rw[minimal_iff_no_lt] at *
  intro b h'
  apply h _ $ mono h'

theorem preimage_maximal_strictAnti {f : α → β} (mono : StrictAntitone f) (h : Maximal (f a)) : Minimal a := by
  rw[maximal_iff_no_lt, minimal_iff_no_lt] at *
  intro b h'
  apply h _ $ mono h'

theorem preimage_minimal_strictAnti {f : α → β} (mono : StrictAntitone f) (h : Minimal (f a)) : Maximal a := by
  rw[maximal_iff_no_lt, minimal_iff_no_lt] at *
  intro b h'
  apply h _ $ mono h'

variable {p : α → Prop} {a : {a // p a}}
theorem Maximal.subtype (h : Maximal a.val) : Maximal a :=
  fun _ h' => Subtype.eq (h _ h')
theorem Minimal.subtype (h : Minimal a.val) : Minimal a :=
  fun _ h' => Subtype.eq (h _ h')


/-! Greatest and least elements -/

@[simp] def Greatest (a : α) := ∀ b, b ≤ a
@[simp] def Least (a : α) := ∀ b, a ≤ b

variable {a a' : α}
theorem Greatest.maximal (h : Greatest a) : Maximal a := fun _ => le_antisymm (h _)
theorem Least.minimal (h : Least a) : Minimal a := fun _ h' => le_antisymm h' (h _)

theorem greatest_iff_op_least : Greatest a ↔ Least (toOp a) := Iff.rfl
theorem least_if_op_greatest : Least a ↔ Greatest (toOp a) := Iff.rfl

theorem Greatest.all_eq (h : Greatest a) (h' : Greatest a') : a = a' :=
  le_antisymm (h' a) (h a')
theorem Least.all_eq (h : Least a) (h' : Least a') : a = a' :=
  le_antisymm (h a') (h' a)
instance : Subsingleton {a : α // Greatest a} where
  allEq := fun ⟨_,h⟩ ⟨_,h'⟩ => Subtype.eq $ h.all_eq h'
instance : Subsingleton {a : α // Least a} where
  allEq := fun ⟨_,h⟩ ⟨_,h'⟩ => Subtype.eq $ h.all_eq h'

theorem Greatest.maximal_eq (h : Greatest a) (h' : Maximal a') : a = a' := h' _ (h _)
theorem Least.minimal_eq (h : Least a) (h' : Minimal a') : a = a' := h' _ (h _)
def Greatest.unique_maximal (h : Greatest a) : Unique {a : α // Maximal a} where
  default := ⟨a, h.maximal⟩
  uniq := fun ⟨_,h'⟩ => Eq.symm $ Subtype.eq $ h.maximal_eq h'
def Least.unique_minimal (h : Least a) : Unique {a : α // Minimal a} where
  default := ⟨a, h.minimal⟩
  uniq := fun ⟨_,h'⟩ => Eq.symm $ Subtype.eq $ h.minimal_eq h'

variable {p : α → Prop} {a : {a // p a}}
theorem Greatest.subtype (h : Greatest a.val) : Greatest a :=
  fun _ => h _
theorem Least.subtype (h : Least a.val) : Least a :=
  fun _ => h _
