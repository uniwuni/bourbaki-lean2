import BourbakiLean2.Order.Monotone
section
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

theorem exists_lt_of_not_maximal (h : ¬ Maximal a) : ∃ b, a < b := by
  rw[maximal_iff_no_lt, Classical.not_forall] at h
  obtain ⟨x,lt⟩ := h
  rw[Classical.not_not] at lt
  exists x

theorem exists_le_of_not_maximal (h : ¬ Maximal a) : ∃ b, a ≤ b := by
  obtain ⟨b,lt⟩ := exists_lt_of_not_maximal h
  exact ⟨b,le_of_lt lt⟩

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
end

/-! Greatest and least elements -/
section
variable {α β : Type*} [Preorder α] [Preorder β]
@[simp] def Greatest (a : α) := ∀ b, b ≤ a
@[simp] def Least (a : α) := ∀ b, a ≤ b

variable {a a' : α}

theorem greatest_iff_op_least : Greatest a ↔ Least (toOp a) := Iff.rfl
theorem least_if_op_greatest : Least a ↔ Greatest (toOp a) := Iff.rfl


variable {p : α → Prop} {a' : {a // p a}}
theorem Greatest.subtype (h : Greatest a'.val) : Greatest a' :=
  fun _ => h _
theorem Least.subtype (h : Least a'.val) : Least a' :=
  fun _ => h _

end
section
variable {α β : Type*} [PartialOrder α] [PartialOrder β]
variable {a a' : α}
theorem Greatest.all_eq (h : Greatest a) (h' : Greatest a') : a = a' :=
  le_antisymm (h' a) (h a')
theorem Least.all_eq (h : Least a) (h' : Least a') : a = a' :=
  le_antisymm (h a') (h' a)

instance : Subsingleton {a : α // Greatest a} where
  allEq := fun ⟨_,h⟩ ⟨_,h'⟩ => Subtype.eq $ h.all_eq h'
instance : Subsingleton {a : α // Least a} where
  allEq := fun ⟨_,h⟩ ⟨_,h'⟩ => Subtype.eq $ h.all_eq h'


theorem Greatest.maximal (h : Greatest a) : Maximal a := fun _ => le_antisymm (h _)
theorem Least.minimal (h : Least a) : Minimal a := fun _ h' => le_antisymm h' (h _)


theorem Greatest.maximal_eq (h : Greatest a) (h' : Maximal a') : a = a' := h' _ (h _)
theorem Least.minimal_eq (h : Least a) (h' : Minimal a') : a = a' := h' _ (h _)
def Greatest.unique_maximal (h : Greatest a) : Unique {a : α // Maximal a} where
  default := ⟨a, h.maximal⟩
  uniq := fun ⟨_,h'⟩ => Eq.symm $ Subtype.eq $ h.maximal_eq h'
def Least.unique_minimal (h : Least a) : Unique {a : α // Minimal a} where
  default := ⟨a, h.minimal⟩
  uniq := fun ⟨_,h'⟩ => Eq.symm $ Subtype.eq $ h.minimal_eq h'

theorem Monotone.greatest_surj {f : α → β} (h : Monotone f) (h1 : f.Surjective) (h2 : Greatest a) :
    Greatest (f a) := by
  intro b
  obtain ⟨a', rfl⟩ := h1.exists_preimage b
  apply h $ h2 _

theorem Monotone.least_surj {f : α → β} (h : Monotone f) (h1 : f.Surjective) (h2 : Least a) :
    Least (f a) := by
  intro b
  obtain ⟨a', rfl⟩ := h1.exists_preimage b
  apply h $ h2 _

theorem Antitone.greatest_surj {f : α → β} (h : Antitone f) (h1 : f.Surjective) (h2 : Least a) :
    Greatest (f a) := by
  intro b
  obtain ⟨a', rfl⟩ := h1.exists_preimage b
  apply h $ h2 _

theorem Antitone.least_surj {f : α → β} (h : Antitone f) (h1 : f.Surjective) (h2 : Greatest a) :
    Least (f a) := by
  intro b
  obtain ⟨a', rfl⟩ := h1.exists_preimage b
  apply h $ h2 _

end

/-! on partial maps -/
variable {α : Type*} {β : α → Type*}
theorem PartialMap.maximal_iff [∀ a, Nonempty (β a)] {x : PartialMap α β} :
    Maximal x ↔ x.carrier = Set.univ := by
  constructor
  · intro h
    classical
    let y : PartialMap α β := ⟨Set.univ,
      fun ⟨b,h⟩ => if h : b ∈ x.carrier then x.function ⟨b,h⟩ else Classical.choice (by infer_instance)⟩
    have : x ≤ y := by
      simp only [LE.le, Set.subset_univ, exists_true_left, y]
      intro a h'
      split
      · simp only
      · simp
    specialize h _ this
    rw[← h]
  · intro h y h'
    simp only [LE.le] at h'
    rcases h' with ⟨h',h''⟩
    rw[h] at h'
    rcases x with ⟨xc, xf⟩
    rcases y with ⟨yc, yf⟩
    simp only [mk.injEq] at *
    let hh : yc = xc := by
      rw[Set.eq_iff_subset_subset]
      constructor
      · rw[h]
        apply Set.subset_univ
      · exact h'
    constructor
    · exact hh
    · apply heq_of_eqRec_eq (congrArg _ hh)
      ext ⟨a,h⟩
      rcases hh
      rw[← h'' a h]

theorem PartialMap.least_iff {x : PartialMap α β} :
    Least x ↔ x.carrier = ∅ := by
  constructor
  · intro h
    specialize h ⟨∅, nofun⟩
    rw[← Set.subset_empty_iff]
    exact h.1
  · intro h ⟨y,f⟩
    constructor
    · intro a h'
      rw[h] at h'
      exact h'.elim
    · simp only [h, Set.empty_subset]


def AdjoinGreatest (α : Type*) := Sum α Unit
def AdjoinGreatest.to : α → AdjoinGreatest α := Sum.inl

def AdjoinGreatest.greatest : AdjoinGreatest α := Sum.inr ()


instance [LE α] : LE (AdjoinGreatest α) where
  le x y := match y with
            | Sum.inl y => match x with
                     | Sum.inl x => x ≤ y
                     | Sum.inr _ => False
            | Sum.inr _ => True

@[simp] theorem AdjoinGreatest.le_greatest [LE α] {x : AdjoinGreatest α} : x ≤ greatest := True.intro
@[simp] theorem AdjoinGreatest.to_le_to_iff [LE α] {a b : α} : to a ≤ to b ↔ a ≤ b := Iff.rfl
instance [Preorder α] : Preorder (AdjoinGreatest α) where
  le_refl a := by
    cases a
    · rfl
    · trivial
  le_trans := by
    rintro (a|⟨⟩) (b|⟨⟩) (c|⟨⟩)
    · exact le_trans
    · exact fun h h' => True.intro
    · exact fun h => nofun
    · exact fun h h' => True.intro
    · exact nofun
    · exact nofun
    · exact fun h => nofun
    · exact fun h h' => True.intro

instance [PartialOrder α] : PartialOrder (AdjoinGreatest α) where
  le_antisymm := by
    rintro (a|⟨⟩) (b|⟨⟩)
    · exact fun h h' => congrArg Sum.inl $ le_antisymm h h'
    · exact fun h => nofun
    · exact nofun
    · exact fun h h' => rfl

@[simp] theorem AdjoinGreatest.greatest_is_greatest [Preorder α]: Greatest (greatest : AdjoinGreatest α) :=
  fun _ => True.intro


def AdjoinLeast (α : Type*) := Op (AdjoinGreatest (Op α))
instance [LE α] : LE (AdjoinLeast α) := by unfold AdjoinLeast; infer_instance
instance [Preorder α] : Preorder (AdjoinLeast α) := by unfold AdjoinLeast; infer_instance
instance [PartialOrder α] : PartialOrder (AdjoinLeast α) := by unfold AdjoinLeast; infer_instance

def AdjoinLeast.to : α → AdjoinLeast α := Sum.inl

def AdjoinLeast.least : AdjoinLeast α := Sum.inr ()

@[simp] theorem AdjoinLeast.least_le [LE α] {x : AdjoinLeast α} : least ≤ x := True.intro
@[simp] theorem AdjoinLeast.to_le_to_iff [LE α] {a b : α} : to a ≤ to b ↔ a ≤ b := Iff.rfl

@[simp] theorem AdjoinLeast.least_is_least [Preorder α]: Least (least : AdjoinLeast α) :=
  fun _ => True.intro

@[simp] theorem greatest_singleton [Preorder α] {a : α} : Greatest (⟨a, rfl⟩ : ({a} : Set α)) := by
  simp only [Greatest, Subtype.le_iff_val, Subtype.forall, Set.mem_singleton_iff, forall_eq, le_rfl]

@[simp] theorem least_singleton [Preorder α] {a : α} : Least (⟨a, rfl⟩ : ({a} : Set α)) := by
  simp only [Least, Subtype.le_iff_val, Subtype.forall, Set.mem_singleton_iff, forall_eq, le_refl]



class HasLeast (α : Type*) [Preorder α] where
  least : α
  least_le (x : α) : least ≤ x

class HasGreatest (α : Type*) [Preorder α] where
  greatest : α
  le_greatest (x : α) : x ≤ greatest

/-- The top (`⊤`, `\top`) element -/
notation "⊤" => HasGreatest.greatest

/-- The bot (`⊥`, `\bot`) element -/
notation "⊥" => HasLeast.least

instance (priority := 100) greatest_nonempty (α : Type*) [Preorder α] [HasGreatest α] : Nonempty α :=
  ⟨⊤⟩

instance (priority := 100) least_nonempty (α : Type*) [Preorder α] [HasLeast α] : Nonempty α :=
  ⟨⊥⟩
attribute [match_pattern] HasGreatest.greatest HasLeast.least

variable {β : Type*}
@[simp] theorem least_le [Preorder α] [HasLeast α] (x : α) : ⊥ ≤ x := HasLeast.least_le x
@[simp] theorem le_greatest [Preorder α] [HasGreatest α] (x : α) : x ≤ ⊤ := HasGreatest.le_greatest x
theorem least_least [Preorder α] [HasLeast α] : Least (⊥ : α) := least_le
theorem greatest_greatest [Preorder α] [HasGreatest α] : Greatest (⊤ : α) := le_greatest
@[simp] theorem le_least_iff [PartialOrder α] [HasLeast α] {x : α} : x ≤ ⊥ ↔ x = ⊥ := by
  constructor
  · apply least_least.minimal
  · rintro rfl; rfl

@[simp] theorem greatest_le_iff [PartialOrder α] [HasGreatest α] {x : α} : ⊤ ≤ x ↔ x = ⊤ := by
  constructor
  · apply greatest_greatest.maximal
  · rintro rfl; rfl

@[simp] theorem ne_least_iff [PartialOrder α] [HasLeast α] {x : α} : x ≠ ⊥ ↔ ⊥ < x := by
  rw[lt_iff_le_not_eq]
  simp only [ne_eq, least_le, Eq.comm, true_and]

@[simp] theorem ne_greatest_iff [PartialOrder α] [HasGreatest α] {x : α} : x ≠ ⊤ ↔ x < ⊤  := by
  rw[lt_iff_le_not_eq]
  simp only [ne_eq, le_greatest, true_and]

@[simp] theorem IsOrderIso.greatest [PartialOrder α] [PartialOrder β]
    [HasGreatest α] [HasGreatest β] {f : α → β} (h : IsOrderIso f) : f ⊤ = ⊤ := by
  apply le_antisymm
  · exact le_greatest (f ⊤)
  · rw[← h.bij.val_inv_val (b := ⊤),h.le_iff]
    exact le_greatest (h.bij.inv ⊤)

@[simp] theorem IsOrderIso.least [PartialOrder α] [PartialOrder β]
    [HasLeast α] [HasLeast β] {f : α → β} (h : IsOrderIso f) : f ⊥ = ⊥ := by
  apply le_antisymm
  · rw[← h.bij.val_inv_val (b := ⊥),h.le_iff]
    exact least_le _
  · exact least_le (f ⊥)

instance [Preorder α] : HasLeast (AdjoinLeast α) where
  least := AdjoinLeast.least
  least_le _ := AdjoinLeast.least_le

instance [Preorder α] : HasGreatest (AdjoinGreatest α) where
  greatest := AdjoinGreatest.greatest
  le_greatest _ := AdjoinGreatest.le_greatest

instance [Preorder α] [HasLeast α] : HasGreatest (Op α) where
  greatest := (⊥ : α)
  le_greatest _ := least_le _

instance [Preorder α] [HasGreatest α] : HasLeast (Op α) where
  least := (⊤ : α)
  least_le _ := le_greatest _
