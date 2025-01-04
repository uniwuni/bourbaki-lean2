import BourbakiLean2.Order.MaxMin

variable {α β : Type*} [Preorder α] [Preorder β]

def UpperBound (s : Set α) (a : α) := ∀ b ∈ s, b ≤ a
def LowerBound (s : Set α) (a : α) := ∀ b ∈ s, a ≤ b

def Set.BoundedAbove (s : Set α) := ∃ a, UpperBound s a
def Set.BoundedBelow (s : Set α) := ∃ a, LowerBound s a
def Set.Bounded (s : Set α) := BoundedAbove s ∧ BoundedBelow s

variable {s t : Set α} {a b : α}
theorem upperBound_iff_greatest_of_mem (h : a ∈ s) :
    Greatest (⟨a,h⟩ : s) ↔ UpperBound s a := by
  constructor
  · intro h' b h''
    have := h' ⟨b,h''⟩
    rwa[Subtype.le_iff_val] at this
  · rintro h' ⟨b,h''⟩
    exact h' b h''

theorem lowerBound_iff_least_of_mem (h : a ∈ s) :
    Least (⟨a,h⟩ : s) ↔ LowerBound s a := by
  constructor
  · intro h' b h''
    have := h' ⟨b,h''⟩
    rwa[Subtype.le_iff_val] at this
  · rintro h' ⟨b,h''⟩
    exact h' b h''

theorem UpperBound.subset (h : UpperBound s a) (h' : t ⊆ s) : UpperBound t a :=
  fun b h'' => h b (h' h'')

theorem LowerBound.subset (h : LowerBound s a) (h' : t ⊆ s) : LowerBound t a :=
  fun b h'' => h b (h' h'')

theorem Set.BoundedAbove.subset (h : BoundedAbove s) (h' : t ⊆ s) : BoundedAbove t :=
  h.imp (fun _ h'' => h''.subset h')

theorem Set.BoundedBelow.subset (h : BoundedBelow s) (h' : t ⊆ s) : BoundedBelow t :=
  h.imp (fun _ h'' => h''.subset h')

theorem Set.Bounded.subset (h : Bounded s) (h' : t ⊆ s) : Bounded t :=
  ⟨h.1.subset h', h.2.subset h'⟩

theorem UpperBound.upperBound_of_le (h : UpperBound s a) (h' : a ≤ b) : UpperBound s b :=
  fun _ h'' => le_trans (h _ h'') h'

theorem LowerBound.lowerBound_of_le (h : LowerBound s a) (h' : b ≤ a) : LowerBound s b :=
  fun _ h'' => le_trans h' (h _ h'')

theorem upperBound_iUnion_iff {ι : Type*} {s : ι → Set α} :
    UpperBound (⋃ i, s i) a ↔ ∀ i, UpperBound (s i) a := by
  unfold UpperBound
  rw[forall_comm]
  apply forall_congr'
  intro a
  simp only [Set.mem_iUnion_iff, forall_exists_index]

theorem UpperBound.upperBound_iInter {ι : Type*} {s : ι → Set α} {i} (h : UpperBound (s i) a) : UpperBound (⋂ i, s i) a := h.subset Set.iInter_subset

theorem lowerbound_iUnion_iff {ι : Type*} {s : ι → Set α} :
    LowerBound (⋃ i, s i) a ↔ ∀ i, LowerBound (s i) a := by
  unfold LowerBound
  rw[forall_comm]
  apply forall_congr'
  intro a
  simp only [Set.mem_iUnion_iff, forall_exists_index]

theorem LowerBound.lowerBound_iInter {ι : Type*} {s : ι → Set α} {i} (h : LowerBound (s i) a) : LowerBound (⋂ i, s i) a := h.subset Set.iInter_subset
@[simp] theorem UpperBound.empty {a : α} : UpperBound ∅ a := nofun
@[simp] theorem LowerBound.empty {a : α} : LowerBound ∅ a := nofun
@[simp] theorem UpperBound.singleton {a b : α} : UpperBound {a} b ↔ a ≤ b := by
  simp only [UpperBound, Set.mem_singleton_iff, forall_eq]
@[simp] theorem LowerBound.singleton {a b : α} : LowerBound {a} b ↔ b ≤ a := by
  simp only [LowerBound, Set.mem_singleton_iff, forall_eq]


theorem Monotone.upperBound_of_upperBound {f : α → β} (h : Monotone f) (h' : UpperBound s a) : UpperBound (f '' s) (f a) := by
  intro b hb
  rw[Set.mem_image_iff] at hb
  obtain ⟨c,rfl,hc⟩ := hb
  apply h $ h' _ hc

theorem Monotone.lowerBound_of_lowerBound {f : α → β} (h : Monotone f) (h' : LowerBound s a) : LowerBound (f '' s) (f a) := by
  intro b hb
  rw[Set.mem_image_iff] at hb
  obtain ⟨c,rfl,hc⟩ := hb
  apply h $ h' _ hc

@[simp] theorem HasGreatest.upperBound [HasGreatest α] {s : _} : UpperBound s (⊤ : α) := by
  intro x
  simp only [le_greatest, implies_true]

@[simp] theorem HasLeast.lowerBound [HasLeast α] {s : _} : LowerBound s (⊥ : α) := by
  intro x
  simp only [least_le, implies_true]
