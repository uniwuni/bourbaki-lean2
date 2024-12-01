import BourbakiLean2.Order.Bounds

def IsGLB {α : Type*} [Preorder α] (s : Set α) (a : α) := ∃ (h : LowerBound s a), Greatest (⟨a,h⟩ : {a : α // LowerBound s a})
def IsLUB {α : Type*} [Preorder α] (s : Set α) (a : α) := ∃ (h : UpperBound s a), Least (⟨a,h⟩ : {a : α // UpperBound s a})
def IsGLBi {α ι : Type*} [Preorder α] (x : ι → α) := IsGLB (x '' Set.univ)
def IsLUBi {α ι : Type*} [Preorder α] (x : ι → α) := IsLUB (x '' Set.univ)
section
variable {α : Type*} [Preorder α] {s t : Set α} {a b : α} {ι : Type*} {x x' : ι → α}
theorem isGLB_iff : IsGLB s a ↔ (LowerBound s a ∧ ∀ b, LowerBound s b → b ≤ a) := by
  unfold IsGLB
  simp only [Greatest, Subtype.le_iff_val, Subtype.forall, exists_prop]

theorem isLUB_iff : IsLUB s a ↔ (UpperBound s a ∧ ∀ b, UpperBound s b → a ≤ b) := by
  unfold IsLUB
  simp only [Least, Subtype.le_iff_val, Subtype.forall, exists_prop, and_congr_right_iff]

 theorem isGLBi_iff : IsGLBi x a ↔ ((∀ i, a ≤ x i) ∧ ∀ b, (∀ i, b ≤ x i) → b ≤ a) := by
  simp only [IsGLBi, isGLB_iff]
  constructor
  · intro ⟨h,h'⟩
    constructor
    · intro i
      apply h _ (by simp only [Set.val_mem_image_univ])
    · intro b h''
      apply h' b
      intro a
      rw[Set.mem_image_iff]
      rintro ⟨i,rfl,_⟩
      apply h'' _
  · intro ⟨h,h'⟩
    constructor
    · intro h
      rw[Set.mem_image_iff]
      rintro ⟨i,rfl,_⟩
      apply h _
    · intro b h''
      apply h'
      intro i
      apply h'' _ (by simp only [Set.val_mem_image_univ])

theorem isLUBi_iff : IsLUBi x a ↔ ((∀ i, x i ≤ a) ∧ ∀ b, (∀ i, x i ≤ b) → a ≤ b) := by
  simp only [IsLUBi, isLUB_iff]
  constructor
  · intro ⟨h,h'⟩
    constructor
    · intro i
      apply h _ (by simp only [Set.val_mem_image_univ])
    · intro b h''
      apply h' b
      intro a
      rw[Set.mem_image_iff]
      rintro ⟨i,rfl,_⟩
      apply h'' _
  · intro ⟨h,h'⟩
    constructor
    · intro h
      rw[Set.mem_image_iff]
      rintro ⟨i,rfl,_⟩
      apply h _
    · intro b h''
      apply h'
      intro i
      apply h'' _ (by simp only [Set.val_mem_image_univ])


theorem Least.isGLB_of_mem {a : s} (h : Least a) : IsGLB s a.val := by
  rcases a with ⟨a,mem⟩
  rw [isGLB_iff]
  have := (lowerBound_iff_least_of_mem mem).mp h
  apply And.intro this
  intro b hlb
  apply hlb _ mem

theorem Greatest.isLUB_of_mem {a : s} (h : Greatest a) : IsLUB s a.val := by
  rcases a with ⟨a,mem⟩
  rw [isLUB_iff]
  have := (upperBound_iff_greatest_of_mem mem).mp h
  apply And.intro this
  intro b hlb
  apply hlb _ mem

@[simp] theorem op_isGLB_iff : IsGLB (α := Op α) s (toOp a) ↔ IsLUB s a := Iff.rfl
@[simp] theorem op_isLUB_iff : IsLUB (α := Op α) s (toOp a) ↔ IsGLB s a := Iff.rfl

@[simp] theorem isGLB_empty_iff_greatest : IsGLB ∅ a ↔ Greatest a := by
  simp only [isGLB_iff, LowerBound.empty, forall_const, true_and, Greatest]

@[simp] theorem isLUB_empty_iff_least : IsLUB ∅ a ↔ Least a := by
  simp only [isLUB_iff, UpperBound.empty, forall_const, true_and, Least]

theorem isGLB_le_isLUB {a b : α} (h : s.Nonempty) (ha : IsGLB s a) (hb : IsLUB s b) : a ≤ b := by
  let ⟨x,h⟩ := h
  simp only [isGLB_iff, isLUB_iff] at ha hb
  replace ha := ha.1 x h
  replace hb := hb.1 x h
  exact le_trans ha hb

theorem IsGLB.le {a b : α} (h : IsGLB s a) (h' : b ∈ s) : a ≤ b :=
  (isGLB_iff.mp h).1 _ h'

theorem IsLUB.ge {a b : α} (h : IsLUB s a) (h' : b ∈ s) : b ≤ a :=
  (isLUB_iff.mp h).1 _ h'

theorem IsGLBi.le {i} (h : IsGLBi x a) : a ≤ x i := IsGLB.le h (by simp only [Set.val_mem_image_univ])
theorem IsLUBi.ge {i} (h : IsLUBi x a) : x i ≤ a := IsLUB.ge h (by simp only [Set.val_mem_image_univ])

@[simp] theorem IsGLB.ge_iff {a b : α} (h : IsGLB s a) : b ≤ a ↔ ∀ x ∈ s, b ≤ x := by
  constructor
  · intro h' x h''
    apply le_trans h' (h.le h'')
  · intro h'
    have : LowerBound s b := h'
    exact h.2 ⟨_,this⟩


@[simp] theorem IsLUB.le_iff {a b : α} (h : IsLUB s a) : a ≤ b ↔ ∀ x ∈ s, x ≤ b := by
  constructor
  · intro h' x h''
    apply le_trans (h.ge h'') h'
  · intro h'
    have : UpperBound s b := h'
    exact h.2 ⟨_,this⟩

theorem IsGLBi.ge_iff (h : IsGLBi x a) : b ≤ a ↔ ∀ i, b ≤ x i := by
  rw[IsGLB.ge_iff h]
  simp only [Set.mem_image_iff, Set.mem_univ, and_true, forall_exists_index,
    forall_eq_apply_imp_iff]

theorem IsLUBi.le_iff (h : IsLUBi x a) : a ≤ b ↔ ∀ i, x i ≤ b := by
  rw[IsLUB.le_iff h]
  simp only [Set.mem_image_iff, Set.mem_univ, and_true, forall_exists_index,
    forall_eq_apply_imp_iff]

theorem isGLB_antitone {t : Set α} {a b : α} (h : s ⊆ t) (h' : IsGLB s a) (h'' : IsGLB t b) : b ≤ a := by
  rw[h'.ge_iff]
  intro x h'''
  apply h''.le $ h h'''

theorem isLUB_monotone {t : Set α} {a b : α} (h : s ⊆ t) (h' : IsLUB s a) (h'' : IsLUB t b) : a ≤ b := by
  rw[h'.le_iff]
  intro x h'''
  apply h''.ge $ h h'''

theorem isGLBi_index_subset {r : Set ι} (h' : IsGLBi x a) (h'' : IsGLBi (x ∘ Subtype.val : r → α) b) :
    a ≤ b := by
  apply isGLB_antitone _ h'' h'
  simp only [Function.image_comp, Subtype.val_image, Set.subset_univ, Function.image_mono]

theorem isLUBi_index_subset {r : Set ι} (h' : IsLUBi x a) (h'' : IsLUBi (x ∘ Subtype.val : r → α) b) :
    b ≤ a := by
  apply isLUB_monotone _ h'' h'
  simp only [Function.image_comp, Subtype.val_image, Set.subset_univ, Function.image_mono]

theorem isGLBi_monotone (h : ∀ i, x i ≤ x' i) (h' : IsGLBi x a) (h'' : IsGLBi x' b) : a ≤ b := by
  rw[h''.ge_iff]
  intro i
  apply le_trans h'.le (h i)

theorem isLUBi_monotone (h : ∀ i, x i ≤ x' i) (h' : IsLUBi x a) (h'' : IsLUBi x' b) : a ≤ b := by
  rw[h'.le_iff]
  intro i
  apply le_trans (h i) h''.ge

theorem isLUBi_covering_iff {ι' : Type*} {j : ι' → Set ι} {a : ι' → α} (h : Set.IsCovering j)
    (h' : ∀ i', IsLUBi (x.restriction $ j i') (a i')) : IsLUBi x b ↔ IsLUBi a b := by
  constructor
  · intro h''
    rw[isLUBi_iff]
    constructor
    · intro i'
      specialize h' i'
      rw[h'.le_iff]
      intro ⟨i,hi⟩
      simp only [Function.restriction, ge_iff_le]
      apply h''.ge
    · intro a' ha
      rw[h''.le_iff]
      intro i
      obtain ⟨i',hi⟩ := h.mem_exists i
      apply le_trans _ $ ha i'
      exact (h' i').ge (ι := j i') (i := ⟨i,hi⟩)
  · intro h''
    rw[isLUBi_iff]
    constructor
    · intro i
      obtain ⟨i',hi⟩ := h.mem_exists i
      have := (h' i').ge (i := ⟨i,hi⟩)
      apply le_trans this h''.ge
    · intro a' ha'
      rw[h''.le_iff]
      intro i'
      rw[(h' i').le_iff]
      intro ⟨i, hi⟩
      exact ha' _

theorem isGLBi_covering_iff {ι' : Type*} {j : ι' → Set ι} {a : ι' → α} (h : Set.IsCovering j)
    (h' : ∀ i', IsGLBi (x.restriction $ j i') (a i')) : IsGLBi x b ↔ IsGLBi a b := by
  rw[IsGLBi,← op_isLUB_iff,IsGLBi,← op_isLUB_iff, ← IsLUBi, ← IsLUBi] at *
  conv at h' =>
    intro i
    rw[IsGLBi, ← op_isLUB_iff, ← IsLUBi]
  apply isLUBi_covering_iff h h'

theorem isLUBi_double_family {ι' : Type} {x : ι' → ι → α} {a : ι' → α} {b : α}
    (h : ∀ i', IsLUBi (x i') (a i')) : IsLUBi x.uncurry b ↔ IsLUBi a b := by
  apply isLUBi_covering_iff (ι' := ι') (ι := ι' × ι) (j := fun i' => {a | i' = a.1}) (a := a) (x := x.uncurry) (b := b)
  · rw[Set.isCovering_iff_mem_exists]
    intro a
    exists a.fst
  · intro i'
    have : (Function.uncurry x|_{a | i' = a.fst}) '' Set.univ = (x i') '' Set.univ := by
      ext a
      simp only [Set.mem_image_iff, Function.restriction, Set.mem_univ, and_true, Subtype.exists,
        Set.mem_setOf_iff, exists_prop, Prod.exists, Function.uncurry_apply_pair, exists_and_left,
        exists_eq_left']
    unfold IsLUBi
    rw[this]
    exact h _

theorem isGLBi_double_family {ι' : Type} {x : ι' → ι → α} {a : ι' → α} {b : α}
    (h : ∀ i', IsGLBi (x i') (a i')) : IsGLBi x.uncurry b ↔ IsGLBi a b := by
  rw[IsGLBi,← op_isLUB_iff,IsGLBi,← op_isLUB_iff, ← IsLUBi, ← IsLUBi] at *
  conv at h =>
    intro i
    rw[IsGLBi, ← op_isLUB_iff, ← IsLUBi]
  apply isLUBi_double_family h

theorem isLUB_pointwise {α : ι → Type*} [∀ i, Preorder (α i)] (x : Set ((i : _) → α i))
    (a : (i : _) → α i) : IsLUB (α := Pointwise ι α) x a ↔ (∀ i, IsLUB ((fun p => p i) '' x) (a i)) := by
  constructor
  · intro h i
    rw[isLUB_iff]
    constructor
    · intro a' h'
      rw[Set.mem_image_iff] at h'
      obtain ⟨p, rfl, pmem⟩ := h'
      apply h.ge pmem
    · intro b hb
      classical
      let a' i' := if h' : i' = i then h' ▸ b else a i'
      have : UpperBound (α := Pointwise _ _) x a' := by
        intro p hp i'
        simp only [a']
        by_cases hi : i' = i
        · rcases hi
          simp only [↓reduceDIte]
          apply hb
          rw[Set.mem_image_iff]
          exists p
        · simp only [hi, ↓reduceDIte]
          exact (h.ge hp) i'
      have := h.2 ⟨_,this⟩
      apply le_trans (this i)
      simp only [dite_eq_ite, ↓reduceIte, le_refl, a']
  · intro h
    rw[isLUB_iff]
    constructor
    · intro p hp i
      apply (h i).ge (Set.val_mem_image_of_mem hp)
    · intro p hp i
      rw[(h i).le_iff]
      intro a' ha'
      rw[Set.mem_image_iff] at ha'
      obtain ⟨a,rfl,ha⟩ := ha'
      apply hp _ ha

theorem isGLB_pointwise {α : ι → Type*} [∀ i, Preorder (α i)] (x : Set ((i : _) → α i))
    (a : (i : _) → α i) : IsGLB (α := Pointwise ι α) x a ↔ (∀ i, IsGLB ((fun p => p i) '' x) (a i)) := by
  conv =>
    rw[← op_isLUB_iff]
    arg 2
    intro i
    rw[← op_isLUB_iff]
  apply isLUB_pointwise (α := fun i => Op (α i)) (a := fun i => toOp $ a i)

theorem IsLUB.in_ambient_le_in_subset
    {s : Set α} {t : Set s} {a : s} {a' : α} (h : IsLUB t a)
    (h' : IsLUB (Subtype.val '' t) a') : a' ≤ a := by
  rw[h'.le_iff]
  intro x
  rw[Set.mem_image_iff]
  rintro ⟨⟨a',ha'⟩,rfl,ha⟩
  apply h.ge ha (b := ⟨x,ha'⟩)

theorem IsGLB.in_subset_le_in_ambient
    {s : Set α} {t : Set s} {a : s} {a' : α} (h : IsGLB t a)
    (h' : IsGLB (Subtype.val '' t) a') : a ≤ a' := by
  rw[h'.ge_iff]
  intro x
  rw[Set.mem_image_iff]
  rintro ⟨⟨a',ha'⟩,rfl,ha⟩
  apply h.le ha (b := ⟨x,ha'⟩)

theorem IsLUB.same_in_subset {s : Set α} {t : Set s} {a : s} (h : IsLUB (Subtype.val '' t) a) :
    IsLUB t a := by
  rcases a with ⟨a,ha⟩
  rw[isLUB_iff]
  constructor
  · intro ⟨b,hbs⟩ hbt
    exact h.ge (Set.val_mem_image_of_mem hbt)
  · intro ⟨b,hbs⟩ hbu
    simp only [h.le_iff, LE.le]
    intro a' ha'
    rw[Set.mem_image_iff] at ha'
    obtain ⟨⟨a,as⟩,rfl,ha'⟩ := ha'
    apply hbu _ ha'

theorem IsGLB.same_in_subset {s : Set α} {t : Set s} {a : s} (h : IsGLB (Subtype.val '' t) a) :
    IsGLB t a := by
  rcases a with ⟨a,ha⟩
  rw[isGLB_iff]
  constructor
  · intro ⟨b,hbs⟩ hbt
    exact h.le (Set.val_mem_image_of_mem hbt)
  · intro ⟨b,hbs⟩ hbu
    simp only [h.ge_iff, LE.le]
    intro a' ha'
    rw[Set.mem_image_iff] at ha'
    obtain ⟨⟨a,as⟩,rfl,ha'⟩ := ha'
    apply hbu _ ha'

section
variable {α : Type*} [PartialOrder α] {s : Set α} {a : α}

theorem IsGLB.all_eq {b : α} (h : IsGLB s a) (h' : IsGLB s b) : a = b := by
  have := Greatest.all_eq (α := {a : α // LowerBound s a}) h.2 h'.2
  rwa[Subtype.eq_iff] at this

theorem IsLUB.all_eq {b : α} (h : IsLUB s a) (h' : IsLUB s b) : a = b := by
  have := Least.all_eq (α := {a : α // UpperBound s a}) h.2 h'.2
  rwa[Subtype.eq_iff] at this

instance : Subsingleton {a : α // IsGLB s a} where
  allEq := fun ⟨_,h⟩ ⟨_,h'⟩ => Subtype.eq $ h.all_eq h'
instance : Subsingleton {a : α // IsLUB s a} where
  allEq := fun ⟨_,h⟩ ⟨_,h'⟩ => Subtype.eq $ h.all_eq h'

@[simp] theorem isGLB_singleton_iff_eq {a' : α} : IsGLB {a} a' ↔ a = a' := by
  constructor
  · rintro ⟨h,h'⟩
    apply le_antisymm
    · exact h' ⟨a, by simp only [LowerBound.singleton, le_rfl]⟩
    · apply h _ rfl
  · rintro rfl
    simp only [isGLB_iff, LowerBound.singleton, le_rfl, imp_self, implies_true, and_self]

@[simp] theorem isLUB_singleton_iff_eq {a' : α} : IsLUB {a} a' ↔ a = a' := by
  constructor
  · rintro ⟨h,h'⟩
    apply le_antisymm
    · apply h _ rfl
    · exact h' ⟨a, by simp only [UpperBound.singleton, le_rfl]⟩
  · rintro rfl
    simp only [isLUB_iff, UpperBound.singleton, le_rfl, imp_self, implies_true, and_self]



end
