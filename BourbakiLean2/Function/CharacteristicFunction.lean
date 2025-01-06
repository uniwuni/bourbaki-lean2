import BourbakiLean2.Data.Nat.Basic

variable {α : Type*}
noncomputable def Set.charfun (a : Set α) : α → Nat :=
  fun x => ite (x ∈ a) (h := (Classical.decidableInhabited _).default) 1 0

@[simp] theorem Set.charfun_one_iff {a : Set α} {x : α} : a.charfun x = 1 ↔ x ∈ a := by simp only [charfun,
  ite_eq_left_iff, reduceCtorEq, imp_false, Classical.not_not]

@[simp] theorem Set.charfun_zero_iff {a : Set α} {x : α} : a.charfun x = 0 ↔ x ∉ a := by simp only [charfun,
  ite_eq_right_iff, Nat.add_one_ne_zero, imp_false]

theorem Set.charfun_zero_or_one (a : Set α) (x : α) : a.charfun x = 0 ∨ a.charfun x = 1 := by simp only [charfun,
  ite_eq_right_iff, Nat.add_one_ne_zero, imp_false, ite_eq_left_iff, reduceCtorEq,
  Classical.not_not, or_comm, Classical.em]

@[simp] theorem Set.charfun_empty : (∅ : Set α).charfun = fun _ => 0 := by ext a; simp only [charfun_zero_iff,
  not_mem_empty, not_false_eq_true]

@[simp] theorem Set.charfun_univ : (Set.univ : Set α).charfun = fun _ => 1 := by ext a; simp only [charfun_one_iff,
  mem_univ]

@[simp] theorem Set.charfun_inter {a b : Set α} : (a ∩ b : Set α).charfun = fun x => a.charfun x * b.charfun x := by
  ext x
  rcases charfun_zero_or_one (a := a) (x := x) with (h|h)
  · rcases charfun_zero_or_one (a := b) (x := x) with (h'|h') <;> {simp[*]; simp at *; simp[*]}
  · rcases charfun_zero_or_one (a := b) (x := x) with (h'|h') <;> {simp[*]; simp at *; simp[*]}

theorem Set.charfun_union_inter {a b : Set α} {x} : (a ∩ b).charfun x + (a ∪ b : Set α).charfun x = a.charfun x + b.charfun x := by
  rcases charfun_zero_or_one (a := a) (x := x) with (h|h)
  · rcases charfun_zero_or_one (a := b) (x := x) with (h'|h') <;> {simp[*]; simp at *; simp[*]}
  · rcases charfun_zero_or_one (a := b) (x := x) with (h'|h')
    · simp only [charfun_inter, Nat.mul_zero, Nat.zero_add, Nat.add_zero, charfun_one_iff,
      mem_union_iff, h, h']
      simp only [charfun_one_iff, charfun_zero_iff] at *
      simp only [or_false, h, h']
    · simp only [charfun_inter, Nat.mul_one, Nat.reduceAdd, h, h']
      simp only [charfun_one_iff] at *
      have : (a ∪ b).charfun x = 1 := by
        simp only [charfun_one_iff, mem_union_iff, h, true_or]
      rw[this]

theorem Set.charfun_union {a b : Set α} : (a ∪ b : Set α).charfun = fun x => a.charfun x + b.charfun x - (a ∩ b).charfun x := by
  ext x
  rw[← Set.charfun_union_inter]
  exact Eq.symm (Nat.add_sub_self_left ((a ∩ b).charfun x) ((a ∪ b).charfun x))

theorem Set.charfun_inj : (Set.charfun : Set α → (α → Nat)).Injective := by
  intro a b h
  ext x
  rcases charfun_zero_or_one a x with (h'|h')
  · have := h ▸ h'
    simp only [charfun_zero_iff] at h' this
    simp only [h', this]
  · have := h ▸ h'
    simp only [charfun_one_iff] at h' this
    simp only [h', this]

theorem Set.charfun_compl {a : Set α} : (a ᶜ : Set α).charfun = fun x => 1 - a.charfun x := by
  ext x
  rcases charfun_zero_or_one a x with (h|h)
  · simp only [h, Nat.sub_zero, charfun_one_iff, mem_compl_iff]
    simp only [charfun_zero_iff] at h
    exact h
  · simp only [h, Nat.sub_self, charfun_zero_iff, mem_compl_iff, Classical.not_not]
    simp only [charfun_one_iff] at h
    exact h
