import BourbakiLean2.Set.Defs
import BourbakiLean2.Logic
namespace Set
variable {α : Type*} {p q : α → Prop}

/-! setOf stuff -/

@[simp]
theorem mem_setOf_iff {x : α} :
    x ∈ {y | p y} ↔ p x := Iff.rfl
theorem mem_setOf_of {x : α} (h : p x) : x ∈ {y | p y} := h
theorem of_mem_setOf {x : α} (h : x ∈ {y | p y}) : p x := h

/-! subsets -/
@[simp, refl]
theorem subset_refl (x : Set α) : x ⊆ x := fun _ h => h

section
variable {x y z : Set α}

theorem subset_rfl : x ⊆ x := subset_refl x
theorem subset_trans (h : x ⊆ y) (h' : y ⊆ z) : x ⊆ z :=
  fun _ h'' => h' (h h'')

instance: Trans (fun (x y : Set α) => x ⊆ y) (fun x y => x ⊆ y) (fun x y => x ⊆ y) where
  trans := subset_trans

theorem subset_antisym (h : x ⊆ y) (h' : y ⊆ x) : x = y := ext (fun x => ⟨@h x, @h' x⟩)

theorem eq_iff_subset_subset : x = y ↔ (x ⊆ y ∧ y ⊆ x) := by
  constructor
  · intro h
    simp only [h, subset_refl, and_self]
  · rintro ⟨h, h'⟩
    exact subset_antisym h h'

@[simp] theorem setOf_subset_iff : {y | p y} ⊆ x ↔ (∀ a, p a → a ∈ x) := Iff.rfl
@[simp] theorem subset_setOf_iff : x ⊆ {y | p y} ↔ (∀ a, a ∈ x → p a) := Iff.rfl
@[simp] theorem setOf_subset_setOf_iff : {y | p y} ⊆ {y | q y} ↔ (∀ a, p a → q a) :=
  Iff.rfl
@[simp] theorem setOf_eq_setOf_iff : {y | p y} = {y | q y} ↔ (∀ a, p a ↔ q a) := by
  simp only [eq_iff_subset_subset, subset_setOf_iff, mem_setOf_iff]
  constructor
  · intro h a
    exact ⟨h.1 a, h.2 a⟩
  · intro h
    exact ⟨fun a => (h a).1, fun a => (h a).2⟩

/-! simp lemmas -/

@[simp] theorem mem_univ {a : α} : a ∈ Set.univ := ⟨⟩
@[simp] theorem subset_univ : x ⊆ Set.univ := fun _ _ => ⟨⟩
@[simp] theorem not_mem_empty {a : α} : a ∉ (∅ : Set α) := fun x => x
@[simp] theorem empty_subset : ∅ ⊆ x := fun _ => False.elim
@[simp] theorem mem_singleton_iff {a b : α} : a ∈ ({b} : Set α) ↔ a = b := Iff.rfl
theorem subset_empty_iff : x ⊆ ∅ ↔ x = ∅ := by
  constructor
  · rw[Set.ext_iff]
    intro h x'
    simp only [not_mem_empty, iff_false]
    intro h'
    exact h h'
  · rintro rfl
    rfl

theorem univ_subset_iff : univ ⊆ x ↔ x = univ := by
  constructor
  · intro h
    ext a
    specialize h (mem_univ (a := a))
    simp only [h, mem_univ]
  · rintro rfl
    rfl
/-! elements of operations -/
@[simp] theorem mem_sdiff_iff {a} : a ∈ x \ y ↔ a ∈ x ∧ a ∉ y := Iff.rfl
@[simp] theorem mem_compl_iff {a} : a ∈ xᶜ ↔ a ∉ x := Iff.rfl
@[simp] theorem mem_powerset_iff {a} : a ∈ 𝒫 x ↔ a ⊆ x := Iff.rfl

/-! complement lemmas -/
@[simp] theorem compl_compl : (xᶜ)ᶜ = x := by ext; simp only [mem_compl_iff, Classical.not_not]
@[simp] theorem sdiff_univ_eq_compl : Set.univ \ x = xᶜ := by ext; simp only [mem_sdiff_iff,
  mem_univ, true_and, mem_compl_iff]
theorem subset_compl_iff_subset_compl : x ⊆ y.compl ↔ y ⊆ x.compl := by
  apply forall_congr'
  intro a
  rw[← @Classical.not_not (a ∈ y)]
  exact imp_iff_not_imp_not

theorem compl_subset_iff_compl_subset : x.compl ⊆ y ↔ y.compl ⊆ x := by
  apply forall_congr'
  intro a
  rw[← @Classical.not_not (a ∈ x)]
  exact imp_iff_not_imp_not

/-! misc -/
@[simp] theorem subset_singleton_iff {a} : x ⊆ {a} ↔ x = {a} ∨ x = ∅ := by
  constructor
  · intro h
    by_cases h' : a ∈ x
    · left
      ext a'
      exact ⟨@h a', fun e => e ▸ h'⟩
    · right
      ext a'
      exact ⟨fun g => ((h g) ▸ h') g, False.elim⟩
  · rintro (rfl|rfl)
    · rfl
    · exact empty_subset



@[simp] theorem empty_not_nonempty : ¬ (∅ : Set α).Nonempty := nofun
end


/-! sets of products -/

section
variable {β : Type*}

def prod (x : Set α) (y : Set β) : Set (α × β) := {a | a.1 ∈ x ∧ a.2 ∈ y}

@[simp] theorem mem_prod_iff {a : α} {b : β} {x : Set α} {y : Set β} :
    (a,b) ∈ prod x y ↔ a ∈ x ∧ b ∈ y := Iff.rfl

/-- for nonempty sets, products are subsets of another iff the factors are -/
@[simp] theorem prod_subset_prod_nonempty_iff {x x' : Set α} {y y' : Set β}
    (hx : x.Nonempty) (hy : y.Nonempty) : prod x y ⊆ prod x' y' ↔ (x ⊆ x' ∧ y ⊆ y') := by
  rcases hx with ⟨ax, hx⟩
  rcases hy with ⟨ay, hy⟩
  constructor
  · intro h
    constructor
    · intro a h2
      specialize @h (a, ay)
      simp only [mem_prod_iff, and_self, forall_const, h2, hy] at h
      exact h.1
    · intro a h2
      specialize @h (ax, a)
      simp only [mem_prod_iff, and_self, forall_const, hx, h2] at h
      exact h.2
  · rintro ⟨h1, h2⟩ ⟨a,b⟩ h
    exact ⟨h1 h.1, h2 h.2⟩

@[simp] theorem prod_empty_iff {x : Set α} {y : Set β} :
    (prod x y).Nonempty ↔ (x.Nonempty ∧ y.Nonempty) := by
  simp only [Set.Nonempty, Prod.exists,  mem_prod_iff, exists_and_left, exists_and_right]

@[simp] theorem prod_univ_univ : prod Set.univ Set.univ = (Set.univ : Set (α × β)) := by
  ext ⟨a,b⟩
  simp only [mem_prod_iff, mem_univ, and_self]

end
/-! nonempty equivalences -/
theorem nonempty_iff_neq_empty {x : Set α} : x.Nonempty ↔ x ≠ ∅ := by
  constructor
  · rintro ⟨a,h⟩ rfl
    exact not_mem_empty h
  · intro h
    by_cases h' : x.Nonempty
    · exact h'
    · have h'' : x = ∅ := by
        ext a
        simp only [not_mem_empty, iff_false]
        intro h''
        apply h' ⟨_,h''⟩
      exact (h h'').elim

@[simp] theorem singleton_neq_empty {a : α} : ({a} : Set α) ≠ ∅ := by
  intro h
  rw[Set.ext_iff] at h
  specialize h a
  simp only [mem_singleton_iff, not_mem_empty, iff_false, not_true_eq_false] at h

@[simp] theorem mem_pair_iff {a b c : α} : c ∈ ({a,b} : Set α) ↔ (c = a ∨ c = b) := Iff.rfl

instance {a : α}: Unique ({a} : Set α) where
  default := ⟨a,rfl⟩
  uniq x := Subtype.eq x.property

theorem cases_of_empty {p : Set α → Prop} (h : p ∅) (h' : ∀ a, a.Nonempty → p a) :
    ∀ a, p a := by
  intro a
  by_cases h : a.Nonempty
  · apply h' _ h
  · rw[nonempty_iff_neq_empty, Ne, Classical.not_not] at h
    rw[h]
    assumption

end Set
