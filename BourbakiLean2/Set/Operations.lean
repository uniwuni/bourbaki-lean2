import BourbakiLean2.Function.Basic
import Batteries
import Batteries.Util.ExtendedBinder
variable {α β : Type*} {ι ι' : Type*} {x : ι → Set α} {y : ι → Set β} {a : α} {i : ι}

namespace Set
def iUnion (x : ι → Set α) := {a | ∃ i, a ∈ x i}
def iInter (x : ι → Set α) := {a | ∀ i, a ∈ x i}
section
open Lean Elab Term Meta Batteries.ExtendedBinder
syntax (name := iUnionBuilder) "⋃ " extBinder ", " term:51 : term
@[term_elab iUnionBuilder]
def elabiUnionBuilder : TermElab
  | `(⋃ $x:ident , $p ), expectedType? => do
    elabTerm (← `(iUnion fun $x:ident ↦ $p)) expectedType?
  | `(⋃ $x:ident : $t , $p ), expectedType? => do
    elabTerm (← `(iUnion fun $x:ident : $t ↦ $p)) expectedType?
  | `(⋃ $x:ident $b:binderPred , $p ), expectedType? => do
    elabTerm (← `(iUnion fun $x:ident ↦ satisfies_binder_pred% $x $b ∧ $p)) expectedType?
  | _, _ => throwUnsupportedSyntax

/-- Unexpander for set builder notation. -/
@[app_unexpander iUnion]
def iUnion.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident ↦ $p) => `(⋃ $x:ident , $p )
  | `($_ fun ($x:ident : $ty:term) ↦ $p) => `(⋃ $x:ident : $ty , $p )
  | _ => throw ()

syntax (name := iInterBuilder) "⋂ " extBinder ", " term:51 : term
@[term_elab iInterBuilder]
def elabiInterBuilder : TermElab
  | `(⋂ $x:ident , $p ), expectedType? => do
    elabTerm (← `(iInter fun $x:ident ↦ $p)) expectedType?
  | `(⋂ $x:ident : $t , $p ), expectedType? => do
    elabTerm (← `(iInter fun $x:ident : $t ↦ $p)) expectedType?
  | `(⋂ $x:ident $b:binderPred , $p ), expectedType? => do
    elabTerm (← `(iInter fun $x:ident ↦ satisfies_binder_pred% $x $b ∧ $p)) expectedType?
  | _, _ => throwUnsupportedSyntax

/-- Unexpander for set builder notation. -/
@[app_unexpander iInter]
def iInter.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident ↦ $p) => `(⋂ $x:ident , $p )
  | `($_ fun ($x:ident : $ty:term) ↦ $p) => `(⋂ $x:ident : $ty , $p )
  | _ => throw ()

end

@[simp] theorem mem_iUnion_iff : a ∈ ⋃ i, x i ↔ ∃i, a ∈ x i := Iff.rfl
theorem mem_iUnion_of (h : a ∈ x i) : a ∈ ⋃ i, x i := mem_iUnion_iff.mpr ⟨_,h⟩
theorem of_mem_iUnion (h : a ∈ ⋃ i, x i) : ∃ i, a ∈ x i := mem_iUnion_iff.mp h
@[simp] theorem subset_iUnion : x i ⊆ ⋃ i, x i := fun _ => mem_iUnion_of

@[simp] theorem iUnion_subset_iff_all {y : Set α} : ⋃ i, x i ⊆ y ↔ ∀i, x i ⊆ y := by
  constructor
  · intro h i
    trans ⋃ i, x i
    · exact subset_iUnion
    · exact h
  · rintro h a ⟨i,h'⟩
    exact h _ h'

theorem iUnion_empty_index (h : ι → False) : ⋃ i, x i = ∅ := by
  rw[← subset_empty_iff]
  rintro i ⟨w,_⟩
  exact h w

@[simp] theorem iUnion_empty_iff : ⋃ i, x i = ∅ ↔ ∀ i, x i = ∅ := by
  constructor
  · intro h i
    rw[← subset_empty_iff, ← h]
    simp only [subset_iUnion]
  · rw[← subset_empty_iff]
    rintro h a ⟨i,h'⟩
    simp only [h i, not_mem_empty] at h'

@[simp] theorem mem_iInter_iff : a ∈ ⋂ i, x i ↔ ∀i, a ∈ x i := Iff.rfl
theorem mem_iInter_of (h : ∀i, a ∈ x i) : a ∈ ⋂ i, x i := mem_iInter_iff.mpr h
theorem of_mem_iInter (h : a ∈ ⋂ i, x i) : a ∈ x i := mem_iInter_iff.mp h i

@[simp] theorem iInter_subset : ⋂ i, x i ⊆ x i := fun _ => of_mem_iInter

@[simp] theorem subset_iInter_iff_all {y : Set α} : y ⊆ ⋂ i, x i ↔ ∀ i, y ⊆ x i := by
  constructor
  · intro h i a h'
    exact iInter_subset (h h')
  · intro h a h' i
    exact h i h'

theorem iInter_empty_index (h : ι → False) : ⋂ i, x i = Set.univ := by
  ext a
  simp only [mem_iInter_iff, mem_univ, iff_true]
  intro i
  exact (h i).elim

@[simp] theorem iInter_univ_iff : ⋂ i, x i = Set.univ ↔ ∀ i, x i = Set.univ := by
  constructor
  · intro h i
    rw[← univ_subset_iff, ← h]
    simp only [iInter_subset]
  · rw[← univ_subset_iff]
    rintro h a _ i
    simp only [h i, mem_univ]

@[simp] theorem iUnion_singleton {x : Unit → Set α} : ⋃ i, x i = x ⟨⟩ := by
  ext a
  constructor
  · rintro ⟨⟨⟩,h⟩
    exact h
  · rintro h
    exact ⟨⟨⟩,h⟩

@[simp] theorem iInter_singleton {x : Unit → Set α} : ⋂ i, x i = x ⟨⟩ := by
  ext a
  constructor
  · intro h
    exact h ⟨⟩
  · rintro h ⟨⟩
    exact h

theorem iUnion_index_change_subset {f : ι' → ι} : ⋃ i', x (f i') ⊆ ⋃ i, x i := by
  intro a
  simp only [mem_iUnion_iff]
  rintro ⟨i', h'⟩
  exact ⟨f i',h'⟩

theorem iUnion_index_change_surj {f : ι' → ι}  (h : f.Surjective) : ⋃ i', x (f i') = ⋃ i, x i := by
  ext a
  simp only [mem_iUnion_iff]
  constructor
  apply iUnion_index_change_subset
  · rintro ⟨i, h'⟩
    obtain ⟨_,rfl⟩ := h.exists_preimage i
    exact ⟨_,h'⟩

theorem iInter_subset_index_change {f : ι' → ι} : ⋂ i, x i ⊆ ⋂ i', x (f i') := by
  intro a h i'
  simp only [mem_iInter_iff]
  exact h (f i')

theorem iInter_index_change_surj {f : ι' → ι} (h : f.Surjective) : ⋂ i', x (f i') = ⋂ i, x i := by
  ext a
  constructor
  · rintro h' i
    simp only [mem_iInter_iff]
    obtain ⟨_,rfl⟩ := h.exists_preimage i
    apply h'
  · apply iInter_subset_index_change

theorem iUnion_constant (h : ∀ i i', x i = x i') : ⋃ i, x i = x i := by
  ext a
  simp
  constructor
  · rintro ⟨i',h'⟩
    rw[h] at h'
    exact h'
  · apply Exists.intro i

theorem iInter_constant (h : ∀ i i', x i = x i') : ⋂ i, x i = x i := by
  ext a
  simp
  constructor
  · intro h'
    exact h' i
  · intro h' i'
    rw[h _ i'] at h'
    exact h'


theorem iUnion_index_mono {p : ι → Prop} : ⋃ i : {i // p i}, x i ⊆ ⋃ i, x i := by
  rintro a ⟨⟨i,h⟩,h'⟩
  exists i

theorem iInter_index_mono {p : ι → Prop} : ⋂ i, x i ⊆ ⋂ i : {i // p i}, x i := by
  rintro a h ⟨i,h'⟩
  apply_assumption

theorem iInter_subset_iUnion [Nonempty ι] : ⋂ i, x i ⊆ ⋃ i, x i := by
  intro a h
  exists Classical.choice (by infer_instance)
  apply h

section
variable {x' : ι → Set α}

theorem iUnion_mono (h : ∀ i, x i ⊆ x' i) : ⋃ i, x i ⊆ ⋃ i, x' i := by
  rw[iUnion_subset_iff_all]
  intro i
  exact subset_trans (h i) subset_iUnion

theorem iInter_mono (h : ∀ i, x i ⊆ x' i) : ⋂ i, x i ⊆ ⋂ i, x' i := by
  rw[subset_iInter_iff_all]
  intro i
  exact subset_trans iInter_subset (h i)
end

theorem iUnion_assoc {x : ι → ι' → Set α} : ⋃ i : ι × ι', x i.1 i.2 = ⋃ j, (⋃ i, x j i) := by
  ext a
  simp only [mem_iUnion_iff, Prod.exists]

theorem iInter_assoc {x : ι → ι' → Set α} : ⋂ i : ι × ι', x i.1 i.2 = ⋂ j, (⋂ i, x j i) := by
  ext a
  simp only [mem_iInter_iff, Prod.forall]

end Set

section
variable {r : Relation α β}

theorem Relation.iUnion_image : r.image (⋃ i, x i) = ⋃ i, r.image (x i) := by
  ext a
  simp only [Relation.mem_image_iff, Set.mem_iUnion_iff]
  rw[exists_comm]
  apply exists_congr
  intro a'
  simp only [exists_and_left]

theorem Relation.iUnion_preimage : r.preimage (⋃ i, y i) = ⋃ i, r.preimage (y i) := by
  rw[← r.image_inv]
  conv =>
    rhs
    rhs
    intro i
    rw[← r.image_inv]
  apply iUnion_image

theorem Relation.subset_iInter_image : r.image (⋂ i, x i) ⊆ ⋂ i, r.image (x i) := by
  intro b ⟨a',h, h'⟩
  intro i
  simp at *
  exact ⟨_,h,h' _⟩

theorem Relation.subset_iInter_preimage : r.preimage (⋂ i, y i) ⊆ ⋂ i, r.preimage (y i) := by
  intro b ⟨a',h, h'⟩
  intro i
  simp at *
  exact ⟨_,h,h' _⟩
end

section
variable {f : α → β}
theorem Set.iUnion_image : Set.image f (⋃ i, x i) = ⋃ i, Set.image f (x i) := Relation.iUnion_image
theorem Set.iUnion_preimage : Set.preimage f (⋃ i, y i) = ⋃ i, Set.preimage f (y i) := Relation.iUnion_preimage
theorem Set.subset_iInter_image : Set.image f (⋂ i, x i) ⊆ ⋂ i, Set.image f (x i) := Relation.subset_iInter_image
theorem Set.iInter_preimage : Set.preimage f (⋂ i, y i) = ⋂ i, Set.preimage f (y i) := by
  apply subset_antisym
  · apply Relation.subset_iInter_preimage
  · intro a h
    simp only [mem_iInter_iff, mem_preimage_iff] at h
    simpa only [mem_preimage_iff, mem_iInter_iff] using h



end
