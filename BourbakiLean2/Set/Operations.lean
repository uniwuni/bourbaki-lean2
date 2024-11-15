import BourbakiLean2.Function.Basic
import Batteries
import Batteries.Util.ExtendedBinder
variable {α β : Type*} {ι ι' : Type*} {a : α} {i : ι}
section
variable {x : ι → Set α} {y : ι → Set β}

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

theorem iUnion_compl : ⋃ i, (x i)ᶜ = (⋂ i, x i)ᶜ := by
  ext
  simp only [mem_iUnion_iff, mem_compl_iff, mem_iInter_iff, Classical.not_forall]

theorem iInter_compl : ⋂ i, (x i)ᶜ = (⋃ i, x i)ᶜ := by
  ext
  simp only [mem_iInter_iff, mem_compl_iff, mem_iUnion_iff, not_exists]


variable {x x' x'' x''' : Set α}

@[simp] theorem mem_union_iff : a ∈ x ∪ x' ↔ a ∈ x ∨ a ∈ x' := Iff.rfl
@[simp] theorem mem_inter_iff : a ∈ x ∩ x' ↔ a ∈ x ∧ a ∈ x' := Iff.rfl
theorem union_eq_iUnion : x ∪ x' = ⋃ i : Bool, if i then x else x' := by
  ext
  simp only [mem_union_iff, mem_iUnion_iff, Bool.exists_bool, Bool.false_eq_true, ↓reduceIte,
    Or.comm]
theorem inter_eq_iInter : x ∩ x' = ⋂ i : Bool, if i then x else x' := by
  ext
  simp only [mem_inter_iff, mem_iInter_iff, Bool.forall_bool, Bool.false_eq_true, ↓reduceIte,
    And.comm]

theorem union_comm : x ∪ x' = x' ∪ x := by ext; simp only [mem_union_iff, Or.comm]
@[simp]  theorem union_assoc : x ∪ x' ∪ x'' = x ∪ (x' ∪ x'') := by ext; simp only [mem_union_iff,
  or_assoc]
theorem inter_comm : x ∩ x' = x' ∩ x := by ext; simp only [mem_inter_iff, And.comm]
@[simp] theorem inter_assoc : x ∩ x' ∩ x'' = x ∩ (x' ∩ x'') := by ext; simp only [mem_inter_iff,
  and_assoc]
@[simp] theorem subset_union_left : x ⊆ x ∪ x' := fun _ => Or.inl
@[simp] theorem subset_union_right : x' ⊆ x ∪ x' := fun _ => Or.inr
@[simp] theorem inter_subset_left : x ∩ x' ⊆ x := fun _ => And.left
@[simp] theorem inter_subset_right : x ∩ x' ⊆ x' := fun _ => And.right
@[simp] theorem inter_subset_union : x ∩ x' ⊆ x ∪ x' := fun _ => Or.inl ∘ And.left
theorem subset_inter_iff : x ⊆ x' ∩ x'' ↔ (x ⊆ x' ∧ x ⊆ x'') := by
  constructor
  · intro h
    exact ⟨subset_trans h inter_subset_left, subset_trans h inter_subset_right⟩
  · rintro ⟨h, h'⟩ a h''
    exact ⟨h h'', h' h''⟩
theorem union_subset_iff : x ∪ x' ⊆ x'' ↔ (x ⊆ x'' ∧ x' ⊆ x'') := by
  constructor
  · intro h
    exact ⟨subset_trans subset_union_left h, subset_trans subset_union_right h⟩
  · rintro ⟨h, h'⟩ a (h''|h'')
    · exact h h''
    · exact h' h''
@[simp] theorem union_eq_iff_subset_left : x ∪ x' = x ↔ x' ⊆ x := by
  constructor
  · intro h a h'
    rw[← h]
    simp only [mem_union_iff, h', or_true]
  · intro h
    ext a
    simpa only [mem_union_iff, or_iff_left_iff_imp] using @h a
@[simp] theorem union_eq_iff_subset_right : x ∪ x' = x' ↔ x ⊆ x' := by
  rw[union_comm]
  simp only [union_eq_iff_subset_left]

@[simp] theorem inter_eq_iff_subset_left : x ∩ x' = x ↔ x ⊆ x' := by
  constructor
  · intro h a h'
    rw[← h] at h'
    exact h'.2
  · intro h
    ext a
    simpa only [mem_inter_iff, and_iff_left_iff_imp] using @h a
@[simp] theorem inter_eq_iff_subset_right : x ∩ x' = x' ↔ x' ⊆ x := by
  rw[inter_comm]
  simp only [inter_eq_iff_subset_left]
@[simp] theorem union_self : x ∪ x = x := by simp only [union_eq_iff_subset_left, subset_refl]
@[simp] theorem inter_self : x ∩ x = x := by simp only [inter_eq_iff_subset_left, subset_refl]
theorem union_inter_distrib_right : x ∪ (x' ∩ x'') = (x ∪ x') ∩ (x ∪ x'') := by ext; simp only [mem_union_iff,
  mem_inter_iff, or_and_left]
theorem union_inter_distrib_left : (x ∩ x') ∪ x'' = (x ∪ x'') ∩ (x' ∪ x'') := by ext; simp only [mem_union_iff,
  mem_inter_iff, and_or_right]
theorem inter_union_distrib_right : x ∩ (x' ∪ x'') = (x ∩ x') ∪ (x ∩ x'') := by ext; simp only [mem_union_iff,
  mem_inter_iff, and_or_left]
theorem inter_union_distrib_left : (x ∪ x') ∩ x'' = (x ∩ x'') ∪ (x' ∩ x'') := by ext; simp only [mem_union_iff,
  mem_inter_iff, or_and_right]

@[simp] theorem inter_union_absorb_right_right : x ∩ (x' ∪ x) = x := by
  ext
  simp only [mem_inter_iff, mem_union_iff, and_iff_left_iff_imp]
  exact Or.inr
@[simp] theorem inter_union_absorb_right_left : x ∩ (x ∪ x') = x := by
  rw[union_comm, inter_union_absorb_right_right]
@[simp] theorem inter_union_absorb_left_right : (x' ∪ x) ∩ x = x := by
  rw[inter_comm, inter_union_absorb_right_right]
@[simp] theorem inter_union_absorb_left_left : (x ∪ x') ∩ x = x := by
  rw[inter_comm, inter_union_absorb_right_left]

@[simp] theorem union_inter_absorb_right_right : x ∪ (x' ∩ x) = x := by
  ext
  simp only [mem_union_iff, mem_inter_iff, or_iff_left_iff_imp, and_imp, imp_self, implies_true]
@[simp] theorem union_inter_absorb_right_left : x ∪ (x ∩ x') = x := by
  rw[inter_comm, union_inter_absorb_right_right]
@[simp] theorem union_inter_absorb_left_right : (x' ∩ x) ∪ x = x := by
  rw[union_comm, union_inter_absorb_right_right]
@[simp] theorem union_inter_absorb_left_left : (x ∩ x') ∪ x = x := by
  rw[union_comm, union_inter_absorb_right_left]

@[simp] theorem union_univ : x ∪ univ = univ := by simp only [union_eq_iff_subset_right,
  subset_univ]
@[simp] theorem univ_union : univ ∪ x = univ := by simp only [union_eq_iff_subset_left,
  subset_univ]
@[simp] theorem union_empty : x ∪ ∅ = x := by simp only [union_eq_iff_subset_left, empty_subset]
@[simp] theorem empty_union : ∅ ∪ x = x := by simp only [union_eq_iff_subset_right,
  empty_subset]

@[simp] theorem inter_univ : x ∩ univ = x := by simp only [inter_eq_iff_subset_left, subset_univ]
@[simp] theorem univ_inter : univ ∩ x = x := by simp only [inter_eq_iff_subset_right, subset_univ]
@[simp] theorem inter_empty : x ∩ ∅ = ∅ := by simp only [inter_eq_iff_subset_right,
  empty_subset]
@[simp] theorem empty_inter : ∅ ∩ x = ∅ := by simp only [inter_eq_iff_subset_left,
  empty_subset]

@[simp] theorem compl_empty : ∅ᶜ = (univ : Set α) := by ext; simp only [mem_compl_iff,
  not_mem_empty, not_false_eq_true, mem_univ]
@[simp] theorem compl_univ : univᶜ = (∅ : Set α) := by ext; simp only [mem_compl_iff, mem_univ,
  not_true_eq_false, not_mem_empty]

theorem compl_inter : (x ∩ x')ᶜ = xᶜ ∪ x'ᶜ := by
  ext
  simp only [mem_compl_iff, mem_inter_iff, not_and, mem_union_iff]
  rw[Classical.or_iff_not_imp_left, Classical.not_not]

theorem compl_union : (x ∪ x')ᶜ = xᶜ ∩ x'ᶜ := by
  ext
  simp only [mem_compl_iff, mem_union_iff, not_or, mem_inter_iff]

theorem sdiff_union : x \ (x' ∪ x'') = (x \ x') ∩ (x \ x'') := by
  ext
  simp only [mem_sdiff_iff, mem_union_iff, not_or, mem_inter_iff]
  exact and_and_left

theorem sdiff_inter : x \ (x' ∩ x'') = (x \ x') ∪ (x \ x'') := by
  ext
  simp only [mem_sdiff_iff, mem_inter_iff, not_and, mem_union_iff]
  rw[imp_iff_not_imp_not, ← Classical.or_iff_not_imp_left, and_or_left, or_comm]

@[simp] theorem sdiff_empty : x \ ∅ = x := by ext; simp only [mem_sdiff_iff, not_mem_empty,
  not_false_eq_true, and_true]
@[simp] theorem empty_sdiff : ∅ \ x = ∅ := by ext; simp only [mem_sdiff_iff, not_mem_empty, false_and]
@[simp] theorem sdiff_self : x \ x = ∅ := by ext; simp only [mem_sdiff_iff, and_not_self,
  not_mem_empty]
theorem sdiff_eq_inter_compl : x \ x' = x ∩ x'ᶜ := by ext; simp only [mem_sdiff_iff, mem_inter_iff,
  mem_compl_iff]

theorem union_sdiff : (x ∪ x') \ x'' = x \ x'' ∪ x' \ x'' := by ext; simp only [mem_sdiff_iff,
  mem_union_iff, or_and_right]
theorem inter_sdiff : (x ∩ x') \ x'' = (x \ x'') ∩ (x' \ x'') := by ext; simp only [mem_sdiff_iff,
  mem_inter_iff, and_assoc, and_congr_right_iff, iff_and_self, and_imp, imp_self, implies_true]
theorem sdiff_sdiff_right : x \ (x' \ x'') = (x \ x') ∪ (x ∩ x'') := by
  ext
  simp only [mem_sdiff_iff, not_and, Classical.not_not, mem_union_iff, mem_inter_iff]
  classical
  rw[Decidable.imp_iff_not_or]
  rw[and_or_left]

theorem sdiff_sdiff_left : (x \ x') \ x'' = x \ (x' ∪ x'') := by ext; simp only [mem_sdiff_iff,
  and_assoc, mem_union_iff, not_or]

-- TODO interaction sdiff,inter,union vs iInter, iUnion

@[simp] theorem union_with_compl : x ∪ xᶜ = Set.univ := by ext; simp only [mem_union_iff, mem_compl_iff,
  Classical.em, mem_univ]

@[simp] theorem inter_with_compl : x ∩ xᶜ = ∅ := by ext; simp only [mem_inter_iff, mem_compl_iff,
  and_not_self, not_mem_empty]

theorem union_mono (h : x ⊆ x') (h' : x'' ⊆ x''') : x ∪ x'' ⊆ x' ∪ x''' := fun _ h'' =>
    h''.elim (Or.inl ∘ @h _) (Or.inr ∘ @h' _)

theorem union_mono_left (h : x ⊆ x') : x ∪ x'' ⊆ x' ∪ x'' := union_mono h subset_rfl
theorem union_mono_right (h : x' ⊆ x'') : x ∪ x' ⊆ x ∪ x'' := union_mono subset_rfl h

theorem inter_mono (h : x ⊆ x') (h' : x'' ⊆ x''') : x ∩ x'' ⊆ x' ∩ x''' := fun _ h'' =>
    ⟨h h''.1, h' h''.2⟩

theorem inter_mono_left (h : x ⊆ x') : x ∩ x'' ⊆ x' ∩ x'' := inter_mono h subset_rfl
theorem inter_mono_right (h : x' ⊆ x'') : x ∩ x' ⊆ x ∩ x'' := inter_mono subset_rfl h

theorem sdiff_mono_left (h : x ⊆ x') : x \ x'' ⊆ x' \ x'' := by
  intro a
  simp only [mem_sdiff_iff, and_imp]
  intro h' h''
  exact ⟨h h', h''⟩

theorem sdiff_mono_right (h : x' ⊆ x'') : x \ x'' ⊆ x \ x' := by
  intro a
  simp only [mem_sdiff_iff, and_imp]
  intro h' h''
  exact ⟨h', h'' ∘ @h a⟩

@[simp] theorem sdiff_subset : x \ x' ⊆ x := fun _ h => h.1
@[simp] theorem sdiff_subset_compl : x \ x' ⊆ x'ᶜ := fun _ h => h.2

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

variable {x x' : Set α} {y y' : Set β}
theorem Relation.union_image : r.image (x ∪ x') = r.image x ∪ r.image x' := by
  ext _
  simp only [mem_image_iff, Set.mem_union_iff, and_or_left]
  apply exists_or

theorem Relation.subset_inter_image : r.image (x ∩ x') ⊆ r.image x ∩ r.image x' := by
  intro b
  simp only [mem_image_iff, Set.mem_inter_iff, forall_exists_index, and_imp]
  intro a' h h' h''
  exact ⟨⟨_,h,h'⟩,⟨_,h,h''⟩⟩

theorem Relation.union_preimage : r.preimage (y ∪ y') = r.preimage y ∪ r.preimage y' := by
  simp only [← image_inv, union_image]

theorem Relation.subset_inter_preimage : r.preimage (y ∩ y') ⊆ r.preimage y ∩ r.preimage y' := by
  simp only [← image_inv, subset_inter_image]
end

namespace Set
section
variable {f : α → β}
theorem iUnion_image : Set.image f (⋃ i, x i) = ⋃ i, Set.image f (x i) := Relation.iUnion_image
theorem iUnion_preimage : Set.preimage f (⋃ i, y i) = ⋃ i, Set.preimage f (y i) := Relation.iUnion_preimage
theorem subset_iInter_image : Set.image f (⋂ i, x i) ⊆ ⋂ i, Set.image f (x i) := Relation.subset_iInter_image
theorem iInter_preimage : Set.preimage f (⋂ i, y i) = ⋂ i, Set.preimage f (y i) := by
  apply subset_antisym
  · apply Relation.subset_iInter_preimage
  · intro a h
    simp only [mem_iInter_iff, mem_preimage_iff] at h
    simpa only [mem_preimage_iff, mem_iInter_iff] using h
theorem iInter_image_of_inj [Nonempty ι] (h : f.Injective) : Set.image f (⋂ i, x i) = ⋂ i, Set.image f (x i) := by
  apply subset_antisym
  · exact subset_iInter_image
  · intro b
    simp only [mem_iInter_iff, mem_image_iff]
    intro h'
    obtain ⟨a,h'a,ha⟩ := h' (Classical.choice (by infer_instance))
    exists a
    constructor
    · assumption
    · intro i
      obtain ⟨a',ha',h'a'⟩ := h' i
      rw[h'a] at ha'
      replace ha' := h _ _ ha'
      rwa[← ha'] at h'a'
variable {x x' : Set α} {y y' : Set β}

theorem union_image : Set.image f (x ∪ x') = Set.image f x ∪ Set.image f x' := Relation.union_image
theorem union_preimage : Set.preimage f (y ∪ y') = Set.preimage f y ∪ Set.preimage f y' := Relation.union_preimage
theorem subset_inter_image : Set.image f (x ∩ x') ⊆ Set.image f x ∩ Set.image f x' := Relation.subset_inter_image
theorem inter_preimage : Set.preimage f (y ∩ y') = Set.preimage f y ∩ Set.preimage f y' := by
  apply subset_antisym
  · apply Relation.subset_inter_preimage
  · intro a
    simp only [mem_inter_iff, mem_preimage_iff, imp_self]

theorem sdiff_preimage : Set.preimage f (y \ y') = Set.preimage f y \ Set.preimage f y' := by
  ext a
  simp only [mem_preimage_iff, mem_sdiff_iff]

theorem compl_preimage : Set.preimage f (yᶜ) = (Set.preimage f y)ᶜ := by
  ext a
  simp only [mem_preimage_iff, mem_compl_iff]

theorem sdiff_image_inj (h : f.Injective) : Set.image f (x \ x') = Set.image f x \ Set.image f x' := by
  ext b
  simp only [mem_image_iff, mem_sdiff_iff, not_exists, not_and]
  constructor
  · rintro ⟨a, h', h'', h'''⟩
    constructor
    · exists a
    · rintro x rfl
      rwa[← h _ _ h'] at h'''
  · rintro ⟨⟨a,rfl,h'⟩, h''⟩
    exists a
    specialize h'' a rfl
    constructor <;> trivial
end
