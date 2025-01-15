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

theorem iUnion_singletons {x : Set α} : ⋃ a : x, {a.1} = x := by
  ext a
  simp only [mem_iUnion_iff, mem_singleton_iff, Subtype.exists, exists_prop, exists_eq_right']

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

variable {y' : ι' → Set β}
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

theorem sprod_iUnion : (⋃ i, x i).prod (⋃ i, y' i) = ⋃ j : ι × ι', (x j.1).prod (y' j.2) := by
  ext ⟨a,b⟩
  simp only [mem_prod_iff, mem_iUnion_iff, Prod.exists, exists_and_left, exists_and_right]

theorem sprod_iInter [inst : Nonempty ι] [inst' : Nonempty ι'] : (⋂ i, x i).prod (⋂ i, y' i) = ⋂ j : ι × ι', (x j.1).prod (y' j.2) := by
  ext ⟨a,b⟩
  simp only [mem_prod_iff, mem_iInter_iff, Prod.forall]
  exact ⟨fun ⟨h, h'⟩ a b => ⟨h a, h' b⟩,
      fun h => ⟨fun a => (h a (Classical.choice inst')).1,
                fun a => (h (Classical.choice inst) a).2⟩⟩


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
theorem compl_inj (h : xᶜ = x'ᶜ) : x = x' := by
  rw[← compl_compl (x := x), ← compl_compl (x := x'), h]

theorem eq_compl_of (h : x ∪ x' = Set.univ) (h' : x ∩ x' = ∅) : x' = x ᶜ := by
  ext a
  constructor
  · intro h'' h'''
    have : a ∈ x ∩ x' := ⟨h''',h''⟩
    rwa[h'] at this
  · intro h''
    by_contra h'''
    have : a ∈ univ := trivial
    rw[← h] at this
    rcases this with (t|t)
    · exact h'' t
    · exact h''' t

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

variable {γ : Type*} {r : ι → Relation α β} {s : Relation β γ} {t : Relation γ α}

theorem Relation.rel_iUnion_image : Relation.image (⋃ i, r i) x = ⋃ i, (r i).image x := by
  ext a
  simp only [mem_image_iff, Set.mem_iUnion_iff, exists_comm, exists_and_right]

theorem Relation.rel_iUnion_preimage : Relation.preimage (⋃ i, r i) y = ⋃ i, (r i).preimage y := by
  ext a
  simp only [mem_preimage_iff, Set.mem_iUnion_iff, exists_comm, exists_and_right]

theorem Relation.rel_iInter_image {a} : Relation.image (⋂ i, r i) {a} = ⋂ i, (r i).image {a} := by
  ext a
  simp only [mem_image_iff, Set.mem_iInter_iff, Set.mem_singleton_iff, exists_eq_right]

theorem Relation.rel_iInter_preimage {b} : Relation.preimage (⋂ i, r i) {b} = ⋂ i, (r i).preimage {b} := by
  ext a
  simp only [mem_preimage_iff, Set.mem_iInter_iff, Set.mem_singleton_iff, exists_eq_right]

theorem Relation.iUnion_comp : Relation.comp (⋃ i, r i) t = ⋃ i, (r i).comp t := by
  ext ⟨_,_⟩
  simp only [mem_comp_iff, Set.mem_iUnion_iff, exists_comm, exists_and_left]

theorem Relation.comp_iUnion : Relation.comp s (⋃ i, r i) = ⋃ i, s.comp (r i) := by
  ext ⟨_,_⟩
  simp only [mem_comp_iff, Set.mem_iUnion_iff, exists_comm, exists_and_right]

variable {r r' : Relation α β}

theorem Relation.union_comp : Relation.comp (r ∪ r') t = r.comp t ∪ r'.comp t := by
  ext ⟨_,_⟩
  simp only [mem_comp_iff, Set.mem_union_iff, exists_or, and_or_left]

theorem Relation.comp_union : Relation.comp s (r ∪ r') = s.comp r ∪ s.comp r' := by
  ext ⟨_,_⟩
  simp only [mem_comp_iff, Set.mem_union_iff, or_and_right, exists_or]

theorem Relation.rel_union_image : Relation.image (r ∪ r') x = r.image x ∪ r'.image x := by
  ext a
  simp only [mem_image_iff, Set.mem_union_iff, or_and_right, exists_or]

theorem Relation.rel_union_preimage : Relation.preimage (r ∪ r') y = r.preimage y ∪ r'.preimage y := by
  ext a
  simp only [mem_preimage_iff, Set.mem_union_iff, or_and_right, exists_or]

theorem Relation.rel_inter_image {a} : Relation.image (r ∩ r') {a} = r.image {a} ∩ r'.image {a} := by
  ext a
  simp only [mem_image_iff, Set.mem_inter_iff, Set.mem_singleton_iff, exists_eq_right]

theorem Relation.rel_inter_preimage {b} : Relation.preimage (r ∩ r') {b} = r.preimage {b} ∩ r'.preimage {b} := by
  ext a
  simp only [mem_preimage_iff, Set.mem_inter_iff, Set.mem_singleton_iff, exists_eq_right]

theorem Relation.comp_inter_subset {t : Relation α γ} :
    (s.comp r) ∩ t ⊆ (s ∩ (t.comp r.inv)).comp (r ∩ (s.inv.comp t)) := by
  rintro ⟨a,c⟩ h
  simp only [Set.mem_inter_iff, mem_comp_iff, mem_inv_iff] at *
  obtain ⟨⟨b,h,h'⟩,h''⟩ := h
  exists b
  constructor
  · constructor
    · assumption
    · exists c
  · constructor
    · assumption
    · exists a

end

namespace Set
section
variable {f : α → β}
@[simp] def Disjoint (x : ι → Set α) := ∀ i i', i ≠ i' → x i ∩ x i' = ∅

theorem Disjoint.eq_of_subset_elem {x : ι → Set α} (hd : Disjoint x) {y : Set α} (h : y.Nonempty)
    {i i'} (ha : a ∈ x i) (ha' : a ∈ y) (h'' : y ⊆ x i') : i = i' := by
  specialize h'' ha'
  by_contra hne
  specialize hd _ _ hne
  have : a ∈ x i ∩ x i' := ⟨ha,h''⟩
  rw[hd] at this
  exact this

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

theorem Disjoint.preimage {y : ι → Set β} (h : Disjoint y) : Disjoint (Set.preimage f ∘ y) := by
  intro i j h'
  simp only [Function.comp_apply, ← inter_preimage]
  rw[h _ _ h']
  simp only [Function.preimage_empty]

theorem Disjoint.inj_of_nonempty {x : ι → Set α} (h : Disjoint x) (h' : ∀ i, (x i).Nonempty) : x.Injective := by
  intro i j h''
  by_contra h'''
  replace h := h i j h'''
  rw[h''] at h
  simp only [inter_self] at h
  specialize h' j
  rw[h] at h'
  simp only [empty_not_nonempty] at h'

end


namespace Set
variable {α ι : Type*} {ι' : ι → Type} {x : (i : ι) → ι' i → Set α}

theorem iUnion_iInter_distrib :
    ⋃ i : ι, ⋂ i' : ι' i, x i i' =  ⋂ f : (i : ι) → ι' i, ⋃ i : ι, x i (f i) := by
  ext a
  simp only [mem_iUnion_iff, mem_iInter_iff]
  constructor
  · intro ⟨i, h'⟩ i'
    specialize h' (i' i)
    exists i
  · rw[imp_iff_not_imp_not]
    intro h' h''
    conv at h' =>
      rw[not_exists]
      intro
      rw[Classical.not_forall]
    replace ⟨f,h'⟩ := Classical.axiomOfChoice h'
    replace ⟨i,h''⟩ := h'' f
    apply h' _ h''

theorem iInter_iUnion_distrib :
    ⋂ i : ι, ⋃ i' : ι' i, x i i' = ⋃ f : (i : ι) → ι' i, ⋂ i : ι, x i (f i) := by
  apply compl_inj
  conv =>
    rw[← iInter_compl, ← iUnion_compl]
    lhs
    intro
    lhs
    intro
    rw[← iInter_compl]
  conv =>
    rhs
    intro
    lhs
    intro
    rw[← iUnion_compl]
  rw[iUnion_iInter_distrib]

variable {α ι ι' : Type*} {x : ι → Set α} {x' : ι' → Set α}
theorem iInter_union_distrib :
    (⋂ i, x i) ∪ (⋂ i', x' i') = ⋂ ii' : ι × ι', x ii'.1 ∪ x' ii'.2 := by
  ext a
  simp only [mem_union_iff, mem_iInter_iff, Prod.forall]
  constructor
  · rintro (h|h) i i'
    · exact Or.inl (h i)
    · exact Or.inr (h i')
  · intro h
    by_contra h'
    rw[not_or, Classical.not_forall, Classical.not_forall] at h'
    obtain ⟨⟨i,h'⟩, ⟨i', h''⟩⟩ := h'
    rcases (h i i') with (h|h)
    · exact h' h
    · exact h'' h

theorem iUnion_inter_distrib :
    (⋃ i, x i) ∩ (⋃ i', x' i') = ⋃ ii' : ι × ι', x ii'.1 ∩ x' ii'.2 := by
  apply compl_inj
  rw[compl_inter, ← iInter_compl, ← iInter_compl,
    ← iInter_compl, iInter_union_distrib]
  conv =>
    arg 1
    arg 1
    intro
    rw[← compl_inter]

end Set
