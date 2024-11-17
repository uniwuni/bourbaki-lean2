import BourbakiLean2.Set.Operations
import BourbakiLean2.Function.Prod
variable {α ι ι' β : Type*} {x : ι → Type*}

def iProd (y : (i : ι) → Set (x i)) : Set ((i : ι) → x i) :=
  {f | ∀ i, f i ∈ y i}

@[simp] def mem_iProd_iff {y : (i : ι) → Set (x i)} {a : (i : ι) → x i} :
  a ∈ iProd y ↔ ∀ i, a i ∈ y i := Iff.rfl

section
open Lean Elab Term Meta Batteries.ExtendedBinder
syntax (name := iProdBuilder) "Πˢ " extBinder ", " term:51 : term
@[term_elab iProdBuilder]
def elabiProdBuilder : TermElab
  | `(Πˢ $x:ident , $p ), expectedType? => do
    elabTerm (← `(iProd fun $x:ident ↦ $p)) expectedType?
  | `(Πˢ $x:ident : $t , $p ), expectedType? => do
    elabTerm (← `(iProd fun $x:ident : $t ↦ $p)) expectedType?
  | `(Πˢ $x:ident $b:binderPred , $p ), expectedType? => do
    elabTerm (← `(iProd fun $x:ident ↦ satisfies_binder_pred% $x $b ∧ $p)) expectedType?
  | _, _ => throwUnsupportedSyntax

@[app_unexpander iProd]
def iProd.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident ↦ $p) => `(Πˢ $x:ident , $p )
  | `($_ fun ($x:ident : $ty:term) ↦ $p) => `(Πˢ $x:ident : $ty , $p )
  | _ => throw ()

namespace Set.Product
/- we show that we dont have to care about this shit for most stuff -/
variable {y : (i : ι) → Set (x i)}
theorem subset_iProd_image_proj {a : Set ((i : ι) → x i)} :
    a ⊆ (Πˢ i, Set.image (fun s => s i) a) := by
  intro f h i
  simp only [mem_image_iff, Subtype.eq_iff]
  exists f

def iProd_to_prod {y : (i : ι) → Set (x i)} (p : iProd y) (i : ι) : y i :=
  ⟨p.1 i, p.2 i⟩

def prod_to_iProd {y : (i : ι) → Set (x i)} (p : (i : ι) → y i) : iProd y :=
  ⟨fun i => p i, fun i => (p i).2⟩

theorem prod_to_iProd_inverse {y : (i : ι) → Set (x i)} :
    (iProd_to_prod (y := y)).IsInverseOf prod_to_iProd := by
  constructor
  · ext p i
    simp only [Function.comp_apply, iProd_to_prod, prod_to_iProd, id_eq]
  · ext p i
    simp only [Function.comp_apply, iProd_to_prod, prod_to_iProd, id_eq]

variable {α ι : Type*} {ι' : ι → Type*} {x : (i : ι)→ Type*}
  {y : (i : ι) → (i' : ι' i) → Set (x i)}

@[simp] theorem iProd_univ : Πˢ i : ι, (Set.univ : Set (x i)) = Set.univ := by
  ext a
  simp only [mem_iProd_iff, mem_univ, implies_true]

theorem iProd_iUnion_distrib :
    Πˢ i : ι, (⋃ i' : ι' i, y i i') = ⋃ i'' : (i : ι) → ι' i, Πˢ i, y i (i'' i) := by
  ext a
  simp only [mem_iProd_iff, mem_iUnion_iff]
  constructor
  · apply Classical.axiomOfChoice (r := fun x x'=> a x ∈ y x x')
  · rintro ⟨i,h⟩ i'
    exists i i'
    apply h

theorem iProd_iInter_distrib (ne : ∀ i, Nonempty (ι' i)):
    Πˢ i : ι, (⋂ i' : ι' i, y i i') = ⋂ i'' : (i : ι) → ι' i, Πˢ i, y i (i'' i) := by
  ext a
  simp only [mem_iProd_iff, mem_iUnion_iff]
  constructor
  · intro h i' i
    apply_assumption
  · simp only [mem_iInter_iff, mem_iProd_iff]
    intro h i i'
    classical
    let f : (i : ι) → ι' i := fun i'' => if h' : i = i'' then h' ▸ i' else Classical.choice (ne i'')
    specialize h f i
    simp only [↓reduceDIte, f] at h
    exact h

theorem iProd_iInter_two_distrib {ι' : Type*} {x : ι → Type*}
  {y : (i : ι) → (i' : ι') → Set (x i)} :
    ⋂ i', Πˢ i, y i i' = Πˢ i : ι, ⋂ i', y i i' := by
  ext a
  simp only [mem_iInter_iff, mem_iProd_iff]
  exact forall_comm

theorem iProd_inter_distrib {x : ι → Type*} {y y' : (i : ι) → Set (x i)} :
    (Πˢ i, y i) ∩ (Πˢ i, y' i) = Πˢ i, y i ∩ y' i := by
  ext a
  simp only [mem_inter_iff, mem_iProd_iff, forall_and]

theorem iInter_prod_distrib {α : Type*} {y y' : (i : ι) → Set α} :
    (⋂ i, y i).prod (⋂ i, y' i) = ⋂ i, (y i).prod (y' i) := by
  ext ⟨a,b⟩
  simp only [mem_prod_iff, mem_iInter_iff, forall_and]

end Product

variable {α ι : Type*} {ι' : ι → Type*} {x : (i : ι) → Type*}
  {y : (i : ι) → (i' : ι' i) → Set (x i)}
theorem Set.prod_isCovering (h : ∀ i, Set.IsCovering (y i)) :
    Set.IsCovering (fun (i' : (i : ι) → ι' i) => Πˢ i : ι, y i (i' i)) := by
  rw[IsCovering, ← Product.iProd_iUnion_distrib]
  conv =>
    lhs
    rhs
    intro i
    rw[h i]
  exact Product.iProd_univ

theorem Set.prod_disjoint  (h : ∀ i, Set.Disjoint (y i)) :
    Set.Disjoint (fun (i' : (i : ι) → ι' i) => Πˢ i : ι, y i (i' i)) := by
  intro i' i'' neq
  ext a
  simp only [mem_inter_iff, mem_iProd_iff, not_mem_empty, iff_false, not_and, Classical.not_forall]
  intro h'
  apply Classical.exists_not_of_not_forall
  intro h''
  obtain ⟨i,neq⟩ : ∃ i, i' i ≠ i'' i := by
    rw[Ne, funext_iff] at neq
    apply Classical.exists_not_of_not_forall neq
  specialize h' i
  specialize h'' i
  specialize h i (i' i) (i'' i) neq
  have h' : a i ∈ y _ _ ∩ y _ _ := ⟨h',h''⟩
  rwa[h] at h'

theorem Set.prod_isPartition (h : ∀ i, Set.IsPartition (y i)) :
    Set.IsPartition (fun (i' : (i : ι) → ι' i) => Πˢ i : ι, y i (i' i)) := by
  constructor
  · apply Set.prod_isCovering
    exact fun x => (h x).left
  · apply Set.prod_disjoint
    exact fun x => (h x).right
