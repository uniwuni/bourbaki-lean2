import BourbakiLean2.Set.Operations

variable {α ι ι' β : Type*} {x : ι → Set α}

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
/- we show that we dont have to care about this shit -/
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

end Product
