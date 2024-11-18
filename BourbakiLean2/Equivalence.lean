import BourbakiLean2.Set.Rel
import BourbakiLean2.Function.Basic
attribute [class] Equivalence
namespace Relation
variable {α : Type*} {r : Relation α α}
abbrev IsEquivalence (r : Relation α α) := Equivalence (fun a b => (a,b) ∈ r)

instance : IsEquivalence (Set.univ : Relation α α) where
  refl _ := trivial
  symm _ := trivial
  trans _ _ := trivial

instance : IsEquivalence (diag : Relation α α) where
  refl _ := rfl
  symm := Eq.symm
  trans := Eq.trans

instance : IsEquivalence (fun ⟨a, b⟩ => Nonempty (Function.Bijection a b)) where
  refl a := ⟨_, Function.bij_id⟩
  symm h := h.elim (fun h => ⟨h.inv⟩)
  trans h1 h2 := by
    dsimp only at h1 h2
    rcases h1 with ⟨f,h1⟩
    rcases h2 with ⟨g,h2⟩
    constructor
    exists g ∘ f
    apply h2.comp h1

theorem isEquivalence_in_set_or_compl (x : Set α) : IsEquivalence
    (fun ⟨a,b⟩ => a ∈ x ↔ b ∈ x) where
  refl _ := Iff.rfl
  symm := Iff.symm
  trans := Iff.trans

theorem isEquivalence_iff :
    r.IsEquivalence ↔ (r.domain = Set.univ ∧ r.inv = r ∧ r.comp r = r) := by
  constructor
  · intro h
    constructor
    · rw[← Set.univ_subset_iff]
      intro a _
      exact ⟨a, h.refl a⟩
    · constructor
      · ext ⟨a,a'⟩
        exact ⟨h.symm, h.symm⟩
      · ext ⟨a,a'⟩
        constructor
        · simp only [mem_comp_iff, forall_exists_index, and_imp]
          exact fun a h' h'' => h.trans h' h''
        · intro h'
          exists a
          exact ⟨h.refl a, h'⟩
  · intro ⟨h,h',h''⟩
    constructor
    · intro a
      rw[Set.ext_iff] at h
      replace h := (h a).mpr trivial
      obtain ⟨b,h⟩ := h
      replace h' := h' ▸ h
      have h''' : (a,a) ∈ r.comp r := ⟨b,h,h'⟩
      rwa[h''] at h'''
    · intro a a' h
      rwa[← h']
    · intro a a' a'' h0 h1
      have h''' : (a,a'') ∈ r.comp r := ⟨a',h0,h1⟩
      rwa[h''] at h'''

end Relation
variable {α β : Type*} {f : α → β} {r : Relation α α}
@[reducible] def Function.identified_under (f : α → β) : Relation α α := fun a => f a.1 = f a.2

@[simp] theorem Function.mem_identified_under {a a' : α} : ⟨a,a'⟩ ∈ f.identified_under ↔ f a = f a' := Iff.rfl
instance Function.identified_under.isEquivalence : f.identified_under.IsEquivalence where
  refl _ := rfl
  symm := Eq.symm
  trans := Eq.trans

@[simp] theorem Quot.mk_eq_iff_rel [h : Relation.IsEquivalence r] {a b : α}: Quot.mk r.curry a = Quot.mk r.curry b ↔ ⟨a,b⟩ ∈ r := by
  constructor
  · intro h'
    let rLift := Quot.lift (f := fun b => (a,b) ∈ r) (r := r.curry)
      (fun a b h' => propext ⟨fun h'' => h.trans h'' h', fun h'' => h.trans h'' (h.symm h')⟩)
    have eq := Quot.liftBeta (f := fun b => (a,b) ∈ r) (r := r.curry) (fun a b h' => propext ⟨fun h'' => h.trans h'' h', fun h'' => h.trans h'' (h.symm h')⟩) b
    rw[← eq, ← h']
    exact h.refl _
  · intro h'
    apply Quot.sound
    exact h'

@[simp] theorem Relation.IsEquivalence.eq_identified_under [h : Relation.IsEquivalence r] : (Quot.mk r.curry).identified_under = r := by
  ext ⟨a,b⟩
  simp only [Function.mem_identified_under, Quot.mk_eq_iff_rel]

def Relation.equiv_class (r : Relation α α) (a : α) := {a' | (a,a') ∈ r ∧ (a', a) ∈ r}

@[simp] theorem Relation.IsEquivalence.mem_equiv_class_iff [h : IsEquivalence r] {a a' : α} : a ∈ r.equiv_class a' ↔ ⟨a', a⟩ ∈ r :=
  ⟨And.left, fun a => ⟨a, h.symm a⟩⟩

@[simp] theorem Relation.IsEquivalence.equiv_class_eq_iff {a a' : α} [h : IsEquivalence r] : r.equiv_class a = r.equiv_class a' ↔ ⟨a, a'⟩ ∈ r := by
  constructor
  · simp only [equiv_class, Set.setOf_eq_setOf_iff]
    intro h'
    apply And.right
    apply (h' a).mp
    exact ⟨h.refl _, h.refl _⟩
  · intro h'
    ext b
    simp
    exact ⟨h.trans (h.symm h'),h.trans h'⟩

theorem Relation.IsEquivalence.mem_equiv_class_swap [h : IsEquivalence r] {a a' : α} : a ∈ r.equiv_class a' ↔ a' ∈ r.equiv_class a := by
  simp only [mem_equiv_class_iff]
  exact ⟨h.symm, h.symm⟩



def Relation.IsEquivalence.quot_equiv_class_bij [h : r.IsEquivalence] : Function.Bijection (Quot r.curry) (Set.univ.image r.equiv_class) := by
  exists Quot.lift ((fun a => (r.equiv_class a)).corestrict (Set.subset_refl _)) (by
    intro a b
    simp only [Function.curry_apply, Subtype.eq_iff, Function.coe_corestrict, equiv_class_eq_iff]
    exact id)
  constructor
  · rintro ⟨a⟩ ⟨a'⟩
    simp only [Subtype.eq_iff, Function.coe_corestrict, equiv_class_eq_iff, Quot.mk_eq_iff_rel,
      imp_self]
  · rw[Function.surj_iff]
    rintro ⟨b,h'⟩
    replace ⟨a, ⟨h', _⟩⟩ := h'
    simp only [mem_graph_iff] at h'
    rcases h'
    exists Quot.mk _ a

@[simp] theorem Relation.equiv_class_diag {a} : (diag : Relation α α).equiv_class a = {a} := by
  ext
  simp only [IsEquivalence.mem_equiv_class_iff, mem_diag_iff, Set.mem_singleton_iff, Eq.comm]


@[simp] theorem Relation.equiv_class_univ {a} : Relation.equiv_class (Set.univ : Relation α α) a = Set.univ := by
  ext
  simp only [IsEquivalence.mem_equiv_class_iff, Set.mem_univ]
