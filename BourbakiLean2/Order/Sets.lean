import BourbakiLean2.Order.MaxMin
import BourbakiLean2.Order.GlbLub
import BourbakiLean2.Order.Monotone

variable {α : Type*}
namespace Set
@[simp] theorem greatest_iff_univ {x : Set α} : Greatest x ↔ x = Set.univ := by
  constructor
  · intro h
    rw[Set.eq_iff_subset_subset]
    simp only [Set.subset_univ, true_and]
    exact h Set.univ
  · rintro rfl x a h
    trivial
@[simp] theorem least_iff_empty {x : Set α} : Least x ↔ x = ∅ := by
  constructor
  · intro h
    specialize h ∅
    simpa only [← Set.subset_empty_iff]
  · rintro rfl a
    exact Set.empty_subset

theorem minimal_iff_singleton_nonempty {x : {x : Set α // x.Nonempty}} :
    Minimal x ↔ ∃ a, x = ⟨{a}, ⟨a, rfl⟩⟩ := by
  constructor
  · intro h
    rcases x with ⟨x,⟨a,ha⟩⟩
    exists a
    exact Eq.symm $ h ⟨{a}, ⟨a,rfl⟩⟩ (fun _ eq => eq ▸ ha)
  · rintro ⟨a,rfl⟩
    intro ⟨y,⟨b,hb⟩⟩ h'
    simp only [Subtype.le_iff_val, le_set_iff_subset, Set.subset_singleton_iff] at h'
    rcases h' with (h'|h')
    · simp only [h']
    · rw[h'] at hb
      exact hb.elim

theorem intersection_least_of_mem {p : Set α → Prop} (h : p (⋂ a : {x // p x}, a)) :
    Least (⟨(⋂ a : {x // p x}, a), h⟩ : {x // p x}) := by
  rintro ⟨x, h'⟩
  simp only [Subtype.le_iff_val, le_set_iff_subset]
  have : (⋂ a : {x // p x}, a) ⊆ (⟨x,h'⟩ : {x // p x}).val := Set.iInter_subset
  exact this

theorem union_greatest_of_mem {p : Set α → Prop} (h : p (⋃ a : {x // p x}, a)) :
    Greatest (⟨(⋃ a : {x // p x}, a), h⟩ : {x // p x}) := by
  rintro ⟨x, h'⟩
  simp only [Subtype.le_iff_val, le_set_iff_subset]
  have : (⟨x,h'⟩ : {x // p x}).val ⊆ (⋃ a : {x // p x}, a) := Set.subset_iUnion
  exact this

theorem least_eq_intersection {p : Set α → Prop} {x : {x // p x}} (h : Least x) :
    x.val = ⋂ a : {x // p x}, a := by
  rw[Set.eq_iff_subset_subset]
  constructor
  · rwa[Set.subset_iInter_iff_all]
  · apply Set.iInter_subset

theorem greatest_eq_union {p : Set α → Prop} {x : {x // p x}} (h : Greatest x) :
    x.val = ⋃ a : {x // p x}, a := by
  rw[Set.eq_iff_subset_subset]
  constructor
  · apply Set.subset_iUnion
  · rwa[Set.iUnion_subset_iff_all]

@[simp] theorem iInter_isGLB {s : Set (Set α)} : IsGLB s (⋂ a : s, a) := by
  simp only [IsGLB, Greatest, LowerBound, Subtype.le_iff_val, le_set_iff_subset,
    subset_iInter_iff_all, Subtype.forall, imp_self, implies_true, exists_prop, and_true]
  intro b hb
  have : ⋂ a : s, a ⊆ (⟨b,hb⟩ : s).val := iInter_subset
  exact this

@[simp] theorem iUnion_isLUB {s : Set (Set α)} : IsLUB s (⋃ a : s, a) := by
  simp only [IsLUB, Least, UpperBound, Subtype.le_iff_val, le_set_iff_subset, iUnion_subset_iff_all,
    Subtype.forall, imp_self, implies_true, exists_prop, and_true]
  intro b hb
  have : (⟨b,hb⟩ : s).val ⊆ ⋃ a : s, a := subset_iUnion
  exact this


end Set
