import BourbakiLean2.Set.FiniteCardinal
universe u v
variable {α β ι : Type*} {x : ι → Type*}

namespace Finite
noncomputable def ftype (x : Type*) [h : Finite x] : FiniteType := ⟨x, h⟩
@[simp] theorem ftype_finiteType_val (x : FiniteType.{u}) :
  ftype (h := x.property) x.val = x := rfl

end Finite


namespace FiniteType
noncomputable def cardinality (x : FiniteType.{u}) : Nat := FiniteCardinal.to_nat $ x.cardinality'

@[simp high] theorem cardinality_empty : (Finite.ftype Empty).cardinality = 0 := by
  simp only [cardinality, cardinality', Finite.ftype]
  suffices h : Cardinal.mk Empty = 0 by
    rw[← FiniteCardinal.to_nat_of_nat (n := 0)]
    congr
  simp only [Cardinal.eq_zero_iff]
  exact Empty.elim

@[simp high] theorem cardinality_empty_set : (Finite.ftype (∅ : Set α)).cardinality = 0 := by
  simp only [cardinality, cardinality', Finite.ftype]
  suffices h : Cardinal.mk (∅ : Set α) = 0 by
    rw[← FiniteCardinal.to_nat_of_nat (n := 0)]
    congr
  simp only [Cardinal.eq_zero_iff]
  exact fun ⟨x,h⟩ => h

@[simp high] theorem cardinality_pempty : (Finite.ftype.{u} (PEmpty.{u + 1} : Type u)).cardinality = 0 := by
  simp only [cardinality, cardinality', Finite.ftype]
  suffices h : Cardinal.mk PEmpty = 0 by
    rw[← FiniteCardinal.to_nat_of_nat (n := 0)]
    congr
  simp only [Cardinal.eq_zero_iff]
  exact PEmpty.elim

@[simp high] theorem cardinality_unit : (Finite.ftype Unit).cardinality = 1 := by
  simp only [cardinality, cardinality', Finite.ftype]
  suffices h : Cardinal.mk Unit = 1 by
    rw[← FiniteCardinal.to_nat_of_nat (n := 1)]
    simp only [FiniteCardinal.of_nat, Cardinal.zero_add]
    congr
  simp only [Cardinal.eq_one_iff]
  constructor
  infer_instance

@[simp high] theorem cardinality_punit : (Finite.ftype.{u} (PUnit.{u + 1} : Type u)).cardinality = 1 := by
  simp only [cardinality, cardinality', Finite.ftype]
  suffices h : Cardinal.mk PUnit = 1 by
    rw[← FiniteCardinal.to_nat_of_nat (n := 1)]
    simp only [FiniteCardinal.of_nat, Cardinal.zero_add]
    congr
  simp only [Cardinal.eq_one_iff]
  constructor
  infer_instance

variable {α β : Type u}
@[simp high] theorem cardinality_sum [Finite α] [Finite β]: (Finite.ftype $ α ⊕ β).cardinality = (Finite.ftype α).cardinality + (Finite.ftype β).cardinality := by
  simp only [cardinality, cardinality', Finite.ftype]
  rw[← FiniteCardinal.to_nat_add]
  simp only [Cardinal.add_mk]

@[simp high] theorem cardinality_mul [Finite α] [Finite β]: (Finite.ftype $ α × β).cardinality = (Finite.ftype α).cardinality * (Finite.ftype β).cardinality := by
  simp only [cardinality, cardinality', Finite.ftype]
  rw[← FiniteCardinal.to_nat_mul]
  simp only [Cardinal.mul_mk]

@[simp high] theorem cardinality_pow [Finite α] [Finite β]: (Finite.ftype $ α → β).cardinality = (Finite.ftype β).cardinality ^ (Finite.ftype α).cardinality := by
  simp only [cardinality, cardinality', Finite.ftype]
  rw[← FiniteCardinal.to_nat_pow]
  simp only [Cardinal.pow_mk]

@[simp low] theorem cardinality_le_iff {a b : FiniteType.{u}} :
    a.cardinality ≤ b.cardinality ↔ Nonempty (Function.Injection a.val b.val) := by
  rcases a with ⟨a,ha⟩
  rcases b with ⟨b,hb⟩
  simp only [cardinality, cardinality', FiniteCardinal.to_nat_le_iff, FiniteCardinal.eq_1,
    Subtype.le_iff_val, Cardinal.mk_le_iff]

@[simp low+1] theorem cardinality_le_ftype_iff {α β : Type u} [Finite α] [Finite β] :
    (Finite.ftype α).cardinality ≤ (Finite.ftype β).cardinality ↔ Nonempty (Function.Injection α β) := by
  simp only [Finite.ftype, cardinality_le_iff]


theorem cardinality_le_of_surj {a b : FiniteType.{u}} (h : Function.Surjection a.val b.val) :
    b.cardinality ≤ a.cardinality := by
  rcases a with ⟨a,ha⟩
  rcases b with ⟨b,hb⟩
  simp only [cardinality, cardinality', FiniteCardinal.to_nat_le_iff, FiniteCardinal.eq_1,
    Subtype.le_iff_val]
  apply Cardinal.ge_of_surj h

theorem cardinality_le_ftype_of_surj {α β : Type u} [Finite α] [Finite β]
    (h : Function.Surjection β α) :
    (Finite.ftype α).cardinality ≤ (Finite.ftype β).cardinality := by
  apply cardinality_le_of_surj h



@[simp] theorem cardinality_eq_iff {a b : FiniteType.{u}} :
    a.cardinality = b.cardinality ↔ Equipotent a.val b.val := by
  rcases a with ⟨a,ha⟩
  rcases b with ⟨b,hb⟩
  simp only [cardinality, cardinality']
  constructor
  · intro h
    have := FiniteCardinal.to_nat_bij.inj _ _ h
    simp only [FiniteCardinal.eq_1, Subtype.eq_iff, Cardinal.eq_iff] at this
    exact this
  · intro h
    congr 1
    simp only [FiniteCardinal.eq_1, Subtype.eq_iff, Cardinal.eq_iff, h]

theorem cardinality_le_of_subset {a b : Set α} (h : a ⊆ b) [h' : Finite a] [h'' : Finite b] :
    (Finite.ftype a).cardinality ≤ (Finite.ftype b).cardinality := by
  simp only [cardinality_le_iff]
  constructor
  exists fun ⟨x,m⟩ => ⟨x, h m⟩
  intro ⟨x,m⟩ ⟨y,m'⟩ eq
  simp only at eq
  congr
  apply Subtype.eq_iff.mp eq

theorem cardinality_image_le {a : Set α} {f : α → β} [h' : Finite a] :
    (Finite.ftype $ f '' a).cardinality ≤ (Finite.ftype $ a).cardinality := by
  apply cardinality_le_ftype_of_surj
  exists fun ⟨x,h⟩ => ⟨f x, Set.val_mem_image_of_mem h⟩
  rw[Function.surj_iff]
  intro ⟨b,c⟩
  rw[Set.mem_image_iff] at c
  obtain ⟨a,rfl,h⟩ := c
  exists ⟨a,h⟩

@[simp] theorem cardinality_set_le {a : Set α} [Finite α] :
    (Finite.ftype a).cardinality ≤ (Finite.ftype α).cardinality := by
  simp only [cardinality_le_ftype_iff]
  exact ⟨Subtype.val,Subtype.val_inj⟩

@[simp] theorem cardinality_set_zero_iff {a : Set α} [Finite a] :
    (Finite.ftype a).cardinality = 0 ↔ a = ∅ := by
  rw[← Nat.le_zero, ← cardinality_pempty, cardinality_le_iff]
  simp only [Finite.ftype]
  constructor
  · intro ⟨h⟩
    ext x
    simp only [Set.not_mem_empty, iff_false]
    intro h'
    exact (h ⟨x,h'⟩).elim
  · rintro rfl
    exact ⟨fun ⟨x,h⟩ => h.elim, fun ⟨x,h⟩ => h.elim⟩

@[simp] theorem cardinality_singleton {x : α} : (Finite.ftype ({x} : Set α)).cardinality = 1 := by
  rw[← cardinality_punit, cardinality_eq_iff]
  constructor
  apply Function.bijection_of_funcs (fun x => PUnit.unit) (fun b => ⟨x,rfl⟩)
  · rintro ⟨⟩; rfl
  · rintro ⟨x,h⟩; exact Subtype.eq h.symm

@[simp] theorem cardinality_insert {a : Set α} [Finite a] {x : α} (h' : x ∉ a):
    (Finite.ftype (a ∪ {x} : Set α)).cardinality = (Finite.ftype a).cardinality + 1 := by
  rw[← cardinality_punit, ← cardinality_sum, Eq.comm, cardinality_eq_iff]
  constructor
  exists Sum.elim (fun ⟨a,h⟩ => ⟨a,Or.inl h⟩) (fun a => ⟨x, Or.inr rfl⟩)
  constructor
  · rintro (y|y) (z|z) h
    · simp only [Sum.elim_inl] at h
      congr
      apply Subtype.eq
      apply Subtype.eq_iff.mp h
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      have := y.property
      rw[Subtype.eq_iff.mp h] at this
      exact (h' this).elim
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      have := z.property
      rw[← Subtype.eq_iff.mp h] at this
      exact (h' this).elim
    · congr
  · rw[Function.surj_iff]
    rintro ⟨y,(hy|rfl)⟩
    · exists Sum.inl ⟨y,hy⟩
    · exists Sum.inr default

end FiniteType
theorem Finite.set_induction {α : Type*} {p : Set α → Prop}
    (he : p ∅) (hs : ∀ x : α, ∀ a : Set α, Finite a → x ∉ a → p a → p (a ∪ {x}))
    : (a : Set α) → [h : Finite a] → p a := by
  have res : (n : Nat) → (a : Set α) →  (h : Finite a) → (eq : (h.ftype).cardinality = n) → p a := by
    intro n
    induction n with
    | zero =>
      intro a h eq
      simp only [FiniteType.cardinality_set_zero_iff] at eq
      rwa[eq]
    | succ n ih =>
        intro a h eq
        obtain ⟨x,hx⟩ : a.Nonempty := by
          rw[Set.nonempty_iff_neq_empty]
          rintro rfl
          rw[FiniteType.cardinality_empty_set] at eq
          injection eq
        have eq2 : a = (a \ {x}) ∪ {x} := by
          ext y
          simp only [Set.mem_union_iff, Set.mem_sdiff_iff, Set.mem_singleton_iff]
          constructor
          · by_cases eq : y = x
            · simp only [eq, not_true_eq_false, and_false, or_true, implies_true]
            · simp only [eq, not_false_eq_true, and_true, or_false, imp_self]
          · rintro (h|h)
            · exact h.left
            · exact h ▸ hx
        have : (ftype ((a \ {x}) ∪ {x} : Set α)).cardinality = n + 1 := by
          rw[← eq, FiniteType.cardinality_eq_iff]
          simp only [ftype]
          rw[← eq2]
          apply Equipotent.of_eq rfl
        have : (ftype (a \ {x} : Set α)).cardinality = n := by
          rw[FiniteType.cardinality_insert] at this
          · exact Nat.succ_inj'.mp this
          · simp only [Set.mem_sdiff_iff, Set.mem_singleton_iff, not_true_eq_false, and_false,
            not_false_eq_true]
        specialize ih _ _ this
        rw[eq2]
        apply hs _ _ inferInstance (by simp only [Set.mem_sdiff_iff, Set.mem_singleton_iff,
          not_true_eq_false, and_false, not_false_eq_true]) ih
  intro a h
  apply res _ _ h rfl
