import BourbakiLean2.Set.FiniteCardinal
universe u v
variable {α β ι : Type*} {x : ι → Type*}

namespace Finite
noncomputable def ftype (x : Type*) [h : Finite x] : FiniteType := ⟨x, h⟩

instance : Finite Empty where
  finite := by
    have : Cardinal.mk Empty = 0 := by
      simp only [Cardinal.eq_zero_iff]
      exact Empty.elim
    rw[this]
    infer_instance

instance : Finite.{u} PEmpty where
  finite := by
    have : Cardinal.mk PEmpty = 0 := by
      simp only [Cardinal.eq_zero_iff]
      exact PEmpty.elim
    rw[this]
    infer_instance

instance : Finite.{u} PUnit where
  finite := by
    have : Cardinal.mk PUnit = 1 := by
      simp only [Cardinal.eq_one_iff]
      constructor
      infer_instance
    rw[this]
    infer_instance

instance : Finite Unit where
  finite := by
    have : Cardinal.mk Unit = 1 := by
      simp only [Cardinal.eq_one_iff]
      constructor
      infer_instance
    rw[this]
    infer_instance

instance : Finite Bool where
  finite := by
    have : Cardinal.mk Bool = 1 + 1 := by
      simp only [Cardinal.one_eq, Cardinal.add_mk, Cardinal.eq_iff]
      constructor
      apply Function.bijection_of_funcs (λ b => if b then Sum.inl default else Sum.inr default)
        (Sum.elim (fun x => true) (fun x => false))
      · rintro (b|b) <;> rfl
      · rintro (b|b) <;> rfl
    rw[this]
    infer_instance

instance {α β : Type u} [Finite α] [Finite β] : Finite (α ⊕ β) where
  finite := by
    have : Cardinal.mk (α ⊕ β) = Cardinal.mk α + Cardinal.mk β := by
      simp only [Cardinal.add_mk, Cardinal.eq_iff]
    rw[this]
    have : (Cardinal.mk α + Cardinal.mk β) = (FiniteCardinal.of_nat $
        FiniteCardinal.to_nat ⟨Cardinal.mk α, inferInstance⟩ + FiniteCardinal.to_nat ⟨Cardinal.mk β, inferInstance⟩).1 := by
      rw[FiniteCardinal.of_nat_add]
      simp only [Cardinal.add_mk, FiniteCardinal.of_nat_to_nat]
    rw[this]
    apply (fun x : FiniteCardinal => x.property)

instance {α β : Type u} [Finite α] [Finite β] : Finite (α × β) where
  finite := by
    have : Cardinal.mk (α × β) = Cardinal.mk α * Cardinal.mk β := by
      simp only [Cardinal.mul_mk, Cardinal.eq_iff]
    rw[this]
    have : (Cardinal.mk α * Cardinal.mk β) = (FiniteCardinal.of_nat $
        FiniteCardinal.to_nat ⟨Cardinal.mk α, inferInstance⟩ * FiniteCardinal.to_nat ⟨Cardinal.mk β, inferInstance⟩).1 := by
      rw[FiniteCardinal.of_nat_mul]
      simp only [Cardinal.mul_mk, FiniteCardinal.of_nat_to_nat]
    rw[this]
    apply (fun x : FiniteCardinal => x.property)

instance {α β : Type u} [Finite α] [Finite β] : Finite (α → β) where
  finite := by
    have : Cardinal.mk (α → β) = Cardinal.mk β ^ Cardinal.mk α := by
      simp only [Cardinal.pow_mk, Cardinal.eq_iff]
    rw[this]
    have : (Cardinal.mk β ^ Cardinal.mk α) = (FiniteCardinal.of_nat $
        FiniteCardinal.to_nat ⟨Cardinal.mk β, inferInstance⟩ ^ FiniteCardinal.to_nat ⟨Cardinal.mk α, inferInstance⟩).1 := by
      rw[FiniteCardinal.of_nat_pow]
      simp only [Cardinal.pow_mk, FiniteCardinal.of_nat_to_nat]
    rw[this]
    apply (fun x : FiniteCardinal => x.property)

instance {α : Type u} [Subsingleton α] : Finite α where
  finite := by
    have : Cardinal.mk α ≤ 1 := by
      simp only [Cardinal.one_eq, Cardinal.mk_le_iff]
      constructor
      exists fun x => default
      intro x x' _
      apply Subsingleton.allEq
    apply Cardinal.Finite.of_le_finite _ this
    infer_instance

end Finite


namespace FiniteType
noncomputable def cardinality (x : FiniteType.{u}) : Nat := FiniteCardinal.to_nat $ x.cardinality'

@[simp] theorem cardinality_empty : (Finite.ftype Empty).cardinality = 0 := by
  simp only [cardinality, cardinality', Finite.ftype]
  suffices h : Cardinal.mk Empty = 0 by
    rw[← FiniteCardinal.to_nat_of_nat (n := 0)]
    congr
  simp only [Cardinal.eq_zero_iff]
  exact Empty.elim

@[simp] theorem cardinality_pempty : (Finite.ftype.{u} (PEmpty.{u + 1} : Type u)).cardinality = 0 := by
  simp only [cardinality, cardinality', Finite.ftype]
  suffices h : Cardinal.mk PEmpty = 0 by
    rw[← FiniteCardinal.to_nat_of_nat (n := 0)]
    congr
  simp only [Cardinal.eq_zero_iff]
  exact PEmpty.elim

@[simp] theorem cardinality_unit : (Finite.ftype Unit).cardinality = 1 := by
  simp only [cardinality, cardinality', Finite.ftype]
  suffices h : Cardinal.mk Unit = 1 by
    rw[← FiniteCardinal.to_nat_of_nat (n := 1)]
    simp only [FiniteCardinal.of_nat, Cardinal.zero_add]
    congr
  simp only [Cardinal.eq_one_iff]
  constructor
  infer_instance

@[simp] theorem cardinality_punit : (Finite.ftype.{u} (PUnit.{u + 1} : Type u)).cardinality = 1 := by
  simp only [cardinality, cardinality', Finite.ftype]
  suffices h : Cardinal.mk P  Unit = 1 by
    rw[← FiniteCardinal.to_nat_of_nat (n := 1)]
    simp only [FiniteCardinal.of_nat, Cardinal.zero_add]
    congr
  simp only [Cardinal.eq_one_iff]
  constructor
  infer_instance

end FiniteType
