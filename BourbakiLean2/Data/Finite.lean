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

@[simp high] theorem cardinality_unique [Unique α] : (Finite.ftype α).cardinality = 1 := by
  simp only [cardinality, cardinality', Finite.ftype]
  suffices h : Cardinal.mk α = 1 by
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

theorem cardinality_univ [Finite α] : (Finite.ftype (Set.univ : Set α)).cardinality = (Finite.ftype α).cardinality := by
  simp only [cardinality, cardinality', Finite.ftype]
  congr 2
  simp only [Set.mem_univ, Cardinal.eq_iff]
  constructor
  apply Function.bijection_of_funcs (fun ⟨x,h⟩ => x) (fun x => ⟨x,trivial⟩)
  · intro b; simp only
  · intro b; simp only

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

@[simp] theorem cardinality_eq_iff' {α β : Type u} [Finite α] [Finite β]:
    (Finite.ftype α).cardinality = (Finite.ftype β).cardinality ↔ Equipotent α β := by
  rw[cardinality_eq_iff]
  rfl

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

theorem cardinality_image_eq_inj {a : Set α} {f : α → β} [h' : Finite a] (h'' : f.Injective):
    (Finite.ftype $ f '' a).cardinality = (Finite.ftype $ a).cardinality := by
  apply Nat.le_antisymm cardinality_image_le
  simp only [cardinality_le_ftype_iff]
  constructor
  exists (f.restriction a).corestrict ?h
  · intro x h
    simp only [Set.mem_image_iff, Function.restriction, Set.mem_univ, and_true, Subtype.exists,
      exists_prop] at h
    simp only [Set.mem_image_iff]
    obtain ⟨x,hx,hx2⟩ := h
    exists x
  · intro ⟨x,hx⟩ ⟨y,hy⟩ h
    simp at h
    simp only [Subtype.eq_iff]
    exact h'' _ _ h

theorem cardinality_preimage_eq_bij {a : Set β} (f : Function.Bijection α β) [h' : Finite a] :
    (Finite.ftype $ f ⁻¹' a).cardinality = (Finite.ftype $ a).cardinality := by
  simp only [f.2.preimage_eq]
  apply cardinality_image_eq_inj
  exact f.2.inv_bij.inj

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

theorem of_cardinality_zero [Finite α] (h : (Finite.ftype α).cardinality = 0) (h2 : α) : False := by
  rw[← cardinality_univ (α := α), cardinality_set_zero_iff] at h
  have : h2 ∈ Set.univ := trivial
  rwa[h] at this

@[simp] theorem cardinality_singleton {x : α} : (Finite.ftype ({x} : Set α)).cardinality = 1 := by
  rw[← cardinality_punit, cardinality_eq_iff]
  constructor
  apply Function.bijection_of_funcs (fun x => PUnit.unit) (fun b => ⟨x,rfl⟩)
  · rintro ⟨⟩; rfl
  · rintro ⟨x,h⟩; exact Subtype.eq h.symm

@[simp] theorem cardinality_manual_insert {a : Set α} [Finite a] {x : α} (h' : x ∉ a):
    (Finite.ftype ({x} ∪ a : Set α)).cardinality = (Finite.ftype a).cardinality + 1 := by
  rw[← cardinality_punit, ← cardinality_sum, Eq.comm, cardinality_eq_iff]
  constructor
  exists Sum.elim (fun ⟨a,h⟩ => ⟨a,Or.inr h⟩) (fun a => ⟨x, Or.inl rfl⟩)
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
    rintro ⟨y,(rfl|hy)⟩
    · exists Sum.inr default
    · exists Sum.inl ⟨y,hy⟩

theorem cardinality_preimage_same_product {α β : Type u} [Finite α] [Finite β] {f : α → β} {n : Nat}
    (h' : ∀ y : β, (Finite.ftype (f ⁻¹' {y})).cardinality = n) :
      (Finite.ftype α).cardinality = n * (Finite.ftype β).cardinality := by
  unfold cardinality cardinality' Finite.ftype
  simp only
  rw[← FiniteCardinal.to_nat_of_nat (n := n), ← FiniteCardinal.to_nat_mul]
  congr 2
  apply Cardinal.preimage_same_product (f := f)
  intro b
  specialize h' b
  rw[← h']
  simp only [Set.mem_preimage_iff, Set.mem_singleton_iff, cardinality, cardinality', Finite.ftype,
    FiniteCardinal.of_nat_to_nat]

@[simp] theorem cardinality_insert {a : Set α} [Finite a] {x : α} (h' : x ∉ a):
    (Finite.ftype (insert x a : Set α)).cardinality = (Finite.ftype a).cardinality + 1 := by
  change (Finite.ftype ({x} ∪ a : Set α)).cardinality = (Finite.ftype a).cardinality + 1
  exact cardinality_manual_insert h'

theorem eq_of_cardinality_eq_subset {a b : Set α} [Finite a] [Finite b] (h : a ⊆ b) (h' : (Finite.ftype a).cardinality = (Finite.ftype b).cardinality) :
    a = b := by
  simp only [cardinality_eq_iff, Finite.ftype] at h'
  let f : Function.Injection a b := ⟨fun ⟨x,hx⟩ => ⟨x, h hx⟩, fun x y h => by simp only [Subtype.eq_iff] at h; exact Subtype.eq h⟩
  have : Function.Bijective f := (Finite.bij_iff_inj h').mpr f.property
  apply Set.eq_iff_subset_subset.mpr ⟨h,?wh⟩
  intro x hx
  obtain ⟨⟨a,ha⟩,eq⟩ := this.surj.exists_preimage ⟨x,hx⟩
  simp only [Subtype.eq_iff] at eq
  rwa[eq]

theorem cardinality_disj_union [Finite α] {a b : Set α} (h : a ∩ b = ∅) : (Finite.ftype (a ∪ b : Set α)).cardinality = (Finite.ftype a).cardinality + (Finite.ftype b).cardinality := by
  rw[← cardinality_sum, Eq.comm, cardinality_eq_iff]
  constructor
  exists Sum.elim (fun ⟨a,h⟩ => ⟨a, Or.inl h⟩) (fun ⟨a,h⟩ => ⟨a, Or.inr h⟩)
  constructor
  · rintro (⟨x,hx⟩|⟨x,hx⟩) (⟨y,hy⟩|⟨y,hy⟩) h'
    · simp only [Sum.elim_inl, Sum.elim_inr] at h'; congr; injection h'
    · simp only [Sum.elim_inl, Sum.elim_inr] at h'
      injection h' with h'; rw[h'] at hx
      have : y ∈ a ∩ b := ⟨hx,hy⟩
      rw[h] at this
      exact this.elim
    · simp only [Sum.elim_inl, Sum.elim_inr] at h'
      injection h' with h'; rw[h'] at hx
      have : y ∈ a ∩ b := ⟨hy,hx⟩
      rw[h] at this
      exact this.elim
    · simp only [Sum.elim_inl, Sum.elim_inr] at h'; congr; injection h'
  · rw[Function.surj_iff]
    rintro ⟨b,(h'|h')⟩
    · exists Sum.inl ⟨b,h'⟩
    · exists Sum.inr ⟨b,h'⟩

@[simp high] theorem cardinality_compl [Finite α] {a : Set α} : (Finite.ftype (a ᶜ)).cardinality = (Finite.ftype α).cardinality - (Finite.ftype a).cardinality := by
  have : (Finite.ftype α).cardinality = (Finite.ftype a).cardinality + (Finite.ftype (a ᶜ)).cardinality := by
    rw[← cardinality_univ]
    have : Set.univ = a ∪ a ᶜ := by
      simp only [Set.mem_univ, Set.union_with_compl]
    rw[this]
    apply cardinality_disj_union
    simp only [Set.inter_with_compl]
  rw[this]
  exact
    Eq.symm
      (Nat.add_sub_self_left (Finite.ftype { a_1 // a_1 ∈ a }).cardinality
        (Finite.ftype { a_1 // a_1 ∈ aᶜ }).cardinality)

theorem cardinality_nonempty [Finite α] [h : Nonempty α] : 1 ≤ (Finite.ftype α).cardinality := by
  obtain ⟨a⟩ := h
  have := cardinality_set_le (a := {a})
  rwa[cardinality_singleton] at this

theorem nonempty_of_cardinality_succ {n} [Finite α] (h : (Finite.ftype α).cardinality = n + 1) : Nonempty α := by
  have h' : 1 ≤ (Finite.ftype α).cardinality := by rw[h]; simp only [Nat.le_add_left]
  rw[← cardinality_punit, cardinality_le_iff] at h'
  obtain ⟨i⟩ := h'
  constructor
  exact i PUnit.unit

theorem cardinality_sets [Finite α] : (Finite.ftype (Set α)).cardinality = 2^(Finite.ftype α).cardinality := by
  trans (Finite.ftype (α → PUnit ⊕ PUnit)).cardinality
  · rw[cardinality_eq_iff, ← Cardinal.eq_iff]
    simp only [Finite.ftype]
    rw[Cardinal.set_eq_two_pow]
    rw[Cardinal.one_eq]
    simp only [Cardinal.add_mk, Cardinal.pow_mk]
  · simp only [cardinality_pow, cardinality_sum, cardinality_unique, Nat.reduceAdd]

end FiniteType
theorem Finite.set_induction {α : Type*} {p : Set α → Prop}
    (he : p ∅) (hs : ∀ x : α, ∀ a : Set α, Finite a → x ∉ a → p a → p (a ∪ {x}))
    : (a : Set α) → [_h : Finite a] → p a := by
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
        have eq2 : a = {x} ∪ (a \ {x}) := by
          ext y
          simp only [Set.mem_union_iff, Set.mem_sdiff_iff, Set.mem_singleton_iff]
          constructor
          · by_cases eq : y = x
            · simp only [eq, not_true_eq_false, and_false, or_false, implies_true]
            · simp only [eq, not_false_eq_true, and_true, false_or, imp_self]
          · rintro (h|h)
            · exact h ▸ hx
            · exact h.left
        have : (ftype ({x} ∪ (a \ {x}) : Set α)).cardinality = n + 1 := by
          rw[← eq, FiniteType.cardinality_eq_iff]
          simp only [ftype]
          rw[← eq2]
          apply Equipotent.of_eq rfl
        have : (ftype (a \ {x} : Set α)).cardinality = n := by
          rw[FiniteType.cardinality_manual_insert] at this
          · exact Nat.succ_inj'.mp this
          · simp only [Set.mem_sdiff_iff, Set.mem_singleton_iff, not_true_eq_false, and_false,
            not_false_eq_true]
        specialize ih _ _ this
        rw[eq2, Set.union_comm]
        apply hs _ _ inferInstance (by simp only [Set.mem_sdiff_iff, Set.mem_singleton_iff,
          not_true_eq_false, and_false, not_false_eq_true]) ih
  intro a h
  apply res _ _ h rfl
