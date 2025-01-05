import BourbakiLean2.Set.Cardinal
universe u
variable {α ι : Type u}

class Cardinal.Finite (a : Cardinal.{u}) where
  neq_plus_one : a ≠ a + 1

@[simp] theorem Cardinal.Finite.lt_plus_one {a : Cardinal.{u}} [h : a.Finite] : a < a + 1 := by
  rw[lt_iff_le_not_eq]
  simp only [le_add_left, ne_eq, neq_plus_one, not_false_eq_true, and_self]

theorem Cardinal.Finite.infer {a : Cardinal.{u}} [h : a.Finite] : a.Finite := h

theorem Cardinal.finite_iff {a : Cardinal.{u}} : a.Finite ↔ a ≠ a + 1 := by
  constructor
  · intro h
    exact h.neq_plus_one
  · intro h
    constructor
    · exact h

@[simp] def FiniteCardinal := {a : Cardinal.{u} // a.Finite}
instance : Coe FiniteCardinal.{u} Cardinal.{u} := ⟨fun x => x.val⟩
noncomputable instance: WellOrder FiniteCardinal := by unfold FiniteCardinal; infer_instance
class Finite (α : Type u) where
  finite : Cardinal.Finite (Cardinal.mk α)

instance {a : FiniteCardinal.{u}} : Cardinal.Finite a.val := a.property

instance {α : Type u} [Finite α] : Cardinal.Finite (Cardinal.mk α) := by
  exact Finite.finite

@[simp] theorem Finite.iff {α : Type u} : Finite α ↔ Cardinal.Finite (Cardinal.mk α) := by
  constructor
  · intro h
    exact h.finite
  · intro h
    constructor
    exact h

@[simp] def FiniteType := {α : Type u // Finite α}
def FiniteType.cardinality' : FiniteType.{u} → FiniteCardinal.{u} := fun ⟨x,h⟩ => ⟨Cardinal.mk x, h.finite⟩

theorem Cardinal.finite_iff_add_one_finite {a : Cardinal.{u}} : (a + 1).Finite ↔ a.Finite := by
  simp only [finite_iff, ne_eq]
  apply not_congr
  constructor
  · apply Cardinal.add_one_cancel
  · intro h
    rw[← h, ← h]

instance Cardinal.Finite.succ {a : Cardinal.{u}} [h : a.Finite] : (a + 1).Finite := by
  rw[Cardinal.finite_iff_add_one_finite]
  exact h

instance Cardinal.Finite.zero : (0 : Cardinal.{u}).Finite := by
  constructor
  intro h
  rw[Cardinal.zero_add] at h
  exact Cardinal.zero_neq_one h

instance Cardinal.Finite.one : (1 : Cardinal.{u}).Finite := by
  rw[← Cardinal.zero_add (a := 1)]
  infer_instance

@[simp low] def Cardinal.ofNat : Nat → Cardinal
| 0 => 0
| n+1 => (ofNat n) + 1

@[simp] theorem Cardinal.ofNat_zero : Cardinal.ofNat 0 = 0 := rfl
@[simp] theorem Cardinal.ofNat_one : Cardinal.ofNat 1 = 1 := by
  simp only [ofNat, zero_add]

theorem Cardinal.Finite.of_le_finite {a b : Cardinal.{u}} (h' : b.Finite) (h : a ≤ b) : a.Finite := by
  rw[finite_iff] at h' |-
  rw[← Cardinal.exists_add_iff_le] at h
  obtain ⟨c,rfl⟩ := h
  intro h''
  have := ((congrArg (· + c) h'').trans Cardinal.add_assoc.symm).trans (congrArg _ Cardinal.add_comm)
  exact h' $ this.trans Cardinal.add_assoc

theorem Cardinal.Finite.has_pred {a : Cardinal.{u}} (h : a.Finite) (h' : a ≠ 0) : ∃ b, a = b + 1 := by
  have : 1 ≤ a := by rwa[Cardinal.one_le_iff_neq_zero]
  obtain ⟨b,rfl⟩ := Cardinal.exists_add_iff_le.mpr this
  exists b
  exact Cardinal.add_comm

theorem Cardinal.Finite.has_unique_pred {a : Cardinal.{u}} (h : a.Finite) (h' : a ≠ 0) : ∃! b, a = b + 1 := by
  obtain ⟨b,rfl⟩ := h.has_pred h'
  constructor
  constructor
  · rfl
  · intro y h
    exact Cardinal.add_one_cancel (Eq.symm h)

noncomputable def Cardinal.Finite.pred {a : Cardinal.{u}} (h : a.Finite) (h' : a ≠ 0) : Cardinal.{u} :=
  (Classical.choose (h.has_unique_pred h'))


@[simp] theorem Cardinal.Finite.pred_of_plus_one {a : Cardinal.{u}} (h' : _) (h'' : _):
    Cardinal.Finite.pred (a := a + 1) h' h'' = a := by
  simp only [pred]
  have := Classical.choose_spec $ has_unique_pred (a := a + 1) inferInstance add_one_neq_zero
  simp only at this
  apply add_one_cancel this.1.symm

@[simp] theorem Cardinal.Finite.pred_plus_one {a : Cardinal.{u}} (h' : _) (h'' : _):
    Cardinal.Finite.pred (a := a) h' h'' + 1 = a := by
  obtain ⟨b,rfl⟩ := h'.has_pred h''
  simp only [pred_of_plus_one]

instance Cardinal.Finite.pred_finite {a : Cardinal.{u}} [h : a.Finite] (h' : a ≠ 0) : (h.pred h').Finite := by
  constructor
  intro h''
  obtain ⟨b,rfl⟩ := h.has_pred h'
  simp only [Cardinal.Finite.pred_of_plus_one] at h''
  exact (Cardinal.finite_iff_add_one_finite.mp h).neq_plus_one h''


theorem Cardinal.Finite.exists_add_iff_lt {a b : Cardinal.{u}} (hfin : Finite b) : (∃ c, b = a + c + 1) ↔ a < b := by
  rw[lt_iff_le_not_eq]
  conv =>
    lhs;rhs;intro c;rw[← add_assoc, add_comm (a := c), add_assoc]
  rw[exists_add_iff_le]
  constructor
  · intro h
    constructor
    · suffices h : a + 0 ≤ b by simp only [add_zero] at h; assumption
      apply le_trans (add_mono_left (zero_le (x := 1))) h
    · intro h'
      rw[h'] at h
      have : b = b + 1 := le_antisymm (by simp only [le_add_left]) h
      exact hfin.neq_plus_one this
  · intro ⟨le,ne⟩
    rw[← exists_add_iff_le] at le |-
    obtain ⟨c,rfl⟩ := le
    have : c ≠ 0 := by intro h; rw[h, add_zero] at ne; exact ne rfl
    have fin : c.Finite := hfin.of_le_finite (by simp only [le_add_right])
    obtain ⟨d,rfl⟩ := fin.has_pred this
    exists d
    simp only [add_assoc, add_comm]

theorem Cardinal.Finite.le_pred_iff {a b : Cardinal.{u}} (h : a.Finite) (h' : a ≠ 0) : b < a ↔ b ≤ h.pred h' := by
  rw[← h.exists_add_iff_lt, ← exists_add_iff_le]
  apply exists_congr
  intro c
  constructor
  · rintro rfl
    simp only [pred_of_plus_one]
  · rintro eq
    rw[← eq]
    simp only [pred_plus_one]

theorem Cardinal.Finite.lt_add_one_iff {a b : Cardinal.{u}} (h : a.Finite) : b < a + 1 ↔ b ≤ a := by
  by_cases h' : a = 0
  · rw[h', zero_add, ← exists_add_iff_le, ← exists_add_iff_lt inferInstance]
    apply exists_congr
    intro c
    rw[← zero_add (a := 1), add_assoc, add_zero (a := b + c)]
    constructor
    · apply add_one_cancel
    · intro h
      rw[h]
  · obtain ⟨c,rfl⟩ := h.has_pred h'
    rw[← exists_add_iff_lt inferInstance, ← exists_add_iff_le]
    apply exists_congr
    intro d
    constructor
    · apply add_one_cancel
    · intro h
      rw[h]

/-- bit of finite set stuff -/

theorem Finite.of_inj_finite {α β : Type u} [h : Finite β] (f : Function.Injection α β) : Finite α := by
  constructor
  apply Cardinal.Finite.of_le_finite h.finite
  exact ⟨f⟩

theorem Finite.of_surj_finite {α β : Type u} [h : Finite α] (f : Function.Surjection α β) : Finite β := by
  constructor
  apply Cardinal.Finite.of_le_finite h.finite
  apply Cardinal.ge_of_surj f

theorem Finite.of_bij_finite {α β : Type u} [h : Finite α] (f : Function.Bijection α β) : Finite β := by
  apply Finite.of_surj_finite (α := α)
  exact ⟨f.1, f.2.surj⟩

instance Finite.set {α : Type u} {s : Set α} [h : Finite α] : Finite s := by
  apply Finite.of_inj_finite (β := α)
  exact ⟨Subtype.val, Subtype.val_inj⟩

instance Finite.subtype {α : Type u} {p : α → Prop} [h : Finite α] : Finite {x // p x} := by
  apply Finite.of_inj_finite (β := α)
  exact ⟨Subtype.val, Subtype.val_inj⟩

theorem Finite.subset {α : Type u} {s t : Set α} [h : Finite s] (h' : t ⊆ s) : Finite t := by
  apply Finite.of_inj_finite (β := s)
  exact ⟨fun ⟨x,h''⟩ => ⟨x, h' h''⟩, by
    rintro ⟨x,hx⟩ ⟨y,hy⟩ eq
    simp only [Subtype.eq_iff] at eq
    apply Subtype.eq eq⟩

instance Finite.inter_left {s t : Set α} [h : Finite s] : Finite (s ∩ t : Set α) := by
  apply Finite.subset (s := s)
  apply Set.inter_subset_left

instance Finite.inter_right {s t : Set α} [h : Finite t] : Finite (s ∩ t : Set α) := by
  rw[Set.inter_comm]
  infer_instance

instance Finite.sdiff {s t : Set α} [h : Finite s] : Finite (s \ t : Set α) := by
  apply Finite.subset (s := s)
  exact Set.sdiff_subset


instance Finite.iInter_all [ne : Nonempty ι] {x : ι → Set α} [h : ∀ i, Finite (x i)] : Finite (⋂ i, x i) := by
  obtain ⟨i⟩ := ne
  apply Finite.subset (s := x i)
  exact fun ⦃a⦄ a ↦ a i

theorem Finite.iInter_one {x : ι → Set α} {i : ι} [h : Finite (x i)] : Finite (⋂ i, x i) := by
  exact subset fun ⦃a⦄ a ↦ a i

instance Finite.empty_set : Finite (∅ : Set α) := by
  have : (Cardinal.mk (∅ : Set α) : Cardinal.{u}) = 0 := by
    simp only [Set.not_mem_empty, Cardinal.eq_zero_iff, Subtype.forall, imp_self, implies_true]
  constructor
  rw[this]
  infer_instance

theorem Cardinal.mk_singleton {a : α} : Cardinal.mk ({a} : Set α) = 1 := by
  simp only [Set.mem_singleton_iff, eq_one_iff]
  constructor
  constructor
  swap
  · exists a
  · intro b
    simp only [Subtype.eq_iff, b.property]

instance Finite.singleton {a} : Finite ({a} : Set α) := by
  constructor
  rw[Cardinal.mk_singleton]
  infer_instance

theorem Finite.ssubset_cardinal_lt {s : Set α} [h : Finite α] (h' : s ≠ Set.univ) : Cardinal.mk s < Cardinal.mk α := by
  obtain ⟨x,nm⟩ : ∃ x, x ∉ s := by
    by_contra h
    simp only [not_exists, Classical.not_not] at h
    have : s = Set.univ := by ext a; simp only [h, Set.mem_univ]
    exact h' this
  have : s ⊆ {x} ᶜ := by intro a; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact fun h h' => nm $ h' ▸ h
  have : Cardinal.mk s ≤ Cardinal.mk {x}ᶜ := Cardinal.mk_le_of_subset this
  apply lt_of_le_lt this
  have : Cardinal.mk α = Cardinal.mk {x}ᶜ + 1 := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Cardinal.one_eq, Cardinal.add_mk,
      Cardinal.eq_iff]
    classical
    exists fun y => if h : y = x then Sum.inr default else Sum.inl ⟨y,h⟩
    constructor
    · intro a b h'
      by_cases eq1 : a = x
      · rcases eq1
        by_cases eq2 : b = x
        · exact eq2.symm
        · simp only [↓reduceDIte, PUnit.default_eq_unit, eq2, reduceCtorEq] at h'
      · by_cases eq2 : b = x
        · rcases eq2
          simp only [eq1, ↓reduceDIte, PUnit.default_eq_unit, reduceCtorEq] at h'
        · simp only [eq1, ↓reduceDIte, eq2, Sum.inl.injEq, Subtype.eq_iff] at h'
          exact h'
    · rw[Function.surj_iff]
      rintro (⟨a,h⟩|a)
      · exists a
        simp only [h, ↓reduceDIte]
      · rcases a
        exists x
        simp only [↓reduceDIte, PUnit.default_eq_unit]
  rw[this]
  rw[Cardinal.Finite.lt_add_one_iff]
  exact (h.set (s := {x} ᶜ)).finite

instance Finite.image {α β : Type u} {s : Set α} [h : Finite s] (f : α → β) : Finite (f '' s) := by
  apply Finite.of_surj_finite (α := s)
  exists fun x => ⟨f x, Set.val_mem_image_of_mem x.property⟩
  rw[Function.surj_iff]
  intro ⟨b,c⟩
  rw[Set.mem_image_iff] at c
  obtain ⟨a,rfl,h'⟩ := c
  exists ⟨a,h'⟩

theorem Finite.surj_of_inj {α β : Type u} [Finite β] {f : α → β} (hab : Equipotent α β) (h : f.Injective) : f.Surjective := by
  have le : Cardinal.mk α ≤ Cardinal.mk (f '' Set.univ) := by
    simp only [Set.mem_univ, and_true, Cardinal.mk_le_iff]
    constructor
    exists f.corestrict Set.subset_rfl
    intro x y eq
    simp only [Subtype.eq_iff, Function.coe_corestrict] at eq
    exact h _ _ eq
  have ge : Cardinal.mk α ≥ Cardinal.mk (f '' Set.univ) := by
    apply Cardinal.ge_of_surj
    exists f.corestrict Set.subset_rfl
    exact Function.corestrict_surjective
  have := le_antisymm le ge
  have : f '' Set.univ = Set.univ (α := β) := by
    by_contra h'
    have lt := Finite.ssubset_cardinal_lt (α := β) (s := f '' Set.univ) h'
    rw[← this, ← not_ge_iff_lt, Cardinal.eq_iff.mpr hab] at lt
    exact lt le_rfl
  exact this

theorem Finite.inj_of_surj {α β : Type u} [Finite α] {f : α → β} (hab : Equipotent α β) (h : f.Surjective) : f.Injective := by
  have : Finite β := Finite.of_surj_finite (α := α) ⟨_,h⟩
  have ⟨g,eq⟩ := h.hasSection
  have inj : g.Injective := eq.inj
  have : f ∘ g = id := by ext a; simp only [Function.comp_apply, eq.gf_eq, id_eq]
  exact Function.inj_of_surj_comp_inj (this ▸ Function.inj_id) (surj_of_inj (Equivalence.symm inferInstance hab) inj)

theorem Finite.bij_iff_inj {α β : Type u} [Finite β] {f : α → β} (hab : Equipotent α β) : f.Bijective ↔ f.Injective := by
  constructor
  · intro h
    exact h.1
  · intro h
    constructor
    · exact h
    · exact surj_of_inj hab h

theorem Finite.bij_iff_surj {α β : Type u} [Finite α] {f : α → β} (hab : Equipotent α β) : f.Bijective ↔ f.Surjective := by
  constructor
  · intro h
    exact h.2
  · intro h
    constructor
    · exact inj_of_surj hab h
    · exact h

theorem Cardinal.Finite.induction {p : FiniteCardinal.{u} → Prop} (h0 : p ⟨0, zero⟩)
    (hs : ∀ a, p a → p ⟨a.1 + (1 : Cardinal.{u}), succ (h := a.2)⟩)
    (a : FiniteCardinal.{u}) : p a := by
  by_contra h
  let s := {x | ∃ y, ¬ p ⟨x,y⟩}
  have : s.Nonempty := ⟨a.1, a.2, h⟩
  obtain ⟨b,mem,lst⟩ := WellOrder.existsLeast this
  have : Finite b := by
    apply Finite.of_le_finite a.2
    exact lst ⟨a.val,a.2,h⟩
  by_cases eq : b = 0
  · rcases eq
    exact mem.2 h0
  · obtain ⟨c,rfl⟩ := this.has_pred eq
    have inst := Cardinal.finite_iff_add_one_finite.mp this
    have : c ∈ s := by
      exists Cardinal.finite_iff_add_one_finite.mp this
      intro h'
      exact mem.2 $ hs _ h'
    have := lst ⟨_,this⟩
    rw[← not_gt_iff_le] at this
    apply this
    simp only [Subtype.lt_iff_val, lt_plus_one]

theorem Cardinal.Finite.recursion_ex {p : FiniteCardinal.{u} → Type*} (h0 : p ⟨0, zero⟩)
    (hs : ∀ a, p a → p ⟨a.1 + (1 : Cardinal.{u}), succ (h := a.2)⟩) :
    ∃ f : (x : FiniteCardinal.{u}) → p x, f ⟨0,zero⟩ = h0 ∧
      ∀ a, f ⟨a.1 + (1 : Cardinal.{u}), succ (h := a.2)⟩ = (hs a (f a)) := by
  classical
  let a : (x : FiniteCardinal) → (h' : x.val ≠ 0) → ⟨(⟨x.2.pred h', Finite.pred_finite (h := x.2) h'⟩ : FiniteCardinal).val + 1, finite_iff_add_one_finite.mpr $ Finite.pred_finite (h := x.property) h'⟩ = (x : FiniteCardinal) :=
    fun x h' => Subtype.eq $ pred_plus_one x.property h'

  let f' : ((x : FiniteCardinal) → ((y : FiniteCardinal) → y < x → p y) → p x) :=
    fun x h => dite (x.val = 0) (fun h' => Subtype.eq (a2 := ⟨0, zero⟩) h' ▸ h0) (fun h' =>
      a x h' ▸ (hs ⟨(x.2.pred h'), Finite.pred_finite (h := x.2) h'⟩  $ h ⟨(x.2.pred h'),_⟩ $
        (le_pred_iff x.2 h').mpr le_rfl))
  let f := WellOrder.wf_recursion (α := FiniteCardinal.{u}) (p := p) f'
  exists f
  simp only [FiniteCardinal, f, f']
  constructor
  · rw[WellOrder.wf_recursion_eq]
    simp only [↓reduceDIte]
  · intro ⟨x,h⟩
    rw[WellOrder.wf_recursion_eq]
    split <;> rename_i h'
    · simp only [add_zero_iff, zero_neq_one.symm, and_false] at h'
    · apply eq_of_heq
      rw[eqRec_heq_iff_heq]
      simp only
      congr
      · simp only [pred_of_plus_one]
      · simp only [pred_of_plus_one]


noncomputable def FiniteCardinal.recursion {p : FiniteCardinal.{u} → Type*} (h0 : p ⟨0, Cardinal.Finite.zero⟩)
    (hs : ∀ a, p a → p ⟨a.1 + (1 : Cardinal.{u}), Cardinal.Finite.succ (h := a.2)⟩) (a : FiniteCardinal.{u}) : p a :=
  (Cardinal.Finite.recursion_ex h0 hs).choose a

@[simp] theorem FiniteCardinal.recursion_zero {p : FiniteCardinal.{u} → Type*} (h0 : p ⟨0, Cardinal.Finite.zero⟩)
    (hs : ∀ a, p a → p ⟨a.1 + (1 : Cardinal.{u}), Cardinal.Finite.succ (h := a.2)⟩) : FiniteCardinal.recursion h0 hs ⟨0, Cardinal.Finite.zero⟩ = h0 :=
  (Cardinal.Finite.recursion_ex h0 hs).choose_spec.1

@[simp] theorem FiniteCardinal.recursion_succ {p : FiniteCardinal.{u} → Type*} {x : FiniteCardinal.{u}} (h0 : p ⟨0, Cardinal.Finite.zero⟩)
    (hs : ∀ a, p a → p ⟨a.1 + (1 : Cardinal.{u}), Cardinal.Finite.succ (h := a.2)⟩)
    : FiniteCardinal.recursion h0 hs ⟨x.1 + 1, Cardinal.Finite.succ (h := x.2)⟩ = hs x (FiniteCardinal.recursion h0 hs x) :=
  (Cardinal.Finite.recursion_ex h0 hs).choose_spec.2 _

/-! correspondence to normal nats -/
section Nat
variable {x y : FiniteCardinal.{u}} {n m : Nat}
namespace FiniteCardinal
noncomputable def to_nat : FiniteCardinal.{u} → Nat :=
  recursion Nat.zero (fun _ f => Nat.succ f)

noncomputable def of_nat : Nat → FiniteCardinal.{u}
| 0 => ⟨0, Cardinal.Finite.zero⟩
| n+1 => ⟨(of_nat n).1 + (1 : Cardinal.{u}), Cardinal.Finite.succ (h := (of_nat n).2)⟩

@[simp high] theorem to_nat_of_nat : FiniteCardinal.to_nat (FiniteCardinal.of_nat n) = n := by
  induction n with
  | zero => simp only [to_nat, FiniteCardinal, Nat.zero_eq, Nat.succ_eq_add_one, of_nat,
    recursion_zero]
  | succ n ih => simp only [to_nat, FiniteCardinal, Nat.zero_eq, Nat.succ_eq_add_one, of_nat,
    recursion_succ, Nat.add_right_cancel_iff]; exact ih

@[simp high] theorem of_nat_to_nat: FiniteCardinal.of_nat (FiniteCardinal.to_nat x) = x := by
  apply Cardinal.Finite.induction (p := fun x => FiniteCardinal.of_nat (FiniteCardinal.to_nat x) = x)
  · simp only [FiniteCardinal, to_nat, Nat.zero_eq, Nat.succ_eq_add_one, recursion_zero, of_nat]
  · intro a h
    simp only [FiniteCardinal, to_nat, Nat.zero_eq, Nat.succ_eq_add_one, recursion_succ, of_nat,
      Subtype.eq_iff]
    congr

@[simp] theorem of_nat_bij : Function.Bijective FiniteCardinal.of_nat := by
  apply Function.hasInverse_iff_bij.mp
  exists FiniteCardinal.to_nat
  constructor
  · ext x; exact to_nat_of_nat
  · ext x; exact of_nat_to_nat

@[simp] theorem to_nat_bij : Function.Bijective FiniteCardinal.to_nat := by
  apply Function.hasInverse_iff_bij.mp
  exists FiniteCardinal.of_nat
  constructor
  · ext x; exact of_nat_to_nat
  · ext x; exact to_nat_of_nat

@[simp] theorem of_nat_add : FiniteCardinal.of_nat (n + m) = (FiniteCardinal.of_nat n : Cardinal.{u}) + FiniteCardinal.of_nat m := by
  induction n with
  | zero => simp only [Nat.zero_add, of_nat, Cardinal.zero_add]
  | succ n ih => rw[Nat.add_assoc, Nat.add_comm 1 m, ← Nat.add_assoc]
                 simp only [of_nat]
                 rw[ih]
                 rw[← Cardinal.add_assoc, Cardinal.add_comm (b := 1), Cardinal.add_assoc]

@[simp] theorem of_nat_mul : FiniteCardinal.of_nat (n * m) = (FiniteCardinal.of_nat n : Cardinal.{u}) * FiniteCardinal.of_nat m := by
  induction n with
  | zero => simp only [Nat.zero_mul, of_nat, Cardinal.zero_mul]
  | succ n ih => rw[Nat.add_mul _ _ _]
                 simp only [Nat.one_mul, of_nat_add, of_nat]
                 rw[ih, Cardinal.mul_add_distrib_right, Cardinal.one_mul]

@[simp] theorem of_nat_pow : FiniteCardinal.of_nat (n ^ m) = (FiniteCardinal.of_nat n : Cardinal.{u}) ^ (FiniteCardinal.of_nat m : Cardinal.{u}):= by
  induction m with
  | zero => simp only [of_nat, Cardinal.zero_add, Cardinal.pow_zero]
  | succ m ih => rw[Nat.pow_add _ _ _]
                 simp only [Nat.pow_one, of_nat_mul, ih, of_nat, Cardinal.pow_add, Cardinal.pow_one]

@[simp] theorem of_nat_isOrderIso : IsOrderIso of_nat := by
  apply isOrderIso_iff_reflect.mpr
  · constructor
    · exact of_nat_bij
    · constructor
      · intro x y h
        induction h with
        | refl => rfl
        | step h' ih => simp only [FiniteCardinal, of_nat, Subtype.le_iff_val] at *;
                        apply le_trans ih Cardinal.le_add_left
      · intro x y h
        have h' := h
        rw[Subtype.le_iff_val, ← Cardinal.exists_add_iff_le] at h
        obtain ⟨c,eq⟩ := h
        have : c ≤ (of_nat y) := by
          rw[← Cardinal.exists_add_iff_le]
          exists (of_nat x).val
          rw[eq, Cardinal.add_comm]
        have fin : c.Finite := Cardinal.Finite.of_le_finite (of_nat y).2 this
        change _ = _ + (⟨c,fin⟩ : FiniteCardinal).val at eq
        rw[← of_nat_to_nat (x := ⟨c,fin⟩), ← of_nat_add, ← Subtype.eq_iff] at eq
        have eq := of_nat_bij.inj _ _ eq
        rw[eq]
        simp only [to_nat, FiniteCardinal, Nat.zero_eq, Nat.succ_eq_add_one, Nat.le_add_right]

@[simp] theorem to_nat_isOrderIso : IsOrderIso to_nat := by
  have: of_nat_bij.inv = to_nat := by
    apply Function.IsInverseOf.eq_inv
    constructor
    · ext x; exact of_nat_to_nat
    · ext x; exact to_nat_of_nat
  rw[← this]
  apply IsOrderIso.inv of_nat_isOrderIso

@[simp] theorem to_nat_le_iff : to_nat x ≤ to_nat y ↔ x ≤ y := to_nat_isOrderIso.le_iff
@[simp] theorem to_nat_lt_iff : to_nat x < to_nat y ↔ x < y := by
  rw[Nat.lt_iff_le_not_le]
  rw[to_nat_le_iff, lt_iff_le_not_le, to_nat_le_iff]

@[simp] theorem of_nat_le_iff : of_nat n ≤ of_nat m ↔ n ≤ m := of_nat_isOrderIso.le_iff
@[simp] theorem of_nat_lt_iff : of_nat n < of_nat m ↔ n < m := by
  rw[Nat.lt_iff_le_not_le, lt_iff_le_not_le]
  rw[of_nat_le_iff, of_nat_le_iff]


end FiniteCardinal
end Nat
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

section
variable {a b : Cardinal.{u}} [ha : Cardinal.Finite a] [hb : Cardinal.Finite b]

instance sum_finite : Cardinal.Finite (a + b) := by
  obtain ⟨a,rfl⟩ := Cardinal.mk_surj.exists_preimage a
  obtain ⟨b,rfl⟩ := Cardinal.mk_surj.exists_preimage b
  have : Finite a := ⟨ha⟩
  have : Finite b := ⟨hb⟩
  simp only [Cardinal.add_mk]
  infer_instance

instance mul_finite : Cardinal.Finite (a * b) := by
  obtain ⟨a,rfl⟩ := Cardinal.mk_surj.exists_preimage a
  obtain ⟨b,rfl⟩ := Cardinal.mk_surj.exists_preimage b
  have : Finite a := ⟨ha⟩
  have : Finite b := ⟨hb⟩
  simp only [Cardinal.mul_mk]
  infer_instance

instance pow_finite : Cardinal.Finite (a ^ b) := by
  obtain ⟨a,rfl⟩ := Cardinal.mk_surj.exists_preimage a
  obtain ⟨b,rfl⟩ := Cardinal.mk_surj.exists_preimage b
  have : Finite a := ⟨ha⟩
  have : Finite b := ⟨hb⟩
  simp only [Cardinal.pow_mk]
  infer_instance

end
variable {x y : FiniteCardinal.{u}} {n m : Nat}
namespace FiniteCardinal
@[simp] theorem to_nat_add : to_nat ⟨x.val + y.val, inferInstance⟩ = to_nat x + to_nat y := by
  apply of_nat_bij.inj _ _
  simp only [FiniteCardinal, Subtype.eq_iff, of_nat_add]
  rw[of_nat_to_nat,of_nat_to_nat,of_nat_to_nat]

@[simp] theorem to_nat_mul : to_nat ⟨x.val * y.val, inferInstance⟩ = to_nat x * to_nat y := by
  apply of_nat_bij.inj _ _
  simp only [FiniteCardinal, Subtype.eq_iff, of_nat_mul]
  rw[of_nat_to_nat,of_nat_to_nat,of_nat_to_nat]

@[simp] theorem to_nat_pow : to_nat ⟨x.val ^ y.val, inferInstance⟩ = to_nat x ^ to_nat y := by
  apply of_nat_bij.inj _ _
  simp only [FiniteCardinal, Subtype.eq_iff, of_nat_pow]
  rw[of_nat_to_nat,of_nat_to_nat,of_nat_to_nat]


end FiniteCardinal
instance {α : Type u} {a b : Set α} [Finite a] [Finite b] : Finite ((a ∪ b) : Set α) where
  finite := by
    apply Cardinal.Finite.of_le_finite (b := Cardinal.mk a + Cardinal.mk b)
    · infer_instance
    · simp only [Cardinal.add_mk]
      apply Cardinal.ge_of_surj
      exists Sum.elim (fun ⟨x,h⟩ => ⟨x, Or.inl h⟩) (fun ⟨x,h⟩ => ⟨x, Or.inr h⟩)
      rw[Function.surj_iff]
      rintro ⟨x,(h|h)⟩
      · exists Sum.inl ⟨x,h⟩
      · exists Sum.inr ⟨x,h⟩

instance {α : Type u} {a : Set α} {b : α} [Finite a] : Finite (insert b a : Set α) := by
  change Finite ({b} ∪ a : Set α)
  infer_instance
