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
noncomputable instance: WellOrder FiniteCardinal := by unfold FiniteCardinal; infer_instance
class Finite (α : Type u) where
  finite : Cardinal.Finite (Cardinal.mk α)

@[simp] theorem Finite.iff {α : Type u} : Finite α ↔ Cardinal.Finite (Cardinal.mk α) := by
  constructor
  · intro h
    exact h.finite
  · intro h
    constructor
    exact h

@[simp] def FiniteType := {α : Type u // Finite α}
def FiniteType.cardinality' : FiniteType.{u} → FiniteCardinal.{u} := fun ⟨x,h⟩ => ⟨Cardinal.mk x, h⟩

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

instance Finite.empty : Finite (∅ : Set α) := by
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

noncomputable def Cardinal.Finite.recursion {p : FiniteCardinal.{u} → Type*} (h0 : p ⟨0, zero⟩)
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
