import BourbakiLean2.Order.TotalOrder
import BourbakiLean2.Order.Intervals
import BourbakiLean2.Order.Coverings
universe u v
variable {α : Type u} {x y z : α}

class WellOrder (α : Type*) extends TotalOrder α where
  existsLeast {s : Set α} (h : s.Nonempty) : ∃ a, ∃ h : a ∈ s, Least (⟨a,h⟩ : s)

class IsWellOrder (r : Relation α α) extends IsTotalOrder r where
  existsLeast {s : Set α} (h : s.Nonempty) : ∃ a, ∃ _h : a ∈ s, ∀ b : s, (a, b.val) ∈ r

instance {r : Relation α α} [inst : IsWellOrder r] : WellOrder (RelAsLE r) where
  existsLeast := inst.existsLeast

theorem WellOrder.isWellOrder [WellOrder α] : IsWellOrder ({p | p.1 ≤ p.2} : Relation α α) where
  le_antisymm := PartialOrder.le_antisymm
  le_refl := Preorder.le_refl
  le_trans := Preorder.le_trans
  le_total := TotalOrder.le_total
  existsLeast := WellOrder.existsLeast

instance: WellOrder Empty where
  existsLeast h := by rcases h with ⟨⟨⟩,h⟩

instance: WellOrder Unit where
  existsLeast h := by
    rcases h with ⟨⟨⟩,h⟩
    exists PUnit.unit
    simp only [Least, le_rfl, implies_true, exists_const, h]

instance [WellOrder α] {p : α → Prop} : WellOrder {x // p x} where
  existsLeast {s} h := by
    rcases h with ⟨⟨a,h⟩,h'⟩
    have ⟨a,⟨hp,hs⟩,hl⟩ := WellOrder.existsLeast (s := {x | ∃ h, ⟨x,h⟩ ∈ s}) ⟨a,h,h'⟩
    exists ⟨a,hp⟩
    exists hs
    simp only [Least, Subtype.le_iff_val, Subtype.forall]
    intro b hbp hbs
    exact hl ⟨b,hbp,hbs⟩

instance [WellOrder α] : WellOrder (AdjoinGreatest α) where
  existsLeast {s} h' := by
    by_cases h : ∃ a, AdjoinGreatest.to a ∈ s
    · rcases h with ⟨a,ha⟩
      let t := Set.preimage AdjoinGreatest.to s
      have ⟨a,ha,hleast⟩ := WellOrder.existsLeast (s := t) ⟨a, Set.mem_preimage_iff.mpr ha⟩
      exists AdjoinGreatest.to a
      exists Set.mem_preimage_iff.mp ha
      intro ⟨b,hb⟩
      rcases b with (b|b)
      · simp only [Subtype.le_iff_val, ge_iff_le]
        exact hleast ⟨b,Set.mem_preimage_iff.mpr hb⟩
      · trivial
    · obtain ⟨(a|a), ha⟩ := h'
      · exact (h ⟨_,ha⟩).elim
      · exists AdjoinGreatest.greatest
        rcases a
        exists ha
        rintro ⟨(b|b),hb⟩
        · exact (h ⟨_,hb⟩).elim
        · trivial

def totalOrder_of_exists_least [PartialOrder α] (h : ∀ {s : Set α} (_ : s.Nonempty), ∃ a, ∃ h : a ∈ s, Least (⟨a,h⟩ : s)) :
    TotalOrder α where
  le_total x y := by
    obtain ⟨a,(rfl|rfl), least⟩ := h (s := {x,y}) ⟨x, Or.inl rfl⟩
    · simp only [Least, Subtype.le_iff_val, Subtype.forall, Set.mem_pair_iff, forall_eq_or_imp,
      le_rfl, forall_eq, true_and] at least
      left
      assumption
    · simp only [Least, Subtype.le_iff_val, Subtype.forall, Set.mem_pair_iff, forall_eq_or_imp,
      forall_eq, le_rfl, and_true] at least
      right
      assumption


def IsOrderIso.wellOrder {β : Type*} [WellOrder α] [PartialOrder β] {f : α → β} (h : IsOrderIso f) : WellOrder β where
  le_total a b := h.totalOrder.le_total a b
  existsLeast {s} h' := by
    rcases h' with ⟨w,h'⟩
    obtain ⟨a,ha,least⟩ := WellOrder.existsLeast (s := f ⁻¹' s) (by
      exists h.bij.inv w
      simp only [Set.mem_preimage_iff, Function.Bijective.val_inv_val, h'])
    exists f a
    exists Set.mem_preimage_iff.mp ha
    rintro ⟨b,hb⟩
    obtain ⟨a',rfl⟩ := h.bij.surj.exists_preimage b
    apply h.monotone
    rw[← Set.mem_preimage_iff] at hb
    exact least ⟨a',hb⟩

namespace WellOrder
variable [WellOrder α]
def carry_bij {β : Type*} (f : Function.Bijection α β) : WellOrder β where
  le := (Preorder.carry_bij f).le
  le_refl := (Preorder.carry_bij f).le_refl
  le_trans := (Preorder.carry_bij f).le_trans
  le_antisymm := (PartialOrder.carry_bij f).le_antisymm
  le_total := (TotalOrder.carry_bij f).le_total
  existsLeast := by
    intro s h
    obtain ⟨a,ha,least⟩ := WellOrder.existsLeast (s := f ⁻¹' s) (by
      obtain ⟨b,hb⟩ := h
      exists f.inv b
      simp only [Set.mem_preimage_iff, Function.Bijection.val_inv_val, hb])
    exists f a
    simp only [Set.mem_preimage_iff] at ha
    exists ha
    intro ⟨b,hb⟩
    specialize least ⟨f.inv b, (by simp only [Set.mem_preimage_iff,
      Function.Bijection.val_inv_val, hb])⟩
    simp only [Subtype.le_iff_val] at least
    rw[← f.inv_val_val (a := a)] at least
    exact least


theorem hasLUB_of_bounded_above {s : Set α} (h : s.BoundedAbove) : ∃ x, IsLUB s x := by
  let t := {a | UpperBound s a}
  have h : t.Nonempty := h
  have ⟨a, h, least⟩ := existsLeast h
  exact ⟨a,⟨h,least⟩⟩

theorem isIio_of_downwardsClosed {s : Set α} (h : s.IsDownwardsClosed) (h' : s ≠ Set.univ) :
    ∃ x, s = Set.Iio x := by
  have h' : (s ᶜ).Nonempty := by
    by_contra h
    rw[Set.nonempty_iff_neq_empty] at h
    simp at h
    rw[← Set.compl_compl (x := ∅), Set.compl_empty] at h
    have h := Set.compl_inj h
    exact h' h
  have ⟨a,ha,least⟩ := existsLeast (s := sᶜ) h'
  have: sᶜ = Set.Ici a := by
    ext b
    constructor
    · intro h
      exact least ⟨b,h⟩
    · intro h' h''
      exact (ha $ Set.mem_of_le_mem h' h'').elim
  exists a
  rw[← Set.compl_compl (x := s), this]
  simp only [Set.Ici_compl]

def InitialSegment (α : Type u) [WellOrder α] : Type u := {s : Set α // s.IsDownwardsClosed}

def InitialSegment.mk (a : α) : InitialSegment α := ⟨Set.Iio a, by infer_instance⟩
def InitialSegment.univ : InitialSegment α := ⟨Set.univ, by infer_instance⟩
noncomputable def InitialSegment.succ_mk (a : α) : InitialSegment α :=
  ⟨Set.Iio a ∪ {a}, by
    constructor
    simp only [Set.Iio_union_point_eq_Iic, Set.mem_Iic_iff]
    exact le_trans⟩

theorem InitialSegment.mk_inj : Function.Injective (InitialSegment.mk : α → InitialSegment α) := by
  intros a b h
  rw[InitialSegment.mk, InitialSegment.mk, Subtype.eq_iff] at h
  simp only at h
  rw[Set.eq_iff_subset_subset, Set.Iio_subset_Iio_iff, Set.Iio_subset_Iio_iff] at h
  exact le_antisymm h.1 h.2

@[simp] theorem InitialSegment.univ_neq_mk {a : α} : InitialSegment.univ ≠ InitialSegment.mk a := by
  intro h
  rw[Subtype.eq_iff, Set.ext_iff] at h
  simp only [univ, Set.mem_univ, mk, Set.mem_Iio_iff, true_iff] at h
  exact (not_lt_self (h a)).elim

instance : PartialOrder (InitialSegment α) where
  le x y := x.val ⊆ y.val
  le_refl a := le_refl a.val
  le_trans a b c h h' := le_trans (a := a.val) h h'
  le_antisymm a b h h' := Subtype.eq $ le_antisymm h h'

@[simp] theorem InitialSegment.mk_le_mk_iff {a b : α} : InitialSegment.mk a ≤ InitialSegment.mk b ↔ a ≤ b := by
  simp only [LE.le, mk, Set.Iio_subset_Iio_iff]

@[simp] theorem InitialSegment.le_univ {a : InitialSegment α} : a ≤ InitialSegment.univ := by
  simp only [LE.le, mk, univ, Set.subset_univ]

theorem InitialSegment.univ_greatest : Greatest (InitialSegment.univ : InitialSegment α) :=
  fun _ => Set.subset_univ

theorem InitialSegment.mk_or_univ (i : InitialSegment α) : (∃ a, i = InitialSegment.mk a) ∨ i = InitialSegment.univ := by
  by_cases h : i.val = Set.univ
  · right
    rwa[Subtype.eq_iff]
  · left
    obtain ⟨a,ha⟩ := isIio_of_downwardsClosed i.property h
    exact ⟨a, Subtype.eq ha⟩

@[simp] theorem InitialSegment.mk_lt_succ_mk {a : α} : InitialSegment.mk a < InitialSegment.succ_mk a := by
  constructor
  · simp only [mk, succ_mk, Set.Iio_union_point_eq_Iic, Set.Iio_subset_Iic]
  · intro h
    simp only [succ_mk, Set.Iio_union_point_eq_Iic, mk] at h
    exact Set.not_mem_Iio_self $ h (le_refl a)

instance : TotalOrder (InitialSegment α) where
  le_total a b := by
    rcases InitialSegment.mk_or_univ a with (⟨a,rfl⟩|rfl)
    · rcases InitialSegment.mk_or_univ b with (⟨b,rfl⟩|rfl)
      · rcases le_total a b with (h|h)
        · left
          simpa only [InitialSegment.mk_le_mk_iff]
        · right
          simpa only [InitialSegment.mk_le_mk_iff]
      · left
        simp only [InitialSegment.le_univ]
    · right
      simp only [InitialSegment.le_univ]

@[simp] def InitialSegment.adjoinGreatest_iso : AdjoinGreatest α → InitialSegment α
  | Sum.inr _ => InitialSegment.univ
  | Sum.inl a => InitialSegment.mk a

theorem InitialSegment.adjoinGreatest_iso_is_iso : IsOrderIso (InitialSegment.adjoinGreatest_iso (α := α)) := by
  apply isOrderIso_iff_reflect.mpr
  constructor
  · constructor
    · rintro (a|⟨⟩) (b|⟨⟩) h
      · simp only [adjoinGreatest_iso] at h
        rw[InitialSegment.mk_inj _ _ h]
      · simp only [adjoinGreatest_iso] at h
        exact (InitialSegment.univ_neq_mk h.symm).elim
      · simp only [adjoinGreatest_iso] at h
        exact (InitialSegment.univ_neq_mk h).elim
      · simp only [adjoinGreatest_iso]
    · rw[Function.surj_iff]
      intro b
      rcases b.mk_or_univ with (⟨b,rfl⟩|rfl)
      · exact ⟨Sum.inl b, rfl⟩
      · exact ⟨Sum.inr (), rfl⟩
  · constructor
    · rintro (a|⟨⟩) (b|⟨⟩) h
      · simp only [adjoinGreatest_iso, mk_le_mk_iff]
        exact h
      · simp only [adjoinGreatest_iso, le_univ]
      · simp only [LE.le] at h
      · simp only [adjoinGreatest_iso, le_rfl]
    · rintro (a|⟨⟩) (b|⟨⟩) h
      · simp only [adjoinGreatest_iso, mk_le_mk_iff] at h
        exact h
      · trivial
      · simp only [adjoinGreatest_iso] at h
        have := InitialSegment.univ_greatest.maximal (α := InitialSegment α) _ h
        exact (InitialSegment.univ_neq_mk this.symm).elim
      · simp only [adjoinGreatest_iso, le_rfl]

instance : WellOrder (InitialSegment α) := IsOrderIso.wellOrder InitialSegment.adjoinGreatest_iso_is_iso

instance {a : InitialSegment α} : Set.IsDownwardsClosed a.val := a.property

theorem InitialSegment.induction {α : Type u} [WellOrder α] {p : InitialSegment α → Prop} {x}
    (h_union : ∀ ι : Type u, ∀ f : ι → InitialSegment α, ((i : ι) → p (f i)) →
      p ⟨⋃ i, (f i).val, @Set.IsDownwardsClosed.iUnion _ _ _ _ (fun i => (f i).property)⟩)
    (h_succ : ∀ a, p (InitialSegment.mk a) → p (InitialSegment.succ_mk a)) :
    p x := by
  by_contra h
  let invalid := {x | ¬ p x}
  have h_invalid : invalid.Nonempty := ⟨x, h⟩
  obtain ⟨a,ha,least⟩ := existsLeast h_invalid
  by_cases h' : ∃ x : a.val, Greatest x
  · rcases h' with ⟨⟨x,h⟩,h''⟩
    have : a = (InitialSegment.succ_mk x) := by
      rw[Subtype.eq_iff, InitialSegment.succ_mk]
      ext y
      simp only [Set.Iio_union_point_eq_Iic, Set.mem_Iic_iff]
      constructor
      · intro hy
        have := h'' ⟨y,hy⟩
        exact this
      · intro hy
        exact a.property.mem_of_le_mem hy h
    have that : p (InitialSegment.mk x) := by
      by_contra h'''
      have that := least (b := ⟨mk x, h'''⟩)
      simp only [this, Subtype.le_iff_val] at that
      apply not_lt_self $ lt_of_le_lt that _
      simp only [mk_lt_succ_mk]
    replace that := h_succ x that
    rw[← this] at that
    exact ha that
  · rw[not_exists] at h'
    have := Set.iUnion_Iio_of_no_greatest h'
    have eq : a.val = ⋃ x : {x : InitialSegment α // x < a}, x.val.val := by
      ext y
      rw[Set.ext_iff] at this
      simp only [Set.mem_iUnion_iff, Set.mem_Iio_iff, Subtype.lt_iff_val, Subtype.exists,
        exists_prop, Set.mem_univ, iff_true, Subtype.forall] at this
      specialize this y
      constructor
      · intro h
        simp only [Set.mem_iUnion_iff, Subtype.exists, exists_prop]
        obtain ⟨b,hb1,hb2⟩ := this h
        exists mk b
        apply And.intro _ hb2
        rw[lt_iff_le_not_eq]
        rcases a.mk_or_univ with (⟨a,rfl⟩|rfl)
        · constructor
          · apply Set.Iio_subset_Iio_iff.mpr $ le_of_lt hb1
          · intro eq
            rw[← eq] at hb1
            apply not_lt_self hb1
        · constructor
          · apply Set.subset_univ
          · intro eq
            rw[← eq] at hb1
            apply not_lt_self hb1
      · rintro ⟨⟨b,blta⟩,hb⟩
        simp only at hb
        exact le_of_lt blta hb
    have : ∀ x : {x : InitialSegment α // x < a}, p x.val := by
      intro x
      by_contra h
      specialize least (b := ⟨x.val, h⟩)
      apply not_lt_self $ lt_of_le_lt least x.property
    have that := h_union (ι := { x // x < a }) (f := Subtype.val) this
    have eq2 : a = ⟨⋃ x : {x : InitialSegment α // x < a}, x.val.val, @Set.IsDownwardsClosed.iUnion _ _ _ _ (fun i => i.val.property)⟩ := by
      rw[Subtype.eq_iff, eq]
    rw[eq2] at ha
    exact ha that

theorem wf_induction {p : α → Prop} (h : ∀ x, (∀ y, y < x → p y) → p x) : ∀ x, p x := by
  intro x
  by_contra h'
  let s := {x | ¬ p x}
  have h' : s.Nonempty := ⟨x, h'⟩
  obtain ⟨a,ha,least⟩ := existsLeast h'
  by_contra h''
  have := h a (λ y hy => by
    by_contra h'''
    have := least ⟨y,h'''⟩
    apply not_lt_self $ lt_of_le_lt this hy)
  exact ha this

theorem wf_recursion_all_eq {p : α → Type*} {f g : ∀ x, p x}
    (h : ∀ x, (∀ y, y < x → p y) → p x)
    (eqf : ∀ x, h x (fun y _ => f y) = f x)
    (eqg : ∀ x, h x (fun y _ => g y) = g x) : f = g := by
  ext a
  apply wf_induction (p := fun x => f x = g x)
  intro x h'
  rw[← eqf x, ← eqg x]
  have h'' : (fun y (_ : y < x) ↦ f y) = fun y (_ : y < x) ↦ g y := by
    funext y lt
    rw[h' y]
    exact lt
  rw[h'']

theorem wf_recursion_exists {p : α → Type u} (h : ∀ x, (∀ y, y < x → p y) → p x) :
    ∃ f : (x : α) → p x, ∀ x, f x = h x (fun y _ => f y) := by
  let q : InitialSegment α → Prop := fun i => ∃ f : (x : i.val) → p x, ∀ x, f x = h x (fun y h' => f ⟨y, i.property.mem_of_le_mem (le_of_lt h') x.property⟩)
  have h_union : ∀ ι : Type u, ∀ f : ι → InitialSegment α, ((i : ι) → q (f i)) →
                  q ⟨⋃ i, (f i).val, @Set.IsDownwardsClosed.iUnion _ _ _ _ (fun i => (f i).property)⟩ := by
    intro ι f h'
    simp only [Subtype.forall, Set.mem_iUnion_iff, forall_exists_index, q] at *
    have cover : Set.IsCovering (fun i => {a : { a // a ∈ ⋃ i, (f i).val } | a.val ∈ (f i).val}) := by
      ext ⟨x, ⟨i, hi⟩⟩
      simp only [Set.mem_iUnion_iff, Set.mem_setOf_iff, Set.mem_univ, iff_true]
      exact ⟨i,hi⟩
    let func : (i : ι) →
    (a : { a : { a // a ∈ ⋃ i, (f i).val } // a ∈ (fun i ↦ {a | a.val ∈ (f i).val}) i }) →
      (fun x ↦ p x.val) a.val := by
      rintro i ⟨a,hi'⟩
      apply Classical.choose (h' i) ⟨_,hi'⟩
    let o : (x : { a // a ∈ ⋃ i, (f i).val }) → p x.val :=
      Set.IsCovering.glue (x := fun i => {a : { a // a ∈ ⋃ i, (f i).val } | a.val ∈ (f i).val}) (β := fun x => p x.val) cover func

    exists o
    intro a i ha
    simp only [Set.mem_setOf_iff, implies_true, o]
    have := fun a i (ha : a ∈ (f i).val) => cover.glue_agrees (β := fun x => p x.val) (f := func) (i := i) (a := ⟨a, ⟨i,by simp only [ha]⟩⟩) (by
      rintro ⟨b,hb⟩ j j' h1 h2
      have := wf_recursion_all_eq
        (α := {a : { a // a ∈ ⋃ i, (f i).val } | a.val ∈ (f j).val ∧ a.val ∈ (f j').val})
        (p := fun a => p a.val.val)
        (f := fun ⟨⟨a,hi⟩,hj,hj'⟩ => func j ⟨⟨a,hi⟩,hj⟩)
        (g := fun ⟨⟨a,hi⟩,hj,hj'⟩ => func j' ⟨⟨a,hi⟩,hj'⟩)
        (by
          intro a hind
          apply h
          intro y hy
          apply hind ⟨⟨y,_⟩,_,_⟩ hy
          · apply Set.IsDownwardsClosed.mem_of_le_mem (le_of_lt hy) a.val.property
          · apply Set.IsDownwardsClosed.mem_of_le_mem (le_of_lt hy) a.property.1
          · apply Set.IsDownwardsClosed.mem_of_le_mem (le_of_lt hy) a.property.2)
        (by
          rintro ⟨⟨a,⟨i, ai⟩⟩,aj,aj'⟩
          simp only [Classical.choose_spec (h' j) a aj, func])
        (by
          rintro ⟨⟨a,⟨i, ai⟩⟩,aj,aj'⟩
          simp only [Classical.choose_spec (h' j') a aj', func])
      exact congrFun this ⟨⟨b,hb⟩,h1,h2⟩) ha

    rw[this a i ha]
    apply Eq.trans
    · simp only [func]
      rw[Classical.choose_spec (h' i) a ha]
    · congr
      ext b hb
      specialize this b i (Set.IsDownwardsClosed.mem_of_le_mem (le_of_lt hb) ha)
      rw[this]
  have h_succ : ∀ a, q (InitialSegment.mk a) → q (InitialSegment.succ_mk a) := by
    intro a ⟨f,hf⟩
    exists (by
      intro ⟨b,hb⟩
      have hb2 := hb
      simp only [InitialSegment.succ_mk, Set.mem_union_iff] at hb2
      classical
      apply hb.by_cases
      · intro hb1
        apply f ⟨_,hb1⟩
      · intro path
        apply h
        intro a lta
        apply f ⟨_,path ▸ lta⟩)
    rintro ⟨b,(hb|hb)⟩
    · simp only [Or.by_cases, hb, ↓reduceDIte, Set.mem_Iio_iff]
      rw[hf]
      congr
      ext y h'
      have : y ∈ Set.Iio a := lt_of_lt_lt h' hb
      simp only [this, ↓reduceDIte]
    · rcases hb
      simp only [Or.by_cases, Set.not_mem_Iio_self, ↓reduceDIte, Set.mem_Iio_iff]
      congr
      ext b hb
      rw[hf ⟨b,hb⟩]
      simp[hb]
      rw[hf ⟨b,hb⟩]
  obtain ⟨f,hf⟩ := InitialSegment.induction h_union h_succ (x := InitialSegment.univ)
  exists fun x => f ⟨x, True.intro⟩
  intro x
  simp only [hf ⟨x, True.intro⟩]

noncomputable def wf_recursion {p : α → Type u} (h : ∀ x, (∀ y, y < x → p y) → p x) : (x : α) → p x :=
  Classical.choose (wf_recursion_exists h)

theorem wf_recursion_eq {p : α → Type u} (h : ∀ x, (∀ y, y < x → p y) → p x) (x : α) :
    (wf_recursion h x) = h x (fun y _ => wf_recursion h y) := by
  unfold wf_recursion
  rw[Classical.choose_spec $ wf_recursion_exists h]


end WellOrder

namespace ZermeloTheorem

instance isWellOrderColimit {ι} {x : ι → Set α} [RightDirected (x '' Set.univ)]
    (h : Set.IsCovering x) {f : (i : ι) → Relation (x i) (x i)} [inst: ∀ i, IsWellOrder $ f i]
    (h' : ∀ i j, (sub : x i ⊆ x j) → ∀ a b, (ha : a ∈ x i) → (hb : b ∈ x i) →
      (⟨a,ha⟩,⟨b,hb⟩) ∈ f i ↔ (⟨a, sub ha⟩,⟨b, sub hb⟩) ∈ f j)
    (h'' : ∀ i j, (sub : x i ⊆ x j) → ∀ a b, (ha : a ∈ x i) → (hb : b ∈ x j) → (⟨b,hb⟩,⟨a,sub ha⟩) ∈ f j → b ∈ x i)
    (h''' : ∀ i j, x i ⊆ x j ∨ x j ⊆ x i):
    IsWellOrder (h.glue_rel f) where
  le_trans := (Set.isPreorderColimit h h').le_trans
  le_refl := (Set.isPreorderColimit h h').le_refl
  le_antisymm := (Set.isPartialOrderColimit h h').le_antisymm
  le_total := (Set.isTotalOrderColimit h h').le_total
  existsLeast := by
    rintro s ⟨n, hn⟩
    have ⟨i,hi⟩ := h.mem_exists n
    have ⟨⟨min, minmemi⟩, minmems, ismin⟩ := (inst i).existsLeast (s := {x | x.val ∈ s}) ⟨⟨n,hi⟩,hn⟩
    exists min
    exists minmems
    intro ⟨b,hb⟩
    have ⟨j,hj⟩ := h.mem_exists b
    rcases h''' i j with (sb|sb)
    · have hi' := sb minmemi
      rw[Set.IsCovering.glue_rel_agrees h h' _ _ hi' hj]
      specialize h'' _ _ sb min b minmemi hj
      rcases (inst j).le_total ⟨b,hj⟩ ⟨min, hi'⟩ with (le|le)
      · specialize h'' le
        rw[← h' i j sb _ _ minmemi h'']
        apply ismin ⟨⟨b,h''⟩,hb⟩
      · exact le
    · have hi' := sb hj
      rw[Set.IsCovering.glue_rel_agrees h h' _ _ minmemi hi']
      apply ismin ⟨⟨b,hi'⟩,hb⟩

structure PartialWellOrder (α : Type*) (s : Set (Set α)) (p : s → α) where
  domain : Set α
  order : WellOrder domain
  iic_mem : ∀ x, {↑ a | a ∈ @Set.Iic _ order.toPreorder x} ∈ s
  iic_func : ∀ x : domain, p ⟨{↑ a | a ∈ @Set.Iic _ order.toPreorder x}, iic_mem x⟩ = (x : α)
  domain_not_mem : domain ∉ s

def make_partialWellOrder {s : Set (Set α)} (p : s → α) (hf : ∀ a, p a ∉ a.val) :
    PartialWellOrder α s p := by
  let M : Set (Sigma (α := Set α) (fun s => Relation s s)) :=
    {pair | IsWellOrder pair.2 ∧ ∀ x : pair.1,
      ∃ h : (Subtype.val : pair.1 → α) '' {y : pair.1 | (y,x) ∈ pair.2} ∈ s,
        p ⟨_,h⟩ = x}
  let x : (i : M) → Set α := fun a => a.val.1
  let f : (i : M) → Relation (x i) (x i) := fun a => a.val.2
  sorry
  /-
  have total : ∀ i j, x i ⊆ x j ∨ x j ⊆ x i := by
    intro i j
    rw[← Set.inter_eq_iff_subset_left, ← Set.inter_eq_iff_subset_right]
    let v := {a | ∃ (h : a ∈ x i ∩ x j), Subtype.val '' {b | ⟨b,⟨a,h.1⟩⟩ ∈ f i} = Subtype.val '' {b | ⟨b,⟨a,h.2⟩⟩ ∈ f j} ∧
      ∀ b c, (hb : b ∈ x i ∩ x j) → (hc : c ∈ x i ∩ x j) → ⟨⟨b,hb.1⟩,⟨c,hc.1⟩⟩ ∈ f i ↔  ⟨⟨b,hb.2⟩,⟨c,hc.2⟩⟩ ∈ f j}

    suffices eq : v = x i ∨ v = x j by
      rcases eq with (eq|eq)
      · rw[← eq]
        left

-/
def zermelo : WellOrder α := by
  let s := {Set.univ (α := α)} ᶜ
  let p : s → α := fun a => Exists.choose (p := fun x => x ∈ a.1 ᶜ) (by
    rcases a with ⟨a,p⟩
    unfold s at p
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.ext_iff, Set.mem_univ, iff_true,
      Classical.not_forall] at p
    exact p)
  have notin : ∀ a, p a ∉ a.1 := by
    intro a
    apply Exists.choose_spec (p := fun x => x ∈ a.1 ᶜ) (by
      rcases a with ⟨a,p⟩
      unfold s at p
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.ext_iff, Set.mem_univ, iff_true,
        Classical.not_forall] at p
      exact p)
  have pwo := make_partialWellOrder p notin
  have := pwo.domain_not_mem
  simp[s] at this
  have order := pwo.order
  rw[this] at order
  exact WellOrder.carry_bij Function.bijection_univ


end ZermeloTheorem
export ZermeloTheorem (zermelo)
