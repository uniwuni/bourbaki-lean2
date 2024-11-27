import BourbakiLean2.Equivalence
import BourbakiLean2.Order.Synonyms
import BourbakiLean2.Set.Prod
variable {α : Type*}

def LE.le_rel [LE α] : Relation α α := fun ⟨a,b⟩ => a ≤ b
def LT.lt_rel [LT α] : Relation α α := fun ⟨a,b⟩ => a < b

@[simp] theorem LE.mem_le_rel_iff [LE α] {a b : α} : ⟨a,b⟩ ∈ LE.le_rel ↔ a ≤ b := Iff.rfl
@[simp] theorem LT.mem_lt_rel_iff [LT α] {a b : α} : ⟨a,b⟩ ∈ LT.lt_rel ↔ a < b := Iff.rfl


/-- type synonym to use the equality relation as a partial order -/
def WithEq (α : Type*) := α

class IsPreorder (r : Relation α α) where
  le_refl : ∀ a, (a, a) ∈ r
  le_trans : ∀ a b c, (a,b) ∈ r → (b,c) ∈ r → (a,c) ∈ r

class IsPartialOrder (r : Relation α α) extends IsPreorder r where
  le_antisymm : ∀ a b, (a,b) ∈ r → (b,a) ∈ r → a = b

class Preorder (α : Type*) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

class PartialOrder (α : Type*) extends Preorder α where
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b

instance {r : Relation α α} [inst : IsPreorder r] : Preorder (RelAsLE r) where
  le_refl := inst.le_refl
  le_trans := inst.le_trans

instance {r : Relation α α} [inst : IsPartialOrder r] : PartialOrder (RelAsLE r) where
  le_antisymm := inst.le_antisymm

instance {r : Relation α α} [inst : r.IsEquivalence] : IsPreorder r where
  le_refl := inst.refl
  le_trans _ _ _ := inst.trans

instance [LE α] {p : α → Prop} : LE {x : α // p x} where
  le x y := (x : α) ≤ y

instance [LT α] {p : α → Prop} : LT {x : α // p x} where
  lt x y := (x : α) < y

instance [Preorder α] {p : α → Prop} : Preorder {x : α // p x} where
  le_trans _ _ _ h h' := Preorder.le_trans _ _ _ h h'
  le_refl _ := Preorder.le_refl _
  lt_iff_le_not_le _ _ := Preorder.lt_iff_le_not_le _ _

instance [PartialOrder α] {p : α → Prop} : PartialOrder {x : α // p x} where
  le_antisymm _ _ h h' := Subtype.eq $ PartialOrder.le_antisymm _ _ h h'

section Preorder
variable [Preorder α] {a b c : α}

/-- The relation `≤` on a preorder is reflexive. -/
@[refl] theorem le_refl : ∀ a : α, a ≤ a := Preorder.le_refl

/-- A version of `le_refl` where the argument is implicit -/
theorem le_rfl : a ≤ a := le_refl a

/-- The relation `≤` on a preorder is transitive. -/
@[trans] theorem le_trans : a ≤ b → b ≤ c → a ≤ c := Preorder.le_trans _ _ _

theorem lt_iff_le_not_le : a < b ↔ a ≤ b ∧ ¬b ≤ a := Preorder.lt_iff_le_not_le _ _

theorem lt_of_le_not_le (hab : a ≤ b) (hba : ¬ b ≤ a) : a < b := lt_iff_le_not_le.2 ⟨hab, hba⟩

theorem le_of_lt (h : a < b) : a ≤ b := by
  rw[lt_iff_le_not_le] at h
  exact h.1

instance opPreorder : Preorder (Op α) where
  le_refl a := le_refl (α := α) a
  le_trans _ _ _ h h' := le_trans h' h
  lt_iff_le_not_le a b := by
    simp only [LT.lt, lt_iff_le_not_le, LE.le]

def Preorder.equivalent_rel : Relation α α := fun ⟨a,b⟩ => a ≤ b ∧ b ≤ a
@[simp] theorem Preorder.mem_equivalent_rel_iff {a b : α} : (a,b) ∈ Preorder.equivalent_rel ↔ (a ≤ b ∧ b ≤ a) := Iff.rfl

instance equivalent_rel : Relation.IsEquivalence (Preorder.equivalent_rel (α := α)) where
  refl _ := ⟨le_rfl, le_rfl⟩
  symm x := ⟨x.2,x.1⟩
  trans x y := ⟨le_trans x.1 y.1, le_trans y.2 x.2⟩

universe u
def Preorder.QuotEquiv (α : Type u) [inst : Preorder α] : Type u := Quot (α := α) (Function.curry Preorder.equivalent_rel)

end Preorder



section PartialOrder
variable [PartialOrder α] {a b : α}
theorem le_antisymm_iff : (a ≤ b ∧ b ≤ a) ↔ a = b :=
  ⟨fun ⟨h,h'⟩ => PartialOrder.le_antisymm _ _ h h',
   fun h => ⟨h ▸ le_refl a, h ▸ le_refl b⟩⟩

theorem le_antisymm : a ≤ b → b ≤ a → a = b := PartialOrder.le_antisymm a b

theorem le_iff_lt_or_eq : a ≤ b ↔ (a = b ∨ a < b) := by
  rw[lt_iff_le_not_le]
  constructor
  · intro h
    by_cases eq : a = b
    · left
      assumption
    · right
      exact ⟨h, fun h' => eq $ le_antisymm h h'⟩
  · rintro (rfl|⟨h,h'⟩)
    · rfl
    · assumption

theorem lt_iff_le_not_eq : a < b ↔ (a ≤ b ∧ a ≠ b) := by
  rw[lt_iff_le_not_le]
  constructor
  · rintro ⟨h,h'⟩
    constructor
    · assumption
    · rintro rfl
      exact h' h
  · rintro ⟨h,h'⟩
    constructor
    · assumption
    · intro h''
      exact h' $ le_antisymm h h''


@[simp] theorem PartialOrder.equivalent_rel_diag : Preorder.equivalent_rel = (Relation.diag (α := α)) := by
  ext ⟨a,b⟩
  simp only [Preorder.mem_equivalent_rel_iff, le_antisymm_iff, Relation.mem_diag_iff]

@[simp] theorem PartialOrder.graph_comp_self : (LE.le_rel (α := α)).comp LE.le_rel = LE.le_rel := by
  ext ⟨a,b⟩
  constructor
  · intro ⟨c,h,h'⟩
    simp only [LE.mem_le_rel_iff, ge_iff_le] at *
    apply le_trans h h'
  · intro h
    simp only [LE.mem_le_rel_iff, Relation.mem_comp_iff] at *
    exists a

@[simp] theorem PartialOrder.graph_inter_inv : (LE.le_rel (α := α)) ∩ LE.le_rel.inv = Relation.diag := by
  ext ⟨a,b⟩
  simp only [Set.mem_inter_iff, LE.mem_le_rel_iff, Relation.mem_inv_iff, le_antisymm_iff,
    Relation.mem_diag_iff]

end PartialOrder

theorem isPartialOrder_of_graph_prop {r : Relation α α} (h : r.comp r = r) (h' : r ∩ r.inv = Relation.diag) :
    IsPartialOrder r where
  le_refl a := by
    have : (a,a) ∈ Relation.diag := by simp only [Relation.mem_diag_iff]
    rw[← h'] at this
    exact this.1
  le_trans := by
    intro a b c h1 h2
    rw[← h]
    exists b
  le_antisymm := by
    intro a b h1 h2
    have : (a,b) ∈ r ∩ r.inv := ⟨h1,h2⟩
    rwa[h'] at this


instance opPartialOrder [PartialOrder α]: PartialOrder (Op α) where
  le_antisymm _ _ h h' := PartialOrder.le_antisymm (α := α) _ _ h' h


instance : PartialOrder (WithEq α) where
  le a b := a = b
  le_refl _ := rfl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ h _ := h


instance : PartialOrder (Set α) where
  le a b := a ⊆ b
  le_refl _ := Set.subset_rfl
  le_trans _ _ _ := Set.subset_trans
  le_antisymm _ _ a b := Set.eq_iff_subset_subset.mpr ⟨a,b⟩

@[simp] theorem le_set_iff_subset {a b : Set α} : a ≤ b ↔ a ⊆ b := Iff.rfl

instance {β : α → Type*} : PartialOrder (PartialMap α β) where
  le_refl _ := ⟨le_rfl, fun _ _ => rfl⟩
  le_trans _ _ _ h h' := ⟨le_trans h.1 h'.1, fun a h'' => Eq.trans (h'.2 a _) (h.2 a _)⟩
  le_antisymm f g (h : f ≤ g) (h' : g ≤ f) := by
    rcases f with ⟨x,f⟩
    rcases g with ⟨y,g⟩
    rcases h with ⟨h,h1⟩
    rcases h' with ⟨h',h'1⟩
    congr
    · exact le_antisymm h h'
    · have := le_antisymm h h'
      simp only at h h1 h' h'1 this
      apply heq_of_eqRec_eq $ congrArg _ this
      rcases this
      ext ⟨a,h''⟩
      rw[h1 _ h'']

instance : Preorder (Set.Covering α) where
  le f g := Set.FinerThan f.covering g.covering
  le_refl _ := Set.finerThan_refl
  le_trans _ _ _ := Set.finerThan_trans

instance : PartialOrder (Set.Partition α) where
  le f g := Set.FinerThan f.partition g.partition
  le_refl _ := Set.finerThan_refl
  le_trans _ _ _ := Set.finerThan_trans
  le_antisymm p q := by
    intro h h'
    simp only [LE.le, Set.FinerThan, Subtype.exists, Subtype.forall] at *
    ext x
    constructor
    · intro h''
      obtain ⟨a,ha,c⟩ := h _ h''
      simp at *
      obtain ⟨b,hb,d⟩ := h' a ha
      have : ⟨x,h''⟩  = (⟨b,hb⟩ : {a // a ∈ p.subsets}) := by
        obtain ⟨elem, mem⟩ := p.all_nonempty h''
        apply p.isPartition'.eq_of_mem (a := elem) mem (d (c mem))
      have : x = b := by rwa[Subtype.eq_iff] at this
      have : x = a := by rw[this] at c |-; apply Set.eq_iff_subset_subset.mpr ⟨c,d⟩
      rwa[this]
    · intro h''
      obtain ⟨a,ha,c⟩ := h' _ h''
      simp at *
      obtain ⟨b,hb,d⟩ := h a ha
      have : ⟨x,h''⟩  = (⟨b,hb⟩ : {a // a ∈ q.subsets}) := by
        obtain ⟨elem, mem⟩ := q.all_nonempty h''
        apply q.isPartition'.eq_of_mem (a := elem) mem (d (c mem))
      have : x = b := by rwa[Subtype.eq_iff] at this
      have : x = a := by rw[this] at c |-; apply Set.eq_iff_subset_subset.mpr ⟨c,d⟩
      rwa[this]

instance [Preorder α] : PartialOrder (Preorder.QuotEquiv α) where
  le := Quot.lift2_same (inst := equivalent_rel) LE.le (by
    intro x x' y y' h h'
    simp only [Function.curry_apply, Preorder.equivalent_rel, eq_iff_iff] at *
    exact ⟨fun h'' => le_trans h.2 (le_trans h'' h'.1), fun h'' => le_trans h.1 (le_trans h'' h'.2)⟩)
  le_refl x := by
    obtain ⟨a,rfl⟩ := x.exists_rep
    simp only [LE.le, Quot.lift2_same_val, le_refl]
  le_trans x y z := by
    obtain ⟨a,rfl⟩ := x.exists_rep
    obtain ⟨b,rfl⟩ := y.exists_rep
    obtain ⟨c,rfl⟩ := z.exists_rep
    exact le_trans
  le_antisymm x y := by
    obtain ⟨a,rfl⟩ := x.exists_rep
    obtain ⟨b,rfl⟩ := y.exists_rep
    intro h h'
    apply Quot.sound
    simp only [Quot.lift2_same_val, Function.curry_apply] at *
    exact ⟨h,h'⟩

instance {β : α → Type*} [∀ x, Preorder (β x)] : Preorder (Pointwise α β) where
  le_refl _ _ := le_refl _
  le_trans _ _ _ h h' a := le_trans (h a) (h' a)

instance {β : α → Type*} [∀ x, PartialOrder (β x)] : PartialOrder (Pointwise α β) where
  le_antisymm _ _ h h' := funext (fun a => le_antisymm (h a) (h' a))

theorem pointwise_graph_product {β : α → Type*} [∀ x, LE (β x)] :
    (LE.le_rel : Relation (Pointwise α β) _) =
    Set.image (fun (x : (i : _) → (β i × β i)) => (fun a => (x a).1, fun a => (x a).2)) (Πˢ i, LE.le_rel) := by
  ext ⟨a,a'⟩
  simp only [LE.mem_le_rel_iff, LE.le, Set.mem_image_iff, Prod.mk.injEq, mem_iProd_iff]
  constructor
  · intro h
    exists fun i => ⟨a i, a' i⟩
  · rintro ⟨b, ⟨rfl, rfl⟩, h''⟩ i
    exact h'' i
