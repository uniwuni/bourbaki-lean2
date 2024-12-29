import BourbakiLean2.Order.WellOrder
import BourbakiLean2.Order.Sets
universe u

class InductiveOrder (α : Type*) [PartialOrder α] where
  chain_boundedAbove : ∀ {s : Set α}, (∀ x ∈ s, ∀ y ∈ s, Comparable x y) → s.BoundedAbove


variable {α : Type*} {β : α → Type*}

instance : InductiveOrder (Set α) where
  chain_boundedAbove := by
    intro s h
    exists Set.univ
    intro h x
    simp only [le_set_iff_subset, Set.subset_univ]

instance [PartialOrder α] [InductiveOrder α] {a : α} : InductiveOrder (Set.Ici a) where
  chain_boundedAbove := by
    intro s h
    by_cases empty : s = ∅
    · exists ⟨a,le_rfl⟩
      intro x hx
      rw[empty] at hx
      exact hx.elim
    obtain ⟨b,ub⟩ := InductiveOrder.chain_boundedAbove (s := Subtype.val '' s) (by
      intro b hb c hc
      rw[Set.mem_image_iff] at hb hc
      obtain ⟨⟨b,geb⟩,rfl,hb2⟩ := hb
      obtain ⟨⟨c,gec⟩,rfl,hc2⟩ := hc
      specialize h ⟨b,geb⟩ hb2 ⟨c,gec⟩ hc2
      exact h)
    obtain ⟨c, hc⟩ : s.Nonempty := by rw[Set.nonempty_iff_neq_empty]; exact empty
    have : b ≥ a := by
      apply le_trans c.property
      apply ub
      · rw[Set.mem_image_iff]
        exists c
    exists ⟨b,this⟩
    intro c hc
    apply ub
    simp only [Set.mem_image_iff, Subtype.exists, Set.mem_Ici_iff, exists_and_left, exists_eq_left']
    exists c.property

noncomputable def PartialMap.iUnion {ι : Type*} (f : ι → PartialMap α β) : PartialMap α β :=
  { carrier := ⋃ i, (f i).carrier,
    function := fun x => (f (Classical.choose $ x.2)).function ⟨x, Classical.choose_spec x.2⟩ }

@[simp] theorem PartialMap.iUnion_lub {ι : Type*} {f : ι → PartialMap α β} (h : ∀ i j, Comparable (f i) (f j)) :
    IsLUB (f '' Set.univ) (PartialMap.iUnion f) := by
  constructor
  swap
  · intro x h'
    rw[Set.mem_image_iff] at h'
    obtain ⟨i,rfl,_⟩ := h'
    simp only [LE.le, iUnion]
    exists Set.subset_iUnion (x := fun i => (f i).carrier)
    intro a ha
    let j := @Classical.choose ι (fun x ↦ a ∈ (f x).carrier) (Set.mem_iUnion_iff.2 ⟨_,ha⟩)
    change (f j).function ⟨a,_⟩ = (f i).function ⟨a,ha⟩
    rcases h i j with (h|h)
    · exact (h.2 a ha)
    · exact (h.2 a _).symm
  · intro ⟨ub, hub⟩
    have := carrier_monotone.upperBound_of_upperBound (f := (PartialMap.carrier : PartialMap α β → Set α)) (a := ub) hub
    constructor
    swap
    · intro a h'
      simp only
      obtain ⟨i,hi⟩ := Set.mem_iUnion_iff.1 h'
      apply this (f i).carrier
      apply Set.val_mem_image_of_mem
      apply Set.val_mem_image_of_mem
      trivial
      assumption
    · intro a h'
      obtain ⟨i,hi⟩ := Set.mem_iUnion_iff.1 h'
      rw[(hub (f i) (Set.val_mem_image_of_mem True.intro)).2 a hi]
      let j := @Classical.choose ι (fun x ↦ a ∈ (f x).carrier) (Set.mem_iUnion_iff.2 ⟨_,hi⟩)
      simp[iUnion]
      change (f i).function ⟨a,_⟩ = (f j).function ⟨a,_⟩
      rcases h i j with (h|h)
      · exact (h.2 a _).symm
      · exact (h.2 a _)

instance: InductiveOrder (PartialMap α β) where
  chain_boundedAbove := by
    intro s h
    let c := ⋃ a : s, a.1.carrier
    have : Set.IsCovering (fun a : s => {x : c | x.val ∈ a.1.carrier}) := by
      ext ⟨a,⟨⟨x,hx⟩,ha⟩⟩
      simp only [Set.mem_iUnion_iff, Set.mem_setOf_iff, Subtype.exists, exists_prop, Set.mem_univ,
        iff_true, c]
      exists x
    let f : (x : c) → β x := this.glue (fun (a : s) x => a.1.function ⟨x.val, x.property⟩)
    exists ⟨c,f⟩
    intro ⟨d,g⟩ hg
    constructor
    swap
    · intro a h'
      simp only [Set.mem_iUnion_iff, Subtype.exists, exists_prop, c]
      exists { carrier := d, function := g }
    · intro b hb
      simp only [f]
      have glue := this.glue_agrees
                (β := fun x : c => β x)
                (f := fun (a : s) (x : {x : c | x.val ∈ a.val.carrier}) => a.1.function ⟨x.val, x.property⟩)
                (i := ⟨_,hg⟩)
                (a := ⟨b,⟨⟨_,hg⟩,hb⟩⟩) ?hole
      swap
      · intro ⟨a,ha⟩ ⟨i,hi⟩ ⟨j,hj⟩ h' h''
        rcases h _ hi _ hj with (h|h)
        · exact (h.2 a h').symm
        · exact (h.2 a h'')
      · exact glue hb


theorem wellOrder_bounded_above_has_maximal [PartialOrder α]
    (h : ∀ {s : Set α}, IsWellOrder {(x,y) : s × s | x.1 ≤ y.1} → s.BoundedAbove) :
    ∃ x, Maximal (x : α) := by
  let g : Set (Set α) := {s | ∃ x, UpperBound s x ∧ x ∉ s}
  let p : g → α := fun s => Classical.choose s.property
  have (x : g) : p x ∉ x.val := (Classical.choose_spec x.property).2
  have pwo := ZermeloTheorem.make_partialWellOrder p this
  have no_sub : ∀ (x : α), UpperBound pwo.domain x → x ∈ pwo.domain := by
    have := pwo.domain_not_mem
    simp only [Set.mem_setOf_iff, not_exists, not_and, Classical.not_not, g] at this
    exact this
  have : (x y : pwo.domain) → pwo.order.lt x y → x.val < y.val := by
    intro x y h
    have : pwo.order.le x y ↔ x ∈ {↑ a | a ∈ @Set.Iic _ pwo.order.toPreorder y} := by
      simp only [Set.mem_Iic_iff, Subtype.eq_iff, Subtype.exists, exists_and_right, exists_eq_right,
        Set.mem_setOf_iff]
      constructor
      · intro h; exists x.property
      · intro ⟨h,h'⟩; exact h'
    rw[lt_iff_le_not_eq (inst := pwo.order.toPartialOrder), this] at h
    have eq : p ⟨{↑ a | a ∈ @Set.Iic _ pwo.order.toPreorder y}, pwo.iic_mem y⟩ = y := pwo.iic_func _
    have : UpperBound {↑ a | a ∈ @Set.Iic _ pwo.order.toPreorder y} (p ⟨{↑ a | a ∈ @Set.Iic _ pwo.order.toPreorder y}, pwo.iic_mem y⟩) :=
      (Classical.choose_spec (pwo.iic_mem y)).1
    rw[eq] at this
    rw[lt_iff_le_not_eq]
    constructor
    · apply this
      simp only [Set.mem_Iic_iff, Subtype.exists, exists_and_right, exists_eq_right,
        Set.mem_setOf_iff]
      obtain ⟨a,b,rfl⟩ := h.1
      exists a.property
    · simp only [Set.mem_Iic_iff, Subtype.eq_iff, Subtype.exists, exists_and_right,
      exists_eq_right, Set.mem_setOf_iff, ne_eq] at h
      exact h.2
  have reflect x y := @TotalOrder.strictMono_le_iff _ _ x y pwo.order.toTotalOrder _ _ this
  specialize h (s := pwo.domain)
  conv at h =>
    arg 1
    arg 1
    intro x
    arg 1
    intro y
    simp
    rw[reflect]
  obtain ⟨x,ab⟩ := h pwo.order.isWellOrder
  exists x
  intro y h'
  have memy := no_sub _ $ ab.upperBound_of_le h'
  exact le_antisymm (ab _ memy) h'


/-- zorns lemma -/
theorem InductiveOrder.has_maximal [PartialOrder α] [InductiveOrder α] : ∃ x, Maximal (x : α) := by
  apply wellOrder_bounded_above_has_maximal
  intro s h
  apply chain_boundedAbove (α := α)
  intro x hx y hy
  apply h.le_total ⟨x,hx⟩ ⟨y,hy⟩

theorem InductiveOrder.has_maximal_above [PartialOrder α] [InductiveOrder α] (a : α): ∃ x, Maximal (x : α) ∧ x ≥ a := by
  obtain ⟨⟨b,le⟩,max⟩ := InductiveOrder.has_maximal (α := Set.Ici a)
  exists b
  constructor
  · intro c h
    have := max ⟨c, le_trans le h⟩ h
    simp only [Subtype.eq_iff] at this
    exact this
  · exact le


theorem subset_totally_ordered_maximum {s : Set (Set α)}
    (h : ∀ t, t ⊆ s → (∀ x ∈ t, ∀ y ∈ t, x ⊆ y ∨ y ⊆ x) → ⋃ a : t, a ∈ s) : ∃ x : s, Maximal x := by
  have inst : InductiveOrder s := by
    constructor
    rintro t ht
    let t' : Set (Set α) := Subtype.val '' t
    exists ⟨⋃ a : t', a.val, ?wah⟩
    · have sub : t' ⊆ s := by
        intro x hx
        rw[Set.mem_image_iff] at hx
        obtain ⟨⟨a,ha⟩,eq⟩ := hx
        simp only [eq.1, ha]
      apply h
      · exact sub
      · intro x hx y hy
        have hx' := hx
        have hy' := hy
        rw[Set.mem_image_iff] at hx hy
        obtain ⟨⟨a,ha⟩,rfl,haa⟩ := hx
        obtain ⟨⟨b,hb⟩,rfl,hbb⟩ := hy
        apply ht ⟨x,ha⟩ haa ⟨y,hb⟩ hbb
    · intro x hx
      simp only [Subtype.le_iff_val, le_set_iff_subset]
      have : x.val ∈ t' := by simp[t', Set.mem_image_iff]; exists x.property
      have : _ ⊆ ⋃ a : t', a.val := Set.subset_iUnion (i := ⟨x.val, this⟩)
      exact this
  exact InductiveOrder.has_maximal (α := s)

theorem subset_totally_ordered_minimum {s : Set (Set α)}
    (h : ∀ t, t ⊆ s → (∀ x ∈ t, ∀ y ∈ t, x ⊆ y ∨ y ⊆ x) → ⋂ a : t, a ∈ s) : ∃ x : s, Minimal x := by
  have inst : InductiveOrder (Op s) := by
    constructor
    rintro t ht
    let t' : Set (Set α) := Subtype.val '' t
    exists ⟨toOp $ ⋂ a : t', a.val, ?wah⟩
    · have sub : t' ⊆ s := by
        intro x hx
        rw[Set.mem_image_iff] at hx
        obtain ⟨⟨a,ha⟩,eq⟩ := hx
        simp only [eq.1, ha]
      apply h
      · exact sub
      · intro x hx y hy
        have hx' := hx
        have hy' := hy
        rw[Set.mem_image_iff] at hx hy
        obtain ⟨⟨a,ha⟩,rfl,haa⟩ := hx
        obtain ⟨⟨b,hb⟩,rfl,hbb⟩ := hy
        have := ht ⟨x,ha⟩ haa ⟨y,hb⟩ hbb
        rcases this with (h|h)
        · right
          exact h
        · left
          exact h
    · intro x hx
      simp only [LE.le, toOp]
      have : x.val ∈ t' := by simp[t', Set.mem_image_iff]; exists x.property
      have : ⋂ a : t', a.val ⊆ _ := Set.iInter_subset (i := ⟨x.val, this⟩)
      exact this
  exact InductiveOrder.has_maximal (α := Op s)
