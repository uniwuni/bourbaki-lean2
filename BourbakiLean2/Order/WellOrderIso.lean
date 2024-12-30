import BourbakiLean2.Order.Inductive

variable {α β : Type*} [WellOrder α] [WellOrder β]

theorem WellOrder.either_embeds (α β : Type*) [WellOrder α] [WellOrder β] :
    (∃ x : InitialSegment β, ∃ f : α → x.val, IsOrderIso f) ∨ (∃ x : InitialSegment α, ∃ f : x.val → β, IsOrderIso f) := by
  let s : Set (PartialMap α $ fun _ => β) := { f | f.carrier.IsDownwardsClosed ∧ StrictMonotone f.function ∧ (f.function '' Set.univ).IsDownwardsClosed}
  have ind : InductiveOrder s := by
    constructor
    intro t h
    let t' := Subtype.val '' t
    have ht' : ∀ x, x ∈ t' → ∀ y, y ∈ t' → Comparable x y := by
        intro x hx y hy
        unfold t' at hx hy
        rw[Set.mem_image_iff] at hx hy
        obtain ⟨⟨x,hx⟩,rfl,hx'⟩ := hx
        obtain ⟨⟨y,hy⟩,rfl,hy'⟩ := hy
        exact h ⟨x,hx⟩ hx' ⟨y,hy⟩ hy'
    obtain ⟨ub,least⟩ := PartialMap.iUnion_lub (f := fun (x : t) => x.val.val) (fun (i : t) (j : t) => h i.val i.property j.val j.property)
    have fins : (PartialMap.iUnion fun x : t ↦ x.val.val) ∈ s := by
        constructor
        · simp only [PartialMap.iUnion]
          have : ∀ x : t, x.val.val.carrier.IsDownwardsClosed := by
            intro ⟨⟨x,mems⟩,mem⟩
            exact mems.1
          apply @Set.IsDownwardsClosed.iUnion
        · constructor
          · intro ⟨x,⟨tx,hx⟩⟩ ⟨y,⟨ty,hy⟩⟩ h'
            rcases (h tx.val tx.property ty.val ty.property) with (h|h)
            · have := (ub ty.val.val Set.val_mem_image_univ).2
              rw[this x $ h.1 hx, this y $ hy]
              apply ty.val.property.2.1
              exact h'
            · have := (ub tx.val.val Set.val_mem_image_univ).2
              rw[this y $ h.1 hy, this x $ hx]
              apply tx.val.property.2.1
              exact h'
          · constructor
            intro b1 b2 le mem
            obtain ⟨fnc,a,rfl⟩ : ∃ a : t, ∃ x, a.val.val.function x = b2 := by
                simp only [PartialMap.iUnion, Set.mem_image_iff, Set.mem_univ, and_true,
                  Subtype.exists, Set.mem_iUnion_iff, exists_prop, exists_and_right] at mem
                obtain ⟨a,h,rfl⟩ := mem
                exact ⟨_,_,rfl⟩
            have : b1 ∈ (fnc.val.val.function '' Set.univ) := by
                apply fnc.val.property.2.2.mem_of_le_mem le Set.val_mem_image_univ
            rw[Set.mem_image_iff] at this
            rw[Set.mem_image_iff]
            obtain ⟨x,rfl,_⟩ := this
            exists ⟨x.val,⟨_,x.property⟩⟩
            simp only [(ub fnc.val.val Set.val_mem_image_univ).2 x.val x.property, Set.mem_univ,
              and_self]
    exists ⟨_,fins⟩
    intro ⟨d,g⟩ hg
    apply ub
    simp only [Set.mem_image_iff, Set.mem_univ, and_true, Subtype.exists, exists_prop,
      exists_and_right, exists_eq_right', hg, g, exists_const]
  obtain ⟨⟨x,xs⟩,xmax⟩ := ind.has_maximal
  simp only [StrictMonotone, Subtype.lt_iff_val, Subtype.forall, Set.mem_setOf_iff, s] at xs
  suffices alt : x.carrier = Set.univ ∨ x.function '' Set.univ = Set.univ by
    rcases alt with (eq|eq)
    · left
      exists ⟨x.function '' Set.univ, xs.2.2⟩
      exists Function.corestrict (fun a => (x.function ⟨a, eq ▸ Set.mem_univ⟩)) (by
        intro b h
        rw[Set.mem_image_iff] at h
        obtain ⟨a,rfl,_⟩ := h
        simp only [Set.val_mem_image_univ])
      apply TotalOrder.strictMono_iso_image
      · intro a b h
        exact xs.2.1 a (by simp only [eq, Set.mem_univ]) b (by simp only [eq, Set.mem_univ]) h
      · simp only [Function.surj_iff, Subtype.eq_iff, Function.coe_corestrict, Subtype.forall,
        Set.mem_image_iff, Set.mem_univ, and_true, Subtype.exists, forall_exists_index]
        rintro b a ha rfl
        exists a
    · right
      exists ⟨x.carrier, xs.1⟩
      exists x.function
      apply TotalOrder.strictMono_iso_image
      · intro a b h
        exact xs.2.1 a.val a.property b.val b.property h
      · rw[Function.Surjective, eq]
  by_contra h
  simp only [not_or] at h
  obtain ⟨enda, eqa⟩ := isIio_of_downwardsClosed xs.1 h.1
  obtain ⟨endb,eqb⟩ := isIio_of_downwardsClosed xs.2.2 h.2
  classical
  let yfunc : Set.Iic enda → β := fun a =>
    if h : a.val ∈ x.carrier then x.function ⟨a.val, h⟩ else endb
  let yf : PartialMap α (fun x => β) := ⟨Set.Iic enda, yfunc⟩
  have yf1 : yf.carrier.IsDownwardsClosed := by
    simp only
    infer_instance
  have yf2 : StrictMonotone yf.function := by
    rintro ⟨a,ha⟩ ⟨b,hb⟩ h
    unfold yf at *
    simp only [yfunc]
    split <;> rename_i hif1
    · split <;> rename_i hif2
      · apply xs.2.1 a (by assumption) b (by assumption) h
      · rw[eqa] at hif2
        simp only [Set.mem_Iio_iff, not_gt_iff_le] at hif2
        have := le_antisymm hb hif2
        rcases this
        have : x.function ⟨a,hif1⟩ ∈ Set.Iio endb := by rw[← eqb]; simp only [Set.val_mem_image_univ]
        exact this
    · split <;> rename_i hif2
      · simp only [eqa,Set.mem_Iio_iff, not_gt_iff_le] at hif1
        have := le_antisymm ha hif1
        rcases this
        exact (not_lt_self $ lt_of_le_lt hb h).elim
      · simp only [eqa,Set.mem_Iio_iff, not_gt_iff_le] at hif1
        simp only [eqa,Set.mem_Iio_iff, not_gt_iff_le] at hif2
        rcases (le_antisymm ha hif1)
        rcases (le_antisymm hb hif2)
        exact (not_lt_self h).elim
  have yf3' : (yf.function '' Set.univ) = Set.Iic endb := by
    ext b
    simp only [Set.mem_image_iff, Set.mem_univ, and_true, Subtype.exists, Set.mem_Iic_iff, yfunc]
    constructor
    · rintro ⟨a,h,h'⟩
      split at h' <;> rename_i hif2
      · rw[h']
        apply le_of_lt
        change x.function ⟨a,hif2⟩ ∈ Set.Iio endb
        rw[← eqb]
        simp only [Set.val_mem_image_univ]
      · rw[h']
    · intro h
      rw[le_iff_lt_or_eq] at h
      rcases h with (lt|eq)
      · have : b ∈ x.function '' Set.univ := by rw[eqb]; exact lt
        rw[Set.mem_image_iff] at this
        obtain ⟨a,rfl,_⟩ := this
        exists a
        have : a.val < enda := by
          change a.val ∈ Set.Iio enda
          rw[← eqa]
          exact a.property
        exists le_of_lt this
        simp only [a.property, ↓reduceDIte]
      · rw[eq]
        exists enda
        exists le_rfl
        have : enda ∉ x.carrier := by rw[eqa]; exact Set.not_mem_Ioi_self
        simp[this]
  have yf3 : (yf.function '' Set.univ).IsDownwardsClosed := by
    rw[yf3']
    infer_instance
  have : yf ∈ s := ⟨yf1,⟨yf2,yf3⟩⟩
  have := xmax ⟨yf,this⟩ (by
      constructor
      swap
      · simp only [eqa, Set.Iio_subset_Iic]
      · intro a h
        simp only [h, ↓reduceDIte, yf, yfunc])
  have : Set.Iio enda = Set.Iic enda := by
    have : yf = x := Subtype.eq_iff.mp this
    rw[← eqa, ← this]
  apply Set.not_mem_Iio_self (a := enda)
  rw[this]
  exact Set.mem_Iic_self

theorem WellOrder.segment_less_strictly_monotone {f g : α → β} (hdc : (f '' Set.univ).IsDownwardsClosed)
    (hf : Monotone f) (hg : StrictMonotone g) {x} : f x ≤ g x := by
  by_contra h
  rw[not_ge_iff_lt] at h
  obtain ⟨a,amem,aleast⟩ := existsLeast (s := {x | g x < f x}) ⟨_,h⟩
  have : ∀ x, x < a → False := by
    intro x lt
    have fxgx : f x ≤ g x := by
      rw[← not_gt_iff_le]
      intro h
      exact not_lt_self $ lt_of_le_lt (aleast ⟨x,h⟩) lt
    have gxga := hg lt
    have := lt_of_lt_lt (lt_of_le_lt fxgx gxga) amem
    have img := hdc.mem_of_le_mem (le_of_lt amem) (by simp only [Set.val_mem_image_univ])
    rw[Set.mem_image_iff] at img
    obtain ⟨z,eq,_⟩ := img
    change g a < f a at amem
    have amem' := amem
    rw[eq] at amem
    have := TotalOrder.mono_lt_reflect hf amem
    have fzgz : f z ≤ g z := by
      rw[← not_gt_iff_le]
      intro h
      exact not_lt_self $ lt_of_le_lt (aleast ⟨z,h⟩) this
    have := lt_of_le_lt fzgz $ hg this
    rw[eq] at this
    apply not_lt_self this
  have a_least : Least a := by
    intro x
    rw[← not_gt_iff_le]
    intro h
    apply this x h
  have ⟨l,_,least⟩ := existsLeast (s := Set.univ) ⟨f a,trivial⟩
  have : l ∉ f '' Set.univ := by
    intro h
    rw[Set.mem_image_iff] at h
    obtain ⟨w,rfl,_⟩ := h
    have := hf $ a_least w
    have := le_antisymm this (least ⟨f a, by trivial⟩)
    have : g a < f w := by
      rw[← this]
      exact amem
    exact not_lt_self $ lt_of_le_lt (least ⟨g a, by trivial⟩) this
  apply this
  apply hdc.mem_of_le_mem (least ⟨f a, by trivial⟩) (by simp only [Set.val_mem_image_univ])

theorem WellOrder.segment_embedding_all_eq' {x y : InitialSegment α} {f : x.val → β} {g : y.val → β}
    (hs : x.val ⊆ y.val)
    (hf : IsOrderIso f) (hg : IsOrderIso g) : ∃ h : x = y, h ▸ f = g := by
  have hf' : (f '' Set.univ).IsDownwardsClosed := by rw[hf.bij.surj]; infer_instance
  have hg' : (g '' Set.univ).IsDownwardsClosed := by rw[hg.bij.surj]; infer_instance
  let g' : x.val → β := fun a => g ⟨a, hs a.property⟩
  have smg : StrictMonotone g' := by
    intro a b h
    exact hg.strictMonotone h
  have dcg : (g' '' Set.univ).IsDownwardsClosed := by
    constructor
    intro a b h
    rw[Set.mem_image_iff, Set.mem_image_iff]
    rintro ⟨⟨a',mem⟩,rfl,_⟩
    have := hg'.mem_of_le_mem h (by simp only [Set.val_mem_image_univ])
    rw[Set.mem_image_iff] at this
    obtain ⟨b',rfl,_⟩ := this
    have : b' ≤ a' := by
      rw[← not_gt_iff_le]
      intro h'
      have := hg.strictMonotone (a := ⟨a', hs mem⟩) (b := b') h'
      exact not_lt_self $ lt_of_le_lt h this
    have := x.2.mem_of_le_mem this mem
    exists ⟨_,this⟩

  have this x := WellOrder.segment_less_strictly_monotone hf' hf.monotone smg (x := x)
  have that x := WellOrder.segment_less_strictly_monotone dcg smg.monotone hf.strictMonotone (x := x)
  have fg := funext (fun a => le_antisymm (this a) (that a))
  have : x.val = y.val := by
    by_contra neq
    obtain ⟨a,ay,nax⟩ : ∃ a, a ∈ y.val ∧ a ∉ x.val := by
      by_contra na
      simp only [not_exists, not_and, Classical.not_not] at na
      apply neq $ Set.eq_iff_subset_subset.mpr ⟨hs,na⟩
    have oops : g ⟨a,ay⟩ ∉ f '' Set.univ := by
      intro h
      rw[Set.mem_image_iff] at h
      obtain ⟨b,eq,_⟩ := h
      rw[fg] at eq
      have := hg.bij.inj _ _ eq
      simp only [Subtype.eq_iff] at this
      exact nax (this ▸ b.property)
    have ie : g ⟨a,ay⟩ ∈ f '' Set.univ := by
        have := hf.bij.surj
        rw[Function.Surjective] at this
        rw[this]
        trivial
    exact oops ie
  have eq := Subtype.eq_iff.mpr this
  rcases eq
  simp only [exists_const]
  rw[fg]

theorem WellOrder.segment_embedding_all_eq {x y : InitialSegment α} {f : x.val → β} {g : y.val → β}
    (hf : IsOrderIso f) (hg : IsOrderIso g) : ∃ h : x = y, h ▸ f = g := by
  rcases le_total x y with (h|h)
  · exact WellOrder.segment_embedding_all_eq' h hf hg
  · obtain ⟨rfl,p⟩ := WellOrder.segment_embedding_all_eq' h hg hf
    exists rfl
    simp only [le_rfl] at *
    exact p.symm

theorem WellOrder.into_segment_embedding_all_eq' {x y : InitialSegment β} {f : α → x.val} {g : α → y.val}
    (hs : x.val ⊆ y.val)
    (hf : IsOrderIso f) (hg : IsOrderIso g) : ∃ h : x = y, h ▸ f = g := by
  have hf' : (f '' Set.univ).IsDownwardsClosed := by rw[hf.bij.surj]; infer_instance
  have hg' : (g '' Set.univ).IsDownwardsClosed := by rw[hg.bij.surj]; infer_instance
  let f' : α → y.val := fun a => ⟨f a, hs (f a).property⟩
  have smg : StrictMonotone f' := by
    intro a b h
    exact hf.strictMonotone h
  have dcg : (f' '' Set.univ).IsDownwardsClosed := by
    constructor
    intro a b h
    rw[Set.mem_image_iff, Set.mem_image_iff]
    rintro ⟨a',rfl,_⟩
    simp only [Subtype.le_iff_val, f'] at h
    have := x.2.mem_of_le_mem (a := a) h $ (f a').property
    obtain ⟨b,eq⟩ := hf.bij.surj.exists_preimage ⟨a.val,this⟩
    exists b
    simp only [Subtype.eq_iff, Set.mem_univ, and_true]
    simp only [← eq]
  have this x := WellOrder.segment_less_strictly_monotone hg' hg.monotone smg (x := x)
  have that x := WellOrder.segment_less_strictly_monotone dcg smg.monotone hg.strictMonotone (x := x)
  have fg := funext (fun a => le_antisymm (this a) (that a))
  have : x.val = y.val := by
    ext a
    constructor
    · intro h
      exact hs h
    · intro h
      have ⟨x,y⟩ := hg.bij.surj.exists_preimage ⟨a,h⟩
      rw[fg] at y
      unfold f' at y
      simp only [Subtype.eq_iff] at y
      rw[y]
      exact (f x).property
  have eq := Subtype.eq_iff.mpr this
  rcases eq
  exists rfl
  simp only [fg]

theorem WellOrder.into_segment_embedding_all_eq {x y : InitialSegment β} {f : α → x.val} {g : α → y.val}
    (hf : IsOrderIso f) (hg : IsOrderIso g) : ∃ h : x = y, h ▸ f = g := by
  rcases le_total x y with (h|h)
  · exact WellOrder.into_segment_embedding_all_eq' h hf hg
  · obtain ⟨rfl,p⟩ := WellOrder.into_segment_embedding_all_eq' h hg hf
    exists rfl
    simp only [le_rfl] at *
    exact p.symm

theorem WellOrder.segment_into_self_iso {x : InitialSegment α} {f : x.val → α}
    (h : IsOrderIso f) : ∃ h : x = InitialSegment.univ, h ▸ f = Subtype.val :=
  WellOrder.segment_embedding_all_eq' (f := f) (g := (Subtype.val : InitialSegment.univ.val → α))
    (by simp only [InitialSegment.univ, Set.subset_univ]) h InitialSegment.univ_val_isOrderIso

theorem WellOrder.self_into_segment_iso {x : InitialSegment α} {f : α → x.val}
    (h : IsOrderIso f) : ∃ h : x = InitialSegment.univ, h ▸ f = (fun x => ⟨x,True.intro⟩) :=
    WellOrder.into_segment_embedding_all_eq' (f := f) (g := (fun x : α => (⟨x,True.intro⟩ : InitialSegment.univ.val)))
    (by simp only [InitialSegment.univ, Set.subset_univ]) h InitialSegment.mk_unit_isOrderIso

theorem WellOrder.iso_all_eq {f g : α → β} (hf : IsOrderIso f) (hg : IsOrderIso g) : f = g := by
  rcases WellOrder.either_embeds α β with (⟨x,h,iso⟩|⟨x,h,iso⟩)
  · have hcompf := hf.comp iso.inv
    have ⟨eqf,hf⟩ := segment_into_self_iso hcompf
    rcases eqf
    have hcompg := hg.comp iso.inv
    have ⟨eqg,hg⟩ := segment_into_self_iso hcompg
    rcases eqg
    simp only at *
    rw[← hg] at hf
    exact iso.bij.inv_bij.surj.comp_right_inj f g hf
  · have hcompf := iso.inv.comp hf
    have ⟨eqf,hf⟩ := self_into_segment_iso hcompf
    rcases eqf
    have hcompg := iso.inv.comp hg
    have ⟨eqg,hg⟩ := self_into_segment_iso hcompg
    rcases eqg
    simp only at *
    rw[← hg] at hf
    exact iso.bij.inv_bij.inj.comp_left_inj f g hf

theorem WellOrder.iso_same_eq_id {f : α → α} (h : IsOrderIso f) : f = id := WellOrder.iso_all_eq h id_isOrderIso

theorem WellOrder.subset_iso_segment {s : Set α} : ∃ t : InitialSegment α, ∃ f : s → t.val, IsOrderIso f := by
  rcases WellOrder.either_embeds s α with (⟨x,h,iso⟩|⟨x,h,iso⟩)
  · exists x
    exists h
  · let f' : α → α := fun x => (iso.bij.inv x).val
    rcases x.mk_or_univ with (⟨a,rfl⟩|rfl)
    · have strict : StrictMonotone f' := by
        intro a b g
        exact iso.inv.strictMonotone g
      have : f' a < a := (iso.bij.inv a).property
      have f := WellOrder.segment_less_strictly_monotone (f := id) (hdc := by simp only [Function.image_id]; infer_instance)  (hf := id_mono) (hg := strict) (x := a.val)
      apply (not_lt_self $ lt_of_le_lt f this).elim
    · exists InitialSegment.univ
      exists fun x => ⟨h ⟨x,True.intro⟩, True.intro⟩
      apply isOrderIso_iff_reflect.mpr
      constructor
      · constructor
        · intro x y eq
          simp only [Subtype.eq_iff] at eq
          have := iso.bij.inj _ _ eq
          simp only [Subtype.eq_iff] at this
          simp only [Subtype.eq_iff, this]
        · rw[Function.surj_iff]
          intro ⟨b,_⟩
          have ⟨a,h'⟩ := iso.bij.surj.exists_preimage b
          exists a
          simp only [h']
      · constructor
        · intro x y h
          apply iso.monotone h
        · intro x y h
          apply iso.le_iff.mp h


/- TODO
theorem WellOrder.iso_pairs_all_id {x : InitialSegment α} {y : InitialSegment β}
    {f : α → y.val} {g : β → x.val} (hf : IsOrderIso f) (hg : IsOrderIso g) :
    ∃ h : x = InitialSegment.univ, ∃ h' : y = InitialSegment.univ,
        Subtype.val ∘ f ∘ Subtype.val ∘ g = id ∧ Subtype.val ∘ g ∘ Subtype.val ∘ f = id := by
  have : IsOrderIso (g ∘ Subtype.val ∘ f) := by
    apply isOrderIso_iff_reflect.mpr
    · constructor

      · constructor
        · exact hg.monotone.comp hf.monotone
        · intro x y h
          rw[← hg, ← hf]
          exact h


-/
