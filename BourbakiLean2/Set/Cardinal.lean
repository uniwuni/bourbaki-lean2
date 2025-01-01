import BourbakiLean2.Order.WellOrderIso
universe u v

def Equipotent (α : Type u) (β : Type v) := Nonempty (Function.Bijection α β)
def equipotent_rel : Relation (Type u) (Type u) := fun ⟨α,β⟩ => Nonempty (Function.Bijection α β)
@[simp] theorem mem_equipotent_rel_iff {α β : Type u} : ⟨α,β⟩ ∈ equipotent_rel ↔ Equipotent α β := Iff.rfl
instance : Equivalence @Equipotent.{u} where
  refl _ := ⟨⟨_,Function.bij_id⟩⟩
  symm := fun ⟨h⟩ => ⟨h.inv⟩
  trans := fun ⟨h⟩ ⟨h'⟩ => ⟨_, h'.property.comp h.property⟩

instance equipotent_equiv : equipotent_rel.IsEquivalence := by
  unfold Relation.IsEquivalence equipotent_rel
  infer_instance

def Cardinal : Type (u+1) := Quot Equipotent
def Cardinal.mk : Type* → Cardinal := Quot.mk Equipotent
theorem Cardinal.alt : @Cardinal.{u} = Quot (Function.curry equipotent_rel) := rfl
theorem Cardinal.mk_alt {α : Type u} : Cardinal.mk α = Quot.mk (Function.curry equipotent_rel) α := rfl
@[simp] theorem Cardinal.eq_iff {α β : Type u} : Cardinal.mk α = Cardinal.mk β ↔ Equipotent α β := by
  rw[Cardinal.mk_alt, Cardinal.mk_alt, Quot.mk_eq_iff_rel]
  exact mem_equipotent_rel_iff

instance : Zero @Cardinal.{u} := ⟨Cardinal.mk PEmpty⟩
instance : One @Cardinal.{u} := ⟨Cardinal.mk PUnit⟩

theorem Cardinal.zero_eq : (0 : @Cardinal.{u}) = Cardinal.mk PEmpty := rfl
theorem Cardinal.one_eq : (1 : @Cardinal.{u}) = Cardinal.mk PUnit := rfl
@[simp] theorem Cardinal.eq_zero_iff {α : Type u} : Cardinal.mk α = 0 ↔ (α → False) := by
  simp only [zero_eq, eq_iff, Function.prod_nonempty_iff, not_nonempty_empty]
  constructor
  · rintro ⟨h⟩
    exact fun x => (h.1 x).elim
  · intro h
    exists (fun x => (h x).elim)
    constructor
    · intro x
      exact (h x).elim
    · rw[Function.surj_iff]
      rintro ⟨⟩

@[simp] theorem Cardinal.eq_one_iff {α : Type u} : Cardinal.mk α = 1 ↔ Nonempty (Unique α) := by
  simp only [one_eq, eq_iff]
  constructor
  · rintro ⟨h⟩
    have a : α := h.2.inv PUnit.unit
    constructor
    constructor
    swap
    · exact ⟨a⟩
    · intro x
      change x = a
      rw[← h.inv_val_val (a := x), ← h.inv_val_val (a := a)]
  · intro ⟨⟨a⟩, h⟩
    exists fun x => PUnit.unit
    constructor
    · intro x y _
      rw[h x, h y]
    · rw[Function.surj_iff]
      intro x
      exists a

@[simp] theorem Cardinal.zero_neq_one : (0 : @Cardinal.{u}) ≠ 1 :=
  fun h => (Cardinal.eq_zero_iff (α := PUnit)).mp h.symm PUnit.unit


theorem Cardinal.le_equipotent_invariant1 {x x' y y' : Type u} (hx : Equipotent x x') (hy : Equipotent y y')
    (h : Nonempty (Function.Injection x y)) : Nonempty (Function.Injection x' y') := by
  rcases h with ⟨h⟩
  rcases hx with ⟨hx⟩
  rcases hy with ⟨hy⟩
  constructor
  exact ⟨_,hy.2.inj.comp $ h.2.comp hx.2.inv_bij.inj⟩

theorem Cardinal.le_equipotent_invariant {x x' y y' : Type u} (hx : Equipotent x x') (hy : Equipotent y y') :
    Nonempty (Function.Injection x y) = Nonempty (Function.Injection x' y') := by
  simp only [eq_iff_iff]
  constructor
  · exact Cardinal.le_equipotent_invariant1 hx hy
  · have :  Equivalence Equipotent := by infer_instance
    exact Cardinal.le_equipotent_invariant1 (Equivalence.symm this hx) (Equivalence.symm this hy)



def Cardinal.injects (α β : Cardinal.{u}) : Prop :=
  Quot.lift2_same (fun α β => Nonempty (Function.Injection α β)) (fun _ _ _ _ => le_equipotent_invariant) α β

@[simp] theorem Cardinal.mk_injects_iff {α β : Type u} : injects (Cardinal.mk α) (Cardinal.mk β) ↔ Nonempty (Function.Injection α β) := by
  simp only [injects, mk, Quot.lift2_same_val]

@[simp] theorem Cardinal.mk_injects_iff' {α β : Type u} : injects (Quot.mk _ α) (Quot.mk _ β) ↔ Nonempty (Function.Injection α β) :=
  Cardinal.mk_injects_iff

instance : Preorder Cardinal where
  le := Cardinal.injects
  le_refl := by
    rintro ⟨x⟩
    exact ⟨_,Function.inj_id⟩
  le_trans := by
    rintro ⟨x⟩ ⟨y⟩ ⟨z⟩
    simp only [LE.le, Cardinal.mk_injects_iff']
    rintro ⟨h⟩ ⟨h'⟩
    exact ⟨_,h'.2.comp h.2⟩

@[simp] theorem Cardinal.mk_le_iff {α β : Type u} : (Cardinal.mk α) ≤ (Cardinal.mk β) ↔ Nonempty (Function.Injection α β) :=
  Cardinal.mk_injects_iff'

@[simp] theorem Cardinal.zero_le (x : Cardinal.{u}) : 0 ≤ x := by
  rcases x with ⟨x⟩
  simp only [LE.le, zero_eq, mk, mk_injects_iff']
  constructor
  exists (fun x => x.elim)
  rintro ⟨⟩

theorem Cardinal.one_le_iff_neq_zero {x : Cardinal.{u}} : 1 ≤ x ↔ x ≠ 0 := by
  rcases x with ⟨x⟩
  change 1 ≤ Cardinal.mk x ↔ Cardinal.mk x ≠ 0
  rw[Ne,Cardinal.eq_zero_iff]
  simp only [one_eq, mk_le_iff, Classical.not_forall, not_false_eq_true]
  constructor
  · rintro ⟨h⟩
    exact ⟨h.1 PUnit.unit, trivial⟩
  · rintro ⟨a,_⟩
    constructor
    exists fun x => a
    rintro ⟨⟩ ⟨⟩ _
    rfl

def Cardinal.ind_mk {p : Cardinal.{u} → Prop} (h : ∀ α : Type u, p (Cardinal.mk α)) (x : Cardinal.{u}) : p x := by
  rcases x with ⟨x⟩
  exact h x

noncomputable instance : WellOrder Cardinal.{u} := by
  let α := Sigma (fun (x : Type u) => x)
  have := zermelo (α := α)
  have get_iso (c : Type u) := WellOrder.subset_iso_segment (s := {p : α | p.1 = c})
  let get_iso_bij (c : Type u) : Function.Bijection c {p : α | p.1 = c} := by
    exists fun x => ⟨⟨_,x⟩,rfl⟩
    constructor
    · intro x y h
      simp only [Subtype.eq_iff] at h
      rw[Sigma.ext_iff] at h
      simp only [heq_eq_eq, true_and] at h
      exact h
    · rw[Function.surj_iff]
      rintro ⟨⟨a,b⟩,rfl⟩
      exists b
  let f (c : Type u) :=
    (WellOrder.least (s := fun (x : WellOrder.InitialSegment α) =>
      Equipotent x.val c))
    (by
      obtain ⟨seg,f,iso⟩ := get_iso c
      exists seg
      let a := (get_iso_bij c).2.inv.comp iso.bij.inv
      exists a
      apply (get_iso_bij c).2.inv_bij.comp iso.bij.inv_bij)
  have f_val (c : Type u) (y)
      := WellOrder.least_least (s := fun (x : WellOrder.InitialSegment α) =>
      Equipotent x.val c)
    (by
      obtain ⟨seg,f,iso⟩ := get_iso c
      exists seg
      let a := (get_iso_bij c).2.inv.comp iso.bij.inv
      exists a
      apply (get_iso_bij c).2.inv_bij.comp iso.bij.inv_bij) (x := y)
  have f_equi : ∀ c : Type u, Equipotent (f c).val c := by
    intro c
    apply WellOrder.least_mem (s := fun (x : WellOrder.InitialSegment α) =>
      Equipotent x.val c)
  have iso_thing (x y : Type u) : Cardinal.mk x ≤ Cardinal.mk y ↔ f x ≤ f y := by
    constructor
    swap
    · intro h
      simp only [Cardinal.mk_le_iff]
      have ⟨f1,b1⟩ := f_equi x
      have ⟨f2,b2⟩ := f_equi y
      let f3 : (f x).val → (f y).val := fun a => ⟨a.1, h a.2⟩
      have f3_inj : f3.Injective := by
        rintro ⟨x,h⟩ ⟨y,h'⟩ eq
        simp only [Subtype.eq_iff] at eq
        simp only [eq]
      constructor
      exists f2.comp $ f3.comp b1.inv
      exact b2.inj.comp $ f3_inj.comp b1.inv_bij.inj
    · simp only [Cardinal.mk_le_iff]
      rintro ⟨⟨i,h⟩⟩
      rw[← not_gt_iff_le, lt_iff_le_not_eq]
      intro h'
      obtain ⟨inj⟩ : Nonempty (Function.Injection x (f y).val) := by
        obtain ⟨⟨c,bij⟩⟩ := f_equi y
        constructor
        exact ⟨_,bij.inv_bij.inj.comp h⟩
      obtain ⟨seg,⟨iso,equi⟩⟩ := WellOrder.subset_iso_segment (α := (f y).val) (s := (inj '' Set.univ))
      have inj2 : Function.Bijection x (Subtype.val '' (inj '' Set.univ)) := by
        rw[← Function.image_comp]
        exists (Subtype.val ∘ inj.1).corestrict Set.subset_rfl
        constructor
        · intro x y h'
          simp only [Function.Injective.eq_1, Function.corestrict] at h'
          rw[Subtype.eq_iff] at h'
          simp only [Function.comp_apply] at h'
          exact inj.2 _ _ $ Subtype.eq h'
        · apply Function.corestrict_surjective
      have final : (f y).lift_double seg ≤ f y := WellOrder.InitialSegment.lift_double_le _
      have ⟨iso2, isiso⟩ := (f y).lift_double_iso seg
      have ⟨lastiso,lastisiso⟩ : Function.Bijection (inj.val '' Set.univ) (Subtype.val '' (inj.val '' Set.univ)) := by
        exists fun ⟨a,h⟩ => ⟨a.val, by
          simp only [Function.Injective.eq_1, Set.mem_image_iff, Subtype.eq_iff, Set.mem_univ,
            and_true, Subtype.exists, exists_and_left, exists_prop, exists_eq_left']
          simp only [Function.Injective.eq_1, Set.mem_image_iff, Subtype.eq_iff, Set.mem_univ,
            and_true] at h
          obtain ⟨b,eq⟩ := h
          rw[eq]
          constructor
          · apply (inj.val b).property
          · exists b⟩
        constructor
        · intro x y h
          simp at h
          apply Subtype.eq $ Subtype.eq h
        · rw[Function.surj_iff]
          rintro ⟨x,hx⟩
          rw[Set.mem_image_iff] at hx
          obtain ⟨a,rfl,ha⟩ := hx
          exists ⟨a,ha⟩
      specialize f_val x ⟨(f y).lift_double seg,  ⟨⟨_,inj2.2.inv_bij.comp $ lastisiso.comp $
        equi.bij.inv_bij.comp isiso.bij.inv_bij⟩⟩⟩
      change f x ≤ (f y).lift_double seg at f_val
      apply h'.2 $ le_antisymm h'.1 $ le_trans f_val final
  obtain g : ∃ g : Cardinal.{u} → f '' Set.univ, IsOrderIso g := by
    exists (fun x => Quot.lift (f := f) (by
      intro α β h
      have : Cardinal.mk α = Cardinal.mk β := by rwa[Cardinal.eq_iff]
      have le : Cardinal.mk α ≤ Cardinal.mk β := by rw[this]
      have ge : Cardinal.mk β ≤ Cardinal.mk α := by rw[this]
      rw[iso_thing] at le ge
      apply le_antisymm le ge
    ) x).corestrict (by
        intro x h
        rw[Set.mem_image_iff] at h
        obtain ⟨⟨y⟩,rfl,mem⟩ := h
        simp only [Set.val_mem_image_univ])
    rw[isOrderIso_iff_reflect]
    constructor
    · constructor
      · rintro ⟨x⟩ ⟨y⟩ h
        simp only [Subtype.eq_iff, Function.coe_corestrict] at h
        change Cardinal.mk x = Cardinal.mk y
        simp only [Cardinal.eq_iff]
        simp only [f] at h
        have ⟨i1⟩ : Equipotent (f x).val y := by
          simp[f]
          rw[h]
          apply WellOrder.least_mem (s := fun (x : WellOrder.InitialSegment α) => Equipotent x.val y)
        have ⟨i2⟩ : Equipotent (f x).val x := by
          simp[f]
          apply WellOrder.least_mem (s := fun (y : WellOrder.InitialSegment α) => Equipotent y.val x)
        constructor
        exact ⟨_,i1.2.comp i2.2.inv_bij⟩
      · rw[Function.surj_iff]
        rintro ⟨b,c⟩
        rw[Set.mem_image_iff] at c
        obtain ⟨a,rfl,mem⟩ := c
        exists Cardinal.mk a
    · constructor
      · rintro ⟨x⟩ ⟨y⟩ h
        change Cardinal.mk x ≤ Cardinal.mk y at h
        rw[iso_thing] at h
        simp only [Subtype.le_iff_val, Function.coe_corestrict, h]
      · rintro ⟨x⟩ ⟨y⟩ h
        change Cardinal.mk x ≤ Cardinal.mk y
        simp only [Subtype.le_iff_val, Function.coe_corestrict] at h
        rwa[iso_thing]
  apply g.choose_spec.inv.wellOrder

theorem cantor_bernstein_schroeder {α β : Type u} (f : Function.Injection α β) (g : Function.Injection β α) : Equipotent α β := by
  rw[← Cardinal.eq_iff]
  apply le_antisymm <;> {simp only [Cardinal.mk_le_iff]; constructor; assumption}

theorem exists_injection {α β : Type u} : (∃ f : α → β, Function.Injective f) ∨ (∃ f : β → α, Function.Injective f) := by
  rcases le_total (Cardinal.mk α) (Cardinal.mk β) with (le|le)
  · left
    rw[Cardinal.mk_le_iff] at le
    rcases le with ⟨le⟩
    exact ⟨le.1, le.2⟩
  · right
    rw[Cardinal.mk_le_iff] at le
    rcases le with ⟨le⟩
    exact ⟨le.1, le.2⟩

def Cardinal.sigma {ι : Type u} (α : ι → Cardinal.{u}) : Cardinal.{u} := by
  apply Cardinal.mk
  let b i := Classical.choose $ Quot.exists_rep (α i)
  exact Sigma fun i => b i

def Cardinal.prod {ι : Type u} (α : ι → Cardinal.{u}) : Cardinal.{u} := by
  apply Cardinal.mk
  let b i := Classical.choose $ Quot.exists_rep (α i)
  exact (i : _) → b i

@[simp] theorem Cardinal.sigma_mk {ι : Type u} {α : ι → Type u} :
    Cardinal.sigma (fun i => Cardinal.mk (α i)) = Cardinal.mk (Sigma fun i => α i) := by
  simp only [sigma, eq_iff]
  have (i) : Equipotent (@Classical.choose (Type u) (fun x ↦ Quot.mk Equipotent x = mk (α i)) $ Quot.exists_rep (Cardinal.mk $ α i)) (α i) := by
    rw[←Cardinal.eq_iff, Cardinal.mk]
    exact @Classical.choose_spec (Type u) (fun x ↦ Quot.mk Equipotent x = mk (α i)) $ Quot.exists_rep (Cardinal.mk $ α i)
  constructor
  exists fun ⟨i,a⟩ => ⟨_,Classical.choice (this i) a⟩
  constructor
  · intro ⟨i,a⟩ ⟨j,b⟩ h
    simp at h
    have h := congrArg (fun a => a.1) h
    simp only at h
    rcases h
    congr
    injection h with h' h''
    apply (Classical.choice (this i)).2.inj _ _ h''
  · rw[Function.surj_iff]
    intro ⟨i,b⟩
    exists ⟨i,(Classical.choice (this i)).2.inv b⟩
    simp only [Function.Bijective.val_inv_val]

@[simp] theorem Cardinal.prod_mk {ι : Type u} {α : ι → Type u} :
    Cardinal.prod (fun i => Cardinal.mk (α i)) = Cardinal.mk ((i : _) → α i) := by
  simp only [prod, eq_iff]
  have (i) : Equipotent (@Classical.choose (Type u) (fun x ↦ Quot.mk Equipotent x = mk (α i)) $ Quot.exists_rep (Cardinal.mk $ α i)) (α i) := by
    rw[←Cardinal.eq_iff, Cardinal.mk]
    exact @Classical.choose_spec (Type u) (fun x ↦ Quot.mk Equipotent x = mk (α i)) $ Quot.exists_rep (Cardinal.mk $ α i)
  constructor
  exists fun p i => Classical.choice (this i) (p i)
  constructor
  · intro p q h
    ext i
    simp at h
    have h := congrFun h i
    simp only at h
    apply (Classical.choice (this i)).2.inj _ _ h
  · rw[Function.surj_iff]
    intro p
    exists fun i => (Classical.choice (this i)).2.inv (p i)
    simp only [Function.Bijective.val_inv_val]

theorem Cardinal.sigma_ub {ι : Type u} {α : ι → Cardinal.{u}} : UpperBound (α '' Set.univ) (Cardinal.sigma α) := by
  intro x
  rw[Set.mem_image_iff]
  rintro ⟨i,rfl,_⟩
  simp only [sigma]
  rcases h : α i with ⟨t⟩
  change Cardinal.mk t ≤ _
  rw[mk_le_iff]
  constructor
  have : Equipotent (@Classical.choose (Type u) (fun x ↦ Quot.mk Equipotent x = α i) $ Quot.exists_rep $ α i) t := by
    rw[h]
    have := @Classical.choose_spec (Type u) (fun x ↦ Quot.mk Equipotent x = α i) $ Quot.exists_rep $ α i
    rw[h] at this
    change Cardinal.mk _ = Cardinal.mk _ at this
    rwa[eq_iff] at this
  exists (fun a => ⟨i, (Classical.choice this).2.inv a⟩)
  intro x y h
  simp only at h
  injection h with h' h''
  apply (Classical.choice this).2.inv_bij.inj _ _ h''

theorem Cardinal.exists_lubi {ι : Type u} {α : ι → Cardinal.{u}} : ∃ x, IsLUBi α x := by
  have : {s | (UpperBound (α '' Set.univ) s)}.Nonempty := ⟨_,Cardinal.sigma_ub⟩
  have ⟨a,h,least⟩ := WellOrder.existsLeast this
  exists a
  constructor
  · exact least

theorem Cardinal.ge_of_surj {α β : Type u} (h : Function.Surjection α β) : Cardinal.mk β ≤ Cardinal.mk α := by
  rw[Cardinal.mk_le_iff]
  obtain ⟨f,s⟩ := h.2.hasSection
  constructor
  exists f
  apply s.inj

theorem Cardinal.iUnion_le_sigma {ι : Type u} {β : Type u} {α : ι → Set β} : (Cardinal.mk (⋃ i, α i)) ≤ Cardinal.sigma (fun i => Cardinal.mk (α i)) := by
  rw[Cardinal.sigma_mk]
  apply Cardinal.ge_of_surj
  exists fun ⟨i,a,mem⟩ => ⟨a,i,mem⟩
  rw[Function.surj_iff]
  intro ⟨b,i,mem⟩
  simp only [Subtype.eq_iff]
  exists ⟨i,b,mem⟩
