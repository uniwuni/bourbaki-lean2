import BourbakiLean2.Order.WellOrderIso
import BourbakiLean2.Set.Sum
universe u v

def Equipotent (α : Type u) (β : Type v) := Nonempty (Function.Bijection α β)

theorem Equipotent.symm {α β : Type*} (h : Equipotent α β) : Equipotent β α := by
  obtain ⟨h⟩ := h
  constructor
  exact h.inv

theorem Equipotent.trans {α β γ : Type*} (h : Equipotent α β) (h' : Equipotent β γ) : Equipotent α γ := by
  obtain ⟨f,h⟩ := h
  obtain ⟨g,h'⟩ := h'
  constructor
  exists g ∘ f
  apply h'.comp h

theorem Equipotent.of_eq {α β : Type u} (h : α = β) : Equipotent α β := by
  subst h
  constructor
  exact ⟨_,Function.bij_id⟩

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

@[simp] theorem Cardinal.mk_surj : Function.Surjective Cardinal.mk := by
  unfold Cardinal.mk
  change Function.Surjective (Quot.mk $ Function.curry equipotent_rel)
  apply Quot.mk_surj

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

theorem Cardinal.factors_through_mk {α : Type v} {f : α → Cardinal.{u}} : ∃ g : α → Type u, f = Cardinal.mk ∘ g := by
  have ⟨s,iss⟩ := Cardinal.mk_surj.hasSection
  exists s ∘ f
  simp only [Function.comp_assoc]
  rw[iss]
  exact Function.comp_id_left

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

section
variable {ι ι' : Type u} {α : ι → Cardinal.{u}}
theorem Cardinal.sigma_reindex (f : Function.Bijection ι' ι) : Cardinal.sigma (α ∘ f) = Cardinal.sigma α := by
  simp only [sigma, eq_iff]
  apply Equivalence.trans inferInstance
  swap
  · constructor
    apply sigma_reindex_bij f
  · apply Equipotent.of_eq
    congr

theorem Cardinal.sigma_reindex_univ : Cardinal.sigma (fun (⟨x,_⟩ : Set.univ) => α x) = Cardinal.sigma α := by
  have val_bij : Function.Bijective (Subtype.val : Set.univ → ι) := by
    constructor
    · apply Subtype.val_inj
    · rw[Function.surj_iff]
      intro x
      exists ⟨x, trivial⟩
  let b : Function.Bijection _ _ := ⟨_,val_bij⟩
  change Cardinal.sigma (α ∘ b) = Cardinal.sigma α
  rw[Cardinal.sigma_reindex]

theorem Cardinal.prod_reindex (f : Function.Bijection ι' ι) : Cardinal.prod (α ∘ f) = Cardinal.prod α := by
  simp only [prod, eq_iff]
  apply Equivalence.trans inferInstance
  swap
  · apply Equivalence.symm inferInstance
    constructor
    apply Function.reindex_by_bij f
  · apply Equipotent.of_eq
    congr

theorem Cardinal.prod_reindex_univ : Cardinal.prod (fun (⟨x,_⟩ : Set.univ) => α x) = Cardinal.prod α := by
  have val_bij : Function.Bijective (Subtype.val : Set.univ → ι) := by
    constructor
    · apply Subtype.val_inj
    · rw[Function.surj_iff]
      intro x
      exists ⟨x, trivial⟩
  let b : Function.Bijection _ _ := ⟨_,val_bij⟩
  change Cardinal.prod (α ∘ b) = Cardinal.prod α
  rw[Cardinal.prod_reindex]

theorem Cardinal.prod_assoc {α : ι → Cardinal.{u}} {p : ι' → Set ι}
    (h : Set.IsPartition p) : Cardinal.prod α = Cardinal.prod (fun i' : ι' => Cardinal.prod (fun i : p i' => α i)) := by
  have ⟨g,eq⟩ := Cardinal.factors_through_mk (f := α)
  rcases eq
  unfold Function.comp
  simp only [prod_mk, eq_iff]
  constructor
  apply h.prod_assoc

theorem Cardinal.sigma_assoc {α : ι → Cardinal.{u}} {p : ι' → Set ι}
    (h : Set.IsPartition p) : Cardinal.sigma α = Cardinal.sigma (fun i' : ι' => Cardinal.sigma (fun i : p i' => α i)) := by
  have ⟨g,eq⟩ := Cardinal.factors_through_mk (f := α)
  rcases eq
  unfold Function.comp
  simp only [sigma_mk, eq_iff]
  constructor
  apply h.sigma_assoc

theorem Cardinal.sigma_prod_distrib {ι' : ι → Type u} {x : (i : ι) → ι' i → Cardinal.{u}} :
    Cardinal.prod (fun (i : ι) => Cardinal.sigma (fun (i' : ι' i) => x i i')) =
     Cardinal.sigma (fun (y : (i : ι) → ι' i) => Cardinal.prod (fun (i : ι) => x i (y i))) := by
  have this i := Classical.choose_spec $ Cardinal.factors_through_mk (f := x i)
  conv => lhs; rhs; intro i; rhs; intro i'; rw[this i]
  conv => rhs; rhs; intro i; rhs; intro i'; rw[this i']
  unfold Function.comp
  simp only [sigma_mk, prod_mk, eq_iff]
  constructor
  apply Sigma.prod_distrib (x := fun i => Classical.choose $ Cardinal.factors_through_mk (f := x i))

instance : Add Cardinal.{u} where
  add x y := Cardinal.mk $ x.exists_rep.choose ⊕ y.exists_rep.choose

instance : Mul Cardinal.{u} where
  mul x y := Cardinal.mk $ x.exists_rep.choose × y.exists_rep.choose

instance : Pow Cardinal.{u} Cardinal.{u} where
  pow x y := Cardinal.mk $ y.exists_rep.choose → x.exists_rep.choose


@[simp] theorem Cardinal.add_mk {α β : Type u} : Cardinal.mk α + Cardinal.mk β = Cardinal.mk (α ⊕ β) := by
  simp only [HAdd.hAdd, Add.add]
  rw[eq_iff]
  have hα := (Quot.exists_rep (mk α)).choose_spec
  have hβ := (Quot.exists_rep (mk β)).choose_spec
  change mk _ = mk α at hα
  change mk _ = mk β at hβ
  simp only [eq_iff] at hα hβ
  obtain ⟨fα,bα⟩ := hα
  obtain ⟨fβ,bβ⟩ := hβ
  constructor
  exists Sum.map fα fβ
  constructor
  · intro a a' h
    rcases a
    · rcases a'
      · simp only [Sum.map_inl, Sum.inl.injEq] at h
        rw[bα.inj _ _ h]
      · simp only [Sum.map_inl, Sum.map_inr, reduceCtorEq] at h
    · rcases a'
      · simp only [Sum.map_inr, Sum.map_inl, reduceCtorEq] at h
      · simp only [Sum.map_inr, Sum.inr.injEq] at h
        rw[bβ.inj _ _ h]
  · rw[Function.surj_iff]
    rintro (a|a)
    · exists (Sum.inl $ bα.inv a)
      simp only [Sum.map_inl, Function.Bijective.val_inv_val]
    · exists (Sum.inr $ bβ.inv a)
      simp only [Sum.map_inr, Function.Bijective.val_inv_val]

@[simp] theorem Cardinal.mul_mk {α β : Type u} : Cardinal.mk α * Cardinal.mk β = Cardinal.mk (α × β) := by
  simp only [HMul.hMul, Mul.mul]
  rw[eq_iff]
  have hα := (Quot.exists_rep (mk α)).choose_spec
  have hβ := (Quot.exists_rep (mk β)).choose_spec
  change mk _ = mk α at hα
  change mk _ = mk β at hβ
  simp only [eq_iff] at hα hβ
  obtain ⟨fα,bα⟩ := hα
  obtain ⟨fβ,bβ⟩ := hβ
  constructor
  exists Prod.map fα fβ
  constructor
  · intro ⟨a,b⟩ ⟨c,d⟩ h
    simp only [Prod.map_apply, Prod.mk.injEq] at h
    congr
    · exact bα.inj _ _ h.1
    · exact bβ.inj _ _ h.2
  · rw[Function.surj_iff]
    intro ⟨a,b⟩
    exists (Prod.mk (bα.inv a) (bβ.inv b))
    simp only [Prod.map_apply, Function.Bijective.val_inv_val]

@[simp] theorem Cardinal.pow_mk {α β : Type u} : Cardinal.mk α ^ Cardinal.mk β = Cardinal.mk (β → α) := by
  simp only [HPow.hPow, Pow.pow]
  rw[eq_iff]
  have hα := (Quot.exists_rep (mk α)).choose_spec
  have hβ := (Quot.exists_rep (mk β)).choose_spec
  change mk _ = mk α at hα
  change mk _ = mk β at hβ
  simp only [eq_iff] at hα hβ
  obtain ⟨fα,bα⟩ := hα
  obtain ⟨fβ,bβ⟩ := hβ
  constructor
  apply Function.bijection_of_funcs (fun f => fα ∘ f ∘ bβ.inv)
    (fun f => bα.inv ∘ f ∘ fβ)
  · intro b
    ext x
    simp only [Function.comp_assoc, Function.comp_apply, Function.Bijective.val_inv_val]
  · intro b
    ext x
    simp only [Function.comp_assoc, Function.comp_apply, Function.Bijective.inv_val_val]

theorem Cardinal.add_comm {a b : Cardinal.{u}} : a + b = b + a := by
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  obtain ⟨b,rfl⟩ := mk_surj.exists_preimage b
  simp only [add_mk, eq_iff]
  constructor
  apply Function.bijection_of_funcs Sum.swap Sum.swap
  · simp only [Sum.swap_swap, implies_true]
  · simp only [Sum.swap_swap, implies_true]

theorem Cardinal.mul_comm {a b : Cardinal.{u}} : a * b = b * a := by
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  obtain ⟨b,rfl⟩ := mk_surj.exists_preimage b
  simp only [mul_mk, eq_iff]
  constructor
  apply Function.bijection_of_funcs Prod.swap Prod.swap
  · simp only [Prod.swap_swap, implies_true]
  · simp only [Prod.swap_swap, implies_true]


@[simp] theorem Cardinal.add_assoc {a b c : Cardinal.{u}} : a + (b + c) = a + b + c := by
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  obtain ⟨b,rfl⟩ := mk_surj.exists_preimage b
  obtain ⟨c,rfl⟩ := mk_surj.exists_preimage c
  simp only [add_mk, eq_iff]
  constructor
  apply Function.bijection_of_funcs (Sum.elim (Sum.inl ∘ Sum.inl) $ Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr)
    (Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) $ Sum.inr ∘ Sum.inr)
  · rintro ((x|x)|x) <;> simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
  · rintro (x|(x|x)) <;> simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply]

@[simp] theorem Cardinal.mul_assoc {a b c : Cardinal.{u}} : a * (b * c) = a * b * c := by
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  obtain ⟨b,rfl⟩ := mk_surj.exists_preimage b
  obtain ⟨c,rfl⟩ := mk_surj.exists_preimage c
  simp only [mul_mk, eq_iff]
  constructor
  apply Function.bijection_of_funcs (fun ⟨a,b,c⟩ => ⟨⟨a,b⟩,c⟩) (fun ⟨⟨a,b⟩,c⟩ => ⟨a,b,c⟩)
  · simp only [implies_true]
  · simp only [implies_true]

theorem Cardinal.mul_add_distrib_right {a b c : Cardinal.{u}} : (a + b) * c = a * c + b * c := by
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  obtain ⟨b,rfl⟩ := mk_surj.exists_preimage b
  obtain ⟨c,rfl⟩ := mk_surj.exists_preimage c
  simp only [mul_mk, eq_iff, add_mk]
  constructor
  apply Function.bijection_of_funcs (fun ⟨a,c⟩ => Sum.elim (fun x => Sum.inl ⟨x,c⟩) (fun x => Sum.inr ⟨x,c⟩) a)
    (Sum.elim (fun ⟨x,c⟩ => ⟨Sum.inl x,c⟩) (fun ⟨x,c⟩ => ⟨Sum.inr x,c⟩))
  · rintro (⟨x,y⟩|⟨x,y⟩) <;> simp only [Sum.elim_inr, Sum.elim_inl]
  · rintro ⟨(x|x),y⟩ <;> simp only [Sum.elim_inr, Sum.elim_inl]

theorem Cardinal.mul_add_distrib_left {a b c : Cardinal.{u}} : a * (b + c) = a * b + a * c := by
  rw[mul_comm, mul_add_distrib_right, mul_comm, mul_comm (a := c)]

theorem Cardinal.sigma_zeros {α : ι → Cardinal.{u}} {s : Set ι} (h : ∀ x, x ∉ s → α x = 0) :
  Cardinal.sigma α = Cardinal.sigma (fun x : s => α x.val) := by
  have ⟨g,eq⟩ := Cardinal.factors_through_mk (f := α)
  rcases eq
  unfold Function.comp
  simp only [sigma_mk, eq_iff]
  apply Equivalence.symm inferInstance
  constructor
  exists fun ⟨i,x⟩ => ⟨i.val, x⟩
  constructor
  · intro ⟨a,b⟩ ⟨c,d⟩ h
    simp only at h
    have : a = c := by injection h with h'; apply Subtype.eq h'
    rcases this
    injection h with h' h''
    rw[h'']
  · rw[Function.surj_iff]
    intro ⟨a,b⟩
    by_cases mem : a ∈ s
    · exists ⟨⟨a,mem⟩,b⟩
    · specialize h _ mem
      simp only [Function.comp_apply, eq_zero_iff] at h
      exact (h b).elim

theorem Cardinal.prod_ones {α : ι → Cardinal.{u}} {s : Set ι} (h : ∀ x, x ∉ s → α x = 1) :
    Cardinal.prod α = Cardinal.prod (fun x : s => α x.val) := by
  have ⟨g,eq⟩ := Cardinal.factors_through_mk (f := α)
  rcases eq
  unfold Function.comp
  simp only [prod_mk, eq_iff]
  constructor
  exists fun f x => f x.val
  constructor
  · intro x y h'
    ext i
    simp only at h'
    by_cases mem : i ∈ s
    · exact congrFun h' ⟨i,mem⟩
    · specialize h _ mem
      simp only [Function.comp_apply, eq_one_iff] at h
      obtain ⟨h⟩ := h
      exact Subsingleton.allEq (x i) (y i)
  · rw[Function.surj_iff]
    intro f
    simp only [Function.comp_apply, eq_one_iff] at h
    classical
    exists fun x => if h' : x ∈ s then f ⟨x,h'⟩ else (Classical.choice (h _ h')).default
    ext x
    simp only
    split
    · rfl
    · apply (Classical.choice (h _ ‹¬ x.val ∈ s›)).eq_default

@[simp] theorem Cardinal.add_zero {a : Cardinal.{u}} : a + 0 = a := by
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  simp only [add_mk, zero_eq, eq_iff]
  constructor
  apply Function.bijection_of_funcs (Sum.elim id PEmpty.elim) Sum.inl
  · simp only [Sum.elim_inl, id_eq, implies_true]
  · rintro (a|a)
    · simp only [Sum.elim_inl, id_eq]
    · cases a

@[simp] theorem Cardinal.zero_add {a : Cardinal.{u}} : 0 + a = a := by
  rw[add_comm, Cardinal.add_zero]

@[simp] theorem Cardinal.mul_one {a : Cardinal.{u}} : a * 1 = a := by
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  simp only [mul_mk, one_eq, eq_iff]
  constructor
  apply Function.bijection_of_funcs Prod.fst (fun x => ⟨x,PUnit.unit⟩)
   <;> (rintro a; rfl)

@[simp] theorem Cardinal.one_mul {a : Cardinal.{u}} : 1 * a = a := by
  rw[mul_comm, Cardinal.mul_one]

@[simp] theorem Cardinal.sigma_constant {α : Type u} {b : Cardinal.{u}} :
    Cardinal.sigma (fun _ : α => b) = Cardinal.mk α * b := by
  obtain ⟨b,rfl⟩ := mk_surj.exists_preimage b
  simp only [mul_mk, sigma_mk, eq_iff]
  constructor
  apply Function.bijection_of_funcs (fun ⟨a,b⟩ => ⟨a,b⟩) (fun ⟨a,b⟩ => ⟨a,b⟩) <;> simp only [Sigma.eta,
    implies_true]

@[simp] theorem Cardinal.prod_constant {α : Type u} {b : Cardinal.{u}} :
    Cardinal.prod (fun _ : α => b) = b ^ Cardinal.mk α := by
  obtain ⟨b,rfl⟩ := mk_surj.exists_preimage b
  simp only [prod_mk, pow_mk, eq_iff]

@[simp] theorem Cardinal.sigma_constant_one {α : Type u} :
    Cardinal.sigma (fun _ : α => 1) = Cardinal.mk α := by
  simp only [sigma_constant, mul_one]

@[simp] theorem Cardinal.prod_zero_iff {x : ι → Cardinal.{u}} :
    Cardinal.prod x = 0 ↔ ∃ i, x i = 0 := by
  have ⟨g,eq⟩ := Cardinal.factors_through_mk (f := x)
  rw[eq]
  unfold Function.comp
  simp only [prod_mk, eq_zero_iff]
  constructor
  · rintro h
    by_contra h'
    simp only [not_exists, Classical.not_forall, not_false_eq_true] at h'
    exact h (fun i => (h' i).choose)
  · rintro ⟨i,h⟩ f
    exact h $ f i

@[simp] theorem Cardinal.sigma_zero_iff {x : ι → Cardinal.{u}} :
    Cardinal.sigma x = 0 ↔ ∀ i, x i = 0 := by
  have ⟨g,eq⟩ := Cardinal.factors_through_mk (f := x)
  rw[eq]
  unfold Function.comp
  simp only [sigma_mk, eq_zero_iff]
  constructor
  · intro h i f
    exact h ⟨_, f⟩
  · intro f ⟨i,h⟩
    exact f i h

theorem Cardinal.sigma_empty {x : ι → Cardinal.{u}} (h : ι → False) :
    Cardinal.sigma x = 0 := by
  simp only [sigma_zero_iff]
  intro i
  exact (h i).elim

theorem Cardinal.prod_empty {x : ι → Cardinal.{u}} (h : ι → False) :
    Cardinal.prod x = 1 := by
  have ⟨g,eq⟩ := Cardinal.factors_through_mk (f := x)
  rw[eq]
  unfold Function.comp
  simp only [prod_mk, eq_zero_iff]
  simp only [eq_one_iff]
  constructor
  constructor
  swap
  · constructor
    exact fun x => (h x).elim
  · intro a
    ext x
    exact (h x).elim

theorem Cardinal.sigma_add {a b : Cardinal.{u}} :
    Cardinal.sigma (Sum.elim (fun _ : PUnit => a) (fun _ : PUnit.{u+1} => b)) = a + b := by
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  obtain ⟨b,rfl⟩ := mk_surj.exists_preimage b
  suffices (Sum.elim (fun _ : PUnit ↦ mk a) fun _ : PUnit.{u+1} ↦ mk b) = fun i => mk $ (Sum.elim (fun _ : PUnit ↦ a) fun _ : PUnit.{u+1} ↦ b) i by
    rw[this]
    apply Eq.symm
    simp only [sigma_mk, add_mk, eq_iff]
    constructor
    exists (Sum.elim (fun a => ⟨Sum.inl default,a⟩) (fun a => ⟨Sum.inr default,a⟩))
    constructor
    · rintro (x|x) (y|y) h
      · simp only [PUnit.default_eq_unit, Sum.elim_inl] at h
        injections
        congr
      · simp only [PUnit.default_eq_unit, Sum.elim_inl, Sum.elim_inr] at h
        injections
      · simp only [PUnit.default_eq_unit, Sum.elim_inr, Sum.elim_inl] at h
        injections
      · simp only [PUnit.default_eq_unit, Sum.elim_inr] at h
        injections
        congr
    · rw[Function.surj_iff]
      rintro ⟨(a|a),h⟩
      · exists Sum.inl h
      · exists Sum.inr h
  ext j
  rcases j with (j|j) <;> simp

theorem Cardinal.prod_mul {a b : Cardinal.{u}} :
    Cardinal.prod (Sum.elim (fun _ : PUnit => a) (fun _ : PUnit.{u+1} => b)) = a * b := by
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  obtain ⟨b,rfl⟩ := mk_surj.exists_preimage b
  suffices (Sum.elim (fun _ : PUnit ↦ mk a) fun _ : PUnit.{u+1} ↦ mk b) = fun i => mk $ (Sum.elim (fun _ : PUnit ↦ a) fun _ : PUnit.{u+1} ↦ b) i by
    rw[this]
    simp only [mul_mk, prod_mk, eq_iff]
    constructor
    exists fun f => ⟨f $ Sum.inl default, f $ Sum.inr default⟩
    constructor
    · intro a b h
      ext i
      injections h
      rcases i with (i|i) <;> {rcases i; assumption}
    · rw[Function.surj_iff]
      intro ⟨a,b⟩
      exists fun f => match f with
        | Sum.inl PUnit.unit => a
        | Sum.inr PUnit.unit => b
  ext j
  rcases j with (j|j) <;> simp

@[simp] theorem Cardinal.mul_zero {a : Cardinal.{u}} : a * 0 = 0 := by
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  change mk a * mk PEmpty = 0
  simp only [mul_mk, eq_zero_iff, Prod.forall]
  exact fun _ h => h.elim

@[simp] theorem Cardinal.zero_mul {a : Cardinal.{u}} : 0 * a = 0 := by
  rw[mul_comm, Cardinal.mul_zero]

theorem Cardinal.zero_of_mul_zero {a b : Cardinal.{u}} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  obtain ⟨b,rfl⟩ := mk_surj.exists_preimage b
  simp only [mul_mk, eq_zero_iff, Prod.forall] at h
  simp only [mul_mk, eq_zero_iff, Prod.forall]
  by_cases h' : a → False
  · left
    exact h'
  · right
    intro x
    simp only [Classical.not_forall, not_false_eq_true] at h'
    exact h h'.choose x

@[simp] theorem Cardinal.mul_zero_iff {a b : Cardinal.{u}} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · apply zero_of_mul_zero
  · rintro (rfl|rfl)
    · rw[zero_mul]
    · rw[mul_zero]

@[simp] theorem Cardinal.add_zero_iff {a b : Cardinal.{u}} : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  obtain ⟨b,rfl⟩ := mk_surj.exists_preimage b
  simp only [add_mk, eq_zero_iff]
  constructor
  · intro h
    constructor
    · exact h ∘ Sum.inl
    · exact h ∘ Sum.inr
  · intro ⟨h,h'⟩
    exact Sum.elim h h'

theorem Cardinal.add_one_cancel {a b : Cardinal.{u}} (h : a + 1 = b + 1) : a = b := by
  obtain ⟨α,rfl⟩ := mk_surj.exists_preimage a
  obtain ⟨β,rfl⟩ := mk_surj.exists_preimage b
  simp[one_eq] at *
  obtain ⟨f,bij⟩ := h
  by_cases h : f (Sum.inr PUnit.unit) = Sum.inr PUnit.unit
  · have : ∀ x, ∃ y, f (Sum.inl x) = Sum.inl y := by
      intro x
      rcases eq : f $ Sum.inl x with (h'|h')
      · exact ⟨h', rfl⟩
      · rcases h'
        rw[← eq] at h
        have := bij.inj _ _ h
        injection this
    obtain ⟨g,hg⟩ := Classical.axiomOfChoice this
    exists g
    constructor
    · intro x y h
      have : Sum.inl (g x) = Sum.inl (β := PUnit) (g y) := by rw[h]
      rw[← hg, ← hg] at this
      have := bij.inj _ _ this
      injection this
    · rw[Function.surj_iff]
      intro x
      obtain ⟨y,eq⟩ := bij.surj.exists_preimage $ Sum.inl x
      rcases y with (y|y)
      · rw[hg] at eq
        injection eq with eq
        exists y
      · rcases y
        rw[h] at eq
        injection eq
  · obtain ⟨b, eq⟩ : ∃ a, f (Sum.inr PUnit.unit) = Sum.inl a := by
      rcases eq : f (Sum.inr PUnit.unit) with (a|a)
      · exists a
      · rcases a
        exact (h eq).elim
    obtain ⟨a, eq'⟩ : ∃ a, bij.inv (Sum.inr PUnit.unit) = Sum.inl a := by
      rcases eq : bij.inv (Sum.inr PUnit.unit) with (c|c)
      · exists c
      · rcases c
        rw[bij.inv_val_iff] at eq
        exact (h eq).elim
    classical
    let g : α → β ⊕ PUnit := fun x => if h : f (Sum.inl x) = Sum.inr PUnit.unit then Sum.inl b else f $ Sum.inl x
    have : ∀ x, ∃ y, g x = Sum.inl y := by
      intro x
      simp only [dite_eq_ite, g]
      split <;> rename_i ite
      · exists b
      · rcases eq : f (Sum.inl x) with (a|a)
        · exists a
        · rcases a
          exact (ite eq).elim
    obtain ⟨g',hg'⟩ := Classical.axiomOfChoice this
    constructor
    exists g'
    constructor
    · intro x y h
      replace h := congrArg (Sum.inl (β := PUnit)) h
      rw[← hg', ← hg'] at h
      simp only [dite_eq_ite, g] at h
      by_cases c : f (Sum.inl x) = Sum.inr PUnit.unit
      · simp only [c, ↓reduceIte] at h
        by_cases c' : f (Sum.inl y) = Sum.inr PUnit.unit
        · have : Sum.inl x = Sum.inl y := bij.inj _ _ $ c.trans c'.symm
          injection this
        · simp only [c', ↓reduceIte] at h
          rw[← eq] at h
          have := bij.inj _ _ h
          injection this
      · simp only [c, ↓reduceIte] at h
        by_cases c' : f (Sum.inl y) = Sum.inr PUnit.unit
        · simp only [c', ↓reduceIte] at h
          rw[← eq] at h
          have := bij.inj _ _ h
          injection this
        · simp only [c', ↓reduceIte] at h
          have := bij.inj _ _ h
          injection this
    · rw[Function.surj_iff]
      intro x
      obtain ⟨a,eq2⟩ := bij.surj.exists_preimage $ Sum.inl x
      rcases a with (a|a)
      · exists a
        suffices h : Sum.inl x = Sum.inl (g' a) (β := PUnit) by injection h
        rw[← hg']
        simp only [dite_eq_ite, g]
        by_cases h : x = b
        · rcases h
          simp only [eq2, ite_self]
        · rw[eq2]
          split <;> rename_i ite
          · rw[ite] at eq2
            injection eq2
          · rfl
      · rcases a
        exists a
        suffices h : Sum.inl x = Sum.inl (g' a) (β := PUnit) by injection h
        rw[eq2, ← hg']
        simp only [dite_eq_ite, g]
        rw[eq]
        suffices eq : f (Sum.inl a) = Sum.inr PUnit.unit by
          simp only [eq, ↓reduceIte]
        rwa[bij.inv_val_iff] at eq'

@[simp] theorem Cardinal.pow_sigma {x : ι → Cardinal.{u}} {a : Cardinal.{u}} :
    a ^ Cardinal.sigma x = Cardinal.prod (fun i => a ^ x i) := by
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  have ⟨g,eq⟩ := Cardinal.factors_through_mk (f := x)
  rcases eq
  unfold Function.comp
  simp only [sigma_mk, pow_mk, prod_mk, eq_iff]
  constructor
  apply Function.bijection_of_funcs (fun f i x => f ⟨i, x⟩) (fun f ⟨i,x⟩ => f i x)
  · rintro f
    simp only
  · rintro f
    simp only

@[simp] theorem Cardinal.prod_pow {x : ι → Cardinal.{u}} {a : Cardinal.{u}} :
    (Cardinal.prod x) ^ a = Cardinal.prod (fun i => x i ^ a) := by
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  have ⟨g,eq⟩ := Cardinal.factors_through_mk (f := x)
  rcases eq
  unfold Function.comp
  simp only [prod_mk, pow_mk, eq_iff]
  constructor
  apply Function.dep_flip.inv

theorem Cardinal.pow_add {a b c : Cardinal.{u}} : a ^ (b + c) = a ^ b * a ^ c := by
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  obtain ⟨b,rfl⟩ := mk_surj.exists_preimage b
  obtain ⟨c,rfl⟩ := mk_surj.exists_preimage c
  simp only [pow_mk, add_mk, mul_mk, eq_iff]
  constructor
  apply Function.bijection_of_funcs (fun f => ⟨f ∘ Sum.inl, f ∘ Sum.inr⟩) Sum.elim.uncurry
  · rintro ⟨f,g⟩
    simp only [Function.uncurry_apply_pair, Sum.elim_comp_inl, Sum.elim_comp_inr]
  · rintro f
    simp only [Function.uncurry_apply_pair, Sum.elim_comp_inl_inr]

theorem Cardinal.pow_mul {a b c : Cardinal.{u}} : a ^ (b * c) = (a ^ b) ^ c := by
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  obtain ⟨b,rfl⟩ := mk_surj.exists_preimage b
  obtain ⟨c,rfl⟩ := mk_surj.exists_preimage c
  simp only [pow_mk, add_mk, mul_mk, eq_iff]
  constructor
  exact ⟨_, Function.dep_flip.2.comp Function.curry_bijective⟩

@[simp] theorem Cardinal.pow_zero {a : Cardinal.{u}} : a ^ (0 : Cardinal.{u}) = 1 := by
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  simp only [zero_eq, pow_mk, eq_one_iff]
  constructor
  constructor
  swap
  · constructor
    exact nofun
  · intro f
    ext a
    rcases a

@[simp] theorem Cardinal.pow_one {a : Cardinal.{u}} : a ^ (1 : Cardinal.{u}) = a := by
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  simp only [one_eq, pow_mk, eq_iff]
  constructor
  apply Function.bijection_of_funcs (fun f => f PUnit.unit) (fun x y => x)
  · simp only [implies_true]
  · simp only [implies_true]

@[simp] theorem Cardinal.one_pow {a : Cardinal.{u}} : (1 : Cardinal.{u}) ^ a = 1 := by
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  simp only [one_eq, pow_mk, eq_iff]
  constructor
  apply Function.bijection_of_funcs (fun f => PUnit.unit) (fun x y => x)
  · simp only [implies_true]
  · simp only [implies_true]

@[simp] theorem Cardinal.zero_pow_neq_zero {a : Cardinal.{u}} (h : a ≠ 0) : (0 : Cardinal.{u}) ^ a = 0 := by
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  simp only [zero_eq, pow_mk, eq_iff]
  simp only [ne_eq, eq_zero_iff, Classical.not_forall, not_false_eq_true] at h
  obtain ⟨h,_⟩ := h
  constructor
  apply Function.bijection_of_funcs (fun f => f h) PEmpty.elim
  · exact nofun
  · intro f
    exact (f h).elim

theorem Cardinal.set_eq_two_pow {α : Type u} : Cardinal.mk (Set α) = ((1 + 1) : Cardinal.{u}) ^ Cardinal.mk α := by
  simp only [one_eq, add_mk, pow_mk, eq_iff]
  classical
  constructor
  apply Function.bijection_of_funcs
    (fun s x => if x ∈ s then Sum.inl PUnit.unit else Sum.inr PUnit.unit)
    (fun p => {x | p x = Sum.inl PUnit.unit})
  · intro b
    ext a
    simp only [Set.mem_setOf_iff]
    split <;> rename_i ite
    · symm
      assumption
    · rcases eq : b a with (h'|h')
      · rcases h'
        rw[eq] at ite
        exact (ite rfl).elim
      · rcases h'
        rfl
  · intro b
    simp only [ite_eq_left_iff, reduceCtorEq, imp_false, Decidable.not_not]
    rfl

theorem Cardinal.exists_add_iff_le {a b : Cardinal.{u}} : (∃ c, b = a + c) ↔ a ≤ b := by
  constructor
  · rintro ⟨c,rfl⟩
    obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
    obtain ⟨c,rfl⟩ := mk_surj.exists_preimage c
    simp only [add_mk, mk_le_iff]
    constructor
    exists Sum.inl
    intro x y h
    injection h
  · intro h
    obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
    obtain ⟨b,rfl⟩ := mk_surj.exists_preimage b
    simp only [mk_le_iff] at h
    obtain ⟨f,inj⟩ := h
    have : mk a = mk (f '' Set.univ) := by
      simp only [and_true, eq_iff]
      constructor
      exists f.corestrict Set.subset_rfl
      constructor
      · intro x y h
        simp only [Subtype.eq_iff, Function.coe_corestrict] at h
        exact inj _ _ h
      · apply f.corestrict_surjective
    exists mk ((f '' Set.univ) ᶜ)
    rw[this]
    simp only [and_true, not_exists, add_mk, eq_iff]
    constructor
    classical
    apply Function.bijection_of_funcs
      (fun x => if h : x ∈ f '' Set.univ then Sum.inl ⟨x,h⟩ else Sum.inr ⟨x,h⟩)
      (Sum.elim Subtype.val Subtype.val)
    · rintro (⟨x,h⟩|⟨x,h⟩)
      · simp only [Sum.elim_inl, Set.mem_image_iff, Set.mem_univ, and_true]
        split <;> rename_i ite
        · simp only
        · rw[Set.mem_image_iff] at h
          obtain ⟨y,h'⟩ := h
          exact (ite ⟨_,h'.1⟩).elim
      · simp only [Sum.elim_inr, Set.mem_image_iff, Set.mem_univ, and_true]
        split <;> rename_i ite
        · simp only [Set.mem_image_iff, Set.mem_univ, and_true, not_exists] at h
          obtain ⟨y,h'⟩ := ite
          exact (h _ h').elim
        · simp only
    · rintro x
      split <;> rename_i ite
      · simp only [Sum.elim_inl]
      · simp only [Sum.elim_inr]

theorem Cardinal.sigma_le {x y : ι → Cardinal.{u}} (h : ∀ i, x i ≤ y i) : Cardinal.sigma x ≤ Cardinal.sigma y := by
  obtain ⟨x,eq1⟩ := Cardinal.factors_through_mk (f := x)
  obtain ⟨y,eq2⟩ := Cardinal.factors_through_mk (f := y)
  rw[eq1,eq2] at h |-
  unfold Function.comp
  simp only [sigma_mk, mk_le_iff]
  simp only [Function.comp_apply, mk_le_iff] at h
  constructor
  exists fun ⟨i,a⟩ => ⟨i, Classical.choice (h i) a⟩
  intro ⟨i,x⟩ ⟨j,y⟩ h
  simp only [Function.Injective.eq_1] at h
  injection h with h' h''
  rcases h'
  simp only [heq_eq_eq] at *
  congr
  apply (Classical.choice (h i)).2 _ _ h''

theorem Cardinal.prod_le {x y : ι → Cardinal.{u}} (h : ∀ i, x i ≤ y i) : Cardinal.prod x ≤ Cardinal.prod y := by
  obtain ⟨x,eq1⟩ := Cardinal.factors_through_mk (f := x)
  obtain ⟨y,eq2⟩ := Cardinal.factors_through_mk (f := y)
  rw[eq1,eq2] at h |-
  unfold Function.comp
  simp only [prod_mk, mk_le_iff]
  simp only [Function.comp_apply, mk_le_iff] at h
  constructor
  exists fun f i => (Classical.choice (h i)) (f i)
  intro f g eq
  have := congrFun eq
  ext i
  specialize this i
  simp only [Function.Injective.eq_1] at this
  exact (Classical.choice (h i)).2 _ _ this

theorem Cardinal.sigma_subset {x : ι → Cardinal.{u}} {s : Set ι} : Cardinal.sigma (fun a : s => x a) ≤ Cardinal.sigma x := by
  obtain ⟨x,eq⟩ := Cardinal.factors_through_mk (f := x)
  rw[eq]
  unfold Function.comp
  simp only [sigma_mk, mk_le_iff]
  constructor
  exists fun ⟨a,b⟩ => ⟨a.val, b⟩
  intro ⟨a,b⟩ ⟨c,d⟩ h
  simp only [Function.Injective.eq_1] at h
  injection h with h' h''
  congr
  exact Subtype.eq h'

theorem Cardinal.prod_subset {x : ι → Cardinal.{u}} {s : Set ι} (h : ∀ i, i ∉ s → x i ≠ 0) : Cardinal.prod (fun a : s => x a) ≤ Cardinal.prod x := by
  obtain ⟨x,eq⟩ := Cardinal.factors_through_mk (f := x)
  rw[eq] at h |-
  unfold Function.comp
  simp only [prod_mk, mk_le_iff]
  constructor
  simp only [Function.comp_apply, ne_eq, eq_zero_iff, Classical.not_forall, not_false_eq_true] at h
  have : ∀ i : s ᶜ, (x i) := by
    intro i
    exact (h i.1 i.2).choose
  classical
  exists fun f x => if h : x ∈ s then f ⟨x,h⟩ else this ⟨x,h⟩
  intro a b h
  ext ⟨i,hi⟩
  replace h := congrFun h i
  simp only [hi, ↓reduceDIte] at h
  exact h

theorem Cardinal.add_mono_left {a : Cardinal.{u}} : Monotone fun b => a + b := by
  intro b c h
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  obtain ⟨b,rfl⟩ := mk_surj.exists_preimage b
  obtain ⟨c,rfl⟩ := mk_surj.exists_preimage c
  simp only [add_mk, mk_le_iff] at *
  obtain ⟨f,hf⟩ := h
  constructor
  exists Sum.map id f
  rintro (x|x) (y|y) h
  · simp only [Sum.map_inl, id_eq, Sum.inl.injEq] at h
    rw[h]
  · simp only [Sum.map_inl, id_eq, Sum.map_inr, reduceCtorEq] at h
  · simp only [Sum.map_inr, Sum.map_inl, id_eq, reduceCtorEq] at h
  · simp only [Sum.map_inr, Sum.inr.injEq] at h
    rw[hf _ _ h]

theorem Cardinal.add_mono_right {b : Cardinal.{u}} : Monotone fun a => a + b := by
  intro a c h
  simp only
  rw[add_comm, add_comm (a := c)]
  exact add_mono_left h

theorem Cardinal.mul_mono_left {a : Cardinal.{u}} : Monotone fun b => a * b := by
  intro b c h
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  obtain ⟨b,rfl⟩ := mk_surj.exists_preimage b
  obtain ⟨c,rfl⟩ := mk_surj.exists_preimage c
  simp only [mul_mk, mk_le_iff] at *
  obtain ⟨f,hf⟩ := h
  constructor
  exists id.prod f
  simp only [Function.Injective, Prod.forall, Function.prod_val, id_eq, Prod.mk.injEq, and_imp]
  rintro a b c d rfl h2
  exact ⟨rfl, hf _ _ h2⟩

theorem Cardinal.mul_mono_right {b : Cardinal.{u}} : Monotone fun a => a * b := by
  intro a c h
  simp only
  rw[mul_comm, mul_comm (a := c)]
  apply mul_mono_left h

theorem Cardinal.pow_mono_right {b : Cardinal.{u}} : Monotone fun a => (a ^ b : Cardinal.{u}) := by
  intro a c h
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  obtain ⟨b,rfl⟩ := mk_surj.exists_preimage b
  obtain ⟨c,rfl⟩ := mk_surj.exists_preimage c
  simp only [pow_mk, mk_le_iff] at *
  obtain ⟨f,hf⟩ := h
  constructor
  exists fun g => f ∘ g
  intro g1 g2 h
  ext x
  have : f (g1 x) = f (g2 x) := congrFun h x
  exact hf _ _ this

theorem Cardinal.pow_mono_left {a : Cardinal.{u}} (h : a ≠ 0) : Monotone fun b : Cardinal.{u} => (a ^ b : Cardinal.{u}) := by
  intro b c h'
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  obtain ⟨b,rfl⟩ := mk_surj.exists_preimage b
  obtain ⟨c,rfl⟩ := mk_surj.exists_preimage c
  simp only [pow_mk, mk_le_iff] at *
  obtain ⟨f,hf⟩ := h'
  constructor
  simp only [ne_eq, eq_zero_iff, Classical.not_forall, not_false_eq_true] at h
  have d := h.choose
  classical
  exists fun g x => if h : ∃ y, f y = x then g h.choose else d
  intro g g' eq
  ext y
  replace eq := congrFun eq $ f y
  simp at eq
  have := hf _ _ $ @Exists.choose_spec b (fun y_1 ↦ f y_1 = f y) ⟨y,rfl⟩
  rwa[this] at eq

theorem Cardinal.cantor {a : Cardinal.{u}} : a < (1 + 1) ^ a := by
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  rw[← set_eq_two_pow]
  rw[lt_iff_le_not_eq]
  constructor
  · simp only [mk_le_iff]
    constructor
    exists fun x => {x}
    intro x y h
    simp only at h
    rw[Set.ext_iff] at h
    exact (h x).mp rfl
  · simp only [ne_eq, eq_iff]
    intro ⟨⟨f,bij⟩⟩
    let s := {x | x ∉ f x}
    have h1 : ¬ bij.inv s ∈ s := by
      intro h
      have h' := h
      unfold s at h'
      rw[Set.mem_setOf_iff] at h'
      rw[bij.val_inv_val] at h'
      exact h' h
    have h2 : ¬ ¬ bij.inv s ∈ s := by
      intro h
      have h' := h
      unfold s at h'
      rw[Set.mem_setOf_iff] at h'
      rw[bij.val_inv_val] at h'
      exact h' h
    exact h2 h1

theorem Cardinal.higher_universe {α : Type u} : ¬ Equipotent α Cardinal.{u} := by
  intro ⟨f,bij⟩
  have (x : Cardinal.{u}) : x ≤ Cardinal.sigma f := by
    obtain ⟨x,rfl⟩ := mk_surj.exists_preimage x
    have ⟨g,eq⟩ := Cardinal.factors_through_mk (f := f)
    rw[eq]
    unfold Function.comp
    simp only [sigma_mk, mk_le_iff]
    obtain ⟨α, eq2⟩ := bij.surj.exists_preimage $ Cardinal.mk x
    rw[eq] at eq2
    simp only [Function.comp_apply, eq_iff] at eq2
    obtain ⟨eq2⟩ := eq2
    constructor
    exists fun x => ⟨α, eq2 x⟩
    intro x1 x2 h
    simp only at h
    injection h with _ h
    apply eq2.2.inj _ _ h
  have := this ((1 + 1) ^ Cardinal.sigma f)
  rw[← not_gt_iff_le] at this
  exact this Cardinal.cantor

@[simp] theorem Cardinal.add_one_neq_zero {a : Cardinal.{u}} : a + 1 ≠ 0 := by
  intro h
  have := Cardinal.add_zero_iff.mp h
  exact (zero_neq_one this.2.symm).elim

@[simp] theorem Cardinal.le_add_left {a b : Cardinal.{u}} : a ≤ a + b := by
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  obtain ⟨b,rfl⟩ := mk_surj.exists_preimage b
  simp only [add_mk, mk_le_iff]
  constructor
  exists Sum.inl
  intro x y h
  injection h

@[simp] theorem Cardinal.le_add_right {a b : Cardinal.{u}} : b ≤ a + b := by
  obtain ⟨a,rfl⟩ := mk_surj.exists_preimage a
  obtain ⟨b,rfl⟩ := mk_surj.exists_preimage b
  simp only [add_mk, mk_le_iff]
  constructor
  exists Sum.inr
  intro x y h
  injection h

@[simp] theorem Cardinal.mk_le_of_subset {α : Type*} {x y : Set α} (h : x ⊆ y) : Cardinal.mk x ≤ Cardinal.mk y := by
  constructor
  exists fun x => ⟨x, h x.property⟩
  intro x y h
  simp only [Subtype.eq_iff] at h
  exact Subtype.eq h

theorem Cardinal.preimage_same_product {α β : Type u} {f : α → β} {c : Cardinal.{u}}
    (h' : ∀ y : β, Cardinal.mk (f ⁻¹' {y}) = c) : Cardinal.mk α = c * Cardinal.mk β := by
  obtain ⟨c,rfl⟩ := mk_surj.exists_preimage c
  symm
  rw[← sigma_constant]
  simp only [sigma_mk, eq_iff]
  simp only [eq_iff] at h'
  have := Set.singleton_partition.preimage (f := f)
  constructor
  have h' y := (Classical.choice (h' y)).inv
  exists fun ⟨c,b⟩ => (h' b c).val
  constructor
  · rintro ⟨x1,y1⟩ ⟨x2,y2⟩ h''
    simp only at h''
    have eq1 := ((h' y1).val x1).property
    have eq2 := ((h' y2).val x2).property
    rw[h''] at eq1
    simp only [Set.mem_preimage_iff, Set.mem_singleton_iff] at eq1 eq2
    rw[eq1] at eq2
    rw[eq2] at h'' |-
    congr
    rw[← Subtype.eq_iff] at h''
    exact (h' y2).property.inj _ _ h''
  · rw[Function.surj_iff]
    intro a
    simp only
    exists ⟨(h' (f a)).inv.val ⟨_,Set.mem_preimage_iff.mpr rfl⟩, f a⟩
    simp only [Function.Bijection.val_inv_val]

theorem Equipotent.subset_subset {α : Type u} {s t : Set α} (h : s ⊆ t) :
    Equipotent {x : t | x.val ∈ s} s := by
  constructor
  exists fun ⟨⟨x,h⟩,h'⟩ => ⟨x,h'⟩
  constructor
  · rintro ⟨⟨x,h⟩,h'⟩ ⟨⟨y,hy⟩,hy'⟩ eq
    simp only [Subtype.eq_iff] at *
    assumption
  · rw[Function.surj_iff]
    intro ⟨b,h'⟩
    exists ⟨⟨b, h h'⟩, h'⟩

theorem Cardinal.disj_iUnion {α ι : Type u} {a : ι → Set α} (h : Set.Disjoint a) :
    Cardinal.mk (⋃ i, a i) = Cardinal.sigma fun i => Cardinal.mk (a i) := by
  symm
  simp only [Set.mem_iUnion_iff, sigma_mk, eq_iff]
  constructor
  exists fun ⟨i, x⟩ => ⟨x, ⟨i, x.2⟩⟩
  constructor
  · intro ⟨i,⟨x,hx⟩⟩ ⟨j,⟨y,hy⟩⟩ eq
    simp only[Subtype.eq_iff] at eq
    have eq2 : i = j := by
      have : _ ∈ a i ∩ a j := ⟨hx, eq ▸ hy⟩
      by_contra h'
      specialize h i j h'
      rwa[h] at this
    congr
    · rw[eq2]
    · apply heq_of_eqRec_eq
      · rfl
      · rw[eq,eq2]
  · rw[Function.surj_iff]
    intro ⟨x,i,hx⟩
    exists ⟨i,x,hx⟩






end
