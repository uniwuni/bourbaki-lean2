import BourbakiLean2.Set.Rel
import BourbakiLean2.Function.Basic
import BourbakiLean2.Function.Prod
import BourbakiLean2.Set.Partitions

attribute [class] Equivalence
variable {α γ : Type*} {r : Relation α α}
abbrev Relation.IsEquivalence (r : Relation α α) := Equivalence (fun a b => (a,b) ∈ r)

namespace Relation

theorem equiv_refl {r : Relation α α} [inst : IsEquivalence r] {a : α} : (a,a) ∈ r :=
  inst.refl _

@[symm] theorem equiv_symm {r : Relation α α} [inst : IsEquivalence r] {a b : α} (h : (a,b) ∈ r) : (b,a) ∈ r :=
  inst.symm h

@[trans] theorem equiv_trans {r : Relation α α} [inst : IsEquivalence r] {a b c: α}
  (h : (a,b) ∈ r) (h' : (b,c) ∈ r): (a,c) ∈ r :=
  inst.trans h h'


instance : IsEquivalence (Set.univ : Relation α α) where
  refl _ := trivial
  symm _ := trivial
  trans _ _ := trivial

instance : IsEquivalence (diag : Relation α α) where
  refl _ := rfl
  symm := Eq.symm
  trans := Eq.trans

instance : IsEquivalence (fun ⟨a, b⟩ => Nonempty (Function.Bijection a b)) where
  refl a := ⟨_, Function.bij_id⟩
  symm h := h.elim (fun h => ⟨h.inv⟩)
  trans h1 h2 := by
    dsimp only at h1 h2
    rcases h1 with ⟨f,h1⟩
    rcases h2 with ⟨g,h2⟩
    constructor
    exists g ∘ f
    apply h2.comp h1

instance {f : γ → α} [inst : IsEquivalence r] : IsEquivalence (r.inverse_image f) where
  refl _ := inst.refl _
  symm := inst.symm
  trans := inst.trans

instance {x : Set α} [inst : IsEquivalence r] : IsEquivalence (r.restrict x) where
  refl _ := inst.refl _
  symm := inst.symm
  trans := inst.trans


instance {ι : Type*} {r : ι → Relation α α} [inst : ∀ x, IsEquivalence (r x)] : IsEquivalence (⋂ i, r i) where
  refl _ := fun i => (inst i).refl _
  symm h := fun i => (inst i).symm $ h i
  trans h1 h2 := fun i => (inst i).trans (h1 i) (h2 i)

theorem isEquivalence_in_set_or_compl (x : Set α) : IsEquivalence
    (fun ⟨a,b⟩ => a ∈ x ↔ b ∈ x) where
  refl _ := Iff.rfl
  symm := Iff.symm
  trans := Iff.trans

theorem isEquivalence_iff :
    r.IsEquivalence ↔ (r.domain = Set.univ ∧ r.inv = r ∧ r.comp r = r) := by
  constructor
  · intro h
    constructor
    · rw[← Set.univ_subset_iff]
      intro a _
      exact ⟨a, h.refl a⟩
    · constructor
      · ext ⟨a,a'⟩
        exact ⟨h.symm, h.symm⟩
      · ext ⟨a,a'⟩
        constructor
        · simp only [mem_comp_iff, forall_exists_index, and_imp]
          exact fun a h' h'' => h.trans h' h''
        · intro h'
          exists a
          exact ⟨h.refl a, h'⟩
  · intro ⟨h,h',h''⟩
    constructor
    · intro a
      rw[Set.ext_iff] at h
      replace h := (h a).mpr trivial
      obtain ⟨b,h⟩ := h
      replace h' := h' ▸ h
      have h''' : (a,a) ∈ r.comp r := ⟨b,h,h'⟩
      rwa[h''] at h'''
    · intro a a' h
      rwa[← h']
    · intro a a' a'' h0 h1
      have h''' : (a,a'') ∈ r.comp r := ⟨a',h0,h1⟩
      rwa[h''] at h'''

theorem isEquivalence_iff' :
    r.IsEquivalence ↔ (r.comp (r.inv.comp r) = r ∧ diag ⊆ r) := by
  constructor
  · intro h
    constructor
    · ext ⟨a,a'⟩
      simp only [comp_assoc, mem_comp_iff, mem_inv_iff]
      constructor
      · rintro ⟨b, ha, b', hb'b, hb'a'⟩
        apply h.trans ha (h.trans (h.symm hb'b) hb'a')
      · intro ha
        exists a'
        apply And.intro ha
        exists a
    · rintro ⟨a,b⟩ h'
      simp only [diag, Set.mem_setOf_iff] at h'
      rw[h']
      apply h.refl _
  · intro ⟨h1,h2⟩
    constructor
    · exact fun _ => h2 rfl
    · intro x y h
      have : (y,x) ∈ r.comp (r.inv.comp r) := by
        exists x
        constructor
        · exists y
          constructor
          · apply h2 rfl
          · assumption
        · apply h2 rfl
      rwa[h1] at this
    · intro x y z h3 h4
      have : (x,z) ∈ r.comp (r.inv.comp r) := by
        exists y
        constructor
        exists y
        · constructor
          · assumption
          · exact h2 rfl
        · assumption
      rwa[h1] at this

theorem isEquivalence_comp_of_comp_eq_left (h : r.domain = Set.univ)
    (h' : r.comp (r.inv.comp r) = r) : (r.inv.comp r).IsEquivalence := by
  constructor
  · intro x
    obtain ⟨y,h⟩ : x ∈ r.domain := by rw[h]; trivial
    exact ⟨y,h,h⟩
  · rintro x y ⟨z,h1,h2⟩
    exists z
  · rintro x y z ⟨v,h1,h2⟩ ⟨w,h3,h4⟩
    simp at *
    have : (x,w) ∈ r := by
      rw[← h']
      exists v
      apply And.intro h1
      exists y
    exists w

theorem isEquivalence_comp_of_comp_eq_right (h : r.range = Set.univ)
    (h' : r.comp (r.inv.comp r) = r) : (r.comp r.inv).IsEquivalence := by
  constructor
  · intro x
    obtain ⟨y,h⟩ : x ∈ r.range := by rw[h]; trivial
    exact ⟨y,h,h⟩
  · rintro x y ⟨z,h1,h2⟩
    exists z
  · rintro x y z ⟨v,h1,h2⟩ ⟨w,h3,h4⟩
    simp at *
    have : (w,x) ∈ r := by
      rw[← h']
      exists y
      apply And.intro h3
      exists v
    exists w

end Relation
variable {α β : Type*} {f : α → β} {r : Relation α α}

theorem Relation.IsEquivalence.comp_right [inst : Relation.IsEquivalence r] {s : Relation α α} (h : s ⊆ r) (h' : s.domain = Set.univ) :
    r.comp s = r := by
  ext ⟨a,b⟩
  constructor
  · rintro ⟨c,h1,h2⟩
    apply inst.trans (h h1) h2
  · intro h1
    obtain ⟨b',ha⟩ : a ∈ s.domain := by simp only [h', Set.mem_univ]
    exists b'
    constructor
    · exact ha
    · apply inst.symm
      apply inst.trans $ inst.symm h1
      apply h ha

theorem Relation.IsEquivalence.comp_left [inst : Relation.IsEquivalence r] {s : Relation α α} (h : s ⊆ r) (h' : s.range = Set.univ) :
    s.comp r = r := by
  ext ⟨a,b⟩
  constructor
  · rintro ⟨c,h1,h2⟩
    apply inst.trans h1 $ h h2
  · intro h1
    obtain ⟨a',ha⟩ : b ∈ s.range := by simp only [h', Set.mem_univ]
    exists a'
    constructor
    · exact inst.trans h1 $ inst.symm $ h ha
    · exact ha

theorem Relation.IsEquivalence.inter_comp_commute [inst : Relation.IsEquivalence r] {s t : Relation α α} (h : s ⊆ r) :
    (r ∩ t).comp s = r ∩ (t.comp s) := by
  ext ⟨a,b⟩
  constructor
  · intro ⟨c,hac,⟨hcbr,hcbt⟩⟩
    constructor
    · exact inst.trans (h hac) hcbr
    · exists c
  · intro ⟨habr, ⟨c,hac,hcb⟩⟩
    exists c
    constructor
    · assumption
    · constructor
      · exact inst.trans (inst.symm $ h hac) habr
      · assumption

theorem Relation.IsEquivalence.comp_inter [inst : Relation.IsEquivalence r] {s t : Relation α α} (h : s ⊆ r) :
    s.comp (r ∩ t) = r ∩ (s.comp t) := by
  ext ⟨a,b⟩
  constructor
  · intro ⟨c,⟨hacr,hact⟩, hcb⟩
    constructor
    · exact inst.trans hacr $ h hcb
    · exists c
  · intro ⟨habr, ⟨c,hac,hcb⟩⟩
    exists c
    constructor
    · constructor
      · exact inst.trans habr (inst.symm $ h hcb)
      · assumption
    · assumption

theorem Relation.IsEquivalence.comp_isEquivalence_iff_commute [inst : Relation.IsEquivalence r]
    {s : Relation α α} [inst' : Relation.IsEquivalence s] : (r.comp s).IsEquivalence ↔ r.comp s = s.comp r := by
  have e1 := (isEquivalence_iff.mp inst).2.1
  have e2 := (isEquivalence_iff.mp inst').2.1
  constructor
  · intro h
    have e := (isEquivalence_iff.mp h).2.1
    rw[← e1, ← e2, ← inv_comp (r := r), e, e1, e2]
  · intro h
    rw[isEquivalence_iff]
    constructor
    · ext a
      simp only [mem_domain_iff, mem_comp_iff, Set.mem_univ, iff_true]
      exists a
      exists a
      simp only [equiv_refl, and_self]
    · constructor
      · rw[inv_comp, h, e1, e2]
      · conv =>
          arg 1
          arg 2
          rw[h]
        rw[← comp_assoc, comp_assoc (r := s), (isEquivalence_iff.mp inst').2.2, ← h, comp_assoc, (isEquivalence_iff.mp inst).2.2]

@[reducible] def Function.identified_under (f : α → β) : Relation α α := fun a => f a.1 = f a.2

@[simp] theorem Function.mem_identified_under {a a' : α} : ⟨a,a'⟩ ∈ f.identified_under ↔ f a = f a' := Iff.rfl
instance Function.identified_under.isEquivalence : f.identified_under.IsEquivalence where
  refl _ := rfl
  symm := Eq.symm
  trans := Eq.trans

@[simp] theorem Quot.mk_eq_iff_rel [h : Relation.IsEquivalence r] {a b : α}: Quot.mk r.curry a = Quot.mk r.curry b ↔ ⟨a,b⟩ ∈ r := by
  constructor
  · intro h'
    let rLift := Quot.lift (f := fun b => (a,b) ∈ r) (r := r.curry)
      (fun a b h' => propext ⟨fun h'' => h.trans h'' h', fun h'' => h.trans h'' (h.symm h')⟩)
    have eq := Quot.liftBeta (f := fun b => (a,b) ∈ r) (r := r.curry) (fun a b h' => propext ⟨fun h'' => h.trans h'' h', fun h'' => h.trans h'' (h.symm h')⟩) b
    rw[← eq, ← h']
    exact h.refl _
  · intro h'
    apply Quot.sound
    exact h'

@[simp] theorem Quot.mk_surj : (Quot.mk r.curry).Surjective := by
  rw[Function.surj_iff]
  intro b
  obtain ⟨a,h⟩ := Quot.exists_rep b
  exact ⟨a, h.symm⟩

@[simp] theorem Relation.IsEquivalence.eq_identified_under [h : Relation.IsEquivalence r] : (Quot.mk r.curry).identified_under = r := by
  ext ⟨a,b⟩
  simp only [Function.mem_identified_under, Quot.mk_eq_iff_rel]

def Relation.equiv_class (r : Relation α α) (a : α) := {a' | (a,a') ∈ r ∧ (a', a) ∈ r}

@[simp] theorem Relation.IsEquivalence.mem_equiv_class_iff [h : IsEquivalence r] {a a' : α} : a ∈ r.equiv_class a' ↔ ⟨a', a⟩ ∈ r :=
  ⟨And.left, fun a => ⟨a, h.symm a⟩⟩

@[simp] theorem Relation.IsEquivalence.equiv_class_eq_iff {a a' : α} [h : IsEquivalence r] : r.equiv_class a = r.equiv_class a' ↔ ⟨a, a'⟩ ∈ r := by
  constructor
  · simp only [equiv_class, Set.setOf_eq_setOf_iff]
    intro h'
    apply And.right
    apply (h' a).mp
    exact ⟨h.refl _, h.refl _⟩
  · intro h'
    ext b
    simp
    exact ⟨h.trans (h.symm h'),h.trans h'⟩

@[simp] theorem Relation.IsEquivalence.mem_equiv_class [h : IsEquivalence r] {a} : a ∈ r.equiv_class a :=
  ⟨h.refl _, h.refl _⟩

theorem Relation.IsEquivalence.mem_equiv_class_swap [h : IsEquivalence r] {a a' : α} : a ∈ r.equiv_class a' ↔ a' ∈ r.equiv_class a := by
  simp only [mem_equiv_class_iff]
  exact ⟨h.symm, h.symm⟩



def Relation.IsEquivalence.quot_equiv_class_bij [h : r.IsEquivalence] : Function.Bijection (Quot r.curry) (Set.univ.image r.equiv_class) := by
  exists Quot.lift ((fun a => (r.equiv_class a)).corestrict (Set.subset_refl _)) (by
    intro a b
    simp only [Function.curry_apply, Subtype.eq_iff, Function.coe_corestrict, equiv_class_eq_iff]
    exact id)
  constructor
  · rintro ⟨a⟩ ⟨a'⟩
    simp only [Subtype.eq_iff, Function.coe_corestrict, equiv_class_eq_iff, Quot.mk_eq_iff_rel,
      imp_self]
  · rw[Function.surj_iff]
    rintro ⟨b,h'⟩
    replace ⟨a, ⟨h', _⟩⟩ := h'
    simp only [mem_graph_iff] at h'
    rcases h'
    exists Quot.mk _ a

@[simp] theorem Relation.equiv_class_diag {a} : (diag : Relation α α).equiv_class a = {a} := by
  ext
  simp only [IsEquivalence.mem_equiv_class_iff, mem_diag_iff, Set.mem_singleton_iff, Eq.comm]


@[simp] theorem Relation.equiv_class_univ {a} : Relation.equiv_class (Set.univ : Relation α α) a = Set.univ := by
  ext
  simp only [IsEquivalence.mem_equiv_class_iff, Set.mem_univ]

theorem Relation.quotient_preimage_isPartition :
    Set.IsPartition (fun x => Set.preimage (Quot.mk r.curry) {a | a = x}) := by
  constructor
  · ext a
    simp only [Set.mem_iUnion_iff, Set.mem_preimage_iff, Set.mem_univ, iff_true]
    exists Quot.mk _ a
  · intro a b neq
    ext c
    simp only [Set.mem_inter_iff, Set.mem_preimage_iff, Set.mem_setOf_iff, Set.not_mem_empty,
      iff_false, not_and]
    intro h' h''
    exact neq (h' ▸ h'')

theorem Set.IsPartition.in_same_equiv {ι : Type*} {p : ι → Set α} (h : IsPartition p) :
    Relation.IsEquivalence (fun (x,y) => ∃ i, x ∈ p i ∧ y ∈ p i) := by
  constructor
  · intro x
    obtain ⟨i,h⟩ := h.1.mem_exists x
    exists i
  · rintro x y ⟨i,h',h''⟩
    exact ⟨i,h'',h'⟩
  · rintro x y z ⟨i,h',h''⟩ ⟨j,hj',hj''⟩
    have eq : i = j := h.eq_of_mem h'' hj'
    rw[← eq] at hj' hj''
    exists i

def Relation.compatible (p : α → β) := ∀ {x x'}, x ∈ r.equiv_class x' → (p x = p x')

@[simp] theorem Relation.diag_compatible {p : α → β} : (Relation.diag : Relation α α).compatible p := by
  intro x x'
  simp only [equiv_class_diag, Set.mem_singleton_iff]
  rintro rfl
  trivial

def Relation.compatible.lift {p : α → β} [inst : r.IsEquivalence] (h : r.compatible p) :
    (Quot (Function.curry r)) → β :=
  Quot.lift p fun _ _ h' => h $ Iff.mpr inst.mem_equiv_class_iff $ inst.symm h'

@[simp] theorem Relation.compatible.lift_iff {p : α → β} {a} [r.IsEquivalence] (h : r.compatible p) :
    h.lift (Quot.mk _ a) = p a := by
  simp only [lift]

def Relation.saturated (x : Set α) := r.compatible (· ∈ x)

@[simp] theorem Relation.IsEquivalence.saturated_iff  [inst : r.IsEquivalence] {x} : r.saturated x ↔ (∀ a ∈ x, r.equiv_class a ⊆ x) := by
  simp[saturated, compatible]
  constructor
  · intro h a h' a' ⟨h'',h'''⟩
    exact (h h''').mp h'
  · intro h a a' h'
    constructor
    · intro h''
      apply h _ h''
      rw[inst.mem_equiv_class_iff]
      exact inst.symm h'
    · intro h''
      apply h _ h''
      rw[inst.mem_equiv_class_iff]
      exact h'

theorem Relation.IsEquivalence.saturated_iff_preimage_image_quotient [inst : r.IsEquivalence] {x} :
    r.saturated x ↔ x = (Quot.mk (Function.curry r)) ⁻¹' ((Quot.mk (Function.curry r)) '' x) := by
  constructor
  · intro h
    ext a
    simp only [Set.mem_preimage_iff, Set.mem_image_iff, Quot.mk_eq_iff_rel]
    constructor
    · intro h
      exists a
      exact ⟨inst.refl _, h⟩
    · rintro ⟨a', h', h''⟩
      apply (h _).mp h''
      simpa only [IsEquivalence.mem_equiv_class_iff]
  · intro h
    rw[h]
    simp only [saturated_iff, Set.mem_preimage_iff, Set.mem_image_iff, Quot.mk_eq_iff_rel,
      forall_exists_index, and_imp]
    rintro a a' h h' a'' ⟨_,h''⟩
    simp only [Set.mem_preimage_iff, Set.mem_image_iff, Quot.mk_eq_iff_rel]
    exists a'
    exact ⟨inst.trans h'' h, h'⟩

theorem Relation.saturated_iUnion {ι : Type*} {x : ι → Set α} (h : ∀ i, r.saturated (x i)) : r.saturated (⋃ i, x i) := by
    intro a a' h'
    ext
    constructor
    · rintro ⟨i,h'''⟩
      exact ⟨_, (h i h').mp h'''⟩
    · rintro ⟨i,h'''⟩
      exact ⟨_, (h i h').mpr h'''⟩

theorem Relation.saturated_iInter {ι : Type*} {x : ι → Set α} (h : ∀ i, r.saturated (x i)) : r.saturated (⋂ i, x i) := by
  intro a a' h'
  ext
  constructor
  · intro h'' i
    apply (h i h').mp (h'' i)
  · intro h'' i
    apply (h i h').mpr (h'' i)

theorem Relation.saturated.inter {x y : Set α} (h : r.saturated x) (h' : r.saturated y) : r.saturated (x ∩ y) := by
  rw[Set.inter_eq_iInter]
  apply Relation.saturated_iInter
  rintro (True|False)
  · simp only [Bool.false_eq_true, ↓reduceIte, h']
  · simp only [↓reduceIte, h]

theorem Relation.saturated.union {x y : Set α} (h : r.saturated x) (h' : r.saturated y) : r.saturated (x ∪ y) := by
  rw[Set.union_eq_iUnion]
  apply Relation.saturated_iUnion
  rintro (True|False)
  · simp only [Bool.false_eq_true, ↓reduceIte, h']
  · simp only [↓reduceIte, h]

theorem Relation.saturated.compl {x : Set α} (h : r.saturated x) : r.saturated x.compl := by
  intro a a' h'
  simp only [Set.mem_compl_iff, h h']

def Relation.saturation (x : Set α) := Quot.mk (Function.curry r) ⁻¹' ((Quot.mk (Function.curry r)) '' x)

@[simp] theorem Relation.isEquivalence.saturation_saturated [inst : r.IsEquivalence] {x} :
    r.saturated (r.saturation x) := by
  rw[Relation.IsEquivalence.saturated_iff_preimage_image_quotient, saturation]
  rw[Quot.mk_surj.image_preimage]

@[simp] theorem Relation.subset_saturation {x : Set α} : x ⊆ r.saturation x := by
  rw[saturation]
  simp only [Function.subset_preimage_image]

theorem Relation.IsEquivalence.saturation_smallest [inst : r.IsEquivalence] {x y : Set α} (h : r.saturated y): x ⊆ y ↔ r.saturation x ⊆ y := by
  constructor
  · intro h' a ⟨a', h'', ⟨a'', h''', h4⟩⟩
    simp only [mem_graph_iff, Set.mem_image_iff] at *
    rcases h''
    rw[Quot.mk_eq_iff_rel] at h'''
    apply (inst.saturated_iff).mp h a'' (h' h4) ⟨inst.symm h''', h'''⟩
  · exact Set.subset_trans subset_saturation

theorem Relation.IsEquivalence.saturation_eq_equivalence_class_union [inst : r.IsEquivalence] {x : Set α} :
    r.saturation x = ⋃ i : x, r.equiv_class i := by
  rw[Set.eq_iff_subset_subset]
  constructor
  · rw[← Relation.IsEquivalence.saturation_smallest ?new]
    · intro a h
      exists ⟨a,h⟩
      simp only [mem_equiv_class_iff, inst.refl]
    · simp only [saturated_iff, Set.mem_iUnion_iff, mem_equiv_class_iff, Subtype.exists,
      exists_prop, forall_exists_index, and_imp]
      intro a a' h hr
      intro b h'
      simp only [mem_equiv_class_iff, Set.mem_iUnion_iff, Subtype.exists, exists_prop] at *
      exact ⟨a', h, inst.trans hr h'⟩
  · simp only [Set.iUnion_subset_iff_all, Subtype.forall]
    have h' : r.saturated (saturation x) := isEquivalence.saturation_saturated (r := r) (x := x)
    rw[Relation.IsEquivalence.saturated_iff] at h'
    intro a h
    apply h' a (Relation.subset_saturation h)

theorem Relation.IsEquivalence.compatible_iff_factors [inst : r.IsEquivalence] {f : α → β} :
    r.compatible f ↔ ∃ g, f = g ∘ Quot.mk (Function.curry r) := by
  constructor
  · intro h
    exists Relation.compatible.lift h
  · rintro ⟨g, rfl⟩
    simp only [compatible, mem_equiv_class_iff, Function.comp_apply]
    intro a a' h
    congr 1
    simp only [Quot.mk_eq_iff_rel, inst.symm h]

@[simp] theorem Function.identified_under_compatible (f : α → β) : f.identified_under.compatible f := by
  simp only [Relation.compatible, Relation.IsEquivalence.mem_equiv_class_iff, mem_identified_under]
  exact Eq.symm

@[simp] theorem Relation.identified_under_compatible_lift_inj {f : α → β} :
    (compatible.lift f.identified_under_compatible).Injective := by
  intro a a' h
  obtain ⟨a,rfl⟩ := Quot.exists_rep a
  obtain ⟨a',rfl⟩ := Quot.exists_rep a'
  simp only [compatible.lift_iff, Quot.mk_eq_iff_rel, Function.mem_identified_under] at *
  exact h

@[simp] theorem Relation.identified_under_compatible_lift_image {f : α → β} :
    Set.univ.image (compatible.lift f.identified_under_compatible) = Set.univ.image f := by
  ext b
  simp only [Set.mem_image_iff, Set.mem_univ, and_true]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨a,rfl⟩ := Quot.exists_rep a
    exists a
  · rintro ⟨a,rfl⟩
    exists Quot.mk _ a

theorem Function.decompose_inj_bij_surj (f : α → β) :
    ∃ k, f = (Subtype.val : Set.univ.image (Relation.compatible.lift f.identified_under_compatible) → β) ∘ k ∘ Quot.mk (Function.curry f.identified_under) := by
  exists (Relation.compatible.lift f.identified_under_compatible).corestrict (Set.subset_refl _)

def Relation.compatible_lift2 {f : α → β} {s : Relation β β} [inst1 : s.IsEquivalence]
    (h : ∀ x x', (x,x') ∈ r → (f x, f x') ∈ s) : Quot (Function.curry r) → Quot (Function.curry s) := by
  apply Quot.lift (f := Quot.mk _ ∘ f)
  intro a b
  simp only [Function.curry_apply, Function.comp_apply, Quot.mk_eq_iff_rel]
  apply h

theorem Relation.compatible_lift2_commutes {f : α → β} {s : Relation β β} [inst1 : s.IsEquivalence]
    (h : ∀ x x', (x,x') ∈ r → (f x, f x') ∈ s) :
    r.compatible_lift2 h ∘ Quot.mk _ = Quot.mk _ ∘ f := by
  ext a
  simp only [compatible_lift2, Function.comp_apply]

@[simp] theorem Relation.compatible_lift2_apply {a} {f : α → β} {s : Relation β β} [inst1 : s.IsEquivalence]
    (h : ∀ x x', (x,x') ∈ r → (f x, f x') ∈ s) :
    r.compatible_lift2 h (Quot.mk _ a) = Quot.mk _ (f a) := by
  change (compatible_lift2 h ∘ Quot.mk (Function.curry r)) a = (Quot.mk (Function.curry s) ∘ f) a
  rw[Relation.compatible_lift2_commutes]


theorem Relation.IsEquivalence.inverse_image_eq_identified_under [inst : r.IsEquivalence] {f : γ → α} :
    r.inverse_image f = (Quot.mk (Function.curry r) ∘ f).identified_under := by
  ext ⟨a,b⟩
  simp only [Relation.mem_inverse_image_iff, Function.mem_identified_under, Function.comp_apply,
    Quot.mk_eq_iff_rel]

@[simp] theorem Relation.compatible_lift2_of_subtype_inj {x : Set α} [inst : r.IsEquivalence] :
    ((r.restrict x).compatible_lift2 Relation.injection_restrict_compatible).Injective := by
  intro a a' h
  obtain ⟨a,rfl⟩ := a.exists_rep
  obtain ⟨a',rfl⟩ := a'.exists_rep
  apply Quot.sound
  simp only [compatible_lift2_apply, Quot.mk_eq_iff_rel] at *
  exact h

@[simp] theorem Relation.IsEquivalence.diag_subset [inst : r.IsEquivalence] : diag ⊆ r := by
  intro ⟨a,b⟩
  simp only [mem_diag_iff]
  rintro rfl
  exact inst.refl _

def Relation.IsEquivalence.quotient_subset_map [r.IsEquivalence] {s : Relation α α} (h : r ⊆ s) :
    Quot (Function.curry r) → Quot (Function.curry s) :=
  Quot.lift (Quot.mk _) (fun _ _ h' => Quot.sound (h h'))

def Relation.IsEquivalence.quotient [r.IsEquivalence] {s : Relation α α} (h : r ⊆ s) :
    Relation (Quot (Function.curry r)) (Quot (Function.curry r)) :=
  (Quot.lift (Quot.mk (Function.curry s))
    (fun _ _ h' => Quot.sound $ h h')).identified_under


theorem Relation.IsEquivalence.equiv_quotient_iff {a a'} [inst : r.IsEquivalence] {s : Relation α α} [inst' : s.IsEquivalence] (h : r ⊆ s) :
    ⟨Quot.mk _ a, Quot.mk _ a'⟩ ∈ inst.quotient h ↔ ⟨a,a'⟩ ∈ s := by
  simp only [quotient, Function.mem_identified_under, Quot.mk_eq_iff_rel]

--theorem Relation.IsEquivalence_quotient_iff {a a'} [inst : r.IsEquivalence] {s : Relation α α} [inst' : s.IsEquivalence] (h : r ⊆ s) :
--    ⟨Quot.mk _ a, Quot.mk _ a'⟩ ∈ inst.quotient h ↔ ∃ b b', (a,b) ∈ r ∧ (b, b') ∈ s ∧ (b', a') \in
--  simp only [quotient, Function.mem_identified_under, Quot.mk_eq_iff_rel]

def Relation.IsEquivalence.quotient_quotient [inst : r.IsEquivalence] {s : Relation α α} [inst' : s.IsEquivalence] (h : r ⊆ s) :
    Quot (Function.curry (inst.quotient h)) → Quot (Function.curry s) :=
  Quot.lift (inst.quotient_subset_map h) (by
    intro a b h'
    obtain ⟨a,rfl⟩ := a.exists_rep
    obtain ⟨b,rfl⟩ := b.exists_rep
    apply Quot.sound
    simp only [quotient, Function.curry_apply, Function.identified_under, Quot.mk_eq_iff_rel] at h'
    exact h')

@[simp] theorem Relation.IsEquivalence.quotient_quotient_bij [inst : r.IsEquivalence] {s : Relation α α} [inst' : s.IsEquivalence] (h : r ⊆ s) :
    (quotient_quotient h).Bijective := by
  constructor
  · intro a a' h'
    obtain ⟨a,rfl⟩ := a.exists_rep
    obtain ⟨a,rfl⟩ := a.exists_rep
    obtain ⟨a',rfl⟩ := a'.exists_rep
    obtain ⟨a',rfl⟩ := a'.exists_rep
    simp[quotient_quotient, quotient_subset_map] at *
    apply Quot.sound
    simp[quotient, Function.identified_under]
    exact h'
  · rw[Function.surj_iff]
    intro a
    obtain ⟨a,rfl⟩ := a.exists_rep
    exists Quot.mk _ (Quot.mk _ a)

theorem Relation.IsEquivalence.is_quotient_quotient [inst : r.IsEquivalence] {s : Relation (Quot (Function.curry r)) (Quot (Function.curry r))} [inst1 : s.IsEquivalence] :
    s = quotient (s := s.inverse_image (Quot.mk _)) (r := _)
      (fun (a,b) h => (by simp; rw[Quot.sound h]; apply inst1.refl)) := by
  ext ⟨a,a'⟩
  obtain ⟨a,rfl⟩ := a.exists_rep
  obtain ⟨a',rfl⟩ := a'.exists_rep
  simp only [equiv_quotient_iff, Relation.mem_inverse_image_iff]


variable {s : Relation β β} [inst : r.IsEquivalence] [inst' : s.IsEquivalence]
instance : (r.prod_rel s).IsEquivalence where
  refl _ := ⟨inst.refl _, inst'.refl _⟩
  symm h := ⟨inst.symm h.1, inst'.symm h.2⟩
  trans h h' := ⟨inst.trans h.1 h'.1, inst'.trans h.2 h'.2⟩

@[simp] theorem Relation.IsEquivalence.prod_rel_equivalence_class {a} {b} :
    (r.prod_rel s).equiv_class ⟨a,b⟩ = (r.equiv_class a).prod (s.equiv_class b) := by
  ext ⟨a',b'⟩
  simp only [IsEquivalence.mem_equiv_class_iff, mem_prod_rel_iff, Set.mem_prod_iff]

theorem Relation.IsEquivalence.prod_rel_is_identified_under :
    r.prod_rel s = ((Quot.mk (Function.curry r)).prod (Quot.mk (Function.curry s))).identified_under := by
  ext ⟨⟨a,b⟩, ⟨a',b'⟩⟩
  simp only [mem_prod_rel_iff, Function.mem_identified_under, Function.prod_val, Prod.mk.injEq,
    Quot.mk_eq_iff_rel]

def Relation.IsEquivalence.prod_quotient :
    Quot (Function.curry (r.prod_rel s)) → (Quot (Function.curry r)) × (Quot (Function.curry s)) :=
  Quot.lift ((Quot.mk _).prod (Quot.mk _))
  (by intro ⟨a,b⟩ ⟨a',b'⟩ ⟨h,h'⟩
      simp only [Function.prod_val, Prod.mk.injEq, Quot.mk_eq_iff_rel]
      exact ⟨h,h'⟩)

theorem Relation.IsEquivalence.prod_quotient_bij :
    (Relation.IsEquivalence.prod_quotient : Quot (Function.curry (r.prod_rel s)) → (Quot (Function.curry r)) × (Quot (Function.curry s))).Bijective := by
  constructor
  · intro a a' h
    obtain ⟨⟨a,b⟩,rfl⟩ := a.exists_rep
    obtain ⟨⟨a',b'⟩,rfl⟩ := a'.exists_rep
    simp[prod_quotient] at h
    apply Quot.sound
    exact h
  · rw[Function.surj_iff]
    intro ⟨a,b⟩
    obtain ⟨a,rfl⟩ := a.exists_rep
    obtain ⟨b,rfl⟩ := b.exists_rep
    exists Quot.mk _ ⟨a,b⟩

def Relation.IsEquivalence.powerset_quotient_subset_powerset {x : Set α} :
    Function.Bijection x.powerset (Quot (Function.curry (fun (y : Set α) => x ∩ y).identified_under)) :=
  Function.bijection_of_funcs
    (Quot.mk _ ∘ Subtype.val)
    (Quot.lift (fun a => ⟨x ∩ a, (by simp only [Set.mem_powerset_iff, Set.inter_subset_left])⟩)
      (fun a b => (by simp only [Function.curry_apply, Function.identified_under, Subtype.eq_iff,
        imp_self])))
    (by
      intro b
      obtain ⟨a,rfl⟩ := b.exists_rep
      simp only [Function.comp_apply, Quot.mk_eq_iff_rel, Function.mem_identified_under,
        Set.inter_eq_iff_subset_right, Set.inter_subset_left])
    (by
      rintro ⟨b,h⟩
      simp only [Function.comp_apply, Subtype.eq_iff, Set.inter_eq_iff_subset_right]
      exact h)

def Relation.IsEquivalence.quotient_image_bij_inverse_image {f : α → β} {r : Relation β β} [inst : r.IsEquivalence] :
    Function.Bijection (Quot $ Function.curry $ r.inverse_image f) (Quot $ Function.curry $ r.restrict $ Set.image f Set.univ) := by
  exists compatible_lift2 (f := f.corestrict $ Set.subset_refl _) (fun _ _ h => h)
  constructor
  · intro a a' h
    obtain ⟨a,rfl⟩ := a.exists_rep
    obtain ⟨a',rfl⟩ := a'.exists_rep
    simp only [compatible_lift2_apply, Quot.mk_eq_iff_rel, mem_restrict_iff,
      Function.coe_corestrict, mem_inverse_image_iff] at *
    exact h
  · rw[Function.surj_iff]
    intro b
    obtain ⟨⟨b,⟨a,h,_⟩⟩,rfl⟩ := b.exists_rep
    exists Quot.mk _ a
    simp only [mem_graph_iff] at h
    simp only [compatible_lift2_apply, Quot.mk_eq_iff_rel, mem_restrict_iff,
      Function.coe_corestrict, h, inst.refl]


def Quot.lift2_same (f : α → α → β) {r : α → α → Prop} [inst : Equivalence r]
    (h : ∀ x x' y y', r x x' → r y y' → f x y = f x' y') : Quot r → Quot r → β :=
  Quot.lift (fun a => Quot.lift (f a) $ fun _ _ h' => h _ _ _ _ (inst.refl _) h')
    (fun _ _ r' => by ext b; obtain ⟨b,rfl⟩ := b.exists_rep; simp only [h _ _ _ _ r' $
        inst.refl _])
@[simp] theorem Quot.lift2_same_val {f : α → α → β} {r : α → α → Prop} [inst : Equivalence r]
    (h : ∀ x x' y y', r x x' → r y y' → f x y = f x' y') {a b : α} :
    Quot.lift2_same f h (Quot.mk r a) (Quot.mk r b) = f a b := rfl
