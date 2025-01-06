import BourbakiLean2.Data.Nat.Basic
import BourbakiLean2.Data.Finite

universe u v
instance finite_sigma {α : Type u} {x : α → Cardinal.{u}} [h1 : Finite α] [h2 : ∀ a, Cardinal.Finite $ x a] :
    Cardinal.Finite $ Cardinal.sigma x := by
  rw[← Cardinal.sigma_reindex_univ]
  apply Finite.set_induction (p := fun a =>
    (Cardinal.sigma fun x_1 : a ↦
      match x_1 with
      | ⟨x_2, property⟩ => x x_2).Finite)
  · rw[Cardinal.sigma_empty]
    · infer_instance
    · exact fun ⟨x,h⟩ => h
  · intro a A fina nmem sumfin
    have : (Cardinal.sigma fun x_1 : (A ∪ {a} : Set _) ↦
            match x_1 with
            |   ⟨x_2, property⟩ => x x_2) =
           x a + (Cardinal.sigma fun x_1 : (A : Set _) ↦
            match x_1 with
            |   ⟨x_2, property⟩ => x x_2) := by
      have ⟨g,eq⟩ := Cardinal.factors_through_mk (f := x)
      rcases eq
      unfold Function.comp
      apply Eq.symm
      simp only [Finite.iff, Function.comp_apply, Cardinal.sigma_mk, Cardinal.add_mk,
        Cardinal.eq_iff] at *
      constructor
      exists Sum.elim
        (fun x => ⟨⟨_,Or.inr rfl⟩, x⟩)
        (fun ⟨⟨a,h⟩,x⟩ => ⟨⟨_,Or.inl h⟩, x⟩)
      constructor
      · rintro (a1|⟨i1,a1⟩) (a2|⟨i2,a2⟩) h
        · simp only [Sum.elim_inl] at h
          congr
          injection h
        · simp only [Sum.elim_inl, Sum.elim_inr] at h
          injection h with h _
          injection h with h
          have := i2.property
          rw[← h] at this
          apply (nmem this).elim
        · simp only [Sum.elim_inr, Sum.elim_inl] at h
          injection h with h _
          injection h with h
          have := i1.property
          rw[h] at this
          apply (nmem this).elim
        · simp at h
          congr
          injection h with h _
          injection h with h
          · simp only [Subtype.eq_iff, h]
          · injection h
      · rw[Function.surj_iff]
        rintro ⟨⟨i,(ha|rfl)⟩,b⟩
        · exists Sum.inr ⟨⟨i,ha⟩,b⟩
        · exists Sum.inl b
    rw[this]
    infer_instance

instance finite_prod {α : Type u} {x : α → Cardinal.{u}} [h1 : Finite α] [h2 : ∀ a, Cardinal.Finite $ x a] :
    Cardinal.Finite $ Cardinal.prod x := by
  rw[← Cardinal.prod_reindex_univ]
  apply Finite.set_induction (p := fun a =>
    (Cardinal.prod fun x_1 : a ↦
      match x_1 with
      | ⟨x_2, property⟩ => x x_2).Finite)
  · rw[Cardinal.prod_empty]
    · infer_instance
    · exact fun ⟨x,h⟩ => h
  · intro a A fina nmem sumfin
    have : (Cardinal.prod fun x_1 : (A ∪ {a} : Set _) ↦
            match x_1 with
            |   ⟨x_2, property⟩ => x x_2) =
           x a * (Cardinal.prod fun x_1 : (A : Set _) ↦
            match x_1 with
            |   ⟨x_2, property⟩ => x x_2) := by
      have ⟨g,eq⟩ := Cardinal.factors_through_mk (f := x)
      rcases eq
      unfold Function.comp
      simp only [Finite.iff, Function.comp_apply, Cardinal.prod_mk, Cardinal.mul_mk,
        Cardinal.eq_iff] at *
      constructor
      exists fun f => ⟨f ⟨a, Or.inr rfl⟩, fun i => f ⟨i, Or.inl i.property⟩⟩
      constructor
      · rintro f1 f2 eq
        simp only [Prod.mk.injEq] at eq
        ext i
        rcases i with ⟨i,(h|rfl)⟩
        · exact congrFun eq.2 ⟨i, h⟩
        · exact eq.1
      · rw[Function.surj_iff]
        intro ⟨b,f⟩
        classical
        exists fun ⟨i,h⟩ => Or.by_cases' h (fun h => f ⟨_,h⟩) (fun h => h ▸ b)
        congr
        · simp only [Or.by_cases', Set.mem_singleton_iff, ↓reduceDIte]
          have (h : a ∈ ({a} : Set α)) : h = rfl := by rcases h; rfl
          rw[this (h := of_eq_true _)]
          simp only [Set.mem_singleton_iff]
        · ext ⟨x,h⟩
          have : x ≠ a := by
            intro h'
            rw[h'] at h
            exact nmem h
          simp only [Or.by_cases', Set.mem_singleton_iff, this, ↓reduceDIte]
    rw[this]
    infer_instance

instance Finite.prod_finite {α : Type u} [Finite α] {x : α → Type u} [∀ i, Finite (x i)] : Finite ((i : _) × x i) where
  finite := by
    rw[← Cardinal.sigma_mk]
    infer_instance

instance Finite.sigma_finite {α : Type u} [Finite α] {x : α → Type u} [∀ i, Finite (x i)] : Finite ((i : _) → x i) where
  finite := by
    rw[← Cardinal.prod_mk]
    infer_instance

instance Finite.pow_finite {α : Type u} [Finite α] : Finite (Set α) where
  finite := by
    rw[Cardinal.set_eq_two_pow]
    infer_instance

instance {α β : Type u} [Finite α] {x : α → Set β} [∀ i, Finite (x i)] : Finite (⋃ i, x i) where
  finite := by
    simp only [Set.mem_iUnion_iff]
    apply Cardinal.Finite.of_le_finite _ Cardinal.iUnion_le_sigma
    infer_instance

noncomputable def Nat.finite_sum {ι : Type*} [Finite ι] (x : ι → Nat) :=
  FiniteCardinal.to_nat ⟨Cardinal.sigma (fun i => FiniteCardinal.of_nat (x i)), inferInstance⟩

noncomputable def Nat.finite_prod {ι : Type*} [Finite ι] (x : ι → Nat) :=
  FiniteCardinal.to_nat ⟨Cardinal.prod (fun i => FiniteCardinal.of_nat (x i)), inferInstance⟩

@[simp] theorem Nat.finite_sum_empty {ι : Type*} [Finite ι] (x : ι → Nat) (h : ι → False) :
    Nat.finite_sum x = 0 := by
  simp only [finite_sum, FiniteCardinal.to_nat, FiniteCardinal.eq_1, zero_eq, succ_eq_add_one,
    Cardinal.sigma_empty h, FiniteCardinal.recursion_zero]

@[simp] theorem Nat.finite_prod_empty {ι : Type*} [Finite ι] (x : ι → Nat) (h : ι → False) :
    Nat.finite_prod x = 1 := by
  simp only [finite_prod, Cardinal.prod_empty h, FiniteCardinal.to_nat_one]

@[simp] theorem Nat.finite_sum_unique {ι : Type v} [h : Unique ι] (x : ι → Nat):
    Nat.finite_sum x = x default := by
  simp only [finite_sum]
  conv =>
    lhs; rhs; lhs; rhs; intro i; rw[Unique.eq_default (a := i)]
  have : Cardinal.mk.{v} ι = 1 := by
    simp only [Cardinal.eq_one_iff]
    exact ⟨h⟩
  simp only [Cardinal.sigma_constant, this, Cardinal.one_mul]
  change FiniteCardinal.to_nat (FiniteCardinal.of_nat (x default)) = _
  rw[FiniteCardinal.to_nat_of_nat]

@[simp] theorem Nat.finite_prod_unique {ι : Type v} [h : Unique ι] (x : ι → Nat):
    Nat.finite_prod x = x default := by
  simp only [finite_prod]
  conv =>
    lhs; rhs; lhs; rhs; intro i; rw[Unique.eq_default (a := i)]
  have : Cardinal.mk.{v} ι = 1 := by
    simp only [Cardinal.eq_one_iff]
    exact ⟨h⟩
  simp only [Cardinal.prod_constant, this, Cardinal.pow_one]
  change FiniteCardinal.to_nat (FiniteCardinal.of_nat (x default)) = _
  rw[FiniteCardinal.to_nat_of_nat]

@[simp] theorem Nat.finite_sum_reindex {ι ι' : Type v} [h : Finite ι] [h' : Finite ι'] (f : Function.Bijection ι' ι)
    {x : ι → Nat} : Nat.finite_sum x = Nat.finite_sum (x ∘ f)
 := by
  simp only [finite_sum]
  congr 2
  simp
  change (Cardinal.sigma (Subtype.val ∘ FiniteCardinal.of_nat ∘ x)) =
    Cardinal.sigma ((Subtype.val ∘ FiniteCardinal.of_nat ∘ x) ∘ f)
  rw[Cardinal.sigma_reindex]

theorem Nat.finite_sum_reindex_univ {ι : Type v} [h : Finite ι]
    {x : ι → Nat} : Nat.finite_sum x = Nat.finite_sum (fun (i : (Set.univ : Set ι)) => x i) := by
  change Nat.finite_sum x = Nat.finite_sum (x ∘ Function.bijection_univ : Set.univ → Nat)
  rw[← finite_sum_reindex]

@[simp] theorem Nat.finite_prod_reindex {ι ι' : Type v} [h : Finite ι] [h' : Finite ι'] (f : Function.Bijection ι' ι)
    {x : ι → Nat} : Nat.finite_prod x = Nat.finite_prod (x ∘ f)
 := by
  simp only [finite_prod]
  congr 2
  simp
  change (Cardinal.prod (Subtype.val ∘ FiniteCardinal.of_nat ∘ x)) =
    Cardinal.prod ((Subtype.val ∘ FiniteCardinal.of_nat ∘ x) ∘ f)
  rw[Cardinal.prod_reindex]

theorem Nat.finite_prod_reindex_univ {ι : Type v} [h : Finite ι]
    {x : ι → Nat} : Nat.finite_prod x = Nat.finite_prod (fun (i : (Set.univ : Set ι)) => x i) := by
  change Nat.finite_prod x = Nat.finite_prod (x ∘ Function.bijection_univ : Set.univ → Nat)
  rw[← finite_prod_reindex]


theorem Nat.finite_sum_assoc {ι ι' : Type v} [h : Finite ι] [h' : Finite ι'] {α : ι → Nat} {p : ι' → Set ι}
    (h'' : Set.IsPartition p) : Nat.finite_sum α = Nat.finite_sum (fun i' : ι' => Nat.finite_sum (fun i : p i' => α i)) := by
  simp only [finite_sum, FiniteCardinal.of_nat_to_nat]
  congr 1
  simp only [FiniteCardinal.eq_1, Subtype.eq_iff]
  rw[Cardinal.sigma_assoc h'']

theorem Nat.finite_prod_assoc {ι ι' : Type v} [h : Finite ι] [h' : Finite ι'] {α : ι → Nat} {p : ι' → Set ι}
    (h'' : Set.IsPartition p) : Nat.finite_prod α = Nat.finite_prod (fun i' : ι' => Nat.finite_prod (fun i : p i' => α i)) := by
  simp only [finite_prod, FiniteCardinal.of_nat_to_nat]
  congr 1
  simp only [FiniteCardinal.eq_1, Subtype.eq_iff]
  rw[Cardinal.prod_assoc h'']

theorem Nat.finite_sum_assoc2 {ι : Type u} {α : ι → Nat} [h : Finite ι] {s t : Set ι} (h' : s ∪ t = Set.univ) (h'' : s ∩ t = ∅) :
    Nat.finite_sum α = Nat.finite_sum (α ∘ Subtype.val : s → Nat) + Nat.finite_sum (α ∘ Subtype.val : t → Nat) := by
  let p : (PUnit.{u + 1} ⊕ PUnit.{u + 1}) → Set ι := Sum.elim (fun _ => s) (fun _ => t)
  have : Set.IsPartition p := by
    constructor
    · ext i
      rw[← h']
      simp only [Set.mem_iUnion_iff, Set.mem_union_iff, p]
      constructor
      · rintro ⟨(h|h),h'⟩
        · left; assumption
        · right; assumption
      · rintro (h|h)
        · exists Sum.inl default
        · exists Sum.inr default
    · rintro (i|i) (j|j) ne
      · exact (ne rfl).elim
      · simp only [Sum.elim_inl, Sum.elim_inr, h'', p]
      · simp only [Sum.elim_inl, Sum.elim_inr, h'', p, Set.inter_comm]
      · exact (ne rfl).elim
  have := Nat.finite_sum_assoc (h := h) (ι := ι) (α := α) (h'' := this)
  rw[this]
  unfold p
  simp only [finite_sum, FiniteCardinal.of_nat_to_nat, Function.comp_apply]
  rw[← FiniteCardinal.to_nat_add]
  congr
  simp
  suffices (fun i' ↦ Cardinal.sigma fun i : p i' ↦ FiniteCardinal.of_nat $ α i.val) = Sum.elim (fun a => Cardinal.sigma fun (i : p (Sum.inl a)) ↦ FiniteCardinal.of_nat $ α i.val) (fun a => Cardinal.sigma fun (i : p (Sum.inr a)) ↦ FiniteCardinal.of_nat $ α i.val) by
    rw[this]
    rw[← Cardinal.sigma_add]
    congr
  ext i'
  rcases i' with (i'|i')
  · rcases i'
    simp only [Sum.elim_inl]
  · rcases i'
    simp only [Sum.elim_inr]

theorem Nat.finite_prod_assoc2 {ι : Type u} {α : ι → Nat} [h : Finite ι] {s t : Set ι} (h' : s ∪ t = Set.univ) (h'' : s ∩ t = ∅) :
    Nat.finite_prod α = Nat.finite_prod (α ∘ Subtype.val : s → Nat) * Nat.finite_prod (α ∘ Subtype.val : t → Nat) := by
  let p : (PUnit.{u + 1} ⊕ PUnit.{u + 1}) → Set ι := Sum.elim (fun _ => s) (fun _ => t)
  have : Set.IsPartition p := by
    constructor
    · ext i
      rw[← h']
      simp only [Set.mem_iUnion_iff, Set.mem_union_iff, p]
      constructor
      · rintro ⟨(h|h),h'⟩
        · left; assumption
        · right; assumption
      · rintro (h|h)
        · exists Sum.inl default
        · exists Sum.inr default
    · rintro (i|i) (j|j) ne
      · exact (ne rfl).elim
      · simp only [Sum.elim_inl, Sum.elim_inr, h'', p]
      · simp only [Sum.elim_inl, Sum.elim_inr, h'', p, Set.inter_comm]
      · exact (ne rfl).elim
  have := Nat.finite_prod_assoc (h := h) (ι := ι) (α := α) (h'' := this)
  rw[this]
  unfold p
  simp only [finite_prod, FiniteCardinal.of_nat_to_nat, Function.comp_apply]
  rw[← FiniteCardinal.to_nat_mul]
  congr
  simp
  suffices (fun i' ↦ Cardinal.prod fun i : p i' ↦ FiniteCardinal.of_nat $ α i.val)
    = Sum.elim (fun a => Cardinal.prod fun (i : p (Sum.inl a)) ↦ FiniteCardinal.of_nat $ α i.val) (fun a => Cardinal.prod fun (i : p (Sum.inr a)) ↦ FiniteCardinal.of_nat $ α i.val) by
    rw[this]
    rw[← Cardinal.prod_mul]
    congr
  ext i'
  rcases i' with (i'|i')
  · rcases i'
    simp only [Sum.elim_inl]
  · rcases i'
    simp only [Sum.elim_inr]

theorem Nat.finite_sum_remove_one {ι : Type v} [h : Finite ι] {α : ι → Nat} (i : ι)
    : Nat.finite_sum α = Nat.finite_sum ((α ∘ Subtype.val) : {i} ᶜ → Nat) + α i := by
  rw[Nat.finite_sum_assoc2 (s := {i} ᶜ) (t := {i})]
  · simp only [Nat.add_left_cancel_iff]
    rw[Nat.finite_sum_unique]
    simp only [default, Function.comp_apply]
  · ext i; simp only [Set.mem_union_iff, Set.mem_compl_iff, Set.mem_singleton_iff, or_comm,
    Classical.em, Set.mem_univ]
  · ext i; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff, not_and_self,
    Set.not_mem_empty]
theorem Nat.finite_prod_remove_one {ι : Type v} [h : Finite ι] {α : ι → Nat} (i : ι)
    : Nat.finite_prod α = Nat.finite_prod ((α ∘ Subtype.val) : {i} ᶜ → Nat) * α i := by
  rw[Nat.finite_prod_assoc2 (s := {i} ᶜ) (t := {i})]
  · congr
    rw[Nat.finite_prod_unique]
    simp only [default, Function.comp_apply]
  · ext i; simp only [Set.mem_union_iff, Set.mem_compl_iff, Set.mem_singleton_iff, or_comm,
    Classical.em, Set.mem_univ]
  · ext i; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff, not_and_self,
    Set.not_mem_empty]

theorem Nat.finite_sum_mono {ι : Type v} [h : Finite ι] {x y : ι → Nat}
    (h' : ∀ i, x i ≤ y i) : finite_sum x ≤ finite_sum y := by
  simp only [finite_sum, FiniteCardinal.to_nat_le_iff, FiniteCardinal.eq_1, Subtype.le_iff_val]
  apply Cardinal.sigma_le
  intro i
  apply FiniteCardinal.of_nat_le_iff.mpr
  apply h'

theorem Nat.finite_sum_lt {ι : Type v} [h : Finite ι] {x y : ι → Nat} {i}
    (h' : ∀ i, x i ≤ y i) (h'' : x i < y i) : finite_sum x < finite_sum y := by
  rw[finite_sum_remove_one i, finite_sum_remove_one i]
  apply lt_of_lt_le (Nat.add_lt_add_left h'' _)
  apply Nat.add_le_add_right
  apply Nat.finite_sum_mono
  intro ⟨i,h⟩
  simp only [Function.comp_apply, h']

@[simp] theorem Nat.finite_sum_zero_iff {ι : Type v} [h : Finite ι] {x : ι → Nat} :
    finite_sum x = 0 ↔ ∀ i, x i = 0 := by
  simp only [finite_sum]
  constructor
  · intro h
    rw[← FiniteCardinal.to_nat_zero] at h
    have h := FiniteCardinal.to_nat_bij.inj _ _ h
    simp only [FiniteCardinal.eq_1, Subtype.eq_iff, Cardinal.sigma_zero_iff] at h
    intro i
    specialize h i
    change (FiniteCardinal.of_nat (x i)).val = (⟨0, inferInstance⟩ : FiniteCardinal).val at h
    replace h := congrArg FiniteCardinal.to_nat $ Subtype.eq h
    simp only [FiniteCardinal.to_nat_of_nat, FiniteCardinal.to_nat_zero] at h
    exact h
  · intro h
    suffices (Cardinal.sigma fun i ↦ (FiniteCardinal.of_nat (x i)).val) = 0 by
      simp only [this, FiniteCardinal.to_nat_zero]
    simp only [Cardinal.sigma_zero_iff]
    intro i
    specialize h i
    rw[h]
    simp only [FiniteCardinal.of_nat_zero]

@[simp] theorem Nat.finite_prod_zero_iff {ι : Type v} [h : Finite ι] {x : ι → Nat} :
    finite_prod x = 0 ↔ ∃ i, x i = 0 := by
  simp only [finite_prod]
  constructor
  · intro h
    rw[← FiniteCardinal.to_nat_zero] at h
    have h := FiniteCardinal.to_nat_bij.inj _ _ h
    simp only [FiniteCardinal.eq_1, Subtype.eq_iff, Cardinal.prod_zero_iff] at h
    obtain ⟨i, eq⟩ := h
    exists i
    change (FiniteCardinal.of_nat (x i)).val = (⟨0, inferInstance⟩ : FiniteCardinal).val at eq
    replace h := congrArg FiniteCardinal.to_nat $ Subtype.eq eq
    simp only [FiniteCardinal.to_nat_of_nat, FiniteCardinal.to_nat_zero] at h
    exact h
  · intro h
    suffices (Cardinal.prod fun i ↦ (FiniteCardinal.of_nat (x i)).val) = 0 by
      simp only [this, FiniteCardinal.to_nat_zero]
    simp only [Cardinal.prod_zero_iff]
    obtain ⟨i,eq⟩ := h
    exists i
    rw[eq]
    simp only [FiniteCardinal.of_nat_zero]
theorem Nat.finite_prod_mono {ι : Type v} [h : Finite ι] {x y : ι → Nat}
  (h' : ∀ i, x i ≤ y i) : finite_prod x ≤ finite_prod y := by
simp only [finite_prod, FiniteCardinal.to_nat_le_iff, FiniteCardinal.eq_1, Subtype.le_iff_val]
apply Cardinal.prod_le
intro i
apply FiniteCardinal.of_nat_le_iff.mpr
apply h'

theorem Nat.finite_prod_lt {ι : Type v} [h : Finite ι] {x y : ι → Nat} {i}
    (h' : ∀ i, x i ≤ y i) (h'' : x i < y i) (h''' : ∀ i, 0 < x i): finite_prod x < finite_prod y := by
  rw[finite_prod_remove_one i, finite_prod_remove_one i]
  have ne : finite_prod (x ∘ Subtype.val : {i}ᶜ → Nat) ≠ 0 := by
    intro h
    simp only [finite_prod_zero_iff, Function.comp_apply, Subtype.exists, Set.mem_compl_iff,
      Set.mem_singleton_iff, exists_prop] at h
    obtain ⟨i,ne,eq⟩ := h
    specialize h''' i
    rw[eq] at h'''
    simp only [Nat.lt_irrefl] at h'''
  rw[Nat.ne_zero_iff_zero_lt] at ne
  apply lt_of_lt_le $ (Nat.mul_lt_mul_left ne).mpr h''
  apply Nat.mul_le_mul_right
  apply Nat.finite_prod_mono
  intro ⟨i,h⟩
  simp only [Function.comp_apply, h']

theorem Nat.pow_strict_mono_left {a a' b : Nat} (h : 0 < b) (h' : a < a') : a ^ b < a' ^ b := by
  induction b with
  | zero => apply (not_lt_self h).elim
  | succ n ih =>
    rcases a with (a|a)
    · rcases a' with (a'|a')
      · apply (not_lt_self h').elim
      · apply Nat.pow_pos h'
    · rcases n with (n|n)
      · simp only [Nat.zero_add, Nat.pow_one, h']
      · specialize ih (zero_lt_succ _)
        rw[Nat.pow_add, Nat.pow_add (a := a'), Nat.pow_one, Nat.pow_one]
        apply lt_of_lt_le
        apply (Nat.mul_lt_mul_left $ Nat.pow_pos $ zero_lt_succ _).mpr h'
        rw[Nat.succ_eq_add_one]
        apply Nat.mul_le_mul_right _ $ le_of_lt ih

theorem Nat.sub_add_sub {a b a' b' : Nat} (h : a ≤ b) (h' : a' ≤ b') :
    (b - a) + (b' - a') = (b + b') - (a + a') := by omega

theorem Nat.mul_finite_sum : ∀{ι : Type v} [Finite ι] {x : ι → Nat} {n : Nat},
    finite_sum (fun i => n * x i) = n * finite_sum x := by
  conv =>
    intro a b c d
    rw[finite_sum_reindex_univ]
    rw[finite_sum_reindex_univ (x := c)]
  intro α inst x n
  apply Finite.set_induction (p := fun a =>
    (finite_sum fun (i : a) => n * x i.val) = n * finite_sum fun (i : a) => x i.val)
  · simp only [Set.not_mem_empty, Subtype.forall, imp_self, implies_true, finite_sum_empty,
    Nat.mul_zero]
  · intro a b fin nmem hyp
    rw[Nat.finite_sum_remove_one ⟨a,Or.inr rfl⟩]
    let f : Function.Bijection b { a_1 // a_1 ∈ ({⟨a, Or.inr rfl⟩}ᶜ : Set (b ∪ {a} : Set α))} := by
      exists fun ⟨x,h⟩ => ⟨⟨x, Or.inl h⟩, by
        intro h'
        simp only [Set.mem_singleton_iff, Subtype.eq_iff] at h'
        rw[h'] at h
        exact nmem h⟩
      constructor
      · intro x y h
        simp only [Subtype.eq_iff] at h
        apply Subtype.eq h
      · rw[Function.surj_iff]
        rintro ⟨⟨x,(hx1|rfl)⟩,hx2⟩
        · simp only [Subtype.eq_iff, Subtype.exists, exists_prop, exists_eq_right', hx1]
        · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_true_eq_false] at hx2
    rw[Nat.finite_sum_remove_one (α := fun i : (b ∪ {a} : Set _) => x i.val) ⟨a,Or.inr rfl⟩]
    rw[Nat.mul_add]
    rw[Nat.finite_sum_reindex (f := f)]
    rw[Nat.finite_sum_reindex (f := f)]
    conv =>
      lhs
      lhs
      rhs
      simp
      change (fun i ↦ n * x i.val)
    conv =>
      rhs
      lhs
      rhs
      rhs
      simp
      change (fun i ↦ x i.val)
    rw[hyp]


theorem Nat.finite_prod_pow : ∀{ι : Type v} [Finite ι] {x : ι → Nat} {n : Nat},
    finite_prod (fun i => x i ^ n) = finite_prod x ^ n := by
  conv =>
    intro a b c d
    rw[finite_prod_reindex_univ]
    rw[finite_prod_reindex_univ (x := c)]
  intro α inst x n
  apply Finite.set_induction (p := fun a =>
    (finite_prod fun (i : a) => x i.val ^ n) = (finite_prod fun (i : a) => x i.val)^n)
  · simp only [Set.not_mem_empty, Subtype.forall, imp_self, implies_true, finite_prod_empty,
    Nat.one_pow]
  · intro a b fin nmem hyp
    rw[Nat.finite_prod_remove_one ⟨a,Or.inr rfl⟩]
    let f : Function.Bijection b { a_1 // a_1 ∈ ({⟨a, Or.inr rfl⟩}ᶜ : Set (b ∪ {a} : Set α))} := by
      exists fun ⟨x,h⟩ => ⟨⟨x, Or.inl h⟩, by
        intro h'
        simp only [Set.mem_singleton_iff, Subtype.eq_iff] at h'
        rw[h'] at h
        exact nmem h⟩
      constructor
      · intro x y h
        simp only [Subtype.eq_iff] at h
        apply Subtype.eq h
      · rw[Function.surj_iff]
        rintro ⟨⟨x,(hx1|rfl)⟩,hx2⟩
        · simp only [Subtype.eq_iff, Subtype.exists, exists_prop, exists_eq_right', hx1]
        · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_true_eq_false] at hx2
    rw[Nat.finite_prod_remove_one (α := fun i : (b ∪ {a} : Set _) => x i.val) ⟨a,Or.inr rfl⟩]
    rw[Nat.mul_pow]
    rw[Nat.finite_prod_reindex (f := f)]
    rw[Nat.finite_prod_reindex (f := f)]
    conv =>
      lhs
      lhs
      rhs
      simp
      change (fun i ↦ x i.val ^ n)
    conv =>
      rhs
      lhs
      lhs
      rhs
      simp
      change (fun i ↦ x i.val)
    rw[hyp]
