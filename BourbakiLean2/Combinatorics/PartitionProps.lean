import BourbakiLean2.Combinatorics.FunctionProps

def Combinatorics.Partitions.FittingPartition (α : Type*) [Finite α] (k) (x : Nat → Nat) :=
  {y : Set.Iio k → Set α | Set.IsPartition y ∧ ∀ i h, (Finite.ftype $ y ⟨i,h⟩).cardinality = x i}

@[simp] def Combinatorics.Partitions.FittingPartition.image_bij {α : Type} [Finite α] {k} {x : Nat → Nat}
    (h : Function.Bijection α α) (y : FittingPartition α k x) : FittingPartition α k x :=
  ⟨fun i => h '' y.val i, by
    constructor
    · apply y.2.1.image_bij h.property
    · intro i h'
      rw[FiniteType.cardinality_image_eq_inj h.2.inj, y.2.2]⟩

@[simp] theorem Combinatorics.Partitions.FittingPartition.image_bij_takes_value {α : Type} [Finite α] {k} {x : Nat → Nat}
    {h : Function.Bijection α α} {y z : FittingPartition α k x} :
    image_bij h y = z ↔ ∀ i, ∃ h' : Function.Bijection (y.val i) (z.val i), (∀ x, h' x = h x) := by
  simp only [image_bij, Subtype.eq_iff, Subtype.forall, Set.mem_Iio_iff]
  constructor
  · intro eq
    rw[funext_iff] at eq
    intro i hi
    let func := (h |_ y.val ⟨i,hi⟩).corestrict (y := z.val ⟨i,hi⟩) (by
      intro x mem
      rwa[Function.image_univ_restriction, eq ⟨i,hi⟩] at mem)
    have : func.Bijective := by
      apply (Finite.bij_iff_inj $ ?wah).mpr
      · intro ⟨a,mema⟩ ⟨b,memb⟩ eq
        simp only [Subtype.eq_iff, Function.coe_corestrict, Function.restriction, func] at eq
        congr
        apply h.2.inj _ _ eq
      · have := y.2.2 i hi
        rw[← z.2.2 i hi] at this
        simp only [FiniteType.cardinality_eq_iff, Finite.ftype] at this
        exact this
    exists ⟨func,this⟩
    intro a ha
    simp only [Function.coe_corestrict, Function.restriction, func]
  · intro invariant
    ext ⟨i,hi⟩ x
    obtain ⟨bij, hbij⟩ := invariant i hi
    constructor
    · intro ha
      simp only [Set.mem_image_iff] at ha
      obtain ⟨a,rfl,mem⟩ := ha
      rw[← hbij a mem]
      exact (bij.val ⟨a, mem⟩).property
    · intro hx
      let x' : z.val ⟨i,hi⟩ := ⟨x,hx⟩
      change x'.val ∈ _
      rw[← bij.val_inv_val (b := x')]
      rw[hbij]
      apply Set.val_mem_image_of_mem
      exact (bij.inv.1 x').property

noncomputable def Combinatorics.Partitions.FittingPartition.preimage_to_bijections {α : Type} [Finite α] {k} {x : Nat → Nat} {y z : FittingPartition α k x} :
    Function.Bijection { f : Function.Bijection α α | ∀ (i : Set.Iio k ), ∃ h' : Function.Bijection (y.val i) (z.val i), ∀ (x_2 : y.val i), (h'.val x_2).val = f x_2.val }
      ((i : Set.Iio k) → Function.Bijection (y.val i) (z.val i)) := by
  exists fun ⟨a,ha⟩ i => (ha i).choose
  constructor
  · intro ⟨a,ha⟩ ⟨b,hb⟩ eq
    dsimp only at eq
    congr
    apply Subtype.eq
    ext i
    have t2 := fun i => (ha i).choose_spec
    have t3 := fun i => (hb i).choose_spec
    conv at t2 =>
      intro a
      intro b
      rw[congrFun eq a]
    obtain ⟨j, mem⟩ := y.2.1.1.mem_exists i
    specialize t2 j ⟨i,mem⟩
    specialize t3 j ⟨i,mem⟩
    exact t2.symm.trans t3
  · rw[Function.surj_iff]
    intro f
    let fn := y.2.1.1.glue (β := fun x => α) (f := fun i j => ((f i).val j).val)
    have fnprop i a := y.2.1.glue_agrees (β := fun x => α) (f := fun i j => ((f i).val j).val) (i := i) (a := a)
    have fnbij : fn.Bijective := by
      apply (Finite.bij_iff_inj $ Equipotent.of_eq rfl).mpr
      intro a b h
      obtain ⟨i, memi⟩ := y.2.1.1.mem_exists a
      obtain ⟨j, memj⟩ := y.2.1.1.mem_exists b
      have eq1 := fnprop i _ memi
      have eq2 := fnprop j _ memj
      unfold fn at h
      rw[eq1, eq2] at h
      by_cases eq : i = j
      · rcases eq
        rw[← Subtype.eq_iff] at h
        exact Subtype.eq_iff.mp ((f i).2.inj _ _ h)
      · have := z.2.1.2 i j eq
        have mem := ((f i).val ⟨a, memi⟩).property
        have mem2 := ((f j).val ⟨b, memj⟩).property
        rw[h] at mem
        have that : _ ∈ z.val i ∩ z.val j := ⟨mem,mem2⟩
        rw[this] at that
        exact that.elim
    let fn' : Function.Bijection _ _ := ⟨fn,fnbij⟩
    have : fn' ∈ { f : Function.Bijection α α | ∀ (i : Set.Iio k ), ∃ h' : Function.Bijection (y.val i) (z.val i), ∀ (x_2 : y.val i), (h'.val x_2).val = f x_2.val } := by
      intro i
      exists f i
      intro h
      unfold fn' fn
      simp only
      rw[fnprop]
    exists ⟨fn', this⟩
    ext i
    have that := (this i).choose_spec
    simp only [Subtype.forall]
    apply Subtype.eq
    ext j
    suffices ((f i).val j).val = ((this i).choose.val j).val by
      rw[this]
      simp only [Subtype.forall]
    rw[that j]
    unfold fn' fn
    simp only
    rw[fnprop]



theorem Combinatorics.Partitions.fittingPartition_nonempty {α : Type} [Finite α] {k} {x : (i : Nat) → Nat}
    (hsum : Nat.sum_ft 0 k x = (Finite.ftype α).cardinality) : (FittingPartition α k x).Nonempty := by
  obtain ⟨f,bij⟩ := Finite.equipotent_Iio (α := α)
  let p (l : Set.Iio k) := Set.Ico (Nat.sum_ft 0 l x) (Nat.sum_ft 0 (l+1) x)
  have hp (l : Set.Iio k) : p l ⊆ Set.Iio (Finite.ftype α).cardinality := by
    unfold p
    intro i hi
    simp only [Nat.zero_le, Set.mem_Ico_iff, Set.mem_Iio_iff] at *
    rw[← hsum]
    apply lt_of_lt_le hi.2
    apply Nat.sum_ft_le_expand_right (Nat.zero_le _)
    exact l.property
  let p' l := f ⁻¹' {x : Set.Iio (Finite.ftype α).cardinality | x.val ∈ p l}
  exists p'
  constructor
  · constructor
    · ext a
      simp only [Nat.zero_le, Set.mem_Ico_iff, Set.mem_iUnion_iff,
        Set.mem_preimage_iff, Set.mem_setOf_iff, Subtype.exists, Set.mem_Iio_iff, exists_and_left,
        exists_prop, Set.mem_univ, iff_true, p', p]
      have bwah : (f a).val < Nat.sum_ft 0 k x := by rw[hsum]; exact (f a).property
      obtain ⟨i,hi1,hi2,hi3⟩ := Nat.sum_ft_find_between (Nat.zero_le k) (x := x) (l := (f a).val) bwah
      exists i
    · intro i j ne
      ext a
      simp only [Nat.zero_le, Nat.sum_ft_succ_right, Set.mem_Ico_iff, Set.mem_inter_iff,
        Set.mem_preimage_iff, Set.mem_setOf_iff, Set.not_mem_empty, iff_false, not_and, Nat.not_lt,
        and_imp, p', p]
      intro h1 h2 h3
      rcases lt_trichotomy i j with (lt|eq|lt)
      · rw[Nat.sum_ft_split (Nat.zero_le _) $ Nat.succ_le_of_lt lt] at *
        have := lt_of_le_lt h3 h2
        simp only [Nat.succ_eq_add_one, Nat.zero_le, Nat.sum_ft_succ_right] at this
        refine (not_lt_self $ lt_of_lt_le this ?wah).elim
        simp only [Nat.le_add_right]
      · exact (ne eq).elim
      · rw[← not_gt_iff_le]
        intro gt
        rw[Nat.sum_ft_split (Nat.zero_le _) $ Nat.succ_le_of_lt lt] at *
        simp only [Nat.succ_eq_add_one, Nat.zero_le, Nat.sum_ft_succ_right] at h1
        exact (not_lt_self $ lt_of_lt_le gt $ Nat.le_of_add_right_le h1).elim
  · intro i h
    unfold p'
    let f' : Function.Bijection _ _ := ⟨f,bij⟩
    change (Finite.ftype { a // a ∈ f' ⁻¹' {x | x.val ∈ p ⟨i, h⟩} }).cardinality = x i
    rw[FiniteType.cardinality_preimage_eq_bij]
    have ( l : { a // a ∈ Set.Iio k }) : (Finite.ftype (Set.Ico (Nat.sum_ft 0 l.val x) (Nat.sum_ft 0 (l.val + 1) x))).cardinality = x l.val := by
      rw[Nat.Ico_cardinality]
      simp only [Nat.zero_le, Nat.sum_ft_succ_right]
      exact Nat.add_sub_self_left (Nat.sum_ft 0 l.val x) (x l.val)
    rw[← this ⟨i,h⟩]
    simp only [FiniteType.cardinality_eq_iff, p]
    unfold Finite.ftype
    simp only
    apply Equipotent.subset_subset (s := Set.Ico (Nat.sum_ft 0 i x) (Nat.sum_ft 0 (i + 1) x))
    rw[← Finite.ftype]
    let l : Set.Iio k := ⟨i,h⟩
    change Set.Ico (Nat.sum_ft 0 l.val x) (Nat.sum_ft 0 (l.val + 1) x) ⊆ Set.Iio (Finite.ftype α).cardinality
    apply hp

instance {α : Type} {k} {x : Nat → Nat} [Finite α] : Finite (Combinatorics.Partitions.FittingPartition α k x) := by
  unfold Combinatorics.Partitions.FittingPartition
  infer_instance

theorem Combinatorics.Partitions.cardinality_partitions' {α : Type} [Finite α] {k n} {x : Nat → Nat} (hn : (Finite.ftype α).cardinality = n) (hsum : Nat.sum_ft 0 k x = n) :
    (Finite.ftype (FittingPartition α k x)).cardinality * Nat.prod_ft 0 k (fun i => (x i).factorial) = n.factorial := by
  have ⟨y,yp⟩ : (FittingPartition α k x).Nonempty := fittingPartition_nonempty $ hsum.trans hn.symm
  symm
  rw[← hn, ← Combinatorics.Bijective.cardinality_bij_self, Finite.ftype, FiniteType.cardinality,FiniteType.cardinality', Finite.ftype, FiniteType.cardinality,FiniteType.cardinality']
  rw[Nat.mul_comm, ← FiniteCardinal.to_nat_of_nat (n := Nat.prod_ft _ _ _), ← FiniteCardinal.to_nat_mul]
  congr 2
  simp only
  let func : Function.Bijection α α → { a // a ∈ FittingPartition α k x } :=
    fun f => FittingPartition.image_bij f ⟨y,yp⟩
  apply Cardinal.preimage_same_product (f := func)
  intro z
  simp only [Set.mem_preimage_iff, Set.mem_singleton_iff,
    Subtype.eq_iff, func]
  conv => lhs; rhs; rhs; intro; rw[← Subtype.eq_iff, FittingPartition.image_bij_takes_value]
  have := FittingPartition.preimage_to_bijections (y := ⟨y,yp⟩) (z := z)
  trans
  · apply Cardinal.eq_iff.mpr ⟨this⟩
  · rw[← Cardinal.prod_mk]
    unfold Nat.prod_ft Nat.finite_prod
    rw[FiniteCardinal.of_nat_to_nat]
    dsimp only
    let bij := bijection_of_eq (s := Set.Ico 0 k) (t := Set.Iio k) Nat.Ico_zero
    rw[← Cardinal.prod_reindex (f := bij)]
    congr
    ext i
    have this (i : Set.Ico 0 k) := (Bijective.cardinality_bij (α := y ⟨i.1,i.2.2⟩) (β := z.val ⟨i.1,i.2.2⟩) (by
      have hy := yp.2 _ i.property.2
      have hz := z.2.2 _ i.property.2
      unfold Finite.ftype FiniteType.cardinality FiniteType.cardinality' at hy hz
      simp only at hy hz
      rw[← FiniteCardinal.to_nat_of_nat (n := x i.val), FiniteCardinal.to_nat_bij.inj.eq_iff] at hy hz
      rw[← hz, Subtype.eq_iff] at hy
      simp only [Cardinal.eq_iff] at hy
      exact hy)).trans (c := (x i.val).factorial) (by
        congr 1
        exact yp.2 _ i.property.2)
    rw[← this i]
    unfold Finite.ftype FiniteType.cardinality FiniteType.cardinality'
    simp only [bijection_of_eq.eq_1, Function.comp_apply, FiniteCardinal.of_nat_to_nat, bij]

theorem Combinatorics.Partitions.cardinality_partitions {α : Type} [Finite α] {k} {x : Nat → Nat} (hn : (Finite.ftype α).cardinality = Nat.sum_ft 0 k x) :
    (Finite.ftype (FittingPartition α k x)).cardinality * Nat.prod_ft 0 k (fun i => (x i).factorial) = (Finite.ftype α).cardinality.factorial := cardinality_partitions' rfl hn.symm

theorem Combinatorics.Partitions.cardinality_partitions_div {α : Type} [Finite α] {k} {x : Nat → Nat} (hn : (Finite.ftype α).cardinality = Nat.sum_ft 0 k x) :
    (Finite.ftype (FittingPartition α k x)).cardinality = (Finite.ftype α).cardinality.factorial / Nat.prod_ft 0 k (fun i => (x i).factorial) := by
  rw[Nat.div_eq_of_eq_mul_left]
  · rw[Nat.pos_iff_ne_zero]
    intro h
    rw[Nat.prod_ft_zero_iff_exists_zero] at h
    obtain ⟨i,_,_,h⟩ := h
    have := Nat.factorial_pos (n := x i)
    rw[h] at this
    apply not_lt_self this
  · symm
    apply Combinatorics.Partitions.cardinality_partitions' rfl hn.symm

noncomputable def Combinatorics.Partitions.FittingPartition.val_1_eq_compl_0_of_2 {α : Type} [Finite α] {x : Set.Iio 2 → Set α} (h : Set.IsPartition x) :
    (x ⟨1, by simp only [Nat.Iio_succ, Set.mem_Iic_self]⟩) =  (x ⟨0, by simp only [Nat.Iio_succ, Set.mem_Iic_iff, Nat.zero_le]⟩) ᶜ := by
  have un : ⋃ i, x i = x ⟨0, by simp only [Nat.Iio_succ, Set.mem_Iic_iff, Nat.zero_le]⟩ ∪ x ⟨1, by simp only [Nat.Iio_succ, Set.mem_Iic_self]⟩ := by
    ext a
    simp only [Set.mem_iUnion_iff, Subtype.exists, Set.mem_union_iff]
    constructor
    · rintro ⟨i,lt, h⟩
      rw[Nat.mem_Iio_2] at lt
      rcases lt with (rfl|rfl)
      · left; assumption
      · right; assumption
    · rintro (h|h) <;> exact ⟨_,_,h⟩
  have := h.1
  rw[Set.IsCovering,un] at this
  have that := h.2 ⟨0, by simp only [Nat.Iio_succ, Set.mem_Iic_iff, Nat.zero_le]⟩ ⟨1, by simp only [Nat.Iio_succ, Set.mem_Iic_self]⟩ (by
    intro h
    simp only [Subtype.eq_iff, reduceCtorEq] at h)
  apply Set.eq_compl_of this that


noncomputable def Combinatorics.Partitions.FittingPartition.subset_as {α : Type} [Finite α] {k} :
    Function.Bijection (FittingPartition α 2 (fun i => if i = 0 then k else (Finite.ftype α).cardinality - k)) {a : Set α | (Finite.ftype a).cardinality = k} := by
  exists fun y => ⟨y.1 ⟨0, Nat.zero_lt_succ _⟩, y.2.2 _ _⟩
  constructor
  · intro x y h
    ext ⟨i,iprp⟩ : 2
    simp only [Subtype.eq_iff] at h
    rcases Nat.mem_Iio_2.mp iprp with (rfl|rfl)
    · rw[h]
    · have eq1 : x.val ⟨1, iprp⟩ = (x.val ⟨0,by simp only [Nat.Iio_succ, Set.mem_Iic_iff,
        Nat.zero_le]⟩).compl := val_1_eq_compl_0_of_2 x.2.1
      have eq2 : y.val ⟨1, iprp⟩ = (y.val ⟨0,by simp only [Nat.Iio_succ, Set.mem_Iic_iff,
        Nat.zero_le]⟩).compl := val_1_eq_compl_0_of_2 y.2.1
      rw[h] at eq1
      rw[eq1,eq2]
  · rw[Function.surj_iff]
    intro ⟨s, cards⟩
    let y : Set.Iio 2 → Set α := fun i => if i.val = 0 then s else sᶜ
    have : y ∈ FittingPartition α 2 (fun i => if i = 0 then k else (Finite.ftype α).cardinality - k) := by
      constructor
      · constructor
        · ext a
          simp only [Set.mem_iUnion_iff, Subtype.exists, Nat.Iio_succ, Set.mem_Iic_iff,
            Set.mem_univ, iff_true]
          by_cases h : a ∈ s
          · exists 0
            exists (Nat.zero_le 1)
          · exists 1
            exists (Nat.le_of_ble_eq_true rfl)
        · intro ⟨i,hi⟩ ⟨j,hj⟩ ne
          rcases Nat.mem_Iio_2.mp hi with (rfl|rfl) <;> rcases Nat.mem_Iio_2.mp hj with (rfl|rfl)
          · simp only [ne_eq, not_true_eq_false] at ne
          · simp only [↓reduceIte, Nat.add_one_ne_zero, Set.inter_with_compl, y]
          · simp only [Nat.add_one_ne_zero, ↓reduceIte, Set.inter_comm, Set.inter_with_compl, y]
          · simp only [ne_eq, not_true_eq_false] at ne
      · intro i h
        by_cases h' : i = 0
        · simp only [h', ↓reduceIte, y]
          exact cards
        · simp only [h', ↓reduceIte, y]
          rw[FiniteType.cardinality_compl, cards]
    exists ⟨_,this⟩

theorem Combinatorics.cardinality_subset_of_size {α : Type} [Finite α] {k : Nat} : (Finite.ftype {s : Set α | (Finite.ftype s).cardinality = k}).cardinality = Nat.binom (Finite.ftype α).cardinality k := by
  have : (Finite.ftype {s : Set α | (Finite.ftype s).cardinality = k}).cardinality = (Finite.ftype (Partitions.FittingPartition α 2 (fun i => if i = 0 then k else (Finite.ftype α).cardinality - k))).cardinality := by
    symm
    simp only [Set.mem_setOf_iff, FiniteType.cardinality_eq_iff]
    constructor
    exact Partitions.FittingPartition.subset_as
  rw[this]
  by_cases h : k ≤ (Finite.ftype α).cardinality
  · rw[Partitions.cardinality_partitions_div]
    · rw[Nat.binom_of_le h]
      simp only [Nat.zero_le, Nat.prod_ft_succ_right, le_rfl, Nat.prod_ft_ge, ↓reduceIte, Nat.one_mul,
        Nat.add_one_ne_zero]
    · simp only [Nat.zero_le, Nat.sum_ft_succ_right, le_rfl, Nat.sum_ft_ge, ↓reduceIte,
        Nat.zero_add, Nat.add_one_ne_zero]
      exact Eq.symm (Nat.add_sub_of_le h)
  · trans 0
    · simp only [FiniteType.cardinality_set_zero_iff]
      ext a
      simp only [Set.not_mem_empty, iff_false]
      intro h'
      replace h' := h'.2 0 (by simp only [Nat.Iio_succ, Set.mem_Iic_iff, Nat.zero_le])
      simp only [↓reduceIte] at h'
      have : (Finite.ftype { a_1 // a_1 ∈ a ⟨0, by simp only [Nat.Iio_succ, Set.mem_Iic_iff,
        Nat.zero_le]⟩ }).cardinality ≤ (Finite.ftype α).cardinality := by simp only [FiniteType.cardinality_set_le]
      rw[h'] at this
      exact h this
    · rw[Nat.binom_zero_of_gt]
      rwa[not_ge_iff_lt] at h

theorem Combinatorics.cardinality_strict_mono_of_size {α β : Type} [Finite α] [Finite β] [TotalOrder α] [TotalOrder β]:
    (Finite.ftype {f : α → β | StrictMonotone f}).cardinality = Nat.binom (Finite.ftype β).cardinality (Finite.ftype α).cardinality := by
  by_cases le : (Finite.ftype α).cardinality ≤ (Finite.ftype β).cardinality
  · rw[← Combinatorics.cardinality_subset_of_size]
    simp only [Set.mem_setOf_iff]
    apply FiniteType.cardinality_eq_iff.mpr
    constructor
    exists fun f => ⟨f.1 '' Set.univ, by rw[FiniteType.cardinality_image_eq_inj, FiniteType.cardinality_univ]; apply TotalOrder.inj_of_strictMono f.2⟩
    constructor
    · intro ⟨f,hf⟩ ⟨g,hg⟩ eq
      rw[Subtype.eq_iff] at eq
      simp only [StrictMonotone.eq_1] at eq
      have f1 := TotalOrder.corestrict_strictMono_iso' hf eq
      have g1 := TotalOrder.corestrict_strictMono_iso hg
      have := WellOrder.iso_all_eq f1 g1
      rw[Function.corestrict_eq_iff] at this
      apply Subtype.eq this
    · rw[Function.surj_iff]
      intro ⟨a,ha⟩
      let x' := Subtype.val ∘ TotalOrder.enumerate (α := α)
      have hx' a : x' a ∈ Set.Iio _ := Subtype.property $ TotalOrder.enumerate (α := α) a
      rw[← ha] at hx'
      let x := Subtype.val ∘ TotalOrder.nth (α := a) ∘ fun i => ⟨x' i, hx' i⟩
      have : StrictMonotone x := by
        intro a b h
        simp only [Function.comp_assoc, Function.comp_apply, x, x']
        rw[← Subtype.lt_iff_val]
        apply TotalOrder.nth_isOrderIso.strictMonotone
        simp only [Subtype.lt_iff_val]
        rw[← Subtype.lt_iff_val]
        apply TotalOrder.enumerate_isOrderIso.strictMonotone h
      exists ⟨x,this⟩
      simp only
      congr
      ext i
      unfold x x'
      constructor
      · intro hi
        simp only [Function.comp_apply, Function.comp_assoc, Function.image_comp, Set.mem_image_iff,
          Subtype.eq_iff, Set.mem_univ, and_true, Subtype.exists, Set.mem_Iio_iff, exists_and_right,
          exists_and_left, exists_prop, exists_eq_left']
        exists i
        constructor
        · exact ⟨hi,rfl⟩
        · exists (TotalOrder.enumerate (α := a) ⟨i,hi⟩)
          constructor
          · exists (TotalOrder.enumerate (α := a) ⟨i,hi⟩).property
            change (⟨i,hi⟩ : a).val  = _
            apply Subtype.eq_iff.mp
            change _ = TotalOrder.nth (TotalOrder.enumerate ⟨i, hi⟩)
            simp only [TotalOrder.nth_enumerate]
          · obtain ⟨a',h1',h2'⟩ : ∃ a' : α, ∃ h : (TotalOrder.enumerate a').val ∈ (Set.Iio (Finite.ftype { a_3 // a_3 ∈ a }).cardinality),
                (TotalOrder.enumerate ⟨i,hi⟩) = (⟨(TotalOrder.enumerate a').val,h⟩ : Set.Iio _) := by
              let x := TotalOrder.enumerate (⟨i, hi⟩ : a)
              let x' : Set.Iio (Finite.ftype α).cardinality := ⟨x.val, by rw[← ha]; exact x.property⟩
              obtain ⟨b,eq⟩ := TotalOrder.enumerate_isOrderIso.bij.surj.exists_preimage x'
              exists b
              have : (TotalOrder.enumerate b).val ∈ Set.Iio (Finite.ftype { a_3 // a_3 ∈ a }).cardinality := by
                rw[← eq, ha]
                exact x'.property
              exists this
              apply Subtype.eq
              simp only
              rw[← eq]
            exists a'
            apply Subtype.eq_iff.mp h2'
      · intro hi
        simp only [Function.comp_apply, Function.comp_assoc, Function.image_comp, Set.mem_image_iff,
          Subtype.eq_iff, Set.mem_univ, and_true, Subtype.exists, Set.mem_Iio_iff, exists_and_right,
          exists_and_left, exists_prop, exists_eq_left'] at hi
        obtain ⟨a,⟨mem,eq⟩,_⟩ := hi
        rwa[eq]
  · trans 0
    · have : {a : α → β| StrictMonotone a} = ∅ := by
        simp only [FiniteType.cardinality_le_ftype_iff] at le
        ext f
        simp only [Set.mem_setOf_iff, Set.not_mem_empty, iff_false,
          Classical.not_forall, not_imp]
        intro hf
        exact le ⟨_,TotalOrder.inj_of_strictMono hf⟩
      rw[this, FiniteType.cardinality_empty_set]
    · rw[not_ge_iff_lt] at le
      simp only [le, Nat.binom_zero_of_gt]
