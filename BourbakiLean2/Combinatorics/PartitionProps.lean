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
