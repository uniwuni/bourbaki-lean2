import BourbakiLean2.Order.Monotone
import BourbakiLean2.Order.Quotient
import BourbakiLean2.Order.Directed
variable {ι : Type*} {x : ι → Type*}

instance [PartialOrder ι] [∀ i, Preorder (x i)] : Preorder (Sigma x) where
  le := fun ⟨i,a⟩ ⟨j,b⟩ => i < j ∨ (∃ (h : i = j), h ▸ a ≤ b)
  le_refl a := Or.inr ⟨rfl,le_rfl⟩
  le_trans := fun ⟨i,a⟩ ⟨j,b⟩ ⟨k,c⟩ h h' => by
    rcases h with (h|⟨rfl,h⟩)
    · rcases h' with (h'|⟨rfl, h'⟩)
      · exact Or.inl $ lt_of_lt_lt h h'
      · exact Or.inl h
    · rcases h' with (h'|⟨rfl, h'⟩)
      · exact Or.inl h'
      · exact Or.inr  ⟨rfl, le_trans h h'⟩

instance [PartialOrder ι] [∀ i, PartialOrder (x i)] : PartialOrder (Sigma x) where
  le_antisymm := fun ⟨i,a⟩ ⟨j,b⟩ h h' => by
    rcases h with (h|⟨rfl,h⟩)
    · rcases h' with (h'|⟨rfl,h'⟩)
      · apply (not_lt_self $ lt_of_lt_lt h h').elim
      · apply (not_lt_self h).elim
    · rcases h' with (h'|⟨eq,h'⟩)
      · apply (not_lt_self h').elim
      · rcases eq
        congr
        apply le_antisymm h h'

theorem le_of_index_lt {i j : ι} {a : x i} {b : x j} [PartialOrder ι] [∀ i, Preorder (x i)] (h : i < j) : (⟨i,a⟩ : Sigma x) ≤ ⟨j,b⟩ := by
  exact Or.inl h

theorem lt_of_index_lt {i j : ι} {a : x i} {b : x j} [PartialOrder ι] [∀ i, Preorder (x i)] (h : i < j) : (⟨i,a⟩ : Sigma x) < ⟨j,b⟩ := by
  rw[lt_iff_le_not_le]
  constructor
  · apply le_of_index_lt h
  · rintro (h'|⟨rfl,h'⟩)
    · apply not_lt_self $ lt_of_lt_lt h h'
    · apply not_lt_self h

theorem index_le_of_le {i j : ι} {a : x i} {b : x j} [PartialOrder ι] [∀ i, Preorder (x i)] (h : (⟨i,a⟩ : Sigma x) ≤ ⟨j,b⟩) : i ≤ j := by
  rcases h with (h|⟨rfl,_⟩)
  · apply le_of_lt h
  · apply le_rfl

@[simp] theorem le_same_index_iff {i : ι} {a b : x i} [PartialOrder ι] [∀ i, Preorder (x i)] : (⟨i,a⟩ : Sigma x) ≤ ⟨i,b⟩ ↔ a ≤ b := by
  constructor
  · rintro (h|⟨path,h⟩)
    · apply (not_lt_self h).elim
    · simp only at h
      exact h
  · intro h
    right
    exists rfl

@[simp] theorem lt_same_index_iff {i : ι} {a b : x i} [PartialOrder ι] [∀ i, Preorder (x i)] : (⟨i,a⟩ : Sigma x) < ⟨i,b⟩ ↔ a < b := by
  rw[lt_iff_le_not_le, lt_iff_le_not_le]
  simp only [le_same_index_iff]

theorem sigma_order_quotient_iso_index [PartialOrder ι] [∀ i, Preorder (x i)] [ne : ∀ i, Nonempty (x i)] :
    IsOrderIso (fun (i : ι) =>
      Quot.mk (Function.curry $ Function.identified_under (fun a : Sigma x => (a.1 : ι))) ⟨i,Classical.choice $ ne i⟩) := by
  have : Function.Bijective fun i ↦ Quot.mk (Function.curry (Function.identified_under fun a : Sigma x↦ a.fst)) ⟨i, Classical.choice $ ne i⟩ := by
    constructor
    · intro i j h
      rwa[Quot.mk_eq_iff_rel, Function.mem_identified_under] at *
    · rw[Function.surj_iff]
      rintro ⟨⟨b,x⟩⟩
      exists b
      simp only [Quot.mk_eq_iff_rel, Function.mem_identified_under]
  constructor
  · intro i j h
    have : (⟨i,Classical.choice $ ne i⟩ : Sigma x) ≤ ⟨j,Classical.choice $ ne j⟩ := by
      by_cases h' : i = j
      · rw[h']
      · exact Or.inl $ lt_of_le_not_le h (fun a => h' $ le_antisymm h a)

    apply Quot.mk_monotone_iff.mpr _ this
    · rintro ⟨i, a⟩ ⟨i',a'⟩ ⟨j,b⟩ le eq
      simp only [Quot.mk_eq_iff_rel, Function.mem_identified_under] at *
      rcases le with (lt|⟨rfl,path⟩)
      · exists ⟨j,b⟩
        apply And.intro rfl $ Or.inl $ eq ▸ lt
      · exists ⟨i',a'⟩
  swap
  · exact this
  · rintro ⟨⟨i,a⟩⟩ ⟨⟨j,b⟩⟩ le
    have eq1 : Quot.mk (Function.curry (Function.identified_under fun a : Sigma x ↦ a.fst)) ⟨i, a⟩ = Quot.mk (Function.curry (Function.identified_under fun a ↦ a.fst)) ⟨i, Classical.choice $ ne i⟩ := by
      simp only [Quot.mk_eq_iff_rel, Function.mem_identified_under]
    have eq2 : Quot.mk (Function.curry (Function.identified_under fun a : Sigma x ↦ a.fst)) ⟨j, b⟩ = Quot.mk (Function.curry (Function.identified_under fun a ↦ a.fst)) ⟨j, Classical.choice $ ne j⟩ := by
      simp only [Quot.mk_eq_iff_rel, Function.mem_identified_under]

    simp[eq1,eq2,this.inv_val_val] at le |-
    obtain ⟨⟨i',a'⟩,eq,le2⟩ := le ⟨i, Classical.choice $ ne i⟩ rfl
    simp only [Quot.mk_eq_iff_rel, Function.mem_identified_under] at eq
    obtain rfl := eq
    rcases le2 with (lt|⟨rfl,_⟩)
    · apply le_of_lt lt
    · exact le_rfl

theorem sum_order_assoc {ι : Type*} {ι' : ι → Type*} {x : (i : ι) → ι' i → Type*}
  [PartialOrder ι] [∀ i, PartialOrder $ ι' i] [∀ i i', Preorder $ x i i'] :
    IsOrderIso (fun (⟨⟨i,i'⟩,a⟩ : Sigma (α := Sigma ι') fun ⟨_j,_j'⟩ => x _j _j') =>
      (⟨i, ⟨i', a⟩⟩ : Sigma fun i => Sigma (x i))) := by
  rw[isOrderIso_iff_reflect]
  constructor
  · constructor
    · rintro ⟨⟨i,i'⟩,a⟩ ⟨⟨i1,i'1⟩,a1⟩ h
      rcases h
      simp only at *
    · rw[Function.surj_iff]
      rintro ⟨i, ⟨i',a⟩⟩
      exists ⟨⟨i,i'⟩,a⟩
  · constructor
    · rintro ⟨⟨i,i'⟩,a⟩ ⟨⟨i1,i'1⟩,a1⟩ (h|⟨eq,h⟩)
      · rw[lt_iff_le_not_eq] at h
        rcases h with ⟨(h|⟨rfl,h⟩) ,h'⟩
        · apply le_of_index_lt h
        · replace h' : i' ≠ i'1 := fun a => h' $ congrArg _ a
          simp only at h
          simp only [le_same_index_iff, ge_iff_le]
          apply le_of_index_lt
          exact lt_iff_le_not_eq.mpr ⟨h, h'⟩
      · have eq1 : i = i1 := congrArg (fun x => x.1) eq
        rcases eq1
        rcases eq
        simp only [le_same_index_iff, h]
    · rintro ⟨⟨i,i'⟩,a⟩ ⟨⟨i1,i'1⟩,a1⟩ (h|⟨rfl,(lt|⟨rfl,h⟩)⟩)
      · apply le_of_index_lt $ lt_of_index_lt h
      · apply le_of_index_lt
        rwa[lt_same_index_iff]
      · simpa only [le_same_index_iff, ge_iff_le]

theorem sum_rightDirected_iff [PartialOrder ι] [∀ i, Preorder (x i)] [ne : ∀ i, Nonempty (x i)]:
    RightDirected (Sigma x) ↔ (RightDirected ι ∧ ∀ i, Maximal i → RightDirected (x i)) := by
  constructor
  · intro h
    constructor
    · constructor
      · intro i i'
        exists (RightDirected.ub (α := Sigma x) ⟨i, Classical.choice $ ne i⟩ ⟨i', Classical.choice $ ne i'⟩).1
        constructor
        · apply index_le_of_le (a := Classical.choice $ ne i) (b := (RightDirected.ub (α := Sigma x) ⟨i, Classical.choice $ ne i⟩ ⟨i', Classical.choice $ ne i'⟩).2)
          simp only [Sigma.eta, RightDirected.le_ub_left]
        · apply index_le_of_le (a := Classical.choice $ ne i') (b := (RightDirected.ub (α := Sigma x) ⟨i, Classical.choice $ ne i⟩ ⟨i', Classical.choice $ ne i'⟩).2)
          simp only [Sigma.eta, RightDirected.le_ub_right]
    · rintro i max
      constructor
      intro a b
      obtain ⟨⟨j,a'⟩,le1,le2⟩ := h.1 ⟨i,a⟩ ⟨i,b⟩
      obtain rfl := max _ $ index_le_of_le le1
      exists a'
      rw[le_same_index_iff] at le1 le2
      exact ⟨le1,le2⟩
  · intro ⟨h,h'⟩
    constructor
    rintro ⟨i,a⟩ ⟨j,b⟩
    by_cases h'' : Maximal i
    · obtain ⟨k,le1,le2⟩ := h.1 i j
      obtain rfl := h'' _ le1
      by_cases eq : j = k
      · rcases eq
        obtain ⟨c,l1,l2⟩ := (h' _ h'').1 a b
        exists ⟨j,c⟩
        simp only [ge_iff_le, le_same_index_iff, and_self, l1, l2]
      · have : j < k := lt_iff_le_not_eq.mpr ⟨le2, eq⟩
        exists ⟨k,a⟩
        exact ⟨le_rfl, le_of_index_lt this⟩
    · obtain ⟨k,lt⟩ := exists_lt_of_not_maximal h''
      obtain ⟨m,le1,le2⟩ := h.1 k j
      by_cases eq : j = m
      · rcases eq
        exists ⟨j,b⟩
        simp only [ge_iff_le, le_rfl, and_true]
        exact le_of_index_lt $ lt_of_lt_le lt le1
      · have := lt_iff_le_not_eq.mpr ⟨le2,eq⟩
        exists ⟨m, Classical.choice $ ne m⟩
        exact ⟨le_of_index_lt $ lt_of_lt_le lt le1,
               le_of_index_lt this⟩
