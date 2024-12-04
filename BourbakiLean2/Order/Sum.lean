import BourbakiLean2.Order.Monotone
import BourbakiLean2.Order.Quotient
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
