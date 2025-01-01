import BourbakiLean2.Set.Partitions
variable {α β : Type*} {ι ι' ι'' : Type*} {a : α} {i j : ι} {x : ι → Set α} {x' : ι' → Set α} {x'' : ι'' → Set α} {f f' : α → β} {y : ι → Set β}
universe u
namespace Set

@[simp]  def sum_to_union : Sigma (fun i => x i) → ⋃ i, x i
| ⟨i,⟨a,h⟩⟩ => ⟨a,⟨i,h⟩⟩

@[simp] theorem sum_to_union_surj : (sum_to_union (x := x)).Surjective := by
  rw[Function.surj_iff]
  rintro ⟨a, ⟨i,h⟩⟩
  exists ⟨i, ⟨a,h⟩⟩

theorem sum_to_union_inj_of_disjoint (h : ∀ i j, i ≠ j → x i ∩ x j = ∅) : (sum_to_union (x := x)).Injective := by
  rintro ⟨i,⟨a,h'⟩⟩ ⟨j,⟨a',h''⟩⟩ h'''
  simp only [sum_to_union, Subtype.eq_iff] at h'''
  rw[h'''] at h'
  have h := eq_of_mem_disjoint h h' h''
  congr
  · ext
    rw[h]
  · simp only [heq_eq_eq, h, h''', h'']

theorem sum_to_union_bij_of_disjoint (h : ∀ i j, i ≠ j → x i ∩ x j = ∅) : (sum_to_union (x := x)).Bijective :=
  ⟨sum_to_union_inj_of_disjoint h, sum_to_union_surj⟩

end Set
variable {α β : Type*} {ι ι' ι'' : Type*} {a : α} {i j : ι} {x : ι → Type*}

def sigma_reindex_bij {x : ι → Type u} (f : Function.Bijection ι' ι) : Function.Bijection (Sigma (x ∘ f)) (Sigma x) :=
  ⟨fun ⟨i',h⟩ => ⟨f i', h⟩, by
    constructor
    · intro ⟨i,a⟩ ⟨j,b⟩ h
      simp only at h
      injection h with h' h''
      rcases f.2.inj _ _ h'
      rcases h''
      rfl
    · rw[Function.surj_iff]
      rintro ⟨i,a⟩
      have : f.val (f.inv.val i) = i := f.val_inv_val
      exists ⟨f.inv i, (congrArg x this).mpr a⟩
      congr
      · exact this.symm
      · generalize congrArg x this = e
        apply heq_mpr⟩
