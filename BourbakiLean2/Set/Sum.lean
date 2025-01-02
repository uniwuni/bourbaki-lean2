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

namespace Set.IsPartition
noncomputable def sigma_assoc {p : ι' → Set ι} (h : IsPartition p) : Function.Bijection ((i : ι) × x i) ((i' : ι') × ((i : p i') × x i)) :=
  Function.bijection_of_funcs
    (fun ⟨i,x⟩ => ⟨Classical.choose (h.1.mem_exists i),
      ⟨⟨i,Classical.choose_spec (h.1.mem_exists i)⟩, x⟩⟩)
    (fun ⟨i',i,x⟩ => ⟨_,x⟩)
    (by rintro ⟨a,⟨b,h'⟩,c⟩
        simp only [IsCovering.eq_1, Disjoint.eq_1, ne_eq]
        have := h.eq_of_mem (Classical.choose_spec (h.1.mem_exists b)) h'
        rcases this
        simp only [IsCovering.eq_1, Disjoint.eq_1, ne_eq])
    (by rintro ⟨i,x⟩
        simp only [IsCovering.eq_1, Disjoint.eq_1, ne_eq])


end Set.IsPartition

def Sigma.prod_distrib {ι' : ι → Type*} {x : (i : ι) → ι' i → Type*} :
    Function.Bijection ((i : ι) → (i' : ι' i) × x i i') ((y : (i : ι) → ι' i) × ((i : ι) → x i (y i))) :=
  Function.bijection_of_funcs (fun f => ⟨fun i => (f i).1,fun i => (f i).2⟩)
  (fun ⟨y,f⟩ i => ⟨y i, f i⟩)
  (by rintro f; simp only [Sigma.eta])
  (by rintro f; simp only [Sigma.eta])
