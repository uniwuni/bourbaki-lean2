import BourbakiLean2.Function.Basic

namespace Relation
variable {α β γ δ : Type*} {f : α → β} {g : γ → α}
variable {r r' : Relation α β}

def proj1 (r : Relation α β) : ↑ r → ↑ r.domain
| ⟨⟨a,_⟩,h⟩ => ⟨a, mem_domain_of h⟩

def proj2 (r : Relation α β) : ↑ r → ↑ r.range
| ⟨⟨_,b⟩,h⟩ => ⟨b, mem_range_of h⟩

@[simp] theorem proj1_val {a : _} : proj1 r a = ((↑ a) : α × β).1 := by
  dsimp only [proj1]

@[simp] theorem proj2_val {a : _} : proj2 r a = ((↑ a) : α × β).2 := by
  dsimp only [proj2]

@[simp] theorem proj1_val' {a b h : _} : proj1 r ⟨⟨a,b⟩,h⟩ = a := by
  dsimp only [proj1_val]

@[simp] theorem proj2_val' {a b h : _} : proj2 r ⟨⟨a,b⟩,h⟩ = b := by
  dsimp only [proj2_val]

theorem proj1_surj : Function.Surjective (proj1 r) := by
  simp only [Function.surj_iff, Subtype.exists, Prod.exists, Subtype.forall, mem_domain_iff,
    forall_exists_index]
  intro a b h
  exists a
  exists b
  exists h

theorem proj2_surj : Function.Surjective (proj2 r) := by
  simp only [Function.surj_iff, Subtype.exists, Prod.exists, Subtype.forall, mem_range_iff,
    forall_exists_index]
  intro a b h
  exists b
  exists a
  exists h


def proj1_inj_domain_iff_functional : (Function.Injective (proj1 r) ∧ r.domain = Set.univ) ↔ r.Functional := by
  constructor
  · rintro ⟨h,h'⟩ a
    rw[Set.ext_iff] at h'
    specialize h' a
    simp only [mem_domain_iff, Set.mem_univ, iff_true] at h'
    obtain ⟨b, h''⟩ := h'
    exists b
    simp only [h'', true_and]
    intro b' h'''
    specialize h ⟨(a,b),h''⟩ ⟨(a,b'),h'''⟩
    simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and] at h
    apply Eq.symm ∘ h
    simp only [Subtype.eq_iff, proj1_val]
  · intro h
    constructor
    · rintro ⟨⟨a,b⟩, h'⟩ ⟨⟨a',b'⟩,h''⟩ h'''
      simp only [Subtype.eq_iff, proj1_val] at *
      simp only [h''', Prod.mk.injEq, true_and] at *
      specialize h a'
      obtain ⟨_,⟨_,h⟩⟩ := h
      have hb := h b h'
      have hb' := h b' h''
      rw[hb, hb']
    · exact domain_functional h

end Relation
