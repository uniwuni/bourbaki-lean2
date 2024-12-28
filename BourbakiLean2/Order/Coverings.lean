import BourbakiLean2.Order.Directed
import BourbakiLean2.Order.TotalOrder
import BourbakiLean2.Set.Partitions

variable {α β : Type*} {ι ι' ι'' : Type*} {a : α} {i : ι} {x : ι → Set α} {x' : ι' → Set α} {x'' : ι'' → Set α} {f f' : α → β} {y : ι → Set β}
namespace Set
noncomputable def IsCovering.glue_rel (h : IsCovering x)
  (f : (i : ι) → Relation (x i) (x i)) : Relation α α :=
  {pair | ∃ i, ∃ a b : x i, (a,b) ∈ f i ∧ pair.1 = a ∧ pair.2 = b}

@[simp] theorem IsCovering.glue_rel_agrees [RightDirected (x '' Set.univ)]
    (h : IsCovering x) {f : (i : ι) → Relation (x i) (x i)}
    (h' : ∀ i j, (sub : x i ⊆ x j) → ∀ a b, (ha : a ∈ x i) → (hb : b ∈ x i) →
      (⟨a,ha⟩,⟨b,hb⟩) ∈ f i ↔ (⟨a, sub ha⟩,⟨b, sub hb⟩) ∈ f j) (a b : α)
    (ha : a ∈ x i) (hb : b ∈ x i)
    : (a,b) ∈ h.glue_rel f ↔ (⟨a,ha⟩,⟨b,hb⟩) ∈ f i := by
  simp only [glue_rel, Subtype.exists, exists_and_right, exists_eq_right_right', exists_eq_right',
    mem_setOf_iff]
  constructor
  · rintro ⟨j,ha',hb',hf⟩
    obtain ⟨⟨s,mem⟩,ik,jk⟩ := RightDirected.exists_ub (α := { a // a ∈ x '' univ }) ⟨x i, by simp⟩ ⟨x j, by simp⟩
    rw[mem_image_iff] at mem
    obtain ⟨k,rfl,_⟩ := mem
    have axk : a ∈ x k := ik ha
    have bxk : b ∈ x k := ik hb
    rw[h' i k ik a b ha hb,
      ←h' j k jk a b ha' hb']
    exact hf
  · intro h
    exists i
    exists ha
    exists hb

instance isPreorderColimit [RightDirected (x '' Set.univ)]
    (h : IsCovering x) {f : (i : ι) → Relation (x i) (x i)} [∀ i, IsPreorder $ f i]
    (h' : ∀ i j, (sub : x i ⊆ x j) → ∀ a b, (ha : a ∈ x i) → (hb : b ∈ x i) →
      (⟨a,ha⟩,⟨b,hb⟩) ∈ f i ↔ (⟨a, sub ha⟩,⟨b, sub hb⟩) ∈ f j) : IsPreorder (h.glue_rel f) where
  le_refl a := by
    obtain ⟨i,mem⟩ := h.mem_exists a
    rw[h.glue_rel_agrees h' a a mem mem]
    apply IsPreorder.le_refl
  le_trans a b c := by
    obtain ⟨i,mema⟩ := h.mem_exists a
    obtain ⟨j,memb⟩ := h.mem_exists b
    obtain ⟨k,memc⟩ := h.mem_exists c
    obtain ⟨⟨s,mem⟩,il,jl⟩ := RightDirected.exists_ub (α := { a // a ∈ x '' univ }) ⟨x i, by simp⟩ ⟨x j, by simp⟩
    rw[mem_image_iff] at mem
    obtain ⟨l,rfl,_⟩ := mem
    obtain ⟨⟨s,mem⟩,km,lm⟩ := RightDirected.exists_ub (α := { a // a ∈ x '' univ }) ⟨x k, by simp⟩ ⟨x l, by simp⟩
    rw[mem_image_iff] at mem
    obtain ⟨m,rfl,_⟩ := mem
    have ak := lm $ il mema
    have bk := lm $ jl memb
    have ck := km $ memc
    rw[h.glue_rel_agrees h' a b ak bk,
       h.glue_rel_agrees h' a c ak ck,
       h.glue_rel_agrees h' b c bk ck]
    apply IsPreorder.le_trans

instance isPartialOrderColimit [RightDirected (x '' Set.univ)]
    (h : IsCovering x) {f : (i : ι) → Relation (x i) (x i)} [∀ i, IsPartialOrder $ f i]
    (h' : ∀ i j, (sub : x i ⊆ x j) → ∀ a b, (ha : a ∈ x i) → (hb : b ∈ x i) →
      (⟨a,ha⟩,⟨b,hb⟩) ∈ f i ↔ (⟨a, sub ha⟩,⟨b, sub hb⟩) ∈ f j) : IsPartialOrder (h.glue_rel f) where
  le_refl := (isPreorderColimit h h').le_refl
  le_antisymm a b := by
    obtain ⟨i,mema⟩ := h.mem_exists a
    obtain ⟨j,memb⟩ := h.mem_exists b
    obtain ⟨⟨s,mem⟩,il,jl⟩ := RightDirected.exists_ub (α := { a // a ∈ x '' univ }) ⟨x i, by simp⟩ ⟨x j, by simp⟩
    rw[mem_image_iff] at mem
    obtain ⟨l,rfl,_⟩ := mem
    have ak := il mema
    have bk := jl memb
    rw[h.glue_rel_agrees h' a b ak bk,
       h.glue_rel_agrees h' b a bk ak]
    intro ha hb
    exact Subtype.eq_iff.mp $ IsPartialOrder.le_antisymm _ _ ha hb
  le_trans := (isPreorderColimit h h').le_trans

instance isTotalOrderColimit [RightDirected (x '' Set.univ)]
    (h : IsCovering x) {f : (i : ι) → Relation (x i) (x i)} [inst: ∀ i, IsTotalOrder $ f i]
    (h' : ∀ i j, (sub : x i ⊆ x j) → ∀ a b, (ha : a ∈ x i) → (hb : b ∈ x i) →
      (⟨a,ha⟩,⟨b,hb⟩) ∈ f i ↔ (⟨a, sub ha⟩,⟨b, sub hb⟩) ∈ f j) : IsTotalOrder (h.glue_rel f) where
  le_trans := (isPreorderColimit h h').le_trans
  le_refl := (isPreorderColimit h h').le_refl
  le_antisymm := (isPartialOrderColimit h h').le_antisymm
  le_total a b := by
    obtain ⟨i,mema⟩ := h.mem_exists a
    obtain ⟨j,memb⟩ := h.mem_exists b
    obtain ⟨⟨s,mem⟩,il,jl⟩ := RightDirected.exists_ub (α := { a // a ∈ x '' univ }) ⟨x i, by simp⟩ ⟨x j, by simp⟩
    rw[mem_image_iff] at mem
    obtain ⟨l,rfl,_⟩ := mem
    have ak := il mema
    have bk := jl memb
    rw[h.glue_rel_agrees h' a b ak bk,
       h.glue_rel_agrees h' b a bk ak]
    exact (inst l).le_total ⟨a,ak⟩ ⟨b,bk⟩



end Set
