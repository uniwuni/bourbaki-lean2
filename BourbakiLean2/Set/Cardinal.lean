import BourbakiLean2.Order.WellOrderIso
universe u

def Equipotent (α β : Type u) := Nonempty (Function.Bijection α β)
def equipotent_rel : Relation (Type u) (Type u) := fun ⟨α,β⟩ => Nonempty (Function.Bijection α β)
@[simp] theorem mem_equipotent_rel_iff {α β : Type u} : ⟨α,β⟩ ∈ equipotent_rel ↔ Equipotent α β := Iff.rfl
instance : Equivalence @Equipotent.{u} where
  refl _ := ⟨⟨_,Function.bij_id⟩⟩
  symm := fun ⟨h⟩ => ⟨h.inv⟩
  trans := fun ⟨h⟩ ⟨h'⟩ => ⟨_, h'.property.comp h.property⟩

instance equipotent_equiv : equipotent_rel.IsEquivalence := by
  unfold Relation.IsEquivalence equipotent_rel
  infer_instance

def Cardinal : Type (u+1) := Quot Equipotent
def Cardinal.mk : Type* → Cardinal := Quot.mk Equipotent
theorem Cardinal.alt : @Cardinal.{u} = Quot (Function.curry equipotent_rel) := rfl
theorem Cardinal.mk_alt {α : Type u} : Cardinal.mk α = Quot.mk (Function.curry equipotent_rel) α := rfl
@[simp] theorem Cardinal.eq_iff {α β : Type u} : Cardinal.mk α = Cardinal.mk β ↔ Equipotent α β := by
  rw[Cardinal.mk_alt, Cardinal.mk_alt, Quot.mk_eq_iff_rel]
  exact mem_equipotent_rel_iff

instance : Zero @Cardinal.{u} := ⟨Cardinal.mk PEmpty⟩
instance : One @Cardinal.{u} := ⟨Cardinal.mk PUnit⟩

theorem Cardinal.zero_eq : (0 : @Cardinal.{u}) = Cardinal.mk PEmpty := rfl
theorem Cardinal.one_eq : (1 : @Cardinal.{u}) = Cardinal.mk PUnit := rfl
@[simp] theorem Cardinal.eq_zero_iff {α : Type u} : Cardinal.mk α = 0 ↔ (α → False) := by
  simp only [zero_eq, eq_iff, Function.prod_nonempty_iff, not_nonempty_empty]
  constructor
  · rintro ⟨h⟩
    exact fun x => (h.1 x).elim
  · intro h
    exists (fun x => (h x).elim)
    constructor
    · intro x
      exact (h x).elim
    · rw[Function.surj_iff]
      rintro ⟨⟩

@[simp] theorem Cardinal.eq_one_iff {α : Type u} : Cardinal.mk α = 1 ↔ Nonempty (Unique α) := by
  simp only [one_eq, eq_iff]
  constructor
  · rintro ⟨h⟩
    have a : α := h.2.inv PUnit.unit
    constructor
    constructor
    swap
    · exact ⟨a⟩
    · intro x
      change x = a
      rw[← h.inv_val_val (a := x), ← h.inv_val_val (a := a)]
  · intro ⟨⟨a⟩, h⟩
    exists fun x => PUnit.unit
    constructor
    · intro x y _
      rw[h x, h y]
    · rw[Function.surj_iff]
      intro x
      exists a

@[simp] theorem Cardinal.zero_neq_one : (0 : @Cardinal.{u}) ≠ 1 :=
  fun h => (Cardinal.eq_zero_iff (α := PUnit)).mp h.symm PUnit.unit


theorem Cardinal.le_equipotent_invariant1 {x x' y y' : Type u} (hx : Equipotent x x') (hy : Equipotent y y')
    (h : Nonempty (Function.Injection x y)) : Nonempty (Function.Injection x' y') := by
  rcases h with ⟨h⟩
  rcases hx with ⟨hx⟩
  rcases hy with ⟨hy⟩
  constructor
  exact ⟨_,hy.2.inj.comp $ h.2.comp hx.2.inv_bij.inj⟩

theorem Cardinal.le_equipotent_invariant {x x' y y' : Type u} (hx : Equipotent x x') (hy : Equipotent y y') :
    Nonempty (Function.Injection x y) = Nonempty (Function.Injection x' y') := by
  simp only [eq_iff_iff]
  constructor
  · exact Cardinal.le_equipotent_invariant1 hx hy
  · have :  Equivalence Equipotent := by infer_instance
    exact Cardinal.le_equipotent_invariant1 (Equivalence.symm this hx) (Equivalence.symm this hy)



def Cardinal.injects (α β : Cardinal.{u}) : Prop :=
  Quot.lift2_same (fun α β => Nonempty (Function.Injection α β)) (fun _ _ _ _ => le_equipotent_invariant) α β

@[simp] theorem Cardinal.mk_injects_iff {α β : Type u} : injects (Cardinal.mk α) (Cardinal.mk β) ↔ Nonempty (Function.Injection α β) := by
  simp only [injects, mk, Quot.lift2_same_val]

@[simp] theorem Cardinal.mk_injects_iff' {α β : Type u} : injects (Quot.mk _ α) (Quot.mk _ β) ↔ Nonempty (Function.Injection α β) :=
  Cardinal.mk_injects_iff

instance : Preorder Cardinal where
  le := Cardinal.injects
  le_refl := by
    rintro ⟨x⟩
    exact ⟨_,Function.inj_id⟩
  le_trans := by
    rintro ⟨x⟩ ⟨y⟩ ⟨z⟩
    simp only [LE.le, Cardinal.mk_injects_iff']
    rintro ⟨h⟩ ⟨h'⟩
    exact ⟨_,h'.2.comp h.2⟩

@[simp] theorem Cardinal.mk_le_iff {α β : Type u} : (Cardinal.mk α) ≤ (Cardinal.mk β) ↔ Nonempty (Function.Injection α β) := by
  simp only [injects, mk, Quot.lift2_same_val]

@[simp] theorem Cardinal.zero_le (x : Cardinal.{u}) : 0 ≤ x := by
  rcases x with ⟨x⟩
  simp only [LE.le, zero_eq, mk, mk_injects_iff']
  constructor
  exists (fun x => x.elim)
  rintro ⟨⟩

theorem Cardinal.one_le_iff_neq_zero {x : Cardinal.{u}} : 1 ≤ x ↔ x ≠ 0 := by
  rcases x with ⟨x⟩
  change 1 ≤ Cardinal.mk x ↔ Cardinal.mk x ≠ 0
  rw[Ne,Cardinal.eq_zero_iff]
  simp only [one_eq, mk_le_iff, Classical.not_forall, not_false_eq_true]
  constructor
  · rintro ⟨h⟩
    exact ⟨h.1 PUnit.unit, trivial⟩
  · rintro ⟨a,_⟩
    constructor
    exists fun x => a
    rintro ⟨⟩ ⟨⟩ _
    rfl
