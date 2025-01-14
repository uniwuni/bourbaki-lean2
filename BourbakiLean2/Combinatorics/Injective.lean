import BourbakiLean2.Combinatorics.Defs

universe u

theorem Combinatorics.Injective.cardinality_inj' {m n : Nat} {β : Type u} [Finite β] (h2 : (Finite.ftype β).cardinality = n) : ∀ {α : Type u} [Finite α]
    (h1 : (Finite.ftype α).cardinality = m) (le : m ≤ n),
    (n - m).factorial * (Finite.ftype (Function.Injection α β)).cardinality = n.factorial := by
  induction m with
  | zero =>
    intro α _ h1 h3
    have : Unique (Function.Injection α β) := by
      have h1 := FiniteType.of_cardinality_zero h1
      constructor
      swap
      · constructor
        exists fun a => (h1 a).elim
        intro b
        apply (h1 b).elim
      · intro ⟨f,h⟩
        congr
        ext a
        apply (h1 a).elim
    simp only [Nat.sub_zero, FiniteType.cardinality_unique, Nat.mul_one]
  | succ m ih =>
    intro α _ h1 h3
    rw[← FiniteType.cardinality_univ] at h1
    obtain ⟨x,_⟩ := FiniteType.nonempty_of_cardinality_succ h1
    have : Set.univ = insert x (({x} : Set α) ᶜ) := by
      ext a
      by_cases h : a = x
      · rw[h]; simp only [Set.mem_univ, insert, Set.insert, Set.mem_compl_iff,
        Set.mem_singleton_iff, Set.mem_setOf_iff, not_true_eq_false, or_false]
      · simp only [Set.mem_univ, insert, Set.insert, Set.mem_compl_iff, Set.mem_singleton_iff,
        Set.mem_setOf_iff, h, not_false_eq_true, or_true]
    rw[this] at h1
    rw[FiniteType.cardinality_insert] at h1
    simp only [Nat.add_right_cancel_iff] at h1
    specialize ih h1 (Nat.le_of_succ_le h3)
    rw[← ih]
    have : n - m = (n - (m + 1)) + 1 :=
      Nat.eq_add_of_sub_eq (Nat.le_sub_of_add_le' h3) rfl
    rw[this]
    simp only [Nat.factorial_succ]
    rw[Nat.mul_assoc]
    congr 1
    rw[← this]
    let fn : Function.Injection α β → Function.Injection {x}ᶜ β := fun ⟨f,h⟩ => ⟨f ∘ Subtype.val, fun _ _ h' => Subtype.eq_iff.mpr $ h _ _ h'⟩
    apply FiniteType.cardinality_preimage_same_product (f := fn)
    swap
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_true_eq_false, not_false_eq_true]
    · intro ⟨f,y⟩
      simp only [Function.Injective.eq_1, Set.mem_preimage_iff, Set.mem_singleton_iff]
      suffices h : Equipotent { a // fn a = ⟨f, y⟩ } ((f '' Set.univ) ᶜ) by
        rw[FiniteType.cardinality_eq_iff'.mpr h]
        rw[FiniteType.cardinality_compl, h2]
        congr
        rw[FiniteType.cardinality_image_eq_inj, FiniteType.cardinality_univ, h1]
        exact y
      constructor
      sorry
