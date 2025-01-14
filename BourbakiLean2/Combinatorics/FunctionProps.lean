import BourbakiLean2.Combinatorics.Defs

universe u

theorem Combinatorics.Injective.cardinality_inj' {m n : Nat} {β : Type u} [Finite β] (h2 : (Finite.ftype β).cardinality = n) : ∀ {α : Type u} [Finite α]
    (_ : (Finite.ftype α).cardinality = m) (_ : m ≤ n),
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
    let fn : Function.Injection α β → Function.Injection {x}ᶜ β := fun f => ⟨f.val ∘ Subtype.val, fun _ _ h' => Subtype.eq_iff.mpr $ f.property _ _ h'⟩
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
      exists fun ⟨g,eq⟩ => ⟨g x, by
        intro h
        rw[Set.mem_image_iff] at h
        obtain ⟨a,eq2,_⟩ := h
        rw[Subtype.eq_iff] at eq
        dsimp at eq
        rw[← eq] at eq2
        unfold Function.comp at eq2
        have := g.property _ _ eq2
        have prop := a.property
        rw[← this] at prop
        exact prop rfl⟩
      constructor
      · rintro ⟨⟨a,a1⟩,ha⟩ ⟨⟨b,b1⟩,hb⟩ eq
        simp only [Function.Injective.eq_1, Subtype.eq_iff] at eq
        congr
        ext i
        by_cases h : i = x
        · rcases h; exact eq
        · unfold fn at ha hb
          rw[Subtype.eq_iff, funext_iff] at ha hb
          specialize ha ⟨i,h⟩
          specialize hb ⟨i,h⟩
          simp only [Function.comp_apply] at ha hb
          rw[ha,hb]
      · rw[Function.surj_iff]
        intro ⟨b,nmem⟩
        classical
        let g i := if h : i = x then b else f ⟨i,h⟩
        have : g.Injective := by
          intro a a' eq
          unfold g at eq
          split at eq <;> rename_i h1
          · split at eq <;> rename_i h2
            · rw[h1,h2]
            · have : b ∈ f '' Set.univ := by rw[eq]; simp only [Set.val_mem_image_univ]
              exact (nmem this).elim
          · split at eq <;> rename_i h2
            · have : b ∈ f '' Set.univ := by rw[← eq]; simp only [Set.val_mem_image_univ]
              exact (nmem this).elim
            · have eq := y _ _ eq
              injection eq
        have bwa : fn ⟨g,this⟩ = ⟨f,y⟩ := by
          simp only [Function.Injective.eq_1, fn]
          congr
          ext ⟨i, hi⟩
          simp only [Function.comp_apply, g]
          split <;> rename_i h2
          · exact (hi h2).elim
          · rfl
        exists ⟨⟨g,this⟩,bwa⟩
        simp only [↓reduceDIte, g]

theorem Combinatorics.Injective.cardinality_inj {α β : Type u} [Finite α] [Finite β] (h : (Finite.ftype α).cardinality ≤ (Finite.ftype β).cardinality):
    ((Finite.ftype β).cardinality - (Finite.ftype α).cardinality).factorial * (Finite.ftype (Function.Injection α β)).cardinality = (Finite.ftype β).cardinality.factorial :=
  cardinality_inj' rfl rfl h

theorem Combinatorics.Injective.cardinality_inj_div {α β : Type u} [Finite α] [Finite β] (h : (Finite.ftype α).cardinality ≤ (Finite.ftype β).cardinality):
    (Finite.ftype (Function.Injection α β)).cardinality = (Finite.ftype β).cardinality.factorial / ((Finite.ftype β).cardinality - (Finite.ftype α).cardinality).factorial := by
  rw[Nat.div_eq_of_eq_mul_right]
  · exact Nat.factorial_pos
  · exact (cardinality_inj h).symm

theorem Combinatorics.Injective.cardinality_inj_self {α : Type u} [Finite α] : (Finite.ftype (Function.Injection α α)).cardinality = (Finite.ftype α).cardinality.factorial := by
  rw[Combinatorics.Injective.cardinality_inj_div le_rfl]
  simp only [Nat.sub_self, Nat.factorial_zero, Nat.div_one]

theorem Combinatorics.Bijective.cardinality_bij_self {α : Type u} [Finite α] : (Finite.ftype (Function.Bijection α α)).cardinality = (Finite.ftype α).cardinality.factorial := by
  rw[← Combinatorics.Injective.cardinality_inj_self]
  simp only [Function.Bijection, Function.Injection,
    FiniteType.cardinality_eq_iff]
  apply Equipotent.of_eq
  congr
  ext i
  exact Finite.bij_iff_inj $ Equipotent.of_eq rfl

theorem Combinatorics.Surjective.cardinality_surj_self {α : Type u} [Finite α] : (Finite.ftype (Function.Surjection α α)).cardinality = (Finite.ftype α).cardinality.factorial := by
  rw[← Combinatorics.Bijective.cardinality_bij_self]
  simp only [Function.Surjection, Function.Bijection,
    FiniteType.cardinality_eq_iff]
  apply Equipotent.of_eq
  congr
  ext i
  symm
  exact Finite.bij_iff_surj $ Equipotent.of_eq rfl

theorem Combinatorics.Bijective.cardinality_bij {α β : Type u} [Finite α] [Finite β] (h : Equipotent α β):
    (Finite.ftype (Function.Bijection α β)).cardinality = (Finite.ftype α).cardinality.factorial := by
  have h' : (Finite.ftype α).cardinality = (Finite.ftype β).cardinality := by
    simp only [Finite.ftype, FiniteType.cardinality_eq_iff, h]
  trans (Finite.ftype (Function.Injection α β)).cardinality
  · simp only [Function.Bijection, Function.Injection,
    FiniteType.cardinality_eq_iff]
    apply Equipotent.of_eq
    congr
    ext i
    exact Finite.bij_iff_inj h
  · rw[Combinatorics.Injective.cardinality_inj_div]
    · rw[h']
      simp only [Nat.sub_self, Nat.factorial_zero, Nat.div_one]
    · apply le_of_eq h'
