import BourbakiLean2.Data.Nat.Basic
import BourbakiLean2.Data.Finite

universe u v
instance finite_sigma {α : Type u} {x : α → Cardinal.{u}} [h1 : Finite α] [h2 : ∀ a, Cardinal.Finite $ x a] :
    Cardinal.Finite $ Cardinal.sigma x := by
  rw[← Cardinal.sigma_reindex_univ]
  apply Finite.set_induction (p := fun a =>
    (Cardinal.sigma fun x_1 : a ↦
      match x_1 with
      | ⟨x_2, property⟩ => x x_2).Finite)
  · rw[Cardinal.sigma_empty]
    · infer_instance
    · exact fun ⟨x,h⟩ => h
  · intro a A fina nmem sumfin
    have : (Cardinal.sigma fun x_1 : (A ∪ {a} : Set _) ↦
            match x_1 with
            |   ⟨x_2, property⟩ => x x_2) =
           x a + (Cardinal.sigma fun x_1 : (A : Set _) ↦
            match x_1 with
            |   ⟨x_2, property⟩ => x x_2) := by
      have ⟨g,eq⟩ := Cardinal.factors_through_mk (f := x)
      rcases eq
      unfold Function.comp
      apply Eq.symm
      simp only [Finite.iff, Function.comp_apply, Cardinal.sigma_mk, Cardinal.add_mk,
        Cardinal.eq_iff] at *
      constructor
      exists Sum.elim
        (fun x => ⟨⟨_,Or.inr rfl⟩, x⟩)
        (fun ⟨⟨a,h⟩,x⟩ => ⟨⟨_,Or.inl h⟩, x⟩)
      constructor
      · rintro (a1|⟨i1,a1⟩) (a2|⟨i2,a2⟩) h
        · simp only [Sum.elim_inl] at h
          congr
          injection h
        · simp only [Sum.elim_inl, Sum.elim_inr] at h
          injection h with h _
          injection h with h
          have := i2.property
          rw[← h] at this
          apply (nmem this).elim
        · simp only [Sum.elim_inr, Sum.elim_inl] at h
          injection h with h _
          injection h with h
          have := i1.property
          rw[h] at this
          apply (nmem this).elim
        · simp at h
          congr
          injection h with h _
          injection h with h
          · simp only [Subtype.eq_iff, h]
          · injection h
      · rw[Function.surj_iff]
        rintro ⟨⟨i,(ha|rfl)⟩,b⟩
        · exists Sum.inr ⟨⟨i,ha⟩,b⟩
        · exists Sum.inl b
    rw[this]
    infer_instance

instance finite_prod {α : Type u} {x : α → Cardinal.{u}} [h1 : Finite α] [h2 : ∀ a, Cardinal.Finite $ x a] :
    Cardinal.Finite $ Cardinal.prod x := by
  rw[← Cardinal.prod_reindex_univ]
  apply Finite.set_induction (p := fun a =>
    (Cardinal.prod fun x_1 : a ↦
      match x_1 with
      | ⟨x_2, property⟩ => x x_2).Finite)
  · rw[Cardinal.prod_empty]
    · infer_instance
    · exact fun ⟨x,h⟩ => h
  · intro a A fina nmem sumfin
    have : (Cardinal.prod fun x_1 : (A ∪ {a} : Set _) ↦
            match x_1 with
            |   ⟨x_2, property⟩ => x x_2) =
           x a * (Cardinal.prod fun x_1 : (A : Set _) ↦
            match x_1 with
            |   ⟨x_2, property⟩ => x x_2) := by
      have ⟨g,eq⟩ := Cardinal.factors_through_mk (f := x)
      rcases eq
      unfold Function.comp
      simp only [Finite.iff, Function.comp_apply, Cardinal.prod_mk, Cardinal.mul_mk,
        Cardinal.eq_iff] at *
      constructor
      exists fun f => ⟨f ⟨a, Or.inr rfl⟩, fun i => f ⟨i, Or.inl i.property⟩⟩
      constructor
      · rintro f1 f2 eq
        simp only [Prod.mk.injEq] at eq
        ext i
        rcases i with ⟨i,(h|rfl)⟩
        · exact congrFun eq.2 ⟨i, h⟩
        · exact eq.1
      · rw[Function.surj_iff]
        intro ⟨b,f⟩
        classical
        exists fun ⟨i,h⟩ => Or.by_cases' h (fun h => f ⟨_,h⟩) (fun h => h ▸ b)
        congr
        · simp only [Or.by_cases', Set.mem_singleton_iff, ↓reduceDIte]
          have (h : a ∈ ({a} : Set α)) : h = rfl := by rcases h; rfl
          rw[this (h := of_eq_true _)]
          simp only [Set.mem_singleton_iff]
        · ext ⟨x,h⟩
          have : x ≠ a := by
            intro h'
            rw[h'] at h
            exact nmem h
          simp only [Or.by_cases', Set.mem_singleton_iff, this, ↓reduceDIte]
    rw[this]
    infer_instance
