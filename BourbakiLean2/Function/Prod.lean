import BourbakiLean2.Function.Basic

namespace Function
variable {α α' β β' γ γ' : Type*} {f : α → β} {f' : α' → β'} {g : γ → α} {g' : γ' → α'} {x : Set α} {x' : Set α'} {y : Set β} {y' : Set β'} {a : α} {a' : α'}

def prod (f : α → β) (f' : α' → β') := fun (x,y) => (f x, f' y)

@[simp] theorem prod_val : (prod f f') (a,a') = (f a, f' a') := rfl

@[simp] theorem prod_image : Set.image (prod f f') (x.prod x') = (Set.image f x).prod (Set.image f' x') := by
  ext ⟨b,b'⟩
  simp only [Set.mem_image_iff, Prod.exists, Set.mem_prod_iff]
  constructor
  · rintro ⟨a,a', h, h', h''⟩
    simp only [prod_val, Prod.mk.injEq] at h
    constructor
    · exists a
      simp only [and_self, h, h']
    · exists a'
      simp only [and_self, h, h'']
  · rintro ⟨⟨a,ha,h'a⟩,⟨a',ha',h'a'⟩⟩
    exists a
    exists a'
    simp only [prod_val, and_self, ha, ha', h'a, h'a']

@[simp] theorem prod_surj_iff [Nonempty β] [Nonempty β']: (prod f f').Surjective ↔ (f.Surjective ∧ f'.Surjective) := by
  simp only [surj_iff, Prod.exists, prod_val, Prod.forall, Prod.mk.injEq, exists_and_left,
    exists_and_right]
  constructor
  · intro h
    constructor
    · intro b
      specialize h b (Classical.choice (by infer_instance))
      exact h.1
    · intro b
      specialize h (Classical.choice (by infer_instance)) b
      exact h.2
  · intro ⟨h,h'⟩ b b'
    exact ⟨h b, h' b'⟩

@[simp] theorem prod_inj_iff [Nonempty α] [Nonempty α']: (prod f f').Injective ↔ (f.Injective ∧ f'.Injective) := by
  simp only [Injective, Prod.forall, prod_val, Prod.mk.injEq, and_imp]
  constructor
  · intro h
    constructor
    · intro a a' h'
      let b : α' := (Classical.choice (by infer_instance))
      specialize h a b a' b h' rfl
      exact h.1
    · intro a a' h'
      let b : α := (Classical.choice (by infer_instance))
      specialize h b a b a' rfl h'
      exact h.2
  · rintro ⟨h1,h2⟩ a b a' b' h' h''
    constructor
    · exact h1 _ _ h'
    · exact h2 _ _ h''

@[simp] theorem prod_bij_iff [Nonempty α] [Nonempty α'] [Nonempty β] [Nonempty β'] :
  (prod f f').Bijective ↔ (f.Bijective ∧ f'.Bijective) := by
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨⟨(prod_inj_iff.mp h).1, (prod_surj_iff.mp h').1⟩,
      ⟨(prod_inj_iff.mp h).2, (prod_surj_iff.mp h').2⟩⟩
  · rintro ⟨⟨h, h'⟩,⟨h'',h'''⟩⟩
    exact ⟨prod_inj_iff.mpr ⟨h,h''⟩, prod_surj_iff.mpr ⟨h',h'''⟩⟩

theorem comp_prod_comp : (f ∘ g).prod (f' ∘ g') = (f.prod f') ∘ (g.prod g') := by
  ext ⟨c,c'⟩
  · simp only [prod_val, comp_apply]
  · simp only [prod_val, comp_apply]

@[simp] theorem id_prod_id : (id : α → α).prod (id : α' → α') = id := by
  ext ⟨c,c'⟩
  · simp only [prod_val, id_eq]
  · simp only [prod_val, id_eq]

theorem prod_inverse {g : β → α} {g' : β' → α'} (h : IsInverseOf g f) (h' : IsInverseOf g' f') :
    IsInverseOf (g.prod g') (f.prod f') := by
  constructor
  · ext ⟨a,a'⟩
    · simp only [comp_apply, prod_val, h.fg_eq, id_eq]
    · simp only [comp_apply, prod_val, h'.fg_eq, id_eq]
  · ext ⟨a,a'⟩
    · simp only [comp_apply, prod_val, h.gf_eq, id_eq]
    · simp only [comp_apply, prod_val, h'.gf_eq, id_eq]

end Function

namespace Function
variable {ι ι' α α' β β' γ γ' : Type*} {f : α → β} {f' : α' → β'} {g : γ → α} {g' : γ' → α'} {x : ι → Type*}

instance {x : False → Type*} : Unique ((a : _) → x a) where
  default := nofun
  uniq _ := funext nofun

theorem prod_const : ((i : ι) → (const _ α) i) = (ι → α) := rfl
def prod_unique [inst : Unique ι] : Bijection ((i : ι) → x i) (x default) :=
  bijection_of_funcs (fun x => x default)
  (fun a i => Eq.ndrec a (Unique.uniq _ i).symm)
  (by intros; simp only)
  (by intro a
      ext i
      rw[Unique.uniq _ i]
      simp only
      cases (Eq.symm (inst.uniq default))
      rfl)

def prod_bool {β} : Bijection ((i : Bool) → if i then α else β) (α × β) :=
  bijection_of_funcs
    (fun f => (f True, f False))
    (fun (x,y) b => by
      cases b
      · exact y
      · exact x)
    (by intro ⟨a,b⟩
        simp only [decide_True, ↓dreduceIte, decide_False, Bool.false_eq_true])
    (by intro p
        ext b
        cases b
        · simp only [Bool.false_eq_true, ↓dreduceIte, decide_False]
        · simp only [↓dreduceIte, decide_True])

theorem nonempty_prod (h : ∀ i, Nonempty (x i)) : Nonempty ((i : ι) → x i) :=
  ⟨fun i => Classical.choice (h i)⟩

def unique_prod_of_unique (h : ∀ i, Unique (x i)) : Unique ((i : ι) → x i) where
  default := fun i => (h i).default
  uniq _ := funext (fun i => (h i).uniq _)

@[simp] theorem const_inj [inst : Nonempty β] : Function.Injective (const (α := α) β) :=
  fun _ _ h => inst.elim (congrFun h)

def reindex_by_bij (f : Bijection ι' ι) : Bijection ((i : ι) → x i) ((i' : ι') → x (f i')) := by
  exists fun h i' => h (f.val i')
  constructor
  · intro a a' h
    simp only at h
    ext i
    replace h := congrFun h (f.inv i)
    rwa[f.val_inv_val] at h
  · rw[surj_iff]
    intro b
    let b' := fun i => b (f.inv.val i)
    conv =>
      rhs
      intro a
      rw[funext_iff]
    exists fun i => f.val_inv_val (b := i) ▸ b' i
    intro i'
    symm
    simp[b']
    apply Eq.rec_of_inj (f := f.val) (a := b) (i := f.inv.val (f.val i')) (i' := i') (h := (Bijection.val_inv_val f))
    exact f.2.1

theorem subfamily_covered {f : Injection ι' ι} (h : ∀ i, Nonempty (x i)):
    (fun (a : (i : ι) → x i) i' => a (f i')).Surjective := by
  rw[surj_iff]
  intro b
  classical
  let a i := if h' : ∃ i', i = f i' then
    (Classical.epsilon_spec h') ▸ b
      (Classical.epsilon (h := nonempty_of_exists h') fun i' => i = f i') else Classical.choice (h i)
  exists a
  ext i'
  simp only [Injective, a]
  have h' : ∃ i'', f.val i' = f.val i'' := ⟨i', rfl⟩
  simp only [h', ↓reduceDIte, Injective]
  symm
  apply Eq.rec_of_inj
  apply f.2


end Function
