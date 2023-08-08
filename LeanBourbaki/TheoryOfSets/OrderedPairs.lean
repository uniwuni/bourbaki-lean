import LeanBourbaki.TheoryOfSets.CollectivizingRelations
/-#
# Theory of Sets
## Ordered Pairs
### The Axiom of the Ordered Pair
-/
section WeakSetModel
variable {o : Type u}
variable [WeakSetModel o]
noncomputable def ordered_pair (x y : o) := unordered_pair {x} (unordered_pair x y)
@[coe, inline, simp] noncomputable abbrev ordered_pair_uncurry (a : o × o) : o := ordered_pair a.fst a.snd
@[inherit_doc] infixl:46 " ,, "   => ordered_pair


/-- A3 and Exercise 2a, 2b
-/
theorem ordered_pair.inj {x x' y y' : o} (h : ordered_pair x y = ordered_pair x' y'):
  x = x' ∧ y = y' := by
  unfold ordered_pair at h
  rw[eq_iff_iff] at h
  have h2 := h {x}
  simp only [unordered_pair.comm, unordered_pair.elem_iff, Or.comm, true_or, Eq.symm_iff, true_iff] at h2 
  rcases h2 with ⟨h3⟩|⟨h4⟩
  · rw[eq_iff_iff] at h3
    specialize h3 x
    simp only [unordered_pair.elem_iff, Eq.symm_iff, singleton.elem_iff, iff_true] at h3 
    rcases h3 with ⟨h4⟩
    · apply And.intro h4
      rw [h4] at h
      specialize h (unordered_pair x' y')
      simp at h
      rcases h with ⟨h5⟩
      · rw[eq_iff_iff] at h5
        specialize h5 y
        simp only [unordered_pair.elem_iff, Or.comm, true_or, Eq.symm_iff, true_iff] at h5 
        rcases h5 with ⟨h6⟩
        · rw [h6] at h5
          rw[eq_iff_iff] at h5
          specialize h5 y'
          simp only [unordered_pair.elem_iff, or_self, Or.comm, true_or, iff_true] at h5 
          exact h5
        · assumption
      · have h5 := h3
        rw[eq_iff_iff] at h3
        specialize h3 y'
        simp only [unordered_pair.elem_iff, Or.comm, true_or, singleton.elem_iff, Eq.symm_iff, true_iff] at h3 
        rw [h3] at h5
        rw[eq_iff_iff,h3,←h4,h3] at h
        specialize h (unordered_pair y' y)
        simp only [singleton, unordered_pair.comm, unordered_pair.elem_iff, Eq.symm_iff, true_or, or_self, true_iff] at h  
        rw[eq_iff_iff] at h
        specialize h y
        simp only [unordered_pair.elem_iff, Eq.symm_iff, true_or, or_self, true_iff] at h 
        exact h
    · rw[←‹x=y'›] at h3
      rw[eq_iff_iff] at h3
      specialize h3 x'
      simp only [unordered_pair.comm, unordered_pair.elem_iff, Or.comm, true_or, singleton.elem_iff, Eq.symm_iff,
        true_iff] at h3 
      apply And.intro h3
      simp only [‹x = y'›, unordered_pair.comm, unordered_pair.elem_iff, Eq.symm_iff, h3.symm] at h 
      have h4 := (h (unordered_pair y y')).mp (Or.inl rfl)
      simp only [or_self, singleton] at h4
      rw[eq_iff_iff] at h4
      specialize h4 y
      simp only [unordered_pair.elem_iff, Eq.symm_iff, true_or, or_self, true_iff] at h4 
      exact h4
  · have h5 := (singleton.inj h4)
    apply And.intro h5
    rw [h5] at h
    have h6 := (h (unordered_pair x' y)).mp (by simp)
    simp only [unordered_pair.comm, unordered_pair.elem_iff, Eq.symm_iff] at h6 
    rcases h6 with ⟨h7⟩|⟨h7⟩
    · rw[eq_iff_iff] at h7
      specialize h7 y
      simp only [unordered_pair.elem_iff, Or.comm, true_or, Eq.symm_iff, true_iff] at h7 
      rcases h7 with ⟨ h8 ⟩
      · rw [h8] at h7
        rw[eq_iff_iff] at h7
        specialize h7 y'
        simp only [unordered_pair.elem_iff, or_self, Or.comm, true_or, iff_true] at h7  
        assumption
      · assumption
    · rw[eq_iff_iff] at h7
      specialize h7 y
      simp only [unordered_pair.elem_iff, Or.comm, true_or, singleton.elem_iff, Eq.symm_iff, true_iff] at h7 
      rw [h7] at h
      have h8 := (h (unordered_pair y y')).mpr (by simp)
      simp only [unordered_pair.comm, unordered_pair.elem_iff, Eq.symm_iff] at h8 
      rcases h8 with ⟨h9⟩|⟨h9⟩
      · rw[eq_iff_iff] at h9
        specialize h9 y'
        simp only [unordered_pair.elem_iff, or_self, Or.comm, true_or, iff_true] at h9 
        exact h9
      · rw[eq_iff_iff] at h9
        specialize h9 y'
        simp only [unordered_pair.elem_iff, Or.comm, true_or, singleton.elem_iff, Eq.symm_iff, true_iff] at h9 
        exact h9

@[simp] theorem ordered_pair.eq  {x x' y y' : o} : ((x,,y) : o) = (x',,y') ↔ (x = x' ∧ y = y') := by
  constructor
  · intro h
    have h2 := ordered_pair.inj h
    dsimp at h2 
    exact h2
  · rintro ⟨h1,h2⟩
    simp only [h1,h2]
    
def is_ordered_pair (z : o) := ∃ x : o, ∃y : o, z = (x,,y)

instance Subtype.value {p : α → Prop}: CoeOut {x : α // p x} α := ⟨Subtype.val⟩

@[simp] theorem is_ordered_pair.ordered_pair_is_ordered_pair {x y : o} : is_ordered_pair (ordered_pair x y) := by
  exists x
  exists y


instance first_projection_is_functional (h : is_ordered_pair z): is_functional_predicate
  (λ x : o ↦ ∃y : o, z = ((x,,y) : o)) where
  exs := h
  sv := by
    intro a b
    rintro ⟨y,yh⟩ ⟨y',yh'⟩
    rcases h with ⟨x1,x2,eq⟩
    simp only [eq, Eq.symm_iff, ordered_pair.eq] at yh yh' 
    rw [yh.1,← yh'.1]

instance second_projection_is_functional (h : is_ordered_pair z): is_functional_predicate
  (λ y : o ↦ ∃x : o, z = ((x,,y) : o)) where
  exs := by
    rcases h with ⟨a,b,c⟩
    exists b
    exists a

  sv := by
    intro a b
    rintro ⟨y,yh⟩ ⟨y',yh'⟩
    rcases h with ⟨x1,x2,eq⟩
    simp only [eq, Eq.symm_iff, ordered_pair.eq] at yh yh' 
    rw [yh.2,← yh'.2]


noncomputable def is_ordered_pair.fst (z : o) : o := τ (λ x : o ↦ ∃y : o, z = (x,,y))
noncomputable def is_ordered_pair.snd (z : o) : o := τ (λ y : o ↦ ∃x : o, z = (x,,y))
@[simp] theorem OrderedPair.exists_eq_iff_fst {z x : o} (h : is_ordered_pair z): 
  (∃y : o, z = (x,,y)) ↔ x = is_ordered_pair.fst z := by
  unfold is_ordered_pair.fst
  have := first_projection_is_functional h
  rw [Classical.epsilon_eq_iff_of_functional]

@[simp] theorem OrderedPair.exists_eq_iff_snd {z y : o} (h : is_ordered_pair z): 
  (∃x : o, z = (x,,y)) ↔ y = is_ordered_pair.snd z := by
  unfold is_ordered_pair.snd
  have := second_projection_is_functional h
  rw [Classical.epsilon_eq_iff_of_functional]
  

theorem is_ordered_pair.eq_iff (x y z : o) :
  (z = (x,,y)) ↔ (is_ordered_pair z ∧ is_ordered_pair.fst z = x ∧ is_ordered_pair.snd z = y) := by
  constructor
  · intro a
    exists (by
            exists x
            exists y)
    simp only at a 
    have is_pair := is_ordered_pair.ordered_pair_is_ordered_pair (x := x) (y := y)
    rw[←a] at is_pair
    rw[Eq.symm_iff,Eq.symm_iff (y := y)]  
    rw[←OrderedPair.exists_eq_iff_fst is_pair, ←OrderedPair.exists_eq_iff_snd is_pair]
    constructor
    · exists y
    · exists x
  · rintro ⟨⟨x',y',eq⟩,⟨hx,hy⟩⟩
    simp only [eq,Eq.symm_iff] at hx hy
    rw[← OrderedPair.exists_eq_iff_fst (by simp)] at hx
    rw[← OrderedPair.exists_eq_iff_snd (z := (↑(x',, y') : o)) (by simp)] at hy
    rcases hx with ⟨y'',hyy⟩
    rcases hy with ⟨x'',hxx⟩
    simp only [Eq.symm_iff] at hyy  hxx
    have hyy'' := ordered_pair.inj hyy
    have hxx'' := ordered_pair.inj hxx
    rw [hyy''.left,← hxx''.right, eq]


theorem Subtype.eq_from_val_eq {p : α → Prop} {x y : {x : α // p x}} (h : x.val = y.val) : x = y := by
  rcases x with ⟨x,hx⟩ 
  rcases y with ⟨y,hy⟩
  simp only at h
  simp[h]

@[simp high] theorem Subtype.eq_iff_val_eq {p : α → Prop} {x y : {x : α // p x}} : x.val = y.val ↔ x = y := by
  constructor
  · apply Subtype.eq_from_val_eq
  · intro h
    simp[h]

@[simp] theorem is_ordered_pair.fst_eq (x y : o): is_ordered_pair.fst ((x,,y) : o) = x := by
  have h2 := is_ordered_pair.eq_iff x y (ordered_pair x y)
  simp only [ordered_pair_uncurry, is_ordered_pair.ordered_pair_is_ordered_pair, Eq.symm_iff, true_and, true_iff] at h2 
  simp [h2.left.symm]

 @[simp] theorem is_ordered_pair.snd_eq (x y : o): is_ordered_pair.snd ((x,,y) : o) = y := by
  have h2 := is_ordered_pair.eq_iff x y (ordered_pair x y)
  simp only [ordered_pair_uncurry, is_ordered_pair.ordered_pair_is_ordered_pair, Eq.symm_iff, true_and, true_iff] at h2 
  simp [h2.right.symm]

@[simp] theorem is_ordered_pair.delta_special {x y : o}:
  (is_ordered_pair.fst (ordered_pair x y),, is_ordered_pair.snd (ordered_pair x y)) = ordered_pair x y := by
  simp only [ordered_pair_uncurry, Eq.symm_iff]
  congr
  · simp
  · simp



theorem is_ordered_pair.iff_equal_pair_projections {z : o}:
  ordered_pair (is_ordered_pair.fst z) (is_ordered_pair.snd z) = z ↔ is_ordered_pair z := by
  unfold fst snd
  constructor
  · intro h
    rw[← h]
    unfold is_ordered_pair
    exists (τ λ x : o ↦ ∃y : o, z = ((x,,y) : o))
    exists (τ λ y : o ↦ ∃x : o, z = ((x,,y) : o))
  · rintro ⟨x,y,p⟩ 
    simp only [p, Eq.symm_iff]
    congr
    · have h3 : is_functional_predicate fun x_1 : o => ∃ y_1 : o, ordered_pair x y = (x_1,,y_1)
        := first_projection_is_functional (by simp)
      have h2 := Classical.epsilon_eq_iff_of_functional x (f := fun x_1 : o=> ∃ y_1 : o, ordered_pair x y = (x_1 ,, y_1))
      rw [h2]
      exists y
         
    · have h3 : is_functional_predicate fun y_1 : o => ∃ x_1 : o, ordered_pair x y = (x_1,,y_1)
        := second_projection_is_functional (by simp)
      have h2 := Classical.epsilon_eq_iff_of_functional y (f := fun y_1 : o => ∃ x_1 : o, ordered_pair x y = (x_1,,y_1))
      rw [h2]
      exists x

noncomputable def uncurry_proposition (r : o → o → Prop) : o → Prop :=
  λz ↦ ∃x:o,∃y:o, z = (x,, y) ∧ r x y 


@[simp] theorem is_ordered_pair.delta {z : o} (h: is_ordered_pair z): (is_ordered_pair.fst z,, is_ordered_pair.snd z) = z
     := by simp[is_ordered_pair.eq_iff, h]


  -- [p, Eq.symm_iff] at *

  

@[simp] theorem uncurry_proposition.iff {r : o → o → Prop} {z : o} (h : is_ordered_pair z) :
  uncurry_proposition r z ↔ r (is_ordered_pair.fst z) (is_ordered_pair.snd z) := by
  unfold uncurry_proposition
  constructor
  · rintro ⟨x,y,⟨a,b⟩⟩
    simp[a,b]
  · intro a
    exists (is_ordered_pair.fst z)
    exists (is_ordered_pair.snd z)
    simp[h,a]


@[simp] theorem uncurry_proposition.pair_iff {r : o → o → Prop} {x y : o} :
  uncurry_proposition r (x,,y) ↔ r x y := by
  simp

@[simp] theorem uncurry_proposition.pair_exists {r : o → o → Prop} {x y : o} :
  (∃ z : o, z = (x,,y) ∧ uncurry_proposition r z) ↔ r x y := by
  constructor
  · rintro ⟨ z, ⟨eq, rp⟩⟩
    rw [eq] at rp
    simp only [is_ordered_pair.ordered_pair_is_ordered_pair, iff, is_ordered_pair.fst_eq, is_ordered_pair.snd_eq] at rp 
    exact rp
  · intro rxy
    exists (x,,y)
    apply And.intro rfl
    simp [rxy]

/-
#### Exercises
-/
/-- 1 a
-/
@[simp] theorem is_ordered_pair.exists_relation_of_projection {r : o → o → Prop}:
  (∃z:o, r (fst z) (snd z)) ↔ (∃x:o,∃y:o, r x y) := by
  constructor
  · rintro ⟨z, rz⟩
    exists fst z
    exists snd z
  · rintro ⟨x,y,rxy⟩
    exists (x,,y)
    simp [rxy]

/-- 1 b
-/
@[simp] theorem is_ordered_pair.forall_relation_of_projection {r : o → o → Prop}:
  (∀z:o, r (fst z) (snd z))  ↔ (∀x:o,∀y:o, r x y) := by
  constructor
  · intro f x y
    specialize f (x,,y)
    simp only [fst_eq, snd_eq] at f 
    exact f
  · intro f z
    apply f

/-
### Product of Two Sets
-/

/-- Theorem 1
-/
theorem product_is_collectivizing (X Y : o):
  ∃Z:o, ∀z:o, (z ∈ Z ↔ ∃ x, ∃ y, z = (x,,y) ∧ x ∈ X ∧ y ∈ Y) := by
  let a (y:o) := {(x,,y) || x ∈ X}
  have h2 (y : o) : ∃ A:o, ∀ z:o, z ∈ a y → z ∈ A := by
    exists a y
    simp
  have h3 := scheme_selection_union h2 Y
  have h3 := h3.prf
  rcases h3 with ⟨prod, prf⟩
  exists prod
  intro z
  specialize prf z
  simp[prf]
  conv =>
    lhs
    congr
    ext
    rw[← Exists.and_const]
  rw[Exists.exists_comm (p := λ x x_1 ↦ x ∈ Y ∧ z = (x_1,, x) ∧ x_1 ∈ X)]
  apply Iff.cong_exists
  intro x
  apply Iff.cong_exists
  intro y
  simp only [And.comm, And.assoc]

instance is_collectivizing.product_set (X Y : o):
  is_collectivizing (λ z : o ↦ is_ordered_pair z ∧ is_ordered_pair.fst z ∈ X ∧ is_ordered_pair.snd z ∈ Y) := by
  constructor
  rcases (product_is_collectivizing X Y) with ⟨prod, prf⟩
  exists prod
  intro x
  rw [prf x]
  constructor
  · rintro ⟨x1,x2,⟨h1,h2,h3⟩⟩
    simp[h1,h2,h3]
  · rintro ⟨h1,h2,h3⟩
    exists is_ordered_pair.fst x
    exists is_ordered_pair.snd x
    simp[*]
      


end WeakSetModel