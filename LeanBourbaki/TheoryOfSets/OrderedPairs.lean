import LeanBourbaki.TheoryOfSets.CollectivizingRelations

section WeakSetModel
variable {o : Type u}
variable [WeakSetModel o]
noncomputable def ordered_pair (x y : o) := unordered_pair {x} (unordered_pair x y)
@[coe] noncomputable def ordered_pair_uncurry (a : o × o) : o := ordered_pair a.fst a.snd
noncomputable instance ordered_pair_map: Coe (o × o) o := ⟨ordered_pair_uncurry⟩


/-- A3
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

@[simp] theorem ordered_pair.eq  {x x' y y' : o} : ((x,y) : o) = (x',y') ↔ (x = x' ∧ y = y') := by
  constructor
  · unfold ordered_pair_uncurry
    intro h
    have h2 := ordered_pair.inj h
    dsimp at h2 
    exact h2
  · rintro ⟨h1,h2⟩
    simp only [h1,h2]
    
def is_ordered_pair (z : o) := ∃ x : o, ∃y : o, z = (x,y)
def OrderedPair := {x : o // is_ordered_pair x}

noncomputable def OrderedPair.mk (x y : o) : OrderedPair (o := o) := @Subtype.mk _ _ (ordered_pair x y) (by
  unfold is_ordered_pair ordered_pair ordered_pair_uncurry
  exists x
  exists y
  )

theorem OrderedPair.mk_inj {x y x' y' : o} (h : OrderedPair.mk x y = OrderedPair.mk x' y') : (x = x' ∧ y = y') := by
  unfold OrderedPair.mk at h
  have h2 := congrArg Subtype.val h
  simp only at h2 
  apply ordered_pair.inj h2

@[coe] noncomputable def ordered_pair_uncurry_type (a : o × o) : OrderedPair (o := o) := OrderedPair.mk a.fst a.snd
noncomputable instance ordered_pair_pair: Coe (o × o) (OrderedPair (o := o)) := ⟨ordered_pair_uncurry_type⟩
instance Subtype.value {p : α → Prop}: CoeOut {x : α // p x} α := ⟨Subtype.val⟩
@[simp] theorem OrderedPair.eq {x x' y y' : o} : ((x,y) : OrderedPair (o := o)) = (x',y') ↔ (x = x' ∧ y = y') := by
  constructor
  · intro h
    apply OrderedPair.mk_inj
    exact h

  · rintro ⟨h1,h2⟩
    simp[*]

@[simp] theorem is_ordered_pair.ordered_pair_is_ordered_pair {x y : o} : is_ordered_pair (ordered_pair x y) := by
  exists x
  exists y


instance first_projection_is_functional (h : is_ordered_pair z): is_functional_predicate
  (λ x : o ↦ ∃y : o, z = ((x,y) : o)) where
  exs := h
  sv := by
    intro a b
    rintro ⟨y,yh⟩ ⟨y',yh'⟩
    rcases h with ⟨x1,x2,eq⟩
    simp only [eq, Eq.symm_iff, ordered_pair.eq] at yh yh' 
    rw [yh.1,← yh'.1]

instance second_projection_is_functional (h : is_ordered_pair z): is_functional_predicate
  (λ y : o ↦ ∃x : o, z = ((x,y) : o)) where
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

instance first_projection_is_functional_in_pair {z : OrderedPair}: is_functional_predicate
  (λ x : o ↦ ∃y : o, z = ((x,y) : OrderedPair (o := o))) where
  exs := by
    rcases z with ⟨a,⟨x,y,p⟩⟩
    exists x
    exists y
    simp[ordered_pair_uncurry_type, OrderedPair.mk,p, ordered_pair_uncurry]
    
  sv := by
    intro a b
    rintro ⟨y,yh⟩ ⟨y',yh'⟩
    have zh : (↑(a, y) : OrderedPair (o := o)) = (↑(b, y') : OrderedPair) := by rw[← yh, yh']
    simp only [OrderedPair.eq] at zh 
    exact zh.left

instance second_projection_is_functional_in_pair (z : OrderedPair): is_functional_predicate
  (λ y : o ↦ ∃x : o, z = ((x,y) : OrderedPair (o := o))) where
  exs := by
    rcases z with ⟨a,⟨x,y,p⟩⟩
    exists y
    exists x
    simp[ordered_pair_uncurry_type, OrderedPair.mk,p, ordered_pair_uncurry]
    
  sv := by
    intro a b
    rintro ⟨y,yh⟩ ⟨y',yh'⟩
    have zh : (↑(y,a) : OrderedPair (o := o)) = (↑(y',b) : OrderedPair) := by rw[← yh, yh']
    simp only [OrderedPair.eq] at zh 
    exact zh.right

noncomputable def OrderedPair.fst (z : OrderedPair (o := o)) : o := τ (λ x : o ↦ ∃y : o, z = (x,y))
noncomputable def OrderedPair.snd (z : OrderedPair (o := o)) : o := τ (λ y : o ↦ ∃x : o, z = (x,y))
@[simp] theorem OrderedPair.exists_eq_iff_fst {z : OrderedPair (o := o)} {x : o}: 
  (∃y : o, z = (x,y)) ↔ x = z.fst := by
  unfold fst
  rw [Classical.epsilon_eq_iff_of_functional]

@[simp] theorem OrderedPair.exists_eq_iff_snd {z : OrderedPair (o := o)} {y : o}: 
  (∃x : o, z = (x,y)) ↔ y = z.snd := by
  unfold snd
  rw [Classical.epsilon_eq_iff_of_functional]

theorem eq_ordered_pair_iff (x y z : o) :
  (z = (x,y)) ↔ (∃ (h : is_ordered_pair z), x = OrderedPair.fst ⟨z,h⟩ ∧ y = OrderedPair.snd ⟨z,h⟩) := by
  constructor
  · intro a
    exists (by
            exists x
            exists y)
    rw[←OrderedPair.exists_eq_iff_fst, ←OrderedPair.exists_eq_iff_snd]
    constructor
    · exists y
      simp only [a, Eq.symm_iff]
      congr
    · exists x
      simp only [a, Eq.symm_iff]
      congr
  · rintro ⟨⟨x',y',eq⟩,⟨hx,hy⟩⟩
    simp only [eq] at hx hy
    rw[← OrderedPair.exists_eq_iff_fst] at hx
    rw[← OrderedPair.exists_eq_iff_snd] at hy
    rcases hx with ⟨y'',hyy⟩
    rcases hy with ⟨x'',hxx⟩
    unfold ordered_pair_uncurry_type OrderedPair.mk at hxx hyy
    have hyy' := congrArg Subtype.val hyy
    have hxx' := congrArg Subtype.val hxx
    simp only [Eq.symm_iff] at hyy' 
    simp only [Eq.symm_iff] at hxx' 
    simp only [ordered_pair_uncurry] at hxx' hyy'
    have hyy'' := ordered_pair.inj hyy'
    have hxx'' := ordered_pair.inj hxx'
    rw [hyy''.left,hxx''.right]
    assumption

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

@[simp] theorem OrderedPair.fst_eq (x y : o): ((x,y) : OrderedPair).fst = x := by
  unfold OrderedPair.fst
  apply Eq.symm
  rw [Classical.epsilon_eq_iff_of_functional]
  exists y

 @[simp] theorem OrderedPair.snd_eq (x y : o): ((x,y) : OrderedPair).snd = y := by
  unfold OrderedPair.snd
  apply Eq.symm
  rw [Classical.epsilon_eq_iff_of_functional]
  exists x

@[simp] theorem OrderedPair.delta_special {x y : o}: ((((x,y) : OrderedPair (o := o)).fst, ((x,y) : OrderedPair (o := o)).snd) : OrderedPair (o := o))
     = ((x,y) : OrderedPair (o := o)) := by
  simp


theorem is_ordered_pair.iff_equal_pair_projections {z : o}:
  ordered_pair (τ λ x : o ↦ ∃y : o, z = ((x,y) : o)) (τ λ y : o ↦ ∃x : o, z = ((x,y) : o)) = z ↔ is_ordered_pair z := by
  constructor
  · intro h
    rw[← h]
    unfold is_ordered_pair
    exists (τ λ x : o ↦ ∃y : o, z = ((x,y) : o))
    exists (τ λ y : o ↦ ∃x : o, z = ((x,y) : o))
  · rintro ⟨x,y,p⟩ 
    unfold ordered_pair_uncurry at p
    simp only [p, Eq.symm_iff]
    congr
    · have h3 : is_functional_predicate fun x_1 : o => ∃ y_1 : o, ordered_pair x y = (↑(x_1, y_1) : o)
        := first_projection_is_functional (by simp)
      have h2 := Classical.epsilon_eq_iff_of_functional x (f := fun x_1 : o=> ∃ y_1 : o, ordered_pair x y = (↑(x_1, y_1) : o))
      rw [h2]
      exists y
         
    · have h3 : is_functional_predicate fun y_1 : o => ∃ x_1 : o, ordered_pair x y = (↑(x_1, y_1) : o)
        := second_projection_is_functional (by simp)
      have h2 := Classical.epsilon_eq_iff_of_functional y (f := fun y_1 : o => ∃ x_1 : o, ordered_pair x y = (↑(x_1, y_1) : o))
      rw [h2]
      exists x

noncomputable def uncurry_proposition (r : o → o → Prop) : o → Prop :=
  λz ↦ ∃x:o,∃y:o, z = ((x,y) : o) ∧ r x y 

noncomputable def uncurry_proposition_pair (r : o → o → Prop) : OrderedPair (o := o) → Prop :=
  λz ↦ ∃x:o,∃y:o, z = ((x,y) : OrderedPair) ∧ r x y 

theorem uncurry_proposition.iff_uncurry_proposition_pair {r : o → o → Prop} {x : OrderedPair} :
  uncurry_proposition r (x.val : o) ↔ uncurry_proposition_pair r x := by
  unfold uncurry_proposition_pair uncurry_proposition
  apply Iff.cong_exists
  intro y
  apply Iff.cong_exists
  intro z
  simp[ordered_pair_uncurry_type, ordered_pair_uncurry]
  apply Iff.cong_andl
  conv => 
    right
    rw[← Subtype.eq_iff_val_eq]
    
@[simp] theorem OrderedPair.delta {z : OrderedPair}: ((z.fst, z.snd) : OrderedPair (o := o))
     = z := by
  rcases z with ⟨z,⟨x,y,p⟩⟩
  unfold ordered_pair_uncurry_type ordered_pair_uncurry OrderedPair.mk
  rw[← Subtype.eq_iff_val_eq]
  dsimp
  simp[p]
  unfold OrderedPair.mk

  -- [p, Eq.symm_iff] at *

  

@[simp] theorem uncurry_proposition_pair.iff_proj {r : o → o → Prop} {z : OrderedPair} :
  uncurry_proposition_pair r z ↔ r z.fst z.snd := by
  unfold uncurry_proposition_pair
  constructor
  · rintro ⟨x,y,⟨a,b⟩⟩
    simp[a,b]
  · intro a
    exists z.fst
    exists z.snd
    simp


end WeakSetModel