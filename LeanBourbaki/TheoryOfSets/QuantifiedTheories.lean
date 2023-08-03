import LeanBourbaki.TheoryOfSets.LogicalTheories

/-
## Quantified Theories
### Definition of Quantifiers
-/

@[inherit_doc] notation:30 "τ" p:40 => Classical.epsilon p

/-- CF11 a
-/

theorem Exists.iff_true_epsilon [Nonempty α] {p : α → Prop}:
  (∃ x, p x) ↔ p (τ p) := by
  apply Iff.intro
  · intro h
    exact Classical.epsilon_spec h
  · intro h
    exact Exists.intro _ h

/-- CF11 b
-/
theorem forall_iff_not_exists_not {p : α → Prop} : (∀ x, p x) ↔ ¬ ∃ x, ¬ (p x) := by
  apply Iff.intro
  · intro h h2
    rcases h2 with ⟨x, h3⟩
    exact h3 (h x)
  · intro h x
    apply Classical.rnotnot
    intro h2
    exact absurd (Exists.intro x h2) h

/-- C26
-/

theorem forall_iff_false_epsilon [Nonempty α] {p : α → Prop}:
  (∀ x, p x) ↔ p (τ (Not ∘ p)) := by
  rw [forall_iff_not_exists_not, Exists.iff_true_epsilon, Iff.notnot]
  unfold Function.comp
  exact Iff.refl _
  
/- C27: metatheorem that cannot be meaningfully translated
-/

/-- C28 
-/     

theorem not_forall_iff_exists_not {p : α → Prop} : ¬(∀ x, p x) ↔ ∃ x, ¬ (p x) := by
  rw [forall_iff_not_exists_not, Iff.notnot]
  exact Iff.refl _

/-
### Axioms of Quantified Theories
-/

/-- S5
-/

example {p : α → Prop}: p x → ∃ x, p x := Exists.intro _

/-
### Properties of Quantifiers
-/

/-- C29
-/
/- Bourbaki proof does not go through because it assumes that the domain
   of discourse is nonempty -/
theorem not_exists_iff_forall_not {p : α → Prop} : ¬(∃ x, p x) ↔ (∀ x, ¬ p x) := by
  rw [← @Iff.notnot (∀ x, ¬ p x),
      @not_forall_iff_exists_not _ (λ a ↦ ¬ p a),
      Iff.notnot_pred]
  exact Iff.refl _

/-- C29' + C11 helper -/
theorem Exists.iff_not_forall_not {p : α → Prop} : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  rw [← @Iff.notnot (∃ x, p x), not_exists_iff_forall_not]
  exact Iff.refl _

/-- C30 
-/

def apply_forall {p : α → Prop} : (∀ y, p y) → p x := by 
  have inhab : Inhabited α := Inhabited.mk x
  have h : (Not ∘ p) x → (Not ∘ p) (τ (Not ∘ p)) := by 
    have h2 := @Exists.intro _ (Not ∘ p) x
    rw [Exists.iff_true_epsilon] at h2
    exact h2
  have h3 := Classical.rcontrapose h 
  rw [← @forall_iff_false_epsilon _ _ p] at h3
  exact h3

/-- C31 a
-/

@[simp] def forall_imp {p q : α → Prop} (h : ∀ x, p x → q x) :
  (∀ x, p x) → (∀ x, q x) := λ h2 x ↦ h x (h2 x) 

/-- C31 b
-/

@[simp] def Exists.imp {p q : α → Prop} (h : ∀ x, p x → q x) :
  (∃ x, p x) → (∃ x, q x) := by
  rw [Exists.iff_not_forall_not, Exists.iff_not_forall_not, ← Iff.contrapose]
  have h2 : ∀ x, (λ x ↦ (p x → q x)) x := h
  rw [Iff.contrapose_pred] at h2
  exact forall_imp h2

/-- C31 c
-/

@[simp] def Iff.cong_forall {p q : α → Prop} (h : ∀ x, p x ↔ q x) :
  (∀ x, p x) ↔ (∀ x, q x) :=
  Iff.intro (forall_imp (λ x ↦ (h x).mp)) (forall_imp (λ x ↦ (h x).mpr))

/-- C31 d
-/

@[simp] def Iff.cong_exists {p q : α → Prop} (h : ∀ x, p x ↔ q x) :
  (∃ x, p x) ↔ (∃ x, q x) :=
  Iff.intro (Exists.imp (λ x ↦ (h x).mp)) (Exists.imp (λ x ↦ (h x).mpr))

/-- C32 a
-/

@[simp] def forall_and_comm {p q : α → Prop} : (∀ x, p x ∧ q x) ↔
  ((∀ x, p x) ∧ (∀ x, q x)) := by
  apply Iff.intro
  · exact (λ h ↦ And.intro (λ x ↦ (h x).left) (λ x ↦ (h x).right))
  · rintro ⟨hl, hr⟩ x
    exact And.intro (hl x) (hr x)

/-- C32 b
-/

@[simp] def Exists.or_comm {p q : α → Prop} : (∃ x, p x ∨ q x) ↔
  ((∃ x, p x) ∨ (∃ x, q x)) := by
  rw [Exists.iff_not_forall_not,
      Exists.iff_not_forall_not,
      Exists.iff_not_forall_not] at *
  rw [← @not_and_iff_or_not (∀ x, ¬ p x) (∀ x, ¬ q x)]
  apply Iff.cong_not
  show (∀ (x : α), (λ x ↦ ¬(p x ∨ q x)) x) ↔ (∀ (x : α), ¬p x) ∧ ∀ (x : α), ¬q x
  rw [@not_or_iff_and_not_pred _ p q, forall_and_comm] 
  exact Iff.refl _

/-- C33 a
-/
@[simp] def forall_or_const {a : Prop} {p : α → Prop} :
  (∀ x, a ∨ p x) ↔ a ∨ (∀ x, p x) := by
  constructor
  · intro h
    rw [Or.iff_not_imp]
    intro h2 x
    cases (h x) with
    | inl l => exact absurd l h2
    | inr r => exact r
  · intro h x
    cases h with
    | inl l => exact Or.inl l 
    | inr r => exact Or.inr (r x)

/-- C33 b
-/
@[simp] theorem Exists.and_const {a : Prop} {p : α → Prop} :
  (∃ x, a ∧ p x) ↔ (a ∧ (∃ x, p x)) := by
  rw [Exists.iff_not_forall_not,
      Exists.iff_not_forall_not,
      And.iff_not_or_not] at *
  apply Iff.cong_not
  show (∀ (x : α), (λ x ↦ ¬(a ∧ p x)) x) ↔ ¬a ∨ ¬¬∀ (x : α), ¬p x
  rw [not_and_iff_or_not_pred, forall_or_const, Iff.notnot]
  exact Iff.refl _


/-- C34 a 
-/
def forall_forall_comm {p : α → α → Prop} : (∀ x, ∀ y, p x y) ↔ (∀ y, ∀ x, p x y) := 
  Iff.intro (λ h x y ↦ h y x) (λ h x y ↦ h y x)

/-- C34 b
-/

theorem Exists.exists_comm {p : α → α → Prop} : (∃ x, ∃ y, p x y) ↔ (∃ y, ∃ x, p x y) := by
  rw [Exists.iff_not_forall_not,
      Exists.iff_not_forall_not]
  apply Iff.cong_not
  conv => 
    lhs
    intro x
    rw [not_exists_iff_forall_not]
    rfl
  conv => 
    rhs
    intro x
    rw [not_exists_iff_forall_not]
  rw [← forall_forall_comm]
  exact Iff.refl _

/-- C34 c
-/

def exists_forall_to_forall_exists {p : α → β → Prop} :
  (∃ x, ∀ y, p x y) → ∀ y, ∃ x, p x y := by
  rintro ⟨x, h⟩ y
  exact Exists.intro _ (h y)
