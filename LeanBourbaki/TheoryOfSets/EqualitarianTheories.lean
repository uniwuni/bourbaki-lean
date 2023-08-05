import LeanBourbaki.TheoryOfSets.QuantifiedTheories
import Std.Tactic.CoeExt
import Init.Coe
/-#
## Equalitarian Theories
### The Axioms
-/
/-- S6
-/

theorem Eq.subst_prop {p : α → Prop} (h : x = y) : p x ↔ p y := by
  simp [h] 

/-- S7
-/
theorem Classical.epsilon_eq_of_iff [Nonempty α]
  {p q : α → Prop} (h : ∀ x, p x ↔ q x):
    Classical.epsilon p = Classical.epsilon q := by
    suffices h : p = q by
      rw [h]
    funext
    exact propext (h _)

/-- C43
-/
@[simp] theorem Iff.and_eq_subst {p : α → Prop} : 
  (a = b ∧ p a) ↔ (a = b ∧ p b) := by
  apply Iff.cong_andr_cond
  exact Eq.subst_prop

/- ### Properties of Equality
-/

/-- Theorem 1
-/
example: x = x := Eq.refl x

/-- Theorem 2
-/
@[simp] theorem Eq.symm_iff: x = y ↔ y = x := by
  constructor
  · exact Eq.symm
  · exact Eq.symm

/-- Theorem 3
-/

theorem Eq.and_trans (h : x = y ∧ y = z) : x = z := by
  apply Eq.trans
  · exact h.left 
  · exact h.right

/-- C44
-/

example {f : α → β} (h : x = y): f x = f y := by congr

--instance {p : α → Prop}: Coe {x : α // p x} α where coe := Subtype.val
attribute [coe] Subtype.val
def is_equation {α} {β} (r : α → Prop) :=
  ∃ (f : α → β), ∃ (g : α → β), ∀ x, r x ↔ f x = g x

def Equation α β :=
  {r : α → Prop // @is_equation _ β r}

noncomputable instance Equation.coeFun : CoeFun (Equation α β) (λ _ ↦ α → Prop) where
  coe := Subtype.val

theorem is_equation.intro (f g : α → β) :
  @is_equation α β (λ (x : α) ↦ f x = g x) := by
  unfold is_equation
  exists f
  exists g
  simp only [implies_true]

def Equation.intro (f g : α → β) : Equation α β :=
  ⟨(λ (x : α) ↦ f x = g x), is_equation.intro f g⟩

example (h : {x : α // x = x}) : α := h 

@[simp] theorem Equation.true_iff {f g : α → β} (x : α) : 
  Equation.intro f g x ↔ f x = g x := by
  simp [Equation.intro]

def Solution (e : Equation α β) := {v : α // e v}

/- ### Functional Relations
-/

def is_single_valued_predicate (f : α → Prop) : Prop :=
  ∀ y z, f y → f z → y = z

/-- C45 a
-/

theorem Classical.epsilon_eq_of_single_valued [Nonempty α] (f : α → Prop)
  (h : is_single_valued_predicate f) (x : α) (hf : f x) :
  x = Classical.epsilon f := by
  have ht := Classical.epsilon_spec ⟨x, hf⟩
  exact h _ _ hf ht

/-- C45 b
-/
theorem is_single_valued_from_eq {f : α → Prop} (t : α) (h : ∀ x, f x → x = t) :
  is_single_valued_predicate f := by
  intro y z fy fz
  have := h _ fy
  have := h _ fz
  simp[*]

def is_functional_predicate (f : α → Prop) : Prop :=
  (∀ y z, f y → f z → y = z) ∧ ∃ x, f x

/-- C46 a
-/
@[simp] theorem Classical.epsilon_eq_iff_of_functional [Nonempty α] (f : α → Prop)
  (h : is_functional_predicate f) (x : α): x = Classical.epsilon f ↔ f x := by
  constructor
  · intro h2
    rw [h2]
    apply Classical.epsilon_spec h.right
  · apply Classical.epsilon_eq_of_single_valued f h.left x

/-- C46 a helper
-/
theorem Classical.epsilon_spec_functional [Nonempty α] (f : α → Prop)
  (h : is_functional_predicate f): f (τ f) := by
  rw[← Classical.epsilon_eq_iff_of_functional f h _]

/-- C46 b
-/

theorem is_functional_from_eq_iff {f : α → Prop} (t : α) (h : ∀ x, f x ↔ x = t) :
  is_functional_predicate f := by
  apply And.intro
  · exact is_single_valued_from_eq t (λ x ↦ (h x).mp)
  · exists t
    exact (h t).mpr (Eq.refl t)
    
/-- C47
-/
theorem functional_exists_and [Nonempty α] {f g : α → Prop}
  (h : is_functional_predicate f): g (Classical.epsilon f)
    ↔ ∃ x, f x ∧ g x := by
  constructor
  · intro h1
    exists (τ f)
    apply And.intro (Classical.epsilon_spec_functional f h) h1
  · rintro ⟨x, ⟨fx, gx⟩⟩
    rw[← Classical.epsilon_eq_iff_of_functional f h x] at fx
    rw[fx] at gx
    assumption

/- ## Exercises Chapter 1 
   ### § 5
-/

/-- 1
-/

theorem Eq.is_functional: is_functional_predicate (λ x ↦ x = y) := by
  constructor
  · intro a b c d
    simp[*]
  · exists y

/-- 2
-/
theorem Eq.exists_eq_and_iff {f : α → α → Prop}:
  (∃ x, x = y ∧ f x y) ↔ f y y := by
  constructor
  · rintro ⟨x, ⟨eq, fxy⟩⟩
    rw [eq] at fxy
    assumption
  · intro fy
    exists y

/-- 3
-/     
theorem is_functional_cond_functional {r s : α → α → Prop} (t : α → α)
  (fr : ∀ x y, s x y → is_functional_predicate (λ x ↦ r x y))
  (h2 : ∀ x y, s x (t y)) : ∀ y, is_functional_predicate (λ x ↦ r x (t y)) := by
  intro y
  constructor
  · intro z1 z2 r1 r2
    have s1 := h2 z1 y
    have funcy := (fr _ _ s1).left
    apply funcy _ _ r1 r2
  · exact (fr _ _ (h2 y y)).right 
    
/-- 4
-/
theorem Imp.cong_is_functional {r s : α → Prop} (h : ∀x, r x ↔ s x)
  (h2 : is_functional_predicate r) : is_functional_predicate s := by
  have h3 : ∀x, r x = s x := by
    intro x
    apply propext
    exact h x
  have h4 := funext h3
  simpa [h4] using h2


/-- 5 a
-/
theorem functional_not_exists_and {r s : α → Prop} 
  (h : is_functional_predicate r) : 
  (¬ (∃ x, r x ∧ s x)) ↔ ∃ x, r x ∧ ¬(s x) := by
  have _ : Nonempty α := by
    rcases (h.right) with ⟨a, b⟩
    constructor
    exact a
  rw [Iff.iff_not_iff_not, Iff.notnot]
  intro i
  have h4 : ∃ x, r x := h.right
  rcases h4 with ⟨x, rx⟩
  rcases Classical.em (s x) with ⟨sx⟩ | ⟨nsx⟩
  · rcases i.mp ⟨x, ⟨rx, sx⟩⟩ with ⟨x', ⟨rx', nsx'⟩⟩
    rw [h.left _ _ rx rx'] at sx
    exact nsx' sx
  · rcases i.mpr ⟨x, ⟨rx, nsx⟩⟩ with ⟨x', ⟨rx', sx'⟩⟩
    rw [h.left _ _ rx' rx] at sx'
    exact nsx sx'

/-- 5 b
-/

theorem functional_exists_and_iff_and {r s t : α → Prop} 
  (h : is_functional_predicate r) : 
  (∃ x, r x ∧ (s x ∧ t x)) ↔
    (∃ x, (r x ∧ s x)) ∧ ∃ x, (r x ∧ t x) := by
  have _ : Nonempty α := by
    rcases (h.right) with ⟨a, b⟩
    constructor
    exact a
  rw[← functional_exists_and h,
     ← functional_exists_and h,
     ← functional_exists_and h]
  apply Iff.refl _

/-- 5 c
-/

theorem Exists.iff_and_or [Nonempty α] {r s t : α → Prop}: 
  (∃ x, r x ∧ (s x ∨ t x)) ↔
    (∃ x, (r x ∧ s x)) ∨ ∃ x, (r x ∧ t x) := by
  constructor
  · rintro ⟨a, ⟨b,c⟩⟩
    rw[← Exists.or_comm]
    exists a
    rw [← And.or_distr]
    constructor
    · assumption
    · assumption
  · intro h
    rcases h with ⟨a, ⟨b,c⟩⟩|⟨a, ⟨b,c⟩⟩
    · exact ⟨a, ⟨b, Or.inl c⟩⟩
    · exact ⟨a, ⟨b, Or.inr c⟩⟩
  
/-- 6
-/

theorem exists_to_forall_all_to_eq_all [Nonempty α] {x y : α}
  (h : ∀ (r : α → Prop) x, (∃ y, r y) → r x) : x = y :=
    h (λ y ↦ x = y) _ ⟨x, Eq.refl x⟩


@[simp] theorem epsilon_eq [Nonempty α] {x : α} :
  (τ (λ y ↦ x = y)) = x := by
  have h : x = (τ (λ y ↦ x = y)) := Classical.epsilon_spec ⟨x, Eq.refl x⟩
  exact h.symm

/-- 7
-/
theorem iff_to_eq_epsilon_to_eq_all [Nonempty α] {x y : α}
  (h : ∀ (r s : α → Prop) x, (r x ↔ s x) → (τ r) = (τ s)) : x = y := by
  have h2 := h (λ x ↦ x = x) (λ x ↦ x = y) y
  have h3 := h (λ x ↦ x = x) (λ y ↦ y = x) x
  simp at h2
  simp at h3
  simp [h2,h3]
  
  
  