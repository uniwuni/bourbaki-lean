import LeanBourbaki.TheoryOfSets.LogicalTheories
import Std.Tactic.Simpa
import Std.Tactic.SimpTrace
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

def forall_imp {p q : α → Prop} (h : ∀ x, p x → q x) :
  (∀ x, p x) → (∀ x, q x) := λ h2 x ↦ h x (h2 x) 

/-- C31 b
-/

def Exists.imp {p q : α → Prop} (h : ∀ x, p x → q x) :
  (∃ x, p x) → (∃ x, q x) := by
  rw [Exists.iff_not_forall_not, Exists.iff_not_forall_not, ← Iff.contrapose]
  have h2 : ∀ x, (λ x ↦ (p x → q x)) x := h
  rw [Iff.contrapose_pred] at h2
  exact forall_imp h2

/-- C31 c
-/

def Iff.cong_forall {p q : α → Prop} (h : ∀ x, p x ↔ q x) :
  (∀ x, p x) ↔ (∀ x, q x) :=
  Iff.intro (forall_imp (λ x ↦ (h x).mp)) (forall_imp (λ x ↦ (h x).mpr))

/-- C31 d
-/

def Iff.cong_exists {p q : α → Prop} (h : ∀ x, p x ↔ q x) :
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

/-
### Typical Quantifiers
-/

/-- CF12 a
-/
@[simp] def TypicalExists (p q : α → Prop) := ∃ x, p x ∧ q x 

/-- CF12 b
-/
def TypicalForall (p q : α → Prop) := ¬ (TypicalExists p (Not ∘ q))

/-- C35
-/
@[simp] theorem TypicalForall.iff_forall {p q : α → Prop} :
  TypicalForall p q ↔ ∀ x, p x → q x := by
    unfold TypicalForall TypicalExists
    conv =>
      lhs
      congr
      congr
      intro x
      simp
      rw [And.iff_not_right]
    rw [forall_iff_not_exists_not]
    exact Iff.refl _

/-- C36
-/
theorem TypicalForall.intro {p q : α → Prop} (h : ∀ x, p x → q x)
  : TypicalForall p q := TypicalForall.iff_forall.mpr h


/-- helper
-/
theorem TypicalForall.apply {p q : α → Prop} (h : TypicalForall p q)
  (h2 : p x) : q x := by
  rw [TypicalForall.iff_forall] at h
  exact h _ h2

/-- helper
-/

theorem TypicalExists.intro {p q : α → Prop} (h1 : p x) (h2 : q x)
  : TypicalExists p q := Exists.intro x (And.intro h1 h2)

/-- C37
-/
theorem TypicalForall.byContradiction {p q : α → Prop} (h : ∀ x, ¬ (p x ∧ ¬ q x)) :
  TypicalForall p q := by
  apply intro
  conv at h =>
    intro x
    rw [And.iff_not_right, Iff.notnot]
    rfl
  exact h

/-- C38 a
-/

theorem not_tforall_iff_texists_not {p q: α → Prop} :
  ¬ (TypicalForall p q) ↔ TypicalExists p (Not ∘ q) := by
  unfold TypicalForall TypicalExists
  exact Iff.notnot

/-- C38 b
-/
theorem not_texists_iff_tforall_not {p q: α → Prop} :
  ¬ (TypicalExists p q) ↔ TypicalForall p (Not ∘ q) := by
  unfold TypicalForall TypicalExists Function.comp
  simp [Iff.notnot]

/-- C38 b helper
-/
theorem TypicalExists.iff_not_tforall_not {p q: α → Prop} :
  TypicalExists p q ↔ ¬ TypicalForall p (Not ∘ q) := by
  rw [← @Iff.notnot (TypicalExists p q), not_texists_iff_tforall_not]
  exact Iff.refl _

/-- C39 a 
-/

theorem TypicalExists.cond_imp {p q r: α → Prop} (h : ∀ x, p x → q x → r x) :
  TypicalExists p q → TypicalExists p r := by
  unfold TypicalExists
  apply Exists.imp
  intro x h2
  exact And.intro h2.left (h x h2.left h2.right)

/-- C39 b
-/

theorem TypicalForall.cond_imp {p q r: α → Prop} (h : ∀ x, p x → q x → r x) :
  TypicalForall p q → TypicalForall p r := by
  rw [TypicalForall.iff_forall, TypicalForall.iff_forall]
  apply forall_imp
  intro x h2 h3
  exact h x h3 (h2 h3)


/-- C39 c
-/

theorem Iff.cond_cong_texists {p q r: α → Prop} (h : ∀ x, p x → (q x ↔ r x)) :
  TypicalExists p q ↔ TypicalExists p r :=
  Iff.intro
    (TypicalExists.cond_imp (λ x h2 ↦ (h x h2).mp)) 
    (TypicalExists.cond_imp (λ x h2 ↦ (h x h2).mpr))

/-- C39 d
-/

theorem Iff.cond_cong_tforall {p q r: α → Prop} (h : ∀ x, p x → (q x ↔ r x)) :
  TypicalForall p q ↔ TypicalForall p r :=
  Iff.intro
    (TypicalForall.cond_imp (λ x h2 ↦ (h x h2).mp)) 
    (TypicalForall.cond_imp (λ x h2 ↦ (h x h2).mpr))

/-- C40 a
-/
theorem TypicalForall.and_comm {p q r: α → Prop} :
  TypicalForall p (λ x ↦ q x ∧ r x) ↔ (TypicalForall p q ∧ TypicalForall p r) := by
  rw [TypicalForall.iff_forall, TypicalForall.iff_forall, TypicalForall.iff_forall]
  conv =>
    lhs
    intro x
    rw [imp_and_iff_and_imp]
  rw [forall_and_comm]
  exact Iff.refl _

/-- C40 b
-/
theorem TypicalExists.or_comm {p q r: α → Prop} :
  TypicalExists p (λ x ↦ q x ∨ r x) ↔ (TypicalExists p q ∨ TypicalExists p r) := by
  unfold TypicalExists
  conv =>
    lhs
    congr
    intro x
    simp
    rw [And.or_distr]
    rfl
  rw [Exists.or_comm]
  exact Iff.refl _

/-- C41 a
-/

theorem TypicalForall.or_const {p q : α → Prop} {a : Prop}:
  TypicalForall p (λ x ↦ a ∨ q x) ↔ a ∨ TypicalForall p q := by
  rw [TypicalForall.iff_forall, TypicalForall.iff_forall]
  constructor
  · intro h
    rcases (Classical.em a) with ⟨x⟩ | ⟨y⟩
    · exact Or.inl x 
    · apply Or.inr
      intro x h2
      rcases (h x h2) with ⟨h3⟩ | ⟨h3⟩
      · exact absurd h3 y
      · exact h3
  · rintro (⟨h1⟩ | ⟨h2⟩)
    · intros
      exact Or.inl h1
    · intros x h
      exact Or.inr (h2 x h)

/-- C41 b
-/

theorem TypicalExists.and_const {p q : α → Prop} {a : Prop}:
  TypicalExists p (λ x ↦ a ∧ q x) ↔ a ∧ TypicalExists p q := by
  rw [TypicalExists.iff_not_tforall_not, TypicalExists.iff_not_tforall_not]
  unfold Function.comp
  conv =>
    lhs
    congr
    arg 2
    intro x
    rw [not_and_iff_or_not]
    rfl
  conv => 
    rhs
    congr
    · rw [← @Iff.notnot a]
  conv =>
    rhs
    rw [← not_or_iff_and_not]
  apply Iff.cong_not
  exact TypicalForall.or_const

/-- C42 aTypicalForall.iff_forall.mpr h
-/

theorem TypicalForall.tforall_comm {p q : α → Prop} {r : α → α → Prop}:
  TypicalForall p (λ a ↦ TypicalForall q (r a)) ↔
    TypicalForall q (λ b ↦ TypicalForall p (λ a ↦ r a b)) := by
  rw [TypicalForall.iff_forall, TypicalForall.iff_forall]
  conv =>
    congr
    · intro x
      rw [TypicalForall.iff_forall]
    · intro x
      rw [TypicalForall.iff_forall]
  apply Iff.intro
  · intro h1 x h2 y h4
    exact h1 y h4 x h2
  · intro h1 x h2 y h3
    exact h1 y h3 x h2

/-- C42 b
-/

theorem TypicalExists.texists_comm {p q : α → Prop} {r : α → α → Prop}:
  TypicalExists p (λ a ↦ TypicalExists q (r a)) ↔
    TypicalExists q (λ b ↦ TypicalExists p (λ a ↦ r a b)) := by
  rw [TypicalExists, TypicalExists]
  conv =>
    lhs
    congr
    intro
    arg 2
    rw [TypicalExists]
  conv =>
    rhs
    congr
    intro
    arg 2
    rw [TypicalExists]
  constructor
  · rintro ⟨x, ⟨ px, ⟨ y, ⟨ qy, rxy ⟩⟩⟩⟩ 
    constructor
    constructor
    exact qy
    constructor
    constructor
    exact px
    exact rxy
  · rintro ⟨x, ⟨ qx, ⟨ y, ⟨ py, rxy ⟩⟩⟩⟩
    constructor
    constructor
    exact py
    constructor
    constructor
    exact qx
    exact rxy

/-- C42 c
-/

theorem texists_tforall_to_tforall_texists {p : α → Prop} {q : β → Prop}
  {r : α → β → Prop}: TypicalExists p (λ x ↦ TypicalForall q (r x)) → 
  TypicalForall q (λ y ↦ TypicalExists p (λ x ↦ r x y)) := by
  rw [TypicalExists, TypicalForall.iff_forall]
  rintro ⟨x, ⟨px, h ⟩⟩
  intro y qy
  apply TypicalExists.intro px
  exact TypicalForall.apply h qy

/- ## Exercises Chapter 1 
   ### § 4
-/

/-- 1
-/

@[simp] theorem Iff.forall_imp_const {p : α → Prop} {a : Prop}: 
  (∀x, a → p x) ↔ (a → ∀ x, p x) := by 
  constructor
  · exact λ h ha x ↦ h x ha
  · exact λ h ha x ↦ h x ha

/-- 2
-/
theorem Exists.imp_const {p : α → Prop} {a : Prop}
  (h : ∀ x, p x → a) : (∃ x, p x) → a := by
  rintro ⟨x,hx⟩
  exact h x hx

/-- 3 a
-/

theorem forall_forall_apply {p : α → α → Prop} :
 (∀ x, ∀ y, p x y) → ∀ x, p x x := λ h x ↦ h x x

/-- 3 b
-/
theorem Exists.exists_apply {p : α → α → Prop} 
  (h : ∃ x, p x x) : ∃ x, ∃ y, p x y := 
    let ⟨x, hx⟩ := h
    ⟨ x, ⟨x, hx ⟩  ⟩

/-- 4 a
-/
theorem forall_or_imp_forall_or_exists {p q : α → Prop} 
  (h : ∀ x, p x ∨ q x) : ((∀ x, p x) ∨ (∃ x, q x)) := by
  apply (Classical.em (∃ x, q x)).elim
  · exact Or.inr
  · intro nq
    apply Or.inl
    intro x
    apply (h x).elim id
    intro qx
    have eq : ∃ x, q x := ⟨x, qx⟩
    exact absurd eq nq

/-- 4 b
-/
theorem exists_and_forall_imp_exists_and_exists {p q : α → Prop} 
  (h1 : ∃ x, p x) (h2 : ∀ x, q x) : ∃ x, p x ∧ q x := by
  rcases h1 with ⟨x, px⟩
  exact ⟨x, ⟨px, h2 x⟩⟩ 

/-- 5
-/
theorem forall_and_pred [Nonempty α] [Nonempty β]
  {p : α → Prop} {q : β → Prop} : 
  (∀x, ∀y, p x ∧ q y) ↔ ((∀ x, p x) ∧ (∀ y, q y)) := by
  constructor
  · intro f
    constructor
    · intro x 
      exact (f x Classical.ofNonempty).left
    · intro x
      exact (f Classical.ofNonempty x).right
  · intro f x y
    exact ⟨f.left x, f.right y⟩


/-- 6 a
-/

theorem TypicalExists.exists {p q: α → Prop}
  (h : TypicalExists p q) : ∃ x, q x := Exists.imp (λ _ ↦ And.right) h

/-- 6 b
-/

theorem TypicalForall.fromForall {p q : α → Prop} (h : ∀ x, q x):
  TypicalForall p q := by
  rw [TypicalForall.iff_forall]
  intros
  apply h


/-- 7 a
-/
theorem TypicalExists.imp_iff_exists {p q : α → Prop} (h : ∀ x, q x → p x):
 (∃ x, q x) ↔ (TypicalExists p q) := by
  unfold TypicalExists
  apply Iff.cong_exists
  intro x
  constructor
  · simpa using h x
    
/-- 7 b
-/
theorem TypicalForall.imp_not_iff_forall {p q : α → Prop}
  (h : ∀ x, ¬ q x → p x): (∀ x, q x) ↔ (TypicalForall p q) := by
  simp only [iff_forall]
  apply Iff.cong_forall
  intro x 
  constructor
  · exact Function.const _
  · intro f
    have f2 := Function.contrapose f
    apply Classical.rnotnot
    intro nq
    exact absurd (h x nq) (f2 nq)

/-- 7 c
-/
theorem TypicalExists.true_imp_iff_exists (h : ∀ x, p x):
 (∃ x, q x) ↔ (TypicalExists p q) :=
   TypicalExists.imp_iff_exists (λ x _ ↦ h x)
  
/-- 7 d
-/
theorem TypicalForall.true_imp_iff_exists (h : ∀ x, p x):
 (∀ x, q x) ↔ (TypicalForall p q) :=
   TypicalForall.imp_not_iff_forall (λ x _ ↦ h x)

/-- 8
-/
example {p q : α → Prop} (h : p x) : q x → TypicalExists p q
  := TypicalExists.intro h

/-- 9
-/
example {p q : α → Prop} (h : p x) : TypicalForall p q → q x
  := λ a ↦ TypicalForall.apply a h