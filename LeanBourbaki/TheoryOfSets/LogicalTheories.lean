import Std.Tactic.RCases

/-!
# Description of Formal Mathematics
## Logical Theories
### The Axioms  
-/

/-- C1
-/
def Function.apply (p : a) (q : a → b) : b := q p


/-- S1
-/
def Or.elim_self (p : a ∨ a) : a := Or.elim p id id

/-- S2
-/
example: a → a ∨ b := Or.inl

/-- S3
-/
def Or.symm (p : a ∨ b) : b ∨ a := Or.elim p Or.inr Or.inl

/-- S4
-/
def Or.map_right (p : a → b) (q : c ∨ a) : c ∨ b := Or.elim q inl (inr.comp p)

/-! ### First Consequences -/

/-- C6
-/
example: (b → c) → (a → b) → a → c := Function.comp

def Function.eq_not_or {a b : Prop} : (a → b) = ((¬ a) ∨ b) :=
  propext (Iff.intro
            (λ x ↦ (Classical.em a).elim (λ y ↦ Or.inr (x y)) Or.inl)
            (λ x ↦ Or.elim x (λ a b ↦ absurd b a) (Function.const a)))

/-- C7
-/
example: b → a ∨ b := Or.inr 

/-- C8
-/
example: a → a := id

/-- C9
-/
example (p : b): a → b := λ _ ↦ p 

/-- C10
-/
example: a ∨ ¬ a := Classical.em a

/-- C11
-/
def Function.notnot: a → ¬ ¬ a := by
  rw [eq_not_or]
  exact (Classical.em (¬ a))

/-- C12
-/
def Function.contrapose (p : a → b) : ¬ b → ¬ a := by
  have h1: (¬ a ∨ b) → (¬ a ∨ ¬ ¬ b) := Or.map_right Function.notnot 
  have h2: ((¬ a ∨ ¬ ¬ b) → (¬ ¬ b ∨ ¬ a)) := Or.symm
  rw [Function.eq_not_or]
  rw [Function.eq_not_or] at p
  exact h2 (h1 p)

/-- C13
-/
def Function.flip_comp (p : a → b): (b → c) → a → c := λ q r ↦ q (p r)  

/-! ### Methods of Proof -/
/-! #### Method of the auxiliary hypothesis -/
/- C14: metatheorem that cannot be meaningfully translated
-/

/-! #### Method of reductio ad absurdum -/
/-- C15
-/
def Classical.rnotnot (h: ¬ a → False) : a := by
  have h1: ¬ a → a := λ x ↦ absurd x h
  have h2: (a ∨ ¬ a) → (a ∨ a) := Or.map_right h1
  exact Or.elim_self (h2 (Classical.em a))

/-- C16 
-/
example: ¬ ¬ a → a := Classical.rnotnot

/-- C17
-/
def Classical.rcontrapose (p : ¬ b → ¬ a) (q : a) : b := by
  apply Classical.rnotnot
  intro r
  exact p r q

/-! #### Method of disjunction of cases -/
/-- C18
-/
example (p : a ∨ b) (q : a → c) (r : b → c) : c := Or.elim p q r

/-! #### Method of the auxiliary constant -/

/-- C19
-/
def Function.apply_implicit {x : α} {a : α → _} (p : a x) (q : (x : α) → a x → b) : b
  := q x p

/-! ### Conjunction -/

/-- CF9
-/
def And.iff_not_or_not: (a ∧ b) = ¬ (¬ a ∨ ¬ b) := by
  apply propext
  apply Iff.intro
  · intro h1 h2
    cases h2 with
    | inl l => exact absurd h1.left l
    | inr r => exact absurd h1.right r  
  · intro h 
    cases Classical.em a with
     | inl h1 => cases Classical.em b with 
                  | inl h3 => exact And.intro h1 h3
                  | inr h4 => exact absurd (Or.inr h4) h
     | inr h2 => cases Classical.em b with 
                  | inl h3 => exact absurd (Or.inl h2) h
                  | inr h4 => exact absurd (Or.inr h4) h

/-- CF9 helper for bound variables -/

def and_iff_not_or_not_pred {p q : α → Prop}:
  (λ x ↦ (p x ∧ q x)) = λ x ↦ ¬ (¬ p x ∨ ¬ q x) := by
  funext
  exact And.iff_not_or_not

/-- C20
-/
example (p : a) (q : b) : a ∧ b := And.intro p q

/-- C21 a
-/
example (p : a ∧ b) : a := by
  rw [And.iff_not_or_not] at p
  have h1: ¬ a → (¬ a ∨ ¬ b) := Or.inl
  have h2: ¬ b → (¬ a ∨ ¬ b) := Or.inr
  have h3: ¬a ∨ ¬b → (¬ (a ∧ b)) := by
    rw [And.iff_not_or_not]
    exact Function.notnot
  have h4: ¬ a → ¬ (a ∧ b) := h3 ∘ Or.inl
  apply Classical.rcontrapose h4
  rw [←And.iff_not_or_not] at p
  exact p


/-- C21 b
-/
example (p : a ∧ b) : b := by
  rw [And.iff_not_or_not] at p
  have h1: ¬ a → (¬ a ∨ ¬ b) := Or.inl
  have h2: ¬ b → (¬ a ∨ ¬ b) := Or.inr
  have h3: ¬a ∨ ¬b → (¬ (a ∧ b)) := by
    rw [And.iff_not_or_not]
    exact Function.notnot
  have h4: ¬ b → ¬ (a ∧ b) := h3 ∘ Or.inr
  apply Classical.rcontrapose h4
  rw [←And.iff_not_or_not] at p
  exact p

/-! ### Equivalence -/
/-- CF10
-/
def Iff.iff_and_imp: (a ↔ b) = ((a → b) ∧ (b → a)) := by
  apply propext
  apply Iff.intro
  · exact (λ p ↦ And.intro p.mp p.mpr)
  · exact (λ p ↦ Iff.intro p.left p.right)

/-- C22 a
-/
example (h : a ↔ b) : b ↔ a := Iff.symm h

/-- C22 b
-/
example (h1 : a ↔ b) (h2 : b ↔ c) : a ↔ c := Iff.trans h1 h2

section

  variable (h1 : a ↔ b) 
  /-- C23 a
  -/
  def Iff.cong_not: ¬ a ↔ ¬ b := by
    apply Iff.intro
    · exact Function.contrapose h1.mpr
    · exact Function.contrapose h1.mp

  /-- C23 b
  -/
  def Iff.cong_impl: (a → c) ↔ (b → c) := by
    apply Iff.intro
    · exact Function.flip_comp h1.mpr
    · exact Function.flip_comp h1.mp

  /-- C23 c
  -/
  def Iff.cong_impr: (c → a) ↔ (c → b) := by
    apply Iff.intro
    · exact Function.comp h1.mp
    · exact Function.comp h1.mpr

  /-- C23 d
  -/
  def Iff.cong_andl: (a ∧ c) ↔ (b ∧ c) := by
    apply Iff.intro
    · exact λ x ↦ And.intro (h1.mp x.left) x.right
    · exact λ x ↦ And.intro (h1.mpr x.left) x.right

  /-- C23 e
  -/
  def Iff.cong_orl: (a ∨ c) ↔ (b ∨ c) := by
    apply Iff.intro
    · exact λ p ↦ Or.elim p (Or.inl ∘ h1.mp) Or.inr
    · exact λ p ↦ Or.elim p (Or.inl ∘ h1.mpr) Or.inr
  
end

/-- C24 a
-/
def Iff.notnot: (¬ (¬ a)) ↔ a := Iff.intro Classical.rnotnot Function.notnot

/-- C24 a' for bound variables -/
def Iff.notnot_pred {p : α → Prop}: (λ x ↦ ¬ ¬ (p x)) = p := by
  funext
  rw [Iff.notnot]

/-- C24 b
-/
def Iff.contrapose: (a → b) ↔ (¬ b → ¬ a) :=
  Iff.intro Function.contrapose Classical.rcontrapose 

/-- C24 b' for bound variables -/

def Iff.contrapose_pred {p q : α → Prop} :
  (λ x ↦ p x → q x) = (λ x ↦ ¬ q x → ¬ p x) := by
  funext
  rw [Iff.contrapose]

/-- C24 c
-/
def And.iff_and_self: (a ∧ a) ↔ a := by simp

/-- C24 d
-/
example: (a ∧ b) ↔ (b ∧ a) := And.comm

/-- C24 e
-/
def And.assoc: (a ∧ (b ∧ c)) ↔ ((a ∧ b) ∧ c) :=
  Iff.intro (λ x ↦ And.intro (And.intro x.left x.right.left) x.right.right)
            (λ x ↦ And.intro x.left.left (And.intro x.left.right x.right))

/-- C24 f
-/
def Or.iff_not_and_not: (a ∨ b) ↔ ¬(¬a ∧ ¬ b) := Iff.intro
  (λ x y ↦ Or.elim x y.left y.right)
  (λ x ↦ Classical.rnotnot
    (λ y ↦ x (And.intro (y ∘ Or.inl) (y ∘ Or.inr))))

/-- C24 g
-/  
def Or.iff_or_self: (a ∨ a) ↔ a := by simp

/-- C24 h
-/
def Or.comm: (a ∨ b) ↔ (b ∨ a) := Iff.intro Or.symm Or.symm

/-- C24 i
-/
def Or.assoc: (a ∨ (b ∨ c)) ↔ ((a ∨ b) ∨ c) := by
  apply Iff.intro
  · intro h 
    cases h with
    | inl h1 => exact Or.inl (Or.inl h1)
    | inr h2 => cases h2 with
                 | inl h3 => exact Or.inl (Or.inr h3)
                 | inr h4 => exact Or.inr h4
  · intro h 
    cases h with
    | inl h1 => cases h1 with
                 | inl h2 => exact Or.inl h2
                 | inr h3 => exact Or.inr (Or.inl h3)
    | inr h4 => exact Or.inr (Or.inr h4)

/-- C24 j
-/
def And.or_distr: (a ∧ (b ∨ c)) ↔ ((a ∧ b) ∨ (a ∧ c)) := by
  apply Iff.intro
  · intro h
    cases h.right with
    | inl h1 => exact Or.inl (And.intro h.left h1) 
    | inr h2 => exact Or.inr (And.intro h.left h2)
  · intro h
    cases h with
    | inl h1 => exact And.intro h1.left (Or.inl h1.right)
    | inr h2 => exact And.intro h2.left (Or.inr h2.right)

/-- C24 k
-/
def Or.and_distr: (a ∨ (b ∧ c)) ↔ ((a ∨ b) ∧ (a ∨ c)) := by
  apply Iff.intro
  · intro h
    cases h with
    | inl h1 => exact And.intro (Or.inl h1) (Or.inl h1) 
    | inr h2 => exact And.intro (Or.inr h2.left) (Or.inr h2.right) 
  · intro h
    cases h.left with
    | inl h1 => exact inl h1
    | inr h2 => cases h.right with
                | inl h3 => exact inl h3
                | inr h4 => exact inr (And.intro h2 h4)

/-- C24 l
-/ 
def And.iff_not_right: (a ∧ ¬ b) ↔ ¬ (a → b) := by
  rw [Function.eq_not_or, ← @Iff.notnot b, ← And.iff_not_or_not, Iff.notnot]
  exact Iff.refl _

/-- C24 m
-/
def Or.iff_not_imp: (a ∨ b) ↔ (¬ a → b) := by
  rw [Function.eq_not_or, @Iff.notnot a]
  exact Iff.refl _

/-- C25 a
-/
def iff_and_with_true (h : a): (a ∧ b) ↔ b := by
  apply Iff.intro
  · exact And.right 
  · exact And.intro h

/-- C25 b
-/
def iff_or_with_false (h : ¬ a): (a ∨ b) ↔ b := by
  apply Iff.intro
  · exact λ x ↦ Or.elim x (λ y ↦ absurd y h) id
  · exact Or.inr

/-- CF9 with not applied
-/
def not_and_iff_or_not: (¬ (a ∧ b)) = (¬ a ∨ ¬ b) := by
  rw [← @Iff.notnot (¬ a ∨ ¬ b), And.iff_not_or_not]

/-- CF9 with not applied with free variables
-/
def not_and_iff_or_not_pred {p q : α → Prop}:
  (λ x ↦ (¬ (p x ∧ q x))) = (λ x ↦ (¬ p x ∨ ¬ q x)) := by
  funext x
  rw [← @Iff.notnot (¬ p x ∨ ¬ q x), And.iff_not_or_not]


/-- C24 f with not applied
-/
def not_or_iff_and_not: (¬ (a ∨ b)) = (¬ a ∧ ¬ b) := by
  rw [← @Iff.notnot (¬ a ∧ ¬ b), Or.iff_not_and_not]

/-- C24f with not applied with free variables
-/
def not_or_iff_and_not_pred {p q : α → Prop}:
  (λ x ↦ (¬ (p x ∨ q x))) = (λ x ↦ (¬ p x ∧ ¬ q x)) := by
  funext x
  rw [← @Iff.notnot (¬ p x ∧ ¬ q x), Or.iff_not_and_not]



/-
## Quantified Theories
### Definition of Quantifiers
-/

@[inherit_doc] notation:30 "τ" p:40 => Classical.epsilon p

/-- CF11 a
-/

def Exists.iff_true_epsilon [Nonempty α] {p : α → Prop}:
  (∃ x, p x) ↔ p (τ p) := by
  apply Iff.intro
  · intro h
    exact Classical.epsilon_spec h
  · intro h
    exact Exists.intro _ h

/-- CF11 b
-/
def forall_iff_not_exists_not {p : α → Prop} : (∀ x, p x) ↔ ¬ ∃ x, ¬ (p x) := by
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

def forall_iff_false_epsilon [Nonempty α] {p : α → Prop}:
  (∀ x, p x) ↔ p (τ (Not ∘ p)) := by
  rw [forall_iff_not_exists_not, Exists.iff_true_epsilon, Iff.notnot]
  unfold Function.comp
  exact Iff.refl _
  
/- C27: metatheorem that cannot be meaningfully translated
-/

/-- C28 
-/     

def not_forall_iff_exists_not {p : α → Prop} : ¬(∀ x, p x) ↔ ∃ x, ¬ (p x) := by
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
def not_exists_iff_forall_not {p : α → Prop} : ¬(∃ x, p x) ↔ (∀ x, ¬ p x) := by
  rw [← @Iff.notnot (∀ x, ¬ p x),
      @not_forall_iff_exists_not _ (λ a ↦ ¬ p a),
      Iff.notnot_pred]
  exact Iff.refl _

/-- C29' + C11 helper -/
def Exists.iff_not_forall_not {p : α → Prop} : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
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
@[simp] def Exists.and_const {a : Prop} {p : α → Prop} :
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

def Exists.exists_comm {p : α → α → Prop} : (∃ x, ∃ y, p x y) ↔ (∃ y, ∃ x, p x y) := by
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
