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
theorem Classical.rnotnot (h: ¬ a → False) : a := by
  have h1: ¬ a → a := λ x ↦ absurd x h
  have h2: (a ∨ ¬ a) → (a ∨ a) := Or.map_right h1
  exact Or.elim_self (h2 (Classical.em a))

/-- C16 
-/
example: ¬ ¬ a → a := Classical.rnotnot

/-- C17
-/
theorem Classical.rcontrapose (p : ¬ b → ¬ a) (q : a) : b := by
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
theorem And.iff_not_or_not: (a ∧ b) = ¬ (¬ a ∨ ¬ b) := by
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

theorem and_iff_not_or_not_pred {p q : α → Prop}:
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
theorem Iff.notnot: (¬ (¬ a)) ↔ a := Iff.intro Classical.rnotnot Function.notnot

/-- C24 a' for bound variables -/
theorem Iff.notnot_pred {p : α → Prop}: (λ x ↦ ¬ ¬ (p x)) = p := by
  funext
  rw [Iff.notnot]

/-- C24 b
-/
theorem Iff.contrapose: (a → b) ↔ (¬ b → ¬ a) :=
  Iff.intro Function.contrapose Classical.rcontrapose 

/-- C24 b' for bound variables -/

theorem Iff.contrapose_pred {p q : α → Prop} :
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
theorem And.iff_not_right: (a ∧ ¬ b) ↔ ¬ (a → b) := by
  rw [Function.eq_not_or, ← @Iff.notnot b, ← And.iff_not_or_not, Iff.notnot]
  exact Iff.refl _

/-- C24 m
-/
theorem Or.iff_not_imp: (a ∨ b) ↔ (¬ a → b) := by
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
theorem not_and_iff_or_not: (¬ (a ∧ b)) = (¬ a ∨ ¬ b) := by
  rw [← @Iff.notnot (¬ a ∨ ¬ b), And.iff_not_or_not]

/-- CF9 with not applied with free variables
-/
theorem not_and_iff_or_not_pred {p q : α → Prop}:
  (λ x ↦ (¬ (p x ∧ q x))) = (λ x ↦ (¬ p x ∨ ¬ q x)) := by
  funext x
  rw [← @Iff.notnot (¬ p x ∨ ¬ q x), And.iff_not_or_not]


/-- C24 f with not applied
-/
theorem not_or_iff_and_not: (¬ (a ∨ b)) = (¬ a ∧ ¬ b) := by
  rw [← @Iff.notnot (¬ a ∧ ¬ b), Or.iff_not_and_not]

/-- C24f with not applied with free variables
-/
theorem not_or_iff_and_not_pred {p q : α → Prop}:
  (λ x ↦ (¬ (p x ∨ q x))) = (λ x ↦ (¬ p x ∧ ¬ q x)) := by
  funext x
  rw [← @Iff.notnot (¬ p x ∧ ¬ q x), Or.iff_not_and_not]

theorem imp_and_iff_and_iff {p q r : Prop}:
  (p → (q ∧ r)) ↔ ((p → q) ∧ (p → r)) := by
  constructor
  · intro x 
    exact And.intro (And.left ∘ x) (And.right ∘ x)
  · intro x y
    exact And.intro (x.left y) (x.right y)

theorem 