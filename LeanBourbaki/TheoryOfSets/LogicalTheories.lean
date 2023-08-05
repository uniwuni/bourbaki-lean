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
@[simp] theorem Iff.notnot: (¬ (¬ a)) ↔ a := Iff.intro Classical.rnotnot Function.notnot

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

/-- helper
-/
def Or.and_distl: ((a ∧ b) ∨ c) ↔ ((a ∨ c) ∧ (b ∨ c)) := by
  rw [Or.comm, Or.and_distr, Or.comm, @Or.comm c b]
  exact Iff.refl _

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

/-- C24 m helper 
-/
theorem imp_iff_not_or: (a → b) ↔ (¬ a ∨ b) := by
  rw [Or.iff_not_imp, Iff.notnot]
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

@[simp] theorem imp_and_iff_and_imp {p q r : Prop}:
  (p → (q ∧ r)) ↔ ((p → q) ∧ (p → r)) := by
  constructor
  · intro x 
    exact And.intro (And.left ∘ x) (And.right ∘ x)
  · intro x y
    exact And.intro (x.left y) (x.right y)

@[simp] theorem imp_or_iff_or_imp {p q r : Prop}: (p → (q ∨ r)) ↔ ((p → q) ∨ (p → r)) := by
  constructor
  · intro x
    apply Or.elim (Classical.em p)
    · intro ph
      have xh := x ph
      apply Or.elim xh
      · exact λ y ↦ Or.inl (Function.const _ y)
      · exact λ y ↦ Or.inr (Function.const _ y)
    · intro nph
      apply Or.inl
      exact λ x ↦ absurd x nph
  · intro x
    apply Or.elim x
    · intro h
      exact Or.inl ∘ h
    · intro h
      exact Or.inr ∘ h 

/- ## Exercises Chapter 1 
   ### § 3
-/
/-- 1 a
-/
example: p → (q → p) := λ x _ ↦ x
/-- 1 b
-/
example: (p → q) → (q → r) → p → r := Function.flip_comp
/-- 1 c
-/
example: p → ¬p → q := absurd
/-- 1 d
-/
theorem Or.iff_imp_imp_self: (p ∨ q) ↔ ((p → q) → q) := by
  constructor
  · intro h1 h2
    apply Or.elim h1
    · exact h2
    · exact id    
  · intro h
    apply Or.elim (Classical.em p)
    · exact Or.inl
    · intro np
      exact Or.inr (h (λ x ↦ absurd x np))

/-- 1 e
-/
theorem Iff.iff_both_or_neither: (p ↔ q) ↔ ((p ∧ q) ∨ (¬p ∧ ¬ q)) := by
  constructor
  · intro h
    apply Or.elim (Classical.em p)
    · intro h1
      exact Or.inl (And.intro h1 (h.mp h1))
    · intro h1
      have h2 := Iff.cong_not h
      exact Or.inr (And.intro h1 (h2.mp h1))
  · intro a
    apply Or.elim a 
    · intro b
      exact Iff.intro
            (Function.const _ b.right) (Function.const _ b.left)
    · intro b
      rw [← @Iff.notnot p, ← @Iff.notnot q]
      apply Iff.cong_not
      apply Iff.intro
            (Function.const _ b.right) (Function.const _ b.left)


theorem Iff.true_and_selfl (h : p) : (p ∧ q) ↔ q := by
  constructor
  · exact And.right
  · exact And.intro h

theorem Iff.true_and_selfr (h : q) : (p ∧ q) ↔ p := by
  constructor
  · exact And.left
  · exact λ h2 ↦ And.intro h2 h

/-- 1 f
-/
theorem Iff.iff_not_iff_not: (p ↔ q) ↔ ¬ ((¬ p) ↔ q) := by
  rw [@Iff.iff_both_or_neither p q, @Iff.iff_both_or_neither (¬ p) q]
  rw [not_or_iff_and_not, not_and_iff_or_not, not_and_iff_or_not]
  rw [Iff.notnot, Iff.notnot, Or.and_distr, Or.and_distl, Or.and_distl]
  rw [Iff.true_and_selfl (Classical.em p), Iff.true_and_selfr (Classical.em q)]
  rw [And.comm, @Or.comm q (¬ p)]
  exact Iff.refl _

/-- 1 g
-/
theorem Iff.imp_or_not_and_imp: (p → (q ∨ ¬ r)) ↔ ((r ∧ p) → q) := by
  rw [imp_or_iff_or_imp]
  constructor
  · intro h
    apply Or.elim h
    · intro f
      exact f ∘ And.right 
    · intro f h2
      exact absurd h2.left (f h2.right)
  · intro h
    rw [← imp_or_iff_or_imp]
    intro hp
    apply Or.elim (Classical.em r)
    · intro hr
      exact Or.inl (h (And.intro hr hp))
    · exact Or.inr
/-- 1 h
-/
theorem imp_or_iff_or {p q r : Prop}: (p → (q ∨ r)) ↔ (q ∨ (p → r)) := by
  rw [imp_or_iff_or_imp]
  constructor
  · intro x
    apply Or.elim x
    · intro f
      rw [Or.iff_not_imp]
      exact λ hnq hp ↦ absurd (f hp) hnq
    · exact Or.inr
  · intro x
    apply Or.elim x
    · intro f
      exact Or.inl (Function.const _ f)
    · exact Or.inr

/-- 1 i
-/

theorem And.cond_intro {p q r : Prop}: (p → q) → (p → r) → p → (q ∧ r ) := 
  λ pq pr p ↦ And.intro (pq p) (pr p)

/-- 1 j
-/
example: (p → r) → (q → r) → (p ∨ q) → r := λ pr qr h ↦ h.elim pr qr 

/-- 1 k
-/

theorem And.map_left : (p → q) → p ∧ r → q ∧ r := by
  rintro f ⟨h1, h2⟩
  exact And.intro (f h1) h2

/-- helper
-/

theorem And.map_right : (p → q) → r ∧ p → r ∧ q := by
  rintro f ⟨h1, h2⟩
  exact And.intro h1 (f h2)

/-- 1 l
-/
def Or.map_left (p : a → b) (q : a ∨ c) : b ∨ c := Or.symm (Or.map_right p (Or.symm q))

/-- 2
-/

def not_iff_not_self (h : a ↔ ¬ a) : ¬ a := 
 λ h2 ↦ absurd h2 (h.mp h2)

/- 3a: takes recursion machinery not yet viable
   3b: takes recursion machinery not yet viable
-/

@[simp] def nand p q := (¬ p) ∨ (¬ q)

namespace nand
  /-- 4 a
  -/
  def not_def: ¬ a ↔ nand a a := Iff.symm Or.iff_or_self
  @[simp] def not_def' : nand a a ↔ ¬ a := Iff.symm not_def
  /-- 4 b
  -/
  def or_def: (a ∨ b) ↔ nand (nand a a) (nand b b) := by
    simp
  /-- 4 c
  -/
  def and_def : (a ∧ b) ↔ nand (nand a b) (nand a b) := by
    simp[And.iff_not_or_not]
  /-- 4 d
  -/
  def imp_def : (a → b) ↔ nand a (nand b b) := by
    simp[imp_iff_not_or]
  
end nand

/- 5: meta theorem that cannot be properly stated 
-/

/- Simp lemmas
-/
set_option tactic.simp.trace true
@[simp] theorem imp_self_true: (p → p) ↔ True := by 
  constructor
  · simp
  · exact Function.const _ id 
