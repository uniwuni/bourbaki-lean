import LeanBourbaki.TheoryOfSets.EqualitarianTheories
import Std.Classes.SetNotation
/-#
# Theory of Sets
## Collectivizing Relations
### The Theory of Sets
-/
class WeakSetModel (o : Type u) extends Membership o o where
  /-- A 1 
  -/
  model_nonempty : Nonempty o
  /-- A 2
  -/
  extent : ∀ {x y},
    (∀ z : o, z ∈ x → z ∈ y) → (∀ z : o, z ∈ y → z ∈ x) → x = (y : o)
  pair_exists: ∀ x y, ∃ z, ∀ w, (w: o) ∈ (z: o) ↔  w = x ∨ w = y

  selection_union {r : o → o → Prop} : (∀ y, ∃ X, ∀ x, r x y → x ∈ (X : o)) →
    ∀ Y, ∃ z, ∀ x, x ∈ (z : o) ↔ (∃ y, y ∈ (Y: o) ∧ r x y)
  powerset_exists: ∀ X : o, ∃ Y : o, ∀ z : o, z ∈ Y ↔ (∀ w, w ∈ z → w ∈ X)


namespace WeakSetModel
variable {o : Type u}
variable [WeakSetModel o]
instance nonempty_model: Nonempty o := model_nonempty
/-
### Inclusion
-/
/-- Definition 1
-/
instance set_model_subset: HasSubset o where
  Subset x y := ∀ z, z ∈ x → z ∈ y

/-- Proposition 1
-/
@[simp] theorem Subset.refl {x : o}: x ⊆ x := λ _ y ↦ y

/-- Proposition 2
-/
theorem Subset.trans {x y z : o} (h1 : x ⊆ y) (h2 : y ⊆ z) : x ⊆ z :=
  λ w wx ↦ h2 w (h1 w wx)

theorem Subset.in_both_iff_inr {x y : o} :
  (∀ z : o, (z ∈ y ∧ z ∈ x) ↔ z ∈ x) ↔ x ⊆ y := by
  constructor
  · intro h z zx
    exact ((h z).mpr zx).left
  · intro h z
    constructor
    · exact And.right
    · exact λ zx ↦ ⟨h z zx, zx⟩

theorem Subset.iff {x y : o}: x ⊆ y ↔ (∀ z : o, z ∈ x → z ∈ y) := by
   unfold Subset set_model_subset
   simp

theorem Subset.from {x y : o} (h : ∀ z, z ∈ x → z ∈ y) : x ⊆ y := by
  rw [Subset.iff]
  exact h

/-
### The Axiom of Extent
-/
/-- A1 restated
-/

theorem extent_subset {x y : o} (h1 : x ⊆ y) (h2 : y ⊆ x) : x = y :=
  extent h1 h2

@[ext]
theorem eq_of_iff_elem {x y : o} (h1 : ∀ z, z ∈ x ↔ z ∈ y) : x = y := by
  apply extent_subset
  · exact λ z ↦ (h1 z).mp
  · exact λ z ↦ (h1 z).mpr

theorem eq_iff_iff {x y : o} : (x = y) ↔ (∀ w, w ∈ x ↔ w ∈ y) := by
  constructor
  · intro h w
    simp[h]
  · intro h
    apply extent
    · exact λ z ↦ (h z).mp
    · exact λ z ↦ (h z).mpr

theorem eq_iff_subset_subset {x y : o}: x = y ↔ (x ⊆ y ∧ y ⊆ x) := by
  rw[eq_iff_iff]
  unfold Subset set_model_subset
  rw[← forall_and_comm]
  conv =>
    congr
    ext
    rw[Iff.iff_and_imp]
  
/-- C48
-/
theorem element_single_valued {R : o → Prop}: is_single_valued_predicate
  (λ (y:o) ↦ ∀ x, ((x ∈ y) ↔ R x)) where
  sv := by
    intros y z ry rz
    rw [eq_iff_iff]
    apply forall_iff_cancelr ry rz

/-
### Collectivizing Relations
-/
class is_collectivizing (R : o → Prop) : Prop :=
  prf : ∃ (y:o), ∀ x, ((x ∈ y) ↔ R x)

noncomputable def is_collectivizing.set (R : o → Prop) [is_collectivizing R] : o :=
  τ (λ y ↦ ∀ x, ((x ∈ y) ↔ R x))

noncomputable abbrev collect (R : o → Prop) [is_collectivizing R] : o :=
  is_collectivizing.set R

@[simp] theorem is_collectivizing.in_set_iff {R : o → Prop} [h : is_collectivizing R]
  {x : o}: x ∈ is_collectivizing.set R ↔ R x := by
  unfold is_collectivizing.set
  have h3: ∀ (x : o), x ∈ (τ λ (y:o) ↦ ∀ (x : o), x ∈ y ↔ R x) ↔ R x := by
      apply @Classical.epsilon_spec _ (λ y ↦ ∀x, x ∈ y ↔ R x)
      apply @is_collectivizing.prf _ _ _ h
  rw [h3 x]
  

/-- Example 1
-/

instance elem.is_collectivizing {y : o} : is_collectivizing (λ x ↦ (x : o) ∈ (y : o)) where
  prf := ⟨y, by simp⟩

@[simp] theorem elem.is_collectivizing_set_self {y : o}:
  is_collectivizing.set (λ x ↦ (x : o) ∈ (y : o)) = y := by
  ext
  simp

/-- Example 2
-/

theorem self_not_elem_not_collectivizing: ¬ is_collectivizing (λ x : o ↦ x ∉ x) := by
  intro h
  let a := @is_collectivizing.set o _ (λ x ↦ x ∉ (x:o)) h
  rcases Classical.em (a ∈ a) with ⟨i⟩ | ⟨ni⟩
  · have j := i
    rw[is_collectivizing.in_set_iff] at i
    exact i j
  · have nj := ni
    rw[is_collectivizing.in_set_iff] at ni
    exact ni nj


/-- C49
-/
instance is_functional_of_collectivizing [is_collectivizing R]: is_functional_predicate
  (λ y : o ↦ ∀ x : o, x ∈ y ↔ R x) where
  sv y z eqy eqz := by
    apply eq_of_iff_elem
    exact forall_iff_cancelr eqy eqz    
  exs := ⟨is_collectivizing.set R, λ x ↦ is_collectivizing.in_set_iff⟩

theorem collectivizes_iff_in_collection_iff [Nonempty o]: 
  is_collectivizing R ↔ (∀ x, (x ∈ (τ (λ y : o ↦ ∀ x : o, ((x ∈ y) ↔ R x)))) ↔ R x) := by
  constructor
  · intro h
    apply is_collectivizing.in_set_iff
  · intro h
    constructor
    exists τ fun y => ∀ (x : o), x ∈ y ↔ R x

/-- C50 a
-/
@[simp] theorem collectivizes_set_subset_iff_imp {R S : o → Prop}
  [is_collectivizing R] [is_collectivizing S]:
  is_collectivizing.set R ⊆ is_collectivizing.set S ↔
  (∀ x, R x → S x) := by
  constructor
  · intro h x rx
    specialize h x
    simp only [is_collectivizing.in_set_iff] at h 
    exact h rx
  · intro h x collx
    specialize h x
    rw [is_collectivizing.in_set_iff]
    rw [is_collectivizing.in_set_iff] at collx
    exact h collx
  
/-- C50 b
-/
@[simp] theorem collectivizes_set_eq_iff_iff {R S : o → Prop}
  [is_collectivizing R] [is_collectivizing S]:
  is_collectivizing.set R = is_collectivizing.set S ↔
  (∀ x, R x ↔ S x) := by
  constructor
  · intro h x
    rw [eq_iff_subset_subset] at h
    simp at h
    rw [← forall_and_comm] at h
    specialize h x
    rw[← Iff.iff_and_imp] at h
    exact h
  · intro h
    ext z
    simp only [is_collectivizing.in_set_iff]
    exact h z

/-
### The Axiom of the Set of Two Elements
-/

instance unordered_pair_collectivizes {x y : o}: is_collectivizing
  (λ z ↦ z = x ∨ z = y) where
  prf := pair_exists x y

/-- Definition 2
-/

noncomputable def unordered_pair (x y : o) := is_collectivizing.set
  (λ z ↦ z = x ∨ z = y) 

@[simp] theorem unordered_pair.elem_iff {x y z : o}:
  z ∈ unordered_pair x y ↔ (x = z ∨ y = z) := by
  rw[unordered_pair,is_collectivizing.in_set_iff]
  simp

@[simp] theorem unordered_pair.comm {x y : o} : unordered_pair x y = unordered_pair y x := by
  ext z
  simp

@[simp] theorem unordered_pair.exists_with {r : o → Prop} :
  (∃z:o, z ∈ unordered_pair x y ∧ r z) ↔ (r x ∨ r y) := by
  simp only [elem_iff]
  rw[Exists.iff_and_orl]
  simp

@[simp] theorem unordered_pair.forall_with {r : o → Prop} :
  (∀z:o, z ∈ unordered_pair x y → r z) ↔ (r x ∧ r y) := by
  simp
  rw[forall_and_comm]
  simp
    

noncomputable instance set_singleton: Singleton o o where
   singleton (x : o) := unordered_pair x x

@[simp] theorem singleton.elem_iff {x y : o}:
  (y : o) ∈ (singleton x : o) ↔ y = x := by
  rw[singleton,set_singleton]
  simp

@[simp] theorem singleton_set.subset_iff {x y : o}:
  singleton x ⊆ y ↔ x ∈ y := by
  simp[Subset]

/-- S8
-/

theorem scheme_selection_union {r : o → o → Prop} : (∀ y, ∃ X, ∀ x, r x y → x ∈ (X : o)) →
    ∀ Y : o, is_collectivizing (λ x ↦ ∃ y, y ∈ Y ∧ r x y) := by
    intro h Y
    constructor
    apply selection_union h

/-- C51
-/
instance restriction_collectivizes {a : o} {p : o → Prop} : 
  is_collectivizing (λ x ↦ p x ∧ x ∈ a) := by
  have h2: is_collectivizing (λ x ↦ ∃ y, y ∈ a ∧ (p x ∧ x = y)) := by
    apply scheme_selection_union
    intro y
    exists singleton y
    intros x h
    simp[h]
  conv at h2 =>
    congr
    ext x
    congr
    · ext y
      rw[And.comm,@And.comm (p x) (x = y)]
      rw[← And.assoc,]
  conv at h2 =>
    congr
    ext x
    rw [Exists.and_eq_iff_selfll]
  exact h2

noncomputable instance set_model.separation: Sep o o where 
  sep p a := is_collectivizing.set (λ x ↦ p x ∧ x ∈ a)


open Std.ExtendedBinder in
syntax "{" extBinder " | " term "}" : term

binder_predicate x " ∈ " y:term => `($x ∈ $y)
macro_rules
  | `({ $x:ident ∈ $t | $p }) => `(Sep.sep (fun $x:ident ↦ $p) $t)
@[app_unexpander Sep.sep]
def Sep.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a $t) => 
    match a with
    | `(fun $x:ident => $p) => `({ $x:ident ∈ $t | $p })
    | _ => throw ()
  | _ => throw ()

 

@[simp] theorem elem_sep_iff_elem_and_holds {p : o → Prop} {a x : o} :
  x ∈ {y ∈ a | p y} ↔ (x ∈ a ∧ p x) := by
  unfold Sep.sep
  unfold set_model.separation
  simp only [is_collectivizing.in_set_iff, And.comm]

/-- C52 
-/

theorem subclass_of_set_collectivizes {r : o → Prop} {a : o}
  (h : ∀ x, r x → x ∈ a): is_collectivizing r :=
  by
  have h2 := @restriction_collectivizes o _ a r
  have eq : (λ x ↦ r x ∧ x ∈ a) = r := by
    ext x
    constructor
    · exact And.left
    · exact λ r ↦ ⟨r, h x r⟩
  rwa[← eq]


theorem subclass_of_collectivizes_collectivizes {r s : o → Prop}
  [inst : is_collectivizing r] (h : ∀x, s x → r x) : is_collectivizing s := by
  apply subclass_of_set_collectivizes (a := is_collectivizing.set r)
  simpa

theorem subclass_of_collectivizes_subset {r s : o → Prop}
  [is_collectivizing r] (h : ∀x, s x → r x) :
   @is_collectivizing.set _ _ _ (subclass_of_collectivizes_collectivizes h) ⊆ is_collectivizing.set r  := by
   have _i := (subclass_of_collectivizes_collectivizes h)
   rw [collectivizes_set_subset_iff_imp]
   exact h

/-- C53
-/

instance restriction_to_terms_collectivizes {a : o} {t : o → o}
  : is_collectivizing (λ y ↦ ∃ x, y = t x ∧ x ∈ a) := by
  let r x y := y = t x
  have h: ∀ x, ∃ X : o, ∀ y, r x y → y ∈ X := by
    intro x
    exists {t x}
    intro y rxy
    simp[*]
  have h2: is_collectivizing λ y ↦ ∃ x, x ∈ a ∧ r x y := scheme_selection_union h _
  simp only [And.comm] at h2 
  exact h2

noncomputable def funcSep (a : o) (t : o → o) (r : o → Prop) : o :=
  (is_collectivizing.set (λ y ↦ ∃ x, y = t x ∧ x ∈ Sep.sep r a))

noncomputable def funcSep' (a : o) (t : o → o) : o :=
  funcSep a t (λ _ ↦ True)


open Std.ExtendedBinder in
syntax "{" term " | " extBinder ", " term "}" : term
open Std.ExtendedBinder in
syntax "{" term " || " extBinder "}" : term
macro_rules 
  | `({ $f | $x:ident ∈ $t , $p }) => `(funcSep $t (fun $x:ident ↦ $f) (fun $x:ident ↦ $p))
  | `({ $f || $x:ident ∈ $t }) => `(funcSep' $t (fun $x:ident ↦ $f))

@[app_unexpander funcSep]
def funcSep.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a $t $r) => 
    match t with
    | `(fun $_:ident => $f) =>
      match r with
      | `(fun $x:ident => $p) => `({ $f | $x:ident ∈ $a , $p })
      | _ => throw ()
    | _ => throw ()
  | _ => throw ()
@[app_unexpander funcSep']
def funcSep'.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a $t) => 
    match t with
    | `(fun $x:ident => $f) => `({ $f || $x:ident ∈ $a })
    | _ => throw ()
  | _ => throw ()



@[simp] theorem funcSep.elem {t : o → o} {p : o → Prop} {y a : o}:
  y ∈ {t x | x ∈ a, p x} ↔ (∃x, y = t x ∧ x ∈ a ∧ p x) := by
  unfold funcSep
  rw[is_collectivizing.in_set_iff]
  simp

@[simp] theorem funcSep'.elem {t : o → o} {y a : o}:
  y ∈ {t x || x ∈ a} ↔ (∃x, y = t x ∧ x ∈ a) := by
  unfold funcSep'
  simp

/-
### Complement of a Set. The Empty Set
-/

noncomputable def set_difference (x y : o) : o := {z ∈ x | z ∉ y}

@[simp] theorem set_difference.elem {x y z : o} : z ∈ set_difference x y ↔ (z ∈ x ∧ z ∉ y) := by
  unfold set_difference
  simp

theorem set_difference.nelem {x y z : o} (h : y ⊆ x): (z ∈ x ∧ z ∉ set_difference x y) ↔ (z ∈ y) := by
  unfold set_difference
  simp[not_and_iff_or_not]
  exact h z

theorem set_difference.self_inverse_of_subset {x y : o} (h : y ⊆ x)
  : set_difference x (set_difference x y) = y := by
  unfold set_difference
  ext z
  specialize h z
  simpa [not_and_iff_or_not]

@[simp] theorem set_difference.reverse_subset {x a b : o} (h1 : a ⊆ x):
  (set_difference x b ⊆ set_difference x a) ↔ a ⊆ b := by
  rw [Subset.iff, Subset.iff]
  apply Iff.cong_forall
  intro z
  simp only [set_difference.elem]
  constructor
  · intro h ha
    apply @Classical.byCases (z ∈ b) _ id
    intro nb
    specialize h (And.intro (h1 _ ha) nb)
    exact absurd ha h.right
  · intro h hX
    have h3:= Function.contrapose h
    exact And.intro hX.left (h3 hX.right)
/-- Theorem 1
-/
instance empty_relation_functional: is_functional_predicate λ y : o ↦ ∀ x, x ∉ y where
  sv := by
    intro y z hy hz
    ext w
    specialize hy w
    specialize hz w
    simp[*]

  exs := by
    exists (set_difference Classical.ofNonempty Classical.ofNonempty)
    intro x
    simp only [set_difference.elem]
    intro h
    exact absurd h.left h.right

noncomputable def empty_set : o := τ (λ y : o ↦ ∀ x : o, x ∉ y)

theorem empty_set.nelem : ∀ x, (x : o) ∉ (empty_set : o) := by
  rw[empty_set]
  apply Classical.epsilon_spec_functional (λ y : o ↦ ∀ x : o, x ∉ y)

@[simp] theorem empty_set.elem (x : o): x ∈ (empty_set : o) ↔ False := by
  simp only [iff_false, empty_set.nelem]

@[simp] theorem empty_set.subset_all (x : o) : empty_set ⊆ x := by
  apply Subset.from
  simp only [elem, false_implies, implies_true]

@[simp] theorem set_difference.of_self: set_difference x x = (empty_set : o) := by
  ext y
  simp

@[simp] theorem set_difference.of_empty: set_difference x empty_set = (x : o) := by
  ext y
  simp
@[simp] theorem empty_set.subset_empty (x : o): (x ⊆ empty_set) ↔ x = empty_set := by
  constructor
  · intro h
    ext z
    simp only [Subset.iff, elem] at h
    simp only [elem, iff_false]
    intro hz
    exact h _ hz
  · intro h
    simp [h]
 
 theorem empty_set.eq (x : o): x = empty_set ↔ ¬(∃ y : o, y ∈ x) := by
  constructor
  · intro h
    simp only [h, elem, not_exists_iff_forall_not, implies_true]
  · intro h
    ext y
    simp only [elem, iff_false]
    rw[not_exists_iff_forall_not] at h
    specialize h y
    exact h
     
   

theorem empty_set.vacuous_true (r : o → Prop): ∀ x, x ∈ (empty_set : o) → r x := 
  by simp

theorem no_full_set (X : o): ¬ ∀ x:o, x ∈ X := by
  intro h
  let y := {x ∈ X | x ∉ x}
  have h2 := @elem.is_collectivizing _ _ y
  apply @self_not_elem_not_collectivizing o _
  simp only [elem_sep_iff_elem_and_holds, h, true_and] at h2
  exact h2

@[simp] theorem empty_set.neq {x : o}: x ≠ empty_set ↔ ∃ y : o, y ∈ x := by
  rw[Exists.iff_not_forall_not]
  apply Iff.cong_not
  simp only [eq, not_exists_iff_forall_not]

    
/-
## Exercises
-/

/-- 1
-/
theorem eq_if_in_same {x y : o}: (x = y) ↔ (∀X : o, x ∈ X → y ∈ X) := by
  constructor
  · intro h 
    simp[h]
  · intro h
    specialize h (singleton x) (by simp)
    simp only [singleton.elem_iff, Eq.symm_iff] at h 
    exact h

/-- 2 a
-/

@[simp] theorem singleton_neq_empty {x : o}: empty_set ≠ ({x} : o) := by
  rw [Ne,eq_iff_iff]
  intro h
  simp at h

/-- 2 b
-/
theorem two_different_sets: ∃ x, ∃ y:o, x ≠ y := by
  exists empty_set
  exists {empty_set}
  simp

@[simp] theorem set_difference.subset {a x : o} :
  (set_difference x a ⊆ x) := by
  apply Subset.from
  intro z h2
  simp only [set_difference.elem] at h2 
  exact h2.left

/-- 3 a
-/
theorem subset_difference_iff_swapped {a b x : o} (ha : a ⊆ x) (hb : b ⊆ x):
  (b ⊆ set_difference x a) ↔ (a ⊆ set_difference x b) := by
  rw[Subset.iff, Subset.iff]
  conv =>
    lhs
    ext z
    rw[set_difference.elem, imp_and_iff_and_imp]
    rw[Iff.true_and_selfl (hb z)]
  conv => 
    rhs  
    ext z
    rw[set_difference.elem, imp_and_iff_and_imp]
    rw[Iff.true_and_selfl (ha z)]
  apply Iff.cong_forall
  intro x
  constructor
  · intro h
    apply Classical.rcontrapose
    rw [Iff.notnot]
    exact h
  · intro h
    apply Classical.rcontrapose
    rw [Iff.notnot]
    exact h
/-- 3 b
-/
theorem difference_subset_if_swapped {a b x : o} (ha : a ⊆ x) (hb : b ⊆ x):
  (set_difference x b ⊆ a) ↔ (set_difference x a ⊆ b) := by
  rw[← set_difference.self_inverse_of_subset ha,]
  rw[subset_difference_iff_swapped]
  rw[set_difference.self_inverse_of_subset ha]
  rw[set_difference.self_inverse_of_subset hb]
  · simp
  · simp
/-- 4
-/
@[simp] theorem singleton.subset {X x : o}:
  (X ⊆ {x}) ↔ (X = {x} ∨ X = empty_set) := by
  constructor
  · intro h
    by_cases h2 : x ∈ X 
    · apply Or.inl
      ext z
      simp
      constructor
      · intro h3  
        specialize h z h3
        simp only [elem_iff, Eq.symm_iff] at h 
        exact h
      · intro h3
        rwa[h3] at h2
    · apply Or.inr
      rw [empty_set.eq]
      rintro ⟨y, hy⟩
      specialize h y hy
      simp only [elem_iff, Eq.symm_iff] at h
      rw [h] at h2 
      exact absurd hy h2
  · rintro ⟨h⟩
    · simp[h]
    · simp[*]
/-- 5
-/
theorem empty_set.eq_epsilon_epsilon:
  (empty_set : o) = (τ (λ X ↦ (τ λ x ↦ (x ∈ X)) ∉ X)) := by
  ext z
  simp only [elem, false_iff]
  intro h
  have h3: ∀ X:o, ¬(τ fun x => x ∈ X) ∈ X → ∀x:o, x ∉ X  := by
    intro X h4 x xX
    have exs: ∃ x, x ∈ X := by exists x
    have h5 := Classical.epsilon_spec exs
    exact absurd h5 h4
  have h6: ∀ X:o, ¬(τ fun x => x ∈ X) ∈ X ↔ ∀x:o, x ∉ X  := by
    intro X
    constructor
    · exact h3 X
    · intro emp
      rw [← not_exists_iff_forall_not, ←empty_set.eq] at emp
      simp [emp]

  specialize h3 (τ fun X => ¬(τ fun x => x ∈ X) ∈ X) ?new z
  · intro h4
    conv at h4 =>
      right
      congr
      ext y
      rw[h6 _]
    rw[← empty_set] at h4
    simp only [elem] at h4 
  · exact absurd h h3
  
end WeakSetModel
/-- 6
-/
theorem alternate_extent [Nonempty p] {r : p → p → Prop}
  (h : ∀ y:p, y = (τ (λ x ↦ ∀ z, r z x ↔ r z y)))
  (x y : p)
  (xy : ∀ z:p, r z x ↔ r z y):
  x = y := by
  rw [h x, h y]
  congr
  ext a
  apply Iff.cong_forall
  intro z
  specialize xy z
  rw [xy]
  

    
