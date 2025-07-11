import Mathlib.Logic.ExistsUnique
import Init.Classical
import Mathlib.Tactic

namespace SetUniverse
  open Classical
  universe u
  variable {U : Type u}

  /-! ### Clase (sin 'class' ni 'structure') que representa pertenencia estensional entre conjuntos ### -/

  /-! ### Introducción de la pertenencia a un conjunto como símbolo primitivo ### -/
  -- Definición axiomática de pertenencia: x pertenece a y
  -- Aquí, 'x' es un elemento y 'y' es un conjunto
  -- Esta definición es intencionalmente abstracta para permitir la flexibilidad en la implementación
  -- de conjuntos en Lean.
  axiom mem (x y : U) : Prop

  /-! ### Notación estándar de la pertenecia a conjuntos ### -/
  notation:50 lhs:51 " ∈ " rhs:51 => mem lhs rhs
  notation:50 lhs:51 " ∉ " rhs:51 => ¬(lhs ∈ rhs)

  /-! ### Axioma de extensionalidad de conjuntos ### -/
  /-! ### ExtSet : x = y ↔ ∀ z, z ∈ x ↔ z ∈ y ### -/
  axiom ExtSet (x y : U): (∀ (z: U), z ∈ x ↔ z ∈ y) → (x = y)

  theorem ExtSetReverse (x y : U) :
    (x = y) → (∀ (z: U), z ∈ x ↔ z ∈ y)
      := by
    intro h_eq
    intro z
    constructor
    · -- Dirección ->
      intro hz_in_x
      rw [h_eq] at hz_in_x
      exact hz_in_x
    · -- Dirección <-
      intro hz_in_y
      rw [← h_eq] at hz_in_y
      exact hz_in_y

  theorem ExtSet_wc {x y : U} (h_x_subs_y: ∀ (z: U), z ∈ x → z ∈ y) (h_y_subs_x: ∀ (z: U), z ∈ y → z ∈ x) :
    (x = y) := by
    apply ExtSet
    intro z
    constructor
    · -- Dirección ->
      intro hz_in_x
      apply h_x_subs_y
      exact hz_in_x
    · -- Dirección <-
      intro hz_in_y
      apply h_y_subs_x
      exact hz_in_y

  theorem ExtSetReverse_wc {x y : U} (h_eq: x = y) :
    (∀ (z: U), z ∈ x ↔ z ∈ y) := by
    apply ExtSetReverse
    exact h_eq

  /-! ### Subconjunto (no estricto) ### -/
  def subseteq (x y : U) : Prop :=
    ∀ (z: U), z ∈ x → z ∈ y

  /-! ### Notación estándar de subconjunto y subconjunto propio ### -/
  notation:50 lhs:51 " ⊆ " rhs:51 => subseteq lhs rhs
  notation:50 lhs:51 " ⊂ " rhs:51 => subseteq lhs rhs ∧ (lhs ≠ rhs)

  /-! ### Notación estándar de superconjunto y superconjunto propio ### -/
  notation:50 lhs:51 " ⊇ " rhs:51 => rhs ⊆ lhs
  notation:50 lhs:51 " ⊃ " rhs:51 => rhs ⊂ lhs

  /-! ### Teorema de igualdad de conjuntos a través de ser subconjunto uno de otro ### -/
  /-! ### EqualityOfSubset : A ⊆ B ∧ B ⊆ A ↔ A = B                                ### -/
  theorem EqualityOfSubset (x y : U) :
    (x ⊆ y) → (y ⊆ x) → (x = y)
      := by
    intro h_xy h_yx
    apply (ExtSet x y)
    intro z
    constructor
    · -- Dirección ->
      intro hz_in_x
      apply h_xy
      exact hz_in_x
    · -- Dirección <-
      intro hz_in_y
      apply h_yx
      exact hz_in_y

  /-! ### Disjuntos (sin relación por '⊆') ### -/

  /-! ### 'U' es un Orden Parcial por '⊆' ### -/
    theorem subseteq_reflexive : ∀ (x : U), x ⊆ x := by
      intro x z h_mem
      exact h_mem

    theorem subseteq_transitive : ∀ (x y z : U), x ⊆ y → y ⊆ z → x ⊆ z := by
      intro x y z h_xy h_yz
      intro w h_w_in_x
      apply h_yz
      apply h_xy
      exact h_w_in_x

    theorem subseteq_antisymmetric : ∀ (x y : U), x ⊆ y → y ⊆ x → x = y := by
      intro x y h_xy h_yx
      apply EqualityOfSubset
      exact h_xy
      exact h_yx

  /-! ### Definición de Conjuntos Disjuntos ### -/
  def disjoint (x y : U) : Prop :=
    ∀ z, z ∈ x → z ∉ y

  /-! ### Notación estándar de conjuntos disjuntos ### -/
  notation:50 lhs:51 " ⟂ " rhs:51 => disjoint lhs rhs

  /-! ### Simetría de los Conjuntos Disjuntos ### -/
  theorem disjoint_symm (x y : U) :
    (x ⟂ y) → (y ⟂ x) := by
    intro h_disj z h_z_in_y h_z_in_x
    apply h_disj z h_z_in_x
    exact h_z_in_y

  /-! ### Teorema de conjuntos disjuntos (todavía sin notación estándar) ### -/
  theorem disjoint_is_empty (x y : U) :
    (x ⟂ y) → (∃ z : U, z ∈ x ∧ z ∈ y) → False := by
    intro h_disj h_exists
    cases h_exists with
    | intro z h_z_both =>
      apply h_disj
      exact h_z_both.1
      exact h_z_both.2

  theorem disjoint_is_empty_wc {x y : U} (h_exists :  ∃ (z : U), z ∈ x ∧ z ∈ y) :
    ¬(x ⟂ y) := by
    intro h_disj
    apply disjoint_is_empty
    exact h_disj
    exact h_exists

  /-! ### 'U' es un Orden Parcial por '⊆' ### -/
  instance : PartialOrder U where
    le := subseteq
    le_refl := subseteq_reflexive
    le_trans := subseteq_transitive
    le_antisymm := subseteq_antisymmetric

  def isEmpty (x : U) : Prop :=
    ∀ y, ¬(y ∈ x)

  def isNonEmpty (x : U) : Prop :=
    ∃ y, y ∈ x

  def isSingleton (x : U) : Prop :=
    ∃ y, ∀ z, z ∈ x ↔ z = y

  def isPair (x : U) : Prop :=
    ∃ y z, ∀ w, w ∈ x ↔ (w = y ∨ w = z)

  def isBinIntersection (x y s: U) : Prop :=
    ∀ z, z ∈ x ↔ (z ∈ y ∧ z ∈ s)

  def isBinUnion (x y s: U) : Prop :=
    ∀ z, z ∈ x ↔ (∃ t, t ∈ y ∧ z ∈ t) ∧ (z ∈ s)

  def isBinDiff (x y s: U) : Prop :=
    ∀ z, z ∈ x ↔ (z ∈ y ∧ ¬(z ∈ s))

  def isBinSymDiff (x y s: U) : Prop :=
    ∀ z, z ∈ x ↔ (z ∈ y ∧ z ∉ s) ∨ (z ∉ y ∧ z ∈ s)

  def isUnion (x X: U) : Prop :=
    ∀ (z : U), z ∈ X ↔ ∃ (y : U), z ∈ y ∧ y ∈ x

  def isIntersection (x X: U) : Prop :=
    ∀ (z: U), z ∈ X ↔ ∀ (y: U), y ∈ x → z ∈ y

end SetUniverse

export SetUniverse (
  mem ExtSet ExtSet_wc ExtSetReverse ExtSetReverse_wc EqualityOfSubset
  subseteq subseteq_reflexive subseteq_transitive subseteq_antisymmetric
  disjoint disjoint_symm disjoint_is_empty disjoint_is_empty_wc
  isEmpty isNonEmpty isSingleton isPair isBinIntersection
  isBinUnion isBinDiff isBinSymDiff isUnion
  isIntersection
)
