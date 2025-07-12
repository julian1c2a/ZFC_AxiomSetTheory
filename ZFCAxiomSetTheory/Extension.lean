import Mathlib.Logic.ExistsUnique
import Init.Classical
import Mathlib.Tactic

namespace SetUniverse
  open Classical
  universe u
  variable {U : Type u}

  /-! ### Introducción de la pertenencia a un conjunto como símbolo primitivo ### -/
  -- Definición axiomática de pertenencia: x pertenece a y
  axiom mem (x y : U) : Prop -- [cite: 117]

  /-! ### Notación estándar de la pertenecia a conjuntos ### -/
  notation:50 lhs:51 " ∈ " rhs:51 => mem lhs rhs -- [cite: 118]

  notation:50 lhs:51 " ∉ " rhs:51 => ¬(lhs ∈ rhs) -- [cite: 118]

  namespace Extension
    /-! ### Axioma de Extensionalidad de Conjuntos ### -/
    /-! ### ExtSet : x = y ↔ ∀ z, z ∈ x ↔ z ∈ y ### -/
    axiom ExtSet (x y : U): (∀ (z: U), z ∈ x ↔ z ∈ y) → (x = y) --

    theorem ExtSetReverse (x y : U) :
      (x = y) → (∀ (z: U), z ∈ x ↔ z ∈ y)
        := by
      intro h_eq
      intro z
      constructor
      · -- Dirección ->
        intro hz_in_x
        rw [h_eq] at hz_in_x -- [cite: 121]
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
        apply h_x_subs_y -- [cite: 122]
      · -- Dirección <-
        apply h_y_subs_x -- [cite: 122]

    /-! ### Subconjunto (no estricto) ### -/
    def subseteq (x y : U) : Prop :=
      ∀ (z: U), z ∈ x → z ∈ y --

    /-! ### Notación estándar de subconjunto (no estricto) ### -/
    notation:50 lhs:51 " ⊆ " rhs:51 => subseteq lhs rhs -- [cite: 124]

    /-! ### Subconjunto propio ### -/
    /-! ### Subset : x ⊆ y ∧ x ≠ y ### -/
    def subset (x y : U) : Prop :=
      subseteq x y ∧ (x ≠ y) -- [cite: 124]

    /-! ### Notación estándar de subconjunto propio ### -/
    notation:50 lhs:51 " ⊂ " rhs:51 => subseteq lhs rhs ∧ (lhs ≠ rhs) -- [cite: 124]

    /-! ### Notación estándar de superconjunto y superconjunto propio ### -/
    notation:50 lhs:51 " ⊇ " rhs:51 => subseteq rhs lhs   -- [cite: 124]

    notation:50 lhs:51 " ⊃ " rhs:51 => subset rhs lhs -- [cite: 124]

    /-! ### Teorema de igualdad de conjuntos a través de ser subconjunto uno de otro ### -/
    theorem EqualityOfSubset (x y : U) :
      (x ⊆ y) → (y ⊆ x) → (x = y)
        := by
      intro h_xy h_yx
      apply (ExtSet x y)
      intro z
      constructor
      · apply h_xy -- [cite: 128]
      · apply h_yx -- [cite: 128]

    /-! ### 'U' es un Orden Parcial por '⊆' ### -/
    theorem subseteq_reflexive : ∀ (x : U), x ⊆ x := by
      intro x z h_mem
      exact h_mem

    theorem subseteq_transitive : ∀ (x y z : U), x ⊆ y → y ⊆ z → x ⊆ z := by
      intro x y z h_xy h_yz
      intro w h_w_in_x
      apply h_yz
      apply h_xy
      exact h_w_in_x -- [cite: 131]

    theorem subseteq_antisymmetric : ∀ (x y : U), x ⊆ y → y ⊆ x → x = y := by
      intro x y h_xy h_yx
      apply EqualityOfSubset
      exact h_xy
      exact h_yx

    instance : PartialOrder U where
      le := subseteq
      le_refl := subseteq_reflexive
      le_trans := subseteq_transitive
      le_antisymm := subseteq_antisymmetric

    /-! ### Definición de Conjuntos Disjuntos ### -/
    def disjoint (x y : U) : Prop :=
      ∀ z, z ∈ x → z ∉ y -- [cite: 132]

    /-! ### Notación estándar de conjuntos disjuntos ### -/
    notation:50 lhs:51 " ⟂ " rhs:51 => disjoint lhs rhs -- [cite: 133]

    /-! ### Propiedades de la relación de Subconjunto Propio ### -/
    theorem subset_subseteq (x y : U) : x ⊂ y → x ⊆ y := by
      intro h_subs
      exact h_subs.1

    theorem subseteq_subset_or_eq (x y : U) : x ⊆ y → (x ⊂ y ∨ x = y) := by
      intro h_subs
      by_cases h_eq : x = y
      · -- Caso x = y
        right
        exact h_eq
      · -- Caso x ≠ y
        left
        constructor
        · exact h_subs
        · exact h_eq

    theorem subset_irreflexive (x : U) : ¬(x ⊂ x) := by
      intro h_subs
      apply h_subs.2
      rfl

    theorem subset_asymmetric (x y : U) : (x ⊂ y) → ¬(y ⊂ x) := by
      intro h_subs
      intro h_subs_reverse
      apply h_subs.2
      apply EqualityOfSubset
      exact h_subs.1
      exact h_subs_reverse.1

    theorem subset_asymmetric' (x y : U) : (x ⊆ y) → ¬(y ⊂ x) := by
      intro h_subs
      by_cases h_eq : x = y
      · -- Caso x = y
        intro h_subs_reverse
        apply h_subs_reverse.2
        exact h_eq.symm
      · -- Caso x ≠ y
        intro h_subs_reverse
        apply h_subs_reverse.2
        apply EqualityOfSubset
        exact h_subs_reverse.1
        exact h_subs

    theorem subset_transitive (x y z : U) : (x ⊂ y) → (y ⊂ z) → (x ⊂ z) := by
      intro h_subs_xy h_subs_yz
      constructor
      · apply subseteq_transitive -- [cite: 136]
        exact h_subs_xy.1
        exact h_subs_yz.1
      · intro h_eq
        apply h_subs_xy.2
        apply EqualityOfSubset
        exact h_subs_xy.1
        rw [h_eq]
        exact h_subs_yz.1

  theorem subset_transitive' (x y z : U) : (x ⊆ y) → (y ⊂ z) → (x ⊂ z) := by
    intro h_subs_xy h_subs_yz
    constructor
    · apply subseteq_transitive -- [cite: 136]
      exact h_subs_xy
      exact h_subs_yz.1
    · intro h_eq
      apply h_subs_yz.2
      apply EqualityOfSubset
      exact h_subs_yz.1
      rw [← h_eq]
      exact h_subs_xy

  theorem subset_transitive'' (x y z : U) : (x ⊂ y) → (y ⊆ z) → (x ⊂ z) := by
    intro h_subs_xy h_subs_yz
    constructor
    · apply subseteq_transitive -- [cite: 136]
      exact h_subs_xy.1
      exact h_subs_yz
    · intro h_eq
      apply h_subs_xy.2
      apply EqualityOfSubset
      exact h_subs_xy.1
      rw [h_eq]
      exact h_subs_yz

  noncomputable def isTransitiveSet (x : U) : Prop :=
    ∀ (y : U), (y ∈ x) → (y ⊂ x) -- [cite: 137]


  end Extension
end SetUniverse

export SetUniverse (mem)
export SetUniverse.Extension (
    ExtSet ExtSetReverse ExtSet_wc EqualityOfSubset
    subseteq subseteq_reflexive subseteq_transitive subseteq_antisymmetric
    disjoint
    subseteq_subset_or_eq subset_subseteq subset_irreflexive
    subset_asymmetric subset_asymmetric' subset_transitive
    subset_transitive' subset_transitive'' isTransitiveSet
)
