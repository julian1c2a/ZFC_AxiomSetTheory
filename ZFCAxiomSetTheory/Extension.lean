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

    /-! ### Notación estándar de subconjunto y subconjunto propio ### -/
    notation:50 lhs:51 " ⊆ " rhs:51 => subseteq lhs rhs -- [cite: 124]

    notation:50 lhs:51 " ⊂ " rhs:51 => subseteq lhs rhs ∧ (lhs ≠ rhs) -- [cite: 124]

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

  end Extension
end SetUniverse

export SetUniverse (mem)
export SetUniverse.Extension (
    ExtSet ExtSetReverse ExtSet_wc EqualityOfSubset
    subseteq subseteq_reflexive subseteq_transitive subseteq_antisymmetric
    disjoint
)
