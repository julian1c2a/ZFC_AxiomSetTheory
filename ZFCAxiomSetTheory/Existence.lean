import Mathlib.Logic.ExistsUnique
import Init.Classical
import Mathlib.Tactic
import ZFCAxiomSetTheory.Extension

namespace SetUniverse
  open Classical
  open SetUniverse.ExtensionAxiom
  universe u
  variable {U : Type u}

  namespace ExistenceAxiom

    /-! ### Axioma de Existencia ### -/
    /-! ### Existence : existe algún conjunto vacío en el universo U ### -/
    axiom ExistsAnEmptySet : ∃ (x : U), ∀ (y : U), y ∉ x

    /-! ### Teorema de Existencia Única ### -/
    /-! ### ExistenceUnique : existe un único conjunto vacío en el universo U ### -/
    theorem ExistsUniqueEmptySet :
      ∃! (x : U), ∀ (y : U), y ∉ x
        := by
      obtain ⟨x, hx⟩ := ExistsAnEmptySet
      apply ExistsUnique.intro x
      · -- Existencia de un conjunto vacío
        exact hx
      · -- Unicidad del conjunto vacío
        intro y hy_empty
        apply (ExtSet y x)
        intro z
        simp [hx, hy_empty]

    noncomputable def EmptySet : U := choose (ExistsUnique.exists ExistsUniqueEmptySet)

    theorem EmptySet_is_empty : ∀ (y : U), y ∉ EmptySet := by
      intro y
      have h := choose_spec (p := fun x => ∀ (y : U), y ∉ x) (ExistsUnique.exists ExistsUniqueEmptySet)
      exact h y

    theorem EmptySet_unique : ∀ (x : U), (∀ (y : U), y ∉ x) → (x = EmptySet) := by
      intro x hx_empty
      apply ExtSet
      intro y
      constructor
      · -- Dirección ->
        intro hy_in_x
        exfalso
        apply hx_empty y
        exact hy_in_x
      · -- Dirección <-
        intro hy_in_empty
        exfalso
        exact EmptySet_is_empty y hy_in_empty

    notation " ∅ " => EmptySet

    theorem EmptySet_subseteq_any (x : U) : ∅ ⊆ x := by
      intro y hy_in_empty
      exfalso
      exact EmptySet_is_empty y hy_in_empty

  end ExistenceAxiom
end SetUniverse

export SetUniverse.ExistenceAxiom (
    ExistsAnEmptySet ExistsUniqueEmptySet EmptySet EmptySet_is_empty EmptySet_unique
    EmptySet_subseteq_any
)
