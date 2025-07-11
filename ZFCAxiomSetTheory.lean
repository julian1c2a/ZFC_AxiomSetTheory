-- This module serves as the root of the `ZFCAxiomSetTheory` library.
-- Import modules here that should be built as part of the library.
import ZFCAxiomSetTheory.Basic
import ZFCAxiomSetTheory.Existence
import Mathlib.Logic.ExistsUnique
import Init.Classical
import Mathlib.Tactic

namespace SetUniverse
  open Classical
  open SetUniverse.ExistenceAxiom
  universe u
  variable {U : Type u}

  namespace SpecificationAxiom

    /-! ### Axioma de Especificación, Separación o Comprehensión ### -/
    /-! ### Specification : si existe algún conjunto en el universo U al que le separamos los elementos que P (Prop) obtenemos de nuevo un conjunto ### -/
    /-! ### Specification : ∃ (y : U), ∀ (x: U), P x ∧ x ∈ y ↔ x ∈ y ### -/
    /-! ### Specification : y := {x ∈ y : P x} es un conjunto de U ### -/
    axiom Specification (x : U) (P : Prop) : ∃ (y : U), ∀ (z : U), z ∈ y ↔ (z ∈ x ∧ P z)


  end SpecificationAxiom
end SetUniverse
