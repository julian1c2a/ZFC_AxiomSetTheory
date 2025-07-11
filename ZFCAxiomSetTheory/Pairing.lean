import Mathlib.Logic.ExistsUnique
import Init.Classical
import Mathlib.Tactic
import ZFCAxiomSetTheory.Basic
import ZFCAxiomSetTheory.Existence
import ZFCAxiomSetTheory.Specification

namespace SetUniverse
  open Classical
  open SetUniverse.ExistenceAxiom
  open SetUniverse.SpecificationAxiom
  universe u
  variable {U : Type u}

  namespace PairingAxiom

  /-! ### Axioma de Pares (No Ordenados) ### -/
  axiom Pairing (x y : U) :
    ∃ (z : U), ∀ (w : U), w ∈ z ↔ (w = x ∨ w = y)

  /-! ### Teorema de Existencia Única para el Axioma de Pares ### -/
  /-! ### PairingUnique : existe un único conjunto que cumple la especificación {x,y} ### -/
  theorem PairingUniqueSet (x y : U) :
    ∃! (z : U), ∀ (w : U), w ∈ z ↔ (w = x ∨ w = y)
      := by
    apply ExistsUnique.intro (choose (Pairing x y))
    · -- Existencia del conjunto especificado por el Axioma de Pares
      exact choose_spec (Pairing x y)
    · -- Unicidad del conjunto especificado por el Axioma de Pares
      intro z hz_pairing
      apply (ExtSet z (choose (Pairing x y)))
      intro w
      constructor
      · -- Dirección ->
        intro hw_in_z
        have h := hz_pairing w
        have h_w_in_pairing : w ∈ (choose (Pairing x y)) := by
          apply choose_spec (Pairing x y)
          exact hw_in_z
        exact h.mp h_w_in_pairing
      · -- Dirección <-
        intro hw_in_pairing
        have h := choose_spec (Pairing x y)
        have h_w_in_x_or_y : w = x ∨ w = y := h.1 hw_in_pairing
        exact (hz_pairing w).mpr h_w_in_x_or_y

  /-! ### Definición del conjunto especificado por el Axioma de Pares ### -/
  noncomputable def PairSet (x y : U) : U :=
    choose (PairingUniqueSet x y)

  theorem PairSet_is_specified (x : U) (P : U → Prop) :

  notation " { " x ", " y " } " => PairSet x y

  end PairingAxiom
end SetUniverse

export SetUniverse.PairingAxiom ()
