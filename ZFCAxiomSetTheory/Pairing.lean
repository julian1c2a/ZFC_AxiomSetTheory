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
        have h_spec := choose_spec (Pairing x y)
        exact (h_spec w).mpr (h.mp hw_in_z)
      · -- Dirección <-
        intro hw_in_pairing
        have h := choose_spec (Pairing x y)
        have h_w_in_x_or_y : w = x ∨ w = y := (h w).mp hw_in_pairing
        exact (hz_pairing w).mpr h_w_in_x_or_y

  /-! ### Definición del conjunto especificado por el Axioma de Pares ### -/
  noncomputable def PairSet (x y : U) : U :=
    choose (PairingUniqueSet x y)

  theorem PairSet_is_specified (x y : U) :
    ∀ (z : U), z ∈ PairSet x y ↔ (z = x ∨ z = y)
      := by
    intro z
    exact (choose_spec (PairingUniqueSet x y)).1 z

  theorem PairSet_unique (x y : U) (z : U) (hz_pairing : ∀ (w : U), w ∈ z ↔ (w = x ∨ w = y)) :
    (z = PairSet x y) := by
    apply ExtSet
    intro w
    constructor
    · -- Dirección ->
      intro hw_in_z
      exact (PairSet_is_specified x y w).mpr ((hz_pairing w).mp hw_in_z)
    · -- Dirección <-
      intro hw_in_pairing
      exact (hz_pairing w).mpr ((PairSet_is_specified x y w).mp hw_in_pairing)

  notation " { " x ", " y " } " => PairSet x y

  noncomputable def Singleton (x : U) : U := { x , x }

  theorem Singleton_is_specified (x : U) :
    ∀ (z : U), z ∈ Singleton x ↔ (z = x)
      := by
    intro z
    constructor
    · -- Dirección ->
      intro hz_in_singleton
      have h := (PairSet_is_specified x x z).mp hz_in_singleton
      cases h with
      | inl h_eq => exact h_eq
      | inr h_eq => exact h_eq
    · -- Dirección <-
      intro hz_eq_x
      exact (PairSet_is_specified x x z).mpr (Or.inl hz_eq_x)

  notation " { " x " } " => Singleton x

  theorem Singleton_unique (x : U) (z : U) (hz_singleton : ∀ (w : U), w ∈ z ↔ (w = x)) :
    z = { x }
      := by
    apply ExtSet
    intro w
    constructor
    · -- Dirección ->
      intro hw_in_z
      exact (Singleton_is_specified x w).mpr ((hz_singleton w).mp hw_in_z)
    · -- Dirección <-
      intro hw_in_singleton
      exact (hz_singleton w).mpr ((Singleton_is_specified x w).mp hw_in_singleton)

  theorem PairSet_is_nonempty (x y : U) :
    PairSet x y ≠ ∅
      := by
    intro h_empty
    have h_pairing := choose_spec (PairingUniqueSet x y)
    have h_x_in_pairing : x ∈ PairSet x y := (h_pairing.1 x).mpr (Or.inl rfl)
    rw [h_empty] at h_x_in_pairing
    exfalso
    exact EmptySet_is_empty x h_x_in_pairing

  theorem PairSet_singleton_is_nonempty (x : U) :
    Singleton x ≠ ∅
      := by
    intro h_empty
    have h_singleton := Singleton_is_specified x x
    have h_x_in_singleton : x ∈ Singleton x := h_singleton.mpr rfl
    rw [h_empty] at h_x_in_singleton
    exfalso
    exact EmptySet_is_empty x h_x_in_singleton

  noncomputable def OrderedPair (x y : U) : U := { { x } , { x , y } }

  theorem OrderedPair_is_specified (x y : U) :
    ∀ (z : U), z ∈ OrderedPair x y ↔ (z = { x } ∨ z = { x , y })
      := by
    intro z
    constructor
    · -- Dirección ->
      intro hz_in_ordered_pair
      unfold OrderedPair at hz_in_ordered_pair
      have h := (PairSet_is_specified { x } { x , y } z).mp hz_in_ordered_pair
      cases h with
      | inl h_eq => exact Or.inl h_eq
      | inr h_eq => exact Or.inr h_eq
    · -- Dirección <-
      intro hz_eq_x_or_pair
      exact (PairSet_is_specified { x } { x , y } z).mpr hz_eq_x_or_pair

  theorem OrderedPair_unique  {z : U} (x y : U) (hz_ordered_pair : ∀ (w : U), w ∈ z ↔ (w = { x } ∨ w = { x , y })) :
    z = OrderedPair x y
      := by
    apply ExtSet
    intro w
    constructor
    · -- Dirección ->
      intro hw_in_z
      exact (OrderedPair_is_specified x y w).mpr ((hz_ordered_pair w).mp hw_in_z)
    · -- Dirección <-
      intro hw_in_ordered_pair
      exact (hz_ordered_pair w).mpr ((OrderedPair_is_specified x y w).mp hw_in_ordered_pair)

  end PairingAxiom
end SetUniverse

export SetUniverse.PairingAxiom (
    Pairing PairingUniqueSet
    PairSet PairSet_is_specified PairSet_unique
    Singleton Singleton_is_specified Singleton_unique
    PairSet_is_nonempty PairSet_singleton_is_nonempty
)
