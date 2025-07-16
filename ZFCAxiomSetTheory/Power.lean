import Mathlib.Logic.ExistsUnique
import Init.Classical
import Mathlib.Tactic
import ZFCAxiomSetTheory.Extension
import ZFCAxiomSetTheory.Existence
import ZFCAxiomSetTheory.Specification
import ZFCAxiomSetTheory.Pairing

namespace SetUniverse
  open Classical
  open SetUniverse.ExtensionAxiom
  open SetUniverse.ExistenceAxiom
  open SetUniverse.SpecificationAxiom
  open SetUniverse.PairingAxiom
  universe u
  variable {U : Type u}

  namespace UnionAxiom

  /-! ### Axioma de Pares (No Ordenados) ### -/
  axiom Power (C : U) :
    ∃ (P_of_S : U), ∀ (S : U), S ⊆ C ↔ S ∈ P_of_S


  end UnionAxiom
end SetUniverse

export SetUniverse.UnionAxiom (

)

/-!
## Power Axiom
# Example of Power Axiom
    C = { x, y , z }
    P_of_S = { ∅, { x }, { y }, { z }, { x, y }, { x, z }, { y, z }, { x, y, z } }
    S = { x, y }
    S ⊆ C ↔ S ∈ P_of_S
# This means that the power set of C is the set of all subsets of C.
# This is a fundamental axiom in set theory, allowing us to construct the power set of any set.
    ∀ C : U,  ∃ Pw : U, S ∈ Pw ↔ S ⊆ C

## Define Cartesian Product of Two Sets

# The Cartesian product of two sets A and B is the set of all ordered pairs (a, b) where a is in A and b is in B.
# This is often denoted as A × B.
# Example of Cartesian Product
    A = { 1, 2 }
    B = { a, b }
    A × B = { ⟨ 1, a ⟩ , ⟨ 1, b ⟩ , ⟨ 2, a ⟩ , ⟨ 2, b ⟩ }
  # By Kuratowski's definition, we can represent ordered pairs as sets:
    A × B = { { {1}, {1,a} }, { {1}, {1,b} }, { {2}, {2,a} }, { {2}, {2,b} } }
  # where {1}, {1, a}, {2}, {2,a} are subsets containing the elements of A and B.
    {1} {1, a} {2} {2,a} ⊆ A ∪ B
    {1} {1, a} {2} {2,a} ∈ Pow (A ∪ B)
    { {1}, {1,a} } { {1}, {1,b} } { {2}, {2,a} } { {2}, {2,b} } ∈ Pow Pow (A ∪ B)
    A × B ⊆ Pow Pow (A ∪ B)
    A × B = SpecSet (Pow Pow (A ∪ B)) (fun w  => ∃ (x : U) (y : U), x ∈ A ∧ y ∈ B ∧ w = ⟨ x , y ⟩)

# This shows that the Cartesian product of two sets can be represented as a subset of the power set of the power set of their union.
# This is a fundamental concept in set theory, allowing us to work with ordered pairs and Cartesian products in a rigorous way.
# It is also used in defining relations and functions in set theory.
# The power set of a set is the set of all subsets of that set, including the empty set and the set itself.
# The power set is denoted as Pow(A) or 2^A, where A is the set.

# We have to proof that doesn't there exist a bijection between a set and its power set (Cantor's theorem).
    f : A → Pow A is function → not surjective f
    g : Pow A → A is function → not injective g


-/
