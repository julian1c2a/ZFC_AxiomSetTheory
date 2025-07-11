import Mathlib.Logic.ExistsUnique
import Init.Classical
import Mathlib.Tactic
import ZFCAxiomSetTheory.Basic
import ZFCAxiomSetTheory.Existence

namespace SetUniverse
  open Classical
  open SetUniverse.ExistenceAxiom
  universe u
  variable {U : Type u}

  namespace SpecificationAxiom

  /-! ### Axioma de Especificación, Separación o Comprehensión ### -/
  /-! ### Specification : existe algún conjunto en el universo U que cumple que es subconjunto de otro y que cumple la proposición P ### -/
  axiom Specification (x : U) (P : U → Prop) :
    ∃ (y : U), ∀ (z : U), z ∈ y ↔ (z ∈ x ∧ P z)

  /-! ### Teorema de Existencia Única para el Axioma de Especificación ### -/
  /-! ### SpecificationUnique : existe un único conjunto que cumple la especificación P ### -/
  theorem SpecificationUnique (x : U) (P : U → Prop) :
    ∃! (y : U), ∀ (z : U), z ∈ y ↔ (z ∈ x ∧ P z)
      := by
    obtain ⟨y, hy⟩ := Specification x P
    apply ExistsUnique.intro y
    · -- Existencia del conjunto especificado
      exact hy
    · -- Unicidad del conjunto especificado
      intro z hz_spec
      apply (ExtSet z y)
      intro w
      constructor
      · -- Dirección ->
        intro hw_in_z
        have h_w_in_y : w ∈ y := by
          apply (hy w).2
          exact (hz_spec w).mp hw_in_z
        exact h_w_in_y
      · -- Dirección <-
        intro hw_in_y
        have h := (hy w).mp hw_in_y
        have h_w_in_x : w ∈ x := h.1
        have h_P_w : P w := h.2
        have h_w_in_z : w ∈ z := by
          apply (hz_spec w).mpr
          exact ⟨h_w_in_x, h_P_w⟩
        exact h_w_in_z

  /-! ### Definición del conjunto especificado por el Axioma de Especificación ### -/
  noncomputable def SpecSet (x : U) (P : U → Prop) : U :=
    choose (SpecificationUnique x P)

  theorem SpecSet_is_specified (x : U) (P : U → Prop) :
    ∀ (z : U), z ∈ SpecSet x P ↔ (z ∈ x ∧ P z)
      := by
    intro z
    exact (choose_spec (SpecificationUnique x P)).1 z

  notation " { " x " | " P " } " => SpecSet x P

  /-! ### Definición del conjunto especificado por el Axioma de Especificación ### -/
  noncomputable def BinIntersection (x y : U) : U :=
    choose (SpecificationUnique x fun z => z ∈ y)

  theorem BinIntersection_is_specified (x y : U) :
    ∀ (z : U), z ∈ BinIntersection x y ↔ (z ∈ x ∧ z ∈ y)
      := by
    intro z
    have h := choose_spec (SpecificationUnique x fun z => z ∈ y)
    exact h.1 z

  theorem BinIntersectionUniqueSet (x y : U) :
    ∃! (z : U), ∀ (w : U), w ∈ z ↔ (w ∈ x ∧ w ∈ y)
      := by
    apply ExistsUnique.intro (BinIntersection x y)
    · -- Existencia del conjunto de intersección binaria
      exact BinIntersection_is_specified x y
    · -- Unicidad del conjunto de intersección binaria
      intro z hz_intersection
      apply (ExtSet z (BinIntersection x y))
      intro w
      constructor
      · -- Dirección ->
        intro hw_in_z
        have h_both := (hz_intersection w).mp hw_in_z
        have h_w_in_x : w ∈ x := h_both.1
        have h_w_in_y : w ∈ y := h_both.2
        exact (BinIntersection_is_specified x y w).mpr ⟨h_w_in_x, h_w_in_y⟩
      · -- Dirección <-
        intro hw_in_bin_intersection
        have h_both := (BinIntersection_is_specified x y w).mp hw_in_bin_intersection
        exact (hz_intersection w).mpr h_both

  /-! ### Notación estándar de conjuntos de la Intersección Binaria ### -/
  notation:50 lhs:51 " ∩ " rhs:51 => BinIntersection lhs rhs

  /-! ### Teorema de la Intersección es Subconjunto ### -/
  theorem BinIntersection_subset (x y : U) :
    (x ∩ y) ⊆ x ∧ (x ∩ y) ⊆ y
      := by
    constructor
    · -- Subconjunto de x
      intro z h_z_in_bin_intersection
      have h := BinIntersection_is_specified x y z
      exact (h.1 h_z_in_bin_intersection).1
    · -- Subconjunto de y
      intro z h_z_in_bin_intersection
      have h := BinIntersection_is_specified x y z
      exact (h.1 h_z_in_bin_intersection).2

  /-! ### Teorema de la Intersección de Conjuntos Disjuntos es Vacía ### -/
  theorem BinIntersection_empty (x y : U) :
    (x ∩ y) = ∅ ↔ (x ⟂ y)
      := by
    constructor
    · -- Dirección ->
      intro h_bin_intersection_empty z h_z_in_x h_z_in_y
      have h_bin_intersection := BinIntersection_is_specified x y z
      have h_z_in_bin_intersection : z ∈ (x ∩ y) := by
        apply h_bin_intersection.mpr
        exact ⟨h_z_in_x, h_z_in_y⟩
      apply EmptySet_is_empty z
      rw [← h_bin_intersection_empty]
      exact h_z_in_bin_intersection
    · -- Dirección <-
      intro h_disj
      apply ExtSet (x ∩ y) ∅
      intro z
      constructor
      · -- Dirección ->
        intro h_z_in_bin_intersection
        have h_bin_intersection := BinIntersection_is_specified x y z
        have h_both := h_bin_intersection.mp h_z_in_bin_intersection
        have h_false := h_disj z h_both.1 h_both.2
        exact False.elim h_false
      · -- Dirección <-
        intro h_z_in_empty
        exact False.elim (EmptySet_is_empty z h_z_in_empty)

  theorem BinIntersection_empty_left_wc {x y : U} (h_empty : (x ∩ y) = ∅) :
    x ⟂ y
      := by
    exact (BinIntersection_empty x y).mp h_empty

  theorem BinIntersection_empty_right_wc {x y : U} (h_perp : x ⟂ y) :
    (x ∩ y) = ∅
      := by
    exact (BinIntersection_empty x y).mpr h_perp

  theorem BinIntersection_commutative (x y : U) :
    (x ∩ y) = (y ∩ x)
      := by
    apply ExtSet
    intro z
    constructor
    · -- Dirección ->
      intro h_z_in_bin_intersection
      have h := BinIntersection_is_specified x y z
      have h_both := h.mp h_z_in_bin_intersection
      exact (BinIntersection_is_specified y x z).mpr ⟨h_both.2, h_both.1⟩
    · -- Dirección <-
      intro h_z_in_bin_intersection
      have h := BinIntersection_is_specified y x z
      have h_both := h.mp h_z_in_bin_intersection
      exact (BinIntersection_is_specified x y z).mpr ⟨h_both.2, h_both.1⟩

  theorem BinIntersection_associative (x y z : U) :
    ((x ∩ y) ∩ z) = (x ∩ (y ∩ z))
      := by
    apply ExtSet
    intro w
    constructor
    · -- Dirección ->
      intro h_w_in_bin_intersection
      have h_bin_intersection := BinIntersection_is_specified (x ∩ y) z w
      have h_both := h_bin_intersection.mp h_w_in_bin_intersection
      have h_w_in_xy := (BinIntersection_is_specified x y w).mp h_both.1
      have h_w_in_y_intersection_z : w ∈ (y ∩ z) := by
        apply (BinIntersection_is_specified y z w).mpr
        exact ⟨h_w_in_xy.2, h_both.2⟩
      have h_w_in_x_intersection_yz : w ∈ (x ∩ (y ∩ z)) := by
        apply (BinIntersection_is_specified x (y ∩ z) w).mpr
        exact ⟨h_w_in_xy.1, h_w_in_y_intersection_z⟩
      exact h_w_in_x_intersection_yz
    · -- Dirección <-
      intro h_w_in_x_intersection_yz
      have h_bin_intersection := BinIntersection_is_specified x (y ∩ z) w
      have h_both := h_bin_intersection.mp h_w_in_x_intersection_yz
      have h_w_in_yz : w ∈ (y ∩ z) := h_both.2
      have h_w_in_yz_components := (BinIntersection_is_specified y z w).mp h_w_in_yz
      have h_w_in_x_intersection_y : w ∈ (x ∩ y) := by
        apply (BinIntersection_is_specified x y w).mpr
        exact ⟨h_both.1, h_w_in_yz_components.1⟩
      have h_w_in_bin_intersection : w ∈ ((x ∩ y) ∩ z) := by
        apply (BinIntersection_is_specified (x ∩ y) z w).mpr
        exact ⟨h_w_in_x_intersection_y, h_w_in_yz_components.2⟩
      exact h_w_in_bin_intersection

  theorem BinIntersection_absorbent_elem (x : U) :
    (x ∩ ∅ ) = ∅ := by
    apply ExtSet
    intro z
    constructor
    · -- Dirección ->
      intro h_z_in_bin_intersection
      have h_bin_intersection := BinIntersection_is_specified x ∅ z
      have h_z_in_empty : z ∈ ∅ := by
        apply EmptySet_is_empty z
      have h_both := h_bin_intersection.mp h_z_in_bin_intersection
      have h_z_in_x : z ∈ x := h_both.1
      have h_z_in_empty : z ∈ ∅ := h_both.2
      exact h_z_in_empty
    · -- Dirección <-
      intro h_z_in_empty
      have h_bin_intersection := BinIntersection_is_specified x ∅ z
      have h_z_in_empty : z ∈ ∅ := by
        apply EmptySet_is_empty z
      have h_both := h_bin_intersection.mp h_z_in_empty
      have h_z_in_x : z ∈ x := h_both.1
      have h_z_in_empty : z ∈ ∅ := h_both.2
      exact h_z_in_empty

  end SpecificationAxiom
end SetUniverse

export SetUniverse.SpecificationAxiom (
    Specification SpecificationUnique SpecSet SpecSet_is_specified
)
