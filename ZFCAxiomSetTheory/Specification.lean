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
    (x ∩ ∅) = ∅
      := by
    apply ExtSet
    intro z
    constructor
    · -- Dirección ->
      intro h_z_in_bin_intersection
      have h_bin_intersection := BinIntersection_is_specified x ∅ z
      have h_both := h_bin_intersection.mp h_z_in_bin_intersection
      have h_z_in_x : z ∈ x := h_both.1
      have h_z_in_empty : z ∈ ∅ := h_both.2
      exact h_z_in_empty
    · -- Dirección <-
      intro h_z_in_empty
      exact False.elim (EmptySet_is_empty z h_z_in_empty)

  theorem BinIntersection_with_subseteq (x y : U) :
    x ⊆ y → (x ∩ y) ⊆ x
      := by
    intro h_subset z h_z_in_bin_intersection
    have h_bin_intersection := BinIntersection_is_specified x y z
    have h_both := h_bin_intersection.mp h_z_in_bin_intersection
    have h_z_in_x : z ∈ x := h_both.1
    have h_z_in_y : z ∈ y := h_both.2
    exact h_z_in_x

  theorem BinIntersection_with_subseteq_full (x y : U) :
    x ⊆ y ↔ (x ∩ y) = x
      := by
    constructor
    · -- Direction: x ⊆ y → (x ∩ y) = x
      intro h_subset
      apply ExtSet
      intro z
      constructor
      · -- z ∈ (x ∩ y) → z ∈ x
        intro h_z_in_intersection
        have h_bin_intersection := BinIntersection_is_specified x y z
        have h_both := h_bin_intersection.mp h_z_in_intersection
        exact h_both.1
      · -- z ∈ x → z ∈ (x ∩ y)
        intro h_z_in_x
        have h_z_in_y := h_subset z h_z_in_x
        exact (BinIntersection_is_specified x y z).mpr ⟨h_z_in_x, h_z_in_y⟩
    · -- Direction: (x ∩ y) = x → x ⊆ y
      intro h_eq z h_z_in_x
      have h_z_in_intersection : z ∈ (x ∩ y) := by
        rw [h_eq]
        exact h_z_in_x
      have h_bin_intersection := BinIntersection_is_specified x y z
      have h_both := h_bin_intersection.mp h_z_in_intersection
      exact h_both.2

  theorem BinIntersection_with_empty (x : U) :
    (x ∩ ∅) = ∅
      := by
    exact BinIntersection_absorbent_elem x

  theorem BinIntersection_idempotence (x : U) :
    (x ∩ x) = x
      := by
    apply ExtSet
    intro z
    constructor
    · -- Dirección ->
      intro h_z_in_bin_intersection
      have h_bin_intersection := BinIntersection_is_specified x x z
      have h_both := h_bin_intersection.mp h_z_in_bin_intersection
      exact h_both.1
    · -- Dirección <-
      intro h_z_in_x
      exact (BinIntersection_is_specified x x z).mpr ⟨h_z_in_x, h_z_in_x⟩

  /-! ### Definición de la Diferencia de Conjuntos ### -/
  noncomputable def Difference (x y : U) : U :=
    choose (SpecificationUnique x (fun z => z ∉ y))

  /-! ### Notación estándar de la Diferencia de Conjuntos ### -/
  notation:50 lhs:51 " \\ " rhs:51 => Difference lhs rhs

  theorem Difference_is_specified (x y : U) :
    ∀ (z : U), z ∈ (x \ y) ↔ (z ∈ x ∧ z ∉ y)
      := by
    intro z
    have h := choose_spec (SpecificationUnique x fun z => z ∉ y)
    exact h.1 z

  theorem DifferenceUniqueSet (x y : U) :
    ∃! (z : U), ∀ (w : U), w ∈ z ↔ (w ∈ x ∧ w ∉ y)
      := by
    apply ExistsUnique.intro (Difference x y)
    · -- Existencia de la diferencia binaria
      exact Difference_is_specified x y
    · -- Unicidad de la diferencia binaria
      intro z hz_difference
      apply (ExtSet z (Difference x y))
      intro w
      constructor
      · -- Dirección ->
        intro hw_in_z
        have h_both := (hz_difference w).mp hw_in_z
        have h_w_in_x : w ∈ x := h_both.1
        have h_w_not_in_y : w ∉ y := h_both.2
        exact (Difference_is_specified x y w).mpr ⟨h_w_in_x, h_w_not_in_y⟩
      · -- Dirección <-
        intro hw_in_difference
        have h_both := (Difference_is_specified x y w).mp hw_in_difference
        exact (hz_difference w).mpr h_both

  theorem Difference_subset (x y : U) :
    (x \ y) ⊆ x
      := by
    intro z h_z_in_difference
    have h_difference := Difference_is_specified x y z
    have h_both := h_difference.mp h_z_in_difference
    exact h_both.1

  theorem Difference_with_superseteq (x : U) {y : U} (h_x_superseteq_y : x ⊆ y) :
    (x \ y) = ∅ := by
    apply ExtSet
    intro z
    constructor
    · -- Dirección ->
      intro h_z_in_difference
      have h_difference := Difference_is_specified x y z
      have h_both := h_difference.mp h_z_in_difference
      have h_z_in_x : z ∈ x := h_both.1
      have h_z_not_in_y : z ∉ y := h_both.2
      have h_z_in_y : z ∈ y := h_x_superseteq_y z h_z_in_x
      exact False.elim (h_z_not_in_y h_z_in_y)
    · -- Dirección <-
      intro h_z_in_empty
      exact False.elim (EmptySet_is_empty z h_z_in_empty)

  theorem Difference_with_empty (x : U) :
    (x \ ∅) = x
      := by
    apply ExtSet
    intro z
    constructor
    · -- Dirección ->
      intro h_z_in_difference
      have h_difference := Difference_is_specified x ∅ z
      have h_both := h_difference.mp h_z_in_difference
      exact h_both.1
    · -- Dirección <-
      intro h_z_in_x
      exact (Difference_is_specified x ∅ z).mpr ⟨h_z_in_x, EmptySet_is_empty z⟩

  theorem Difference_self_empty (x : U) :
    (x \ x) = ∅
      := by
    apply ExtSet
    intro z
    constructor
    · -- Dirección ->
      intro h_z_in_difference
      have h_difference := Difference_is_specified x x z
      have h_both := h_difference.mp h_z_in_difference
      have h_z_in_x : z ∈ x := h_both.1
      have h_z_not_in_x : z ∉ x := h_both.2
      exact False.elim (h_z_not_in_x h_z_in_x)
    · -- Dirección <-
      intro h_z_in_empty
      exact False.elim (EmptySet_is_empty z h_z_in_empty)

  theorem Difference_disjoint (x : U) {y: U} (h_disjoint : x ⟂ y) :
    (x \ y) = x
      := by
    apply ExtSet
    intro z
    constructor
    · -- Dirección ->
      intro h_z_in_difference
      have h_difference := Difference_is_specified x y z
      have h_both := h_difference.mp h_z_in_difference
      have h_z_in_x : z ∈ x := h_both.1
      have h_z_not_in_y : z ∉ y := h_both.2
      exact h_z_in_x
    · -- Dirección <-
      intro h_z_in_x
      have h_z_not_in_y : z ∉ y := h_disjoint z h_z_in_x
      exact (Difference_is_specified x y z).mpr ⟨h_z_in_x, h_z_not_in_y⟩

  end SpecificationAxiom
end SetUniverse

export SetUniverse.SpecificationAxiom (
    Specification SpecificationUnique SpecSet SpecSet_is_specified
    BinIntersection BinIntersection_is_specified BinIntersectionUniqueSet
    BinIntersection_subset BinIntersection_empty BinIntersection_empty_left_wc
    BinIntersection_empty_right_wc BinIntersection_commutative
    BinIntersection_associative BinIntersection_absorbent_elem
    BinIntersection_with_subseteq BinIntersection_with_subseteq_full
    BinIntersection_with_empty BinIntersection_idempotence
)
