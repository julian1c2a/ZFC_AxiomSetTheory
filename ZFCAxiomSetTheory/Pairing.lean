import Mathlib.Logic.ExistsUnique
import Mathlib.Logic.Basic
import Init.Classical
import ZFCAxiomSetTheory.Extension
import ZFCAxiomSetTheory.Existence
import ZFCAxiomSetTheory.Specification

namespace SetUniverse
  open Classical
  open SetUniverse.ExtensionAxiom
  open SetUniverse.ExistenceAxiom
  open SetUniverse.SpecificationAxiom
  universe u
  variable {U : Type u}

  namespace PairingAxiom

    -- Helper: existence proof for an element in a nonempty set
    @[simp] noncomputable def ExistsAnElementInSet {U : Type u} (w : U) (h : ∃ y, y ∈ w) : ∃ y, y ∈ w := h

    /-! ### Axioma de Pares (No Ordenados) ### -/
    @[simp] axiom Pairing (x y : U) :
      ∃ (z : U), ∀ (w : U), w ∈ z ↔ (w = x ∨ w = y)

    /-! ### Teorema de Existencia Única para el Axioma de Pares ### -/
    /-! ### PairingUnique : existe un único conjunto que cumple la especificación {x,y} ### -/
    @[simp] theorem PairingUniqueSet (x y : U) :
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
    @[simp] noncomputable def PairSet (x y : U) : U :=
    choose (PairingUniqueSet x y)

    @[simp] theorem PairSet_is_specified (x y : U) :
    ∀ (z : U), z ∈ PairSet x y ↔ (z = x ∨ z = y)
      := by
    intro z
    exact (choose_spec (PairingUniqueSet x y)).1 z

    @[simp] theorem PairSet_unique (x y : U) (z : U) (hz_pairing : ∀ (w : U), w ∈ z ↔ (w = x ∨ w = y)) :
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

    @[simp] noncomputable def Singleton (x : U) : U := { x , x }

    @[simp] theorem Singleton_is_specified (x z : U) :
    z ∈ Singleton x ↔ (z = x)
      := by
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

    @[simp] theorem Singleton_unique (x : U) (z : U) (hz_singleton : ∀ (w : U), w ∈ z ↔ (w = x)) :
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


    @[simp] theorem PairSet_is_nonempty (x y : U) :
    PairSet x y ≠ ∅
      := by
    intro h_empty
    have h_pairing := choose_spec (PairingUniqueSet x y)
    have h_x_in_pairing : x ∈ PairSet x y := (h_pairing.1 x).mpr (Or.inl rfl)
    rw [h_empty] at h_x_in_pairing
    exfalso
    exact EmptySet_is_empty x h_x_in_pairing


    @[simp] theorem PairSet_singleton_is_nonempty (x : U) :
    Singleton x ≠ ∅
      := by
    intro h_empty
    have h_singleton := Singleton_is_specified x x
    have h_x_in_singleton : x ∈ Singleton x := h_singleton.mpr rfl
    rw [h_empty] at h_x_in_singleton
    exfalso
    exact EmptySet_is_empty x h_x_in_singleton

    /-! ### Definición de ser miembro (∈) de la Intersección de una Familia de Conjuntos ### -/
    @[simp] def member_intersection (w v : U) : Prop :=
      ∀ (y : U), ( y ∈ w ) → ( v ∈ y )

    /-! ### Definición del conjunto Intersección de una Familia de Conjuntos ### -/
    @[simp] noncomputable def Intersection (w : U) : U :=
    if h : ∃ y, y ∈ w then
      let y₀ := choose h
      SpecSet y₀ (fun v => ∀ y, y ∈ w → v ∈ y)
    else
      ∅ -- convención, debería ser U

    /-! ### Notación estándar de la Intersección de una Familia de Conjuntos ### -/
    notation " ⋂ " w => Intersection w

    @[simp] lemma nonempty_iff_exists_mem (w : U) : w ≠ ∅ ↔ ∃ y, y ∈ w := by
      calc
        w ≠ ∅ ↔ ¬(∀ y, ¬ (y ∈ w)) := by
          constructor
          · intro h h_all
            apply h
            apply ExtSet
            intro y
            constructor
            · intro hy_in_w
              exfalso
              exact h_all y hy_in_w
            · intro hy_in_empty
              exfalso
              exact EmptySet_is_empty y hy_in_empty
          · intro h h_eq
            have h_all : ∀ y, ¬ (y ∈ w) := by
              intro y
              rw [h_eq]
              exact EmptySet_is_empty y
            exact h h_all
        _ ↔ ∃ y, ¬ ( ¬ ( y ∈ w ) ) := by apply not_forall
        _ ↔ ∃ y, y ∈ w := by
          apply exists_congr
          intro y
          exact not_not

    @[simp] theorem Intersection_is_specified
      (w x : U) (h_nonempty : w ≠ ∅) (h_inter_nonempty : ∃ y, y ∈ w) :
      x ∈ (⋂ w) ↔ member_intersection w x
        := by
      constructor
      · -- Dirección ->
        intro hx_in_intersection
        have h_exists : ∃ y, y ∈ w := (nonempty_iff_exists_mem w).mp h_nonempty
        -- By definition of Intersection, x ∈ ⋂ w ↔ x ∈ SpecSet (choose h_exists) (fun v => ∀ y, y ∈ w → v ∈ y)
        have h_inter_def : x ∈ (⋂ w) ↔ x ∈ SpecSet (choose h_exists) (fun v => ∀ y, y ∈ w → v ∈ y) := by
          simp only [Intersection, dif_pos h_exists]
        have h := choose_spec (SpecificationUnique (choose h_exists) (fun v => ∀ y, y ∈ w → v ∈ y))
        -- Now use the equivalence to convert hx_in_intersection
        have hx_in_specset : x ∈ SpecSet (choose h_exists) (fun v => ∀ y, y ∈ w → v ∈ y) := h_inter_def.mp hx_in_intersection
        exact ((SpecSet_is_specified (choose h_exists) x (fun v => ∀ y, y ∈ w → v ∈ y)).mp hx_in_specset).right
      · -- Dirección <-
        intro hx_in_intersection
        have h := choose_spec (SpecificationUnique (choose h_inter_nonempty) (fun v => ∀ y, y ∈ w → v ∈ y))
        have hx_in_specset : x ∈ SpecSet (choose h_inter_nonempty) (fun v => ∀ y, y ∈ w → v ∈ y) :=
          (SpecSet_is_specified (choose h_inter_nonempty) x (fun v => ∀ y, y ∈ w → v ∈ y)).mpr (
            And.intro
              (by
                -- x ∈ choose h_inter_nonempty follows from member_intersection w x and choose h_inter_nonempty ∈ w
                exact hx_in_intersection (choose h_inter_nonempty) (choose_spec h_inter_nonempty))
              (fun y hy_in_w => hx_in_intersection y hy_in_w)
          )
        -- Use the equivalence to convert back to membership in Intersection
        -- By definition of Intersection, x ∈ (⋂ w) ↔ x ∈ SpecSet (choose h_inter_nonempty) (fun v => ∀ y, y ∈ w → v ∈ y)
        have h_inter_def : x ∈ (⋂ w) ↔ x ∈ SpecSet (choose h_inter_nonempty) (fun v => ∀ y, y ∈ w → v ∈ y) := by
          simp only [Intersection, dif_pos h_inter_nonempty]
        exact h_inter_def.mpr hx_in_specset

    /-! ### Teorema de existencia única del conjunto Intersección ### -/
    @[simp] theorem Intersection_unique_set (w : U) : w ≠ (∅ : U) → ∃! (z : U), ∀ (v : U), v ∈ z ↔ member_intersection w v
      := by
    intro h_nonempty
    by_cases h_intersection_nonempty : (⋂ w) ≠ ∅
    . -- Si la intersección es no vacía, entonces existe un elemento en w
      have h_exists : ∃ y, y ∈ w := (nonempty_iff_exists_mem w).mp h_nonempty
      -- Provide all required arguments: w, (⋂ w), h_nonempty, h_exists
      apply ExistsUnique.intro (⋂ w)
      · -- Existence: (⋂ w) satisfies the specification
        exact fun v => (Intersection_is_specified w v h_nonempty h_exists)
      · -- Uniqueness: any z satisfying the specification is equal to (⋂ w)
        intro z hz_spec
        apply ExtSet
        intro v
        constructor
        · intro hv_in_z
          have h := hz_spec v
          exact (Intersection_is_specified w v h_nonempty h_exists).mpr (h.mp hv_in_z)
        · intro hv_in_inter
          have h := hz_spec
          exact (h v).mpr ((Intersection_is_specified w v h_nonempty h_exists).mp hv_in_inter)
    . -- Si la intersección es vacía, entonces el conjunto vacío cumple la especificación
      apply ExistsUnique.intro ∅
      · -- Existencia: ∅ cumple la especificación
        intro v
        constructor
        · intro hv_in_empty
          exfalso
          exact EmptySet_is_empty v hv_in_empty
        · intro h_member_intersection
          exfalso
          -- member_intersection w v requires v ∈ y for all y ∈ w, but w ≠ ∅, so contradiction
          have h_exists : ∃ y, y ∈ w := (nonempty_iff_exists_mem w).mp h_nonempty
          rcases h_exists with ⟨y, hy_in_w⟩
          have h_v_in_y := h_member_intersection y hy_in_w
          -- But ∅ has no elements
          exact EmptySet_is_empty v h_v_in_y
      · -- Unicidad: cualquier z que cumple la especificación es igual a ∅
        intro z hz_spec
        apply ExtSet
        intro v
        constructor
        · intro hv_in_z
          exfalso
          exact EmptySet_is_empty v hv_in_empty
        · intro hv_in_empty
          exfalso
          exact EmptySet_is_empty v hv_in_empty


    -- Theorem: Intersection is specified by the intersection of a family of sets
    /-! ### Teorema que ∀ (x : U), x ∈ W → ⋂ W ⊆ x ### -/
    @[simp] theorem Intersection_subset (W : U) (x : U) : x ∈ W → (⋂ W) ⊆ x
      := by
    intro hx_in_W z hz_in_intersection
    have h_nonempty : W ≠ ∅ := by
      intro h_empty
      rw [h_empty] at hx_in_W
      exact EmptySet_is_empty x hx_in_W
    have hz_member_intersection := (Intersection_is_specified W h_nonempty z).mp hz_in_intersection
    unfold member_intersection at hz_member_intersection
    exact hz_member_intersection x hx_in_W

    /-! ### Inversión de ser subconjunto W ⊆ V → ⋂V ⊆ ⋂W ### --/
    @[simp] theorem Intersection_subset_of_superset (W V : U) : ( W ≠ ∅ ∧ V ≠ ∅ ) → ( W ⊆ V → (⋂ V) ⊆ (⋂ W) )
      := by
    intro h_nonempty h_w_subs_v z hz_in_intersection_v
    have h_nonempty_w : W ≠ ∅ := h_nonempty.1
    have h_nonempty_v : V ≠ ∅ := h_nonempty.2
    have hz_member_intersection_v := (Intersection_is_specified V h_nonempty_v z).mp hz_in_intersection_v
    unfold member_intersection at hz_member_intersection_v
    have hz_member_intersection_w : member_intersection W z := by
      unfold member_intersection
      intro y hy_in_w
      exact hz_member_intersection_v y (h_w_subs_v y hy_in_w)
    exact (Intersection_is_specified W h_nonempty_w z).mpr hz_member_intersection_w

    /-! ### Si un elemento de la familia a interseccionar es vacío, la intersección es vacía ### -/
    @[simp] theorem Intersection_empty_if_empty (W : U) : (∃ (x : U), x ∈ W ∧ x = ∅) → ((⋂ W) = ∅)
      := by
    intro h_exists_empty
    have h_nonempty : W ≠ ∅ := by
      intro h_empty
      have h := choose_spec h_exists_empty
      have h_mem : choose h_exists_empty ∈ W := h.left
      have h_mem_empty : choose h_exists_empty ∈ ∅ := h_empty ▸ h_mem
      exact EmptySet_is_empty (choose h_exists_empty) h_mem_empty
    apply (ExtSet (⋂ W) ∅)
    intro z
    constructor
    · -- Dirección ->
      intro hz_in_intersection
      exfalso
      have h := choose_spec h_exists_empty
      have h_empty_in_w : choose h_exists_empty ∈ W := h.left
      have h_empty_eq : choose h_exists_empty = ∅ := h.right
      have hz_in_empty : z ∈ choose h_exists_empty := by
        have hz_member_intersection := (Intersection_is_specified W h_nonempty z).mp hz_in_intersection
        unfold member_intersection at hz_member_intersection
        exact hz_member_intersection (choose h_exists_empty) h_empty_in_w
      rw [h_empty_eq] at hz_in_empty
      exact EmptySet_is_empty z hz_in_empty
    · -- Dirección <-
      intro hz_in_empty
      exfalso
      exact EmptySet_is_empty z hz_in_empty

    /-! ### ⋂{A , B} = A ∩ B ### -/
    @[simp] theorem Intersection_of_pair (A B : U) : (⋂ { A , B }) = (A ∩ B)
        := by
      apply ExtSet
      intro z
      constructor
      · -- Dirección ->
        intro hz_in_intersection
        have h_nonempty : ({ A , B }) ≠ EmptySet := PairSet_is_nonempty A B
        have hz_member_intersection := (Intersection_is_specified ({ A , B } : U) h_nonempty z).mp hz_in_intersection
        unfold member_intersection at hz_member_intersection
        have hz_in_A : z ∈ A := hz_member_intersection A ((PairSet_is_specified A B A).mpr (Or.inl rfl))
        have hz_in_B : z ∈ B := hz_member_intersection B ((PairSet_is_specified A B B).mpr (Or.inr rfl))
        exact (BinIntersection_is_specified A B z).mpr ⟨hz_in_A, hz_in_B⟩
      · -- Dirección <-
        intro hz_in_A_and_B
        unfold Intersection
        have h_exists : ∃ y, y ∈ ({ A , B } : U) := by
          by_contra h_not_exists
          push_neg at h_not_exists
          have h_empty : ({ A , B } : U) = (∅ : U) := by
            apply ExtSet
            intro y
            constructor
            · intro hy_in_pair_set
              exfalso
              exact h_not_exists y hy_in_pair_set
            · intro hy_in_empty
              exfalso
              exact EmptySet_is_empty y hy_in_empty
          exfalso
          exact PairSet_is_nonempty A B h_empty
        simp only [dif_pos h_exists]
        have h := SpecSet_is_specified (choose h_exists) (fun v => ∀ y, y ∈ ({ A , B } : U) → (v ∈ y)) z
        have hz_in_A_and_B_spec := (BinIntersection_is_specified A B z).mp hz_in_A_and_B
        have hz_in_A : z ∈ A := hz_in_A_and_B_spec.left
        have hz_in_B : z ∈ B := hz_in_A_and_B_spec.right
        have h_choose_in_pair := choose_spec h_exists
        have h_choose_spec := PairSet_is_specified A B (choose h_exists)
        cases (h_choose_spec.mp h_choose_in_pair) with
        | inl h_eq => -- choose h_exists = A
          exact h.mpr ⟨h_eq.symm ▸ hz_in_A, fun y hy_in_pair =>
            have h_spec := PairSet_is_specified A B y
            match h_spec.mp hy_in_pair with
            | Or.inl h_eq_A => h_eq_A ▸ hz_in_A
            | Or.inr h_eq_B => h_eq_B ▸ hz_in_B⟩
        | inr h_eq => -- choose h_exists = B
          exact h.mpr ⟨h_eq.symm ▸ hz_in_B, fun y hy_in_pair =>
            have h_spec := PairSet_is_specified A B y
            match h_spec.mp hy_in_pair with
            | Or.inl h_eq_A => h_eq_A ▸ hz_in_A
            | Or.inr h_eq_B => h_eq_B ▸ hz_in_B⟩

    /-! ### ⋂{A} = A ### -/
    @[simp] theorem Intersection_of_singleton (A : U) : (⋂ { A }) = A
      := by
    apply ExtSet
    intro z
    constructor
    · -- Dirección ->
      intro hz_in_intersection
      have h_nonempty : ({ A } : U) ≠ EmptySet := PairSet_singleton_is_nonempty A
      have hz_member_intersection := (Intersection_is_specified { A } h_nonempty z).mp hz_in_intersection
      unfold member_intersection at hz_member_intersection
      exact hz_member_intersection A ((PairSet_is_specified A A A).mpr (Or.inl rfl))
    · -- Dirección <-
      intro hz_in_A
      unfold Intersection
      have h_exists : ∃ y, y ∈ ({ A } : U) := by
        by_contra h_not_exists
        push_neg at h_not_exists
        have h_empty : ({ A } : U) = (∅ : U) := by
          apply ExtSet
          intro y
          constructor
          · intro hy_in_pair_set
            exfalso
            exact h_not_exists y hy_in_pair_set
          · intro hy_in_empty
            exfalso
            exact EmptySet_is_empty y hy_in_empty
        exact PairSet_singleton_is_nonempty A h_empty
      simp only [dif_pos h_exists]
      have h := SpecSet_is_specified (choose h_exists) (fun v => ∀ y, y ∈ ({ A } : U) → (v ∈ y)) z
      have h_choose_in_singleton := choose_spec h_exists
      have h_choose_spec := Singleton_is_specified A (choose h_exists)
      have h_choose_eq_A : choose h_exists = A := h_choose_spec.mp h_choose_in_singleton
      exact h.mpr ⟨h_choose_eq_A.symm ▸ hz_in_A, fun y hy_in_singleton =>
        have h_spec := Singleton_is_specified A y
        (h_spec.mp hy_in_singleton) ▸ hz_in_A⟩

    /-! ### Definición del Par Ordenado (x,y) = { { x } , { x , y } } ### -/
    noncomputable def OrderedPair (x y : U) : U := (({ (({ x }): U) , (({ x , y }): U) }): U)

    /-! ### Notación estándar del Par Ordenado (x,y) = { { x } , { x , y } } ### -/
    notation " ⟨ " x " , " y " ⟩ " => OrderedPair x y

    @[simp] theorem OrderedPair_is_specified (x y : U) :
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

    @[simp] theorem OrderedPair_unique  {z : U} (x y : U) (hz_ordered_pair : ∀ (w : U), w ∈ z ↔ (w = { x } ∨ w = { x , y })) :
    z = ⟨ x, y ⟩
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

    @[simp] lemma nonempty_iff_exists_mem (w : U) : w ≠ ∅ ↔ ∃ y, y ∈ w := by
    constructor
    · intro h_nonempty
      by_contra h_not_exists
      push_neg at h_not_exists
      have h_empty : w = ∅ := by
        apply ExtSet
        intro y
        constructor
        · intro hy_in_w
          exfalso
          exact h_not_exists y hy_in_w
        · intro hy_in_empty
          exfalso
          exact EmptySet_is_empty y hy_in_empty
      exact h_nonempty h_empty
    · intro h_exists
      intro h_empty
      rcases h_exists with ⟨y, hy_in_w⟩
      rw [h_empty] at hy_in_w
      exact EmptySet_is_empty y hy_in_w

    /-! ### Función que dice (`Prop`) si un conjunto `w` tiene un solo elemento ### -/
    def isSingleton_concept (w : U) : Prop :=
      (w ≠ ∅) ∧ (∀ (x : U), x ∈ w → ∀ (y : U), y ∈ w → x = y)

    def isSingleton (w : U) : Prop :=
      if h : ∀ (x : U), x ∉ w then
        False -- El conjunto vacío no es un singleton
              -- El vacío no tiene elementos (0)
      else
        have h_exists : ∃ t, t ∈ w := by push_neg at h; exact h
        let v : U := choose h_exists
        let y : U := w \ ({ v } : U)
        if v ≠ (∅ : U) then
          False  -- Caso que más de un solo elemento
        else
          True   -- Caso que tiene un solo elemento (singleton)

    /-! ### Función que dice (`Prop`) si un conjunto `w` tiene dos elementos ### -/
    def isPairOfElements_concept (w : U) : Prop :=
      (w ≠ ∅) ∧ (∃ (x y : U), (x ≠ y) ∧ (w = ({ x , y }: U)))

    def isPairOfElements (w : U) : Prop :=
      if h : ∀ (x : U), x ∉ w then
        False -- El vacío no tiene elementos (0)
      else
        have h_exists : ∃ t, t ∈ w := by push_neg at h; exact h
        let v : U := choose h_exists
        let y : U := w \ ({ v } : U)
        if h_y_nonempty : ∃ (t : U), t ∈ y then
          let s : U := choose h_y_nonempty
          let z : U := y \ {s}
          if h_z_nonempty : ∃ (t : U), t ∈ z then
            False -- Caso que más de dos elementos
          else
            True -- Caso que tiene dos elementos (no necesariamente par ordenado)
        else
          False -- Caso que tiene un solo elemento (singleton no necesariamente par diagonal)

    /-! ### Función que dice (`Prop`) si un conjunto `w` es un par ordenado diagonal ### -/
    def isDiagonalOrderedPair_concept (w : U) : Prop :=
      (isSingleton_concept w) ∧ (isSingleton_concept (⋂ w))

    def isDiagonalOrderedPair_concept_2 (w : U) : Prop :=
      ∃ (x : U), w = ({ ({ x }: U) } : U)

    def isDiagonalOrderedPair_concept_3 (w : U) : Prop :=
      ∃ (x : U), w = ( ⟨ x , x ⟩ : U )

    def isDiagonalOrderedPair (w : U) : Prop :=
      if h : ∀ (x : U), x ∉ w then
        False -- El vacío no tiene elementos (0)
      else
        if h_single : isSingleton w then
          let v : U := choose (by push_neg at h; exact h)
          (isSingleton v)
        else
          False

    /-! ### Función que dice (`Prop`) si un conjunto `w` es un par ordenado no diagonal ### -/
    def isNonDiagonalOrderedPair_concept (w : U) : Prop :=
      ∃ (x y : U), (x ≠ y) ∧ w = ({ ({ x }: U), ({ x , y }: U) }: U)

    def isNonDiagonalOrderedPair_concept_2 (w : U) : Prop :=
      ∃ (x y : U), (x ≠ y) ∧ w = (⟨ x , y ⟩ : U)

    def isNonDiagonalOrderedPair (w : U) : Prop :=
    if ∀ (x : U), x ∉ w then
      False -- El vacío no tiene elementos (0)
    else
      if isDiagonalOrderedPair w then
        False -- Caso que es un par ordenado diagonal
      else
        if isPairOfElements w then
          let v : U := {(⋂ w)}
          let z : U := w \ v
          if ∃ (t : U), t ∈ v then
            if ∃ (t : U), t ∈ z then
              if v ⊂ z then
                isSingleton (z \ v)
              else if z ⊂ v then
                isSingleton (v \ z)
              else
                False
          else
            False -- Si la intersección es vacía no puede ser un par ordenado
        else
          False -- Caso que no son dos elementos (no es un par ordenado)
      else
        False -- Caso que no es un par ordenado (no es un par ordenado diagonal o no diagonal)

    /-! ### Función que dice (`Prop`) si un conjunto `w` es un par ordenado ### -/
    def isOrderedPair_concept (w : U) : Prop :=
      ∃ (x y : U), w = (⟨ x , y ⟩  : U)

    def isOrderedPair (w : U) : Prop :=
      isDiagonalOrderedPair w ∨ isNonDiagonalOrderedPair w

    /-! ### Teorema de que un par ordenado es un conjunto no vacío ### -/
    @[simp] theorem OrderedPair_is_nonempty (x y : U) :
    ⟨ x, y ⟩  ≠ (∅: U)
      := by
    intro h_empty
    have h_ordered_pair : ⟨ x, y ⟩ = { { x } , { x , y } } := rfl
    have h_singleton_x_in_pair : (({ x }): U) ∈ ( (⟨ x , y ⟩): U ) := by
      rw [h_ordered_pair]
      exact (PairSet_is_specified {x} {x, y} {x}).mpr (Or.inl rfl)
    rw [h_empty] at h_singleton_x_in_pair
    exfalso
    exact EmptySet_is_empty {x} h_singleton_x_in_pair

    @[simp] theorem IntersectionOrderedPair_is_nonempty (x y : U) :
    (⋂ (⟨ x , y ⟩)) ≠ (∅: U)
      := by
    intro h_empty
    have h_ordered_pair : (⟨ x , y ⟩) = { { x } , { x , y } } := rfl
    have h_singleton_x_in_pair : {x} ∈ ((⟨ x , y ⟩): U) := by
      rw [h_ordered_pair]
      exact (PairSet_is_specified {x} {x, y} {x}).mpr (Or.inl rfl)
    have h_intersection : (⋂ (⟨ x , y ⟩)) = {x} := by
      rw [h_ordered_pair, Intersection_of_pair]
      apply ExtSet
      intro z
      rw [BinIntersection_is_specified, Singleton_is_specified, PairSet_is_specified]
      tauto
    rw [h_intersection] at h_empty
    have h_singleton_nonempty := PairSet_singleton_is_nonempty x
    exact h_singleton_nonempty h_empty

    noncomputable def fst (w : U) : U := (⋂ (⋂ w))

    noncomputable def snd (w : U) : U :=
    let v₀ : U := (⋂ w) -- v₀ = { x }
    let v : U := { v₀ } -- v = { { x } }
    let s : U := (w \ v) -- s = { { x , y } }
    let s₀ : U := (⋂ s) -- s₀ = { x , y }
    let r₀ : U := (s₀ \ v₀) -- r₀ = { y }
    let r₁ : U := (⋂ r₀)  -- r₁ = y
                          -- evalua a y = (⋂ ((⋂ (w \ {(⋂ w)})) \ (⋂ w))) -- w = ⟨ x, y ⟩ = { { x } , { x , y } } , x ≠ y
    if r₁ = (∅ : U) then
      ⋂ v₀ -- evalua a x = (⋂ (⋂ w)) -- w = ⟨ x, y ⟩ = { { x } , { x , y } } , x ≠ y
    else
      r₁ -- evalua a y

    @[simp] theorem OrderedPairSet_is_specified (x y : U) :
    ∀ (z : U), z ∈ (⟨ x , y ⟩: U) ↔ (z = ({ x }: U) ∨ z = ({ x , y }: U))
      := by
    intro z
    exact OrderedPair_is_specified x y z

    @[simp] theorem OrderedPairSet_unique (x y : U) (z : U)
    (hz_ordered_pair : ∀ (w : U), w ∈ z ↔ (w = ({ x }: U) ∨ w = ({ x , y }: U))) :
    z = ⟨ x, y ⟩
      := by
    apply OrderedPair_unique x y hz_ordered_pair

    /-! ### Necesitamos unos cuantos lemas para usar en el teroema principal. ### TO DO -/ -- TO DO
    @[simp] theorem OrderedPair_functRet_isOrderedPair_x_eq_y (x y : U) (h_eq : x = y) :
      isOrderedPair_concept (⟨ x , y ⟩ : U)
        := by sorry
    -- TO DO: Completar la demostración de este teorema.

    @[simp] theorem OrderedPair_functRet_isOrderedPair_x_ne_y (x y : U) (h_ne : x ≠ y) :
      isOrderedPair_concept (⟨ x , y ⟩ : U)
        := by sorry

    @[simp] theorem OrderedPair_functRet_isOrderedPair (x y : U):
        isOrderedPair_concept (⟨ x , y ⟩ : U)
          := by
        -- Por casos (h_eq: x=y) o (h_ne: x≠y).
        by_cases h_eq : x = y
        · -- Caso x = y
          exact OrderedPair_functRet_isOrderedPair_x_eq_y x y h_eq
        · -- Caso x ≠ y
          exact OrderedPair_functRet_isOrderedPair_x_ne_y x y h_eq

    -- Demostración de que fst recupera el primer elemento.
    @[simp] theorem fst_of_ordered_pair (x y : U) : fst ⟨x, y⟩ = x :=
      by sorry

    -- Demostración de que snd recupera el segundo elemento.
    -- Esta prueba es más compleja porque debe considerar si x = y o no.
    @[simp] theorem snd_of_ordered_pair (x y : U) : snd ⟨x, y⟩ = y :=
      by sorry

    -- El teorema principal que une todo.
    @[simp] theorem OrderedPairSet_is_WellConstructed (w : U) :
      (isOrderedPair w) → w = (⟨ fst w, snd w ⟩ : U) :=
      by sorry

    /-! ### Relaciones y Funciones: Inyectividad, Sobreyectividad, Equivalencia y Orden ### -/

    noncomputable def isRelation (w : U) : Prop :=
      ∀ (z : U), (z ∈ w) ↔ (isOrderedPair_concept z)

    noncomputable def isRelation_in_Sets (A B R : U) : Prop :=
      ∀ (z : U), z ∈ R → ∃ (x y : U), z = ⟨ x , y ⟩ → x ∈ A ∧ y ∈ B

    noncomputable def domain (R : U) : U :=
      SpecSet (fst R) (fun x => ∃ y, ⟨ x , y ⟩ ∈ R)

    noncomputable def range (R : U) : U :=
      SpecSet (snd R) (fun y => ∃ x, ⟨ x , y ⟩ ∈ R)

    noncomputable def isReflexive (w : U) : Prop :=
      ∃ (x y : U), ⟨ x , y ⟩ ∈ w → ⟨ x , x ⟩ ∈ w

    noncomputable def isReflexive_in_Set ( A R : U ) : Prop :=
      ∃ (x : U), x ∈ A → ⟨ x , x ⟩ ∈ R

    noncomputable def isIReflexive (w : U) : Prop :=
      ∀ (x : U), ⟨ x , x ⟩ ∉ w

    noncomputable def isSymmetric (w : U) : Prop :=
      ∀ (x y : U), ⟨ x , y ⟩ ∈ w → ⟨ y , x ⟩ ∈ w

    noncomputable def isAsymmetric (w : U) : Prop :=
      ∀ (x y : U), ⟨ x , y ⟩ ∈ w → ⟨ y , x ⟩ ∉ w

    noncomputable def isAntiSymmetric (w : U) : Prop :=
      ∀ (x y : U), ⟨ x , y ⟩ ∈ w → ⟨ y , x ⟩ ∈ w → x = y

    noncomputable def isTransitive (w : U) : Prop :=
      ∀ (x y z : U), ⟨ x , y ⟩ ∈ w → ⟨ y , z ⟩ ∈ w → ⟨ x , z ⟩ ∈ w

    noncomputable def isEquivalenceRelation (w : U) : Prop :=
      isReflexive w ∧ isSymmetric w ∧ isTransitive w

    noncomputable def isEquivalenceRelation_in_Set (A R : U) : Prop :=
      isReflexive_in_Set A R ∧ isSymmetric R ∧ isTransitive R

    noncomputable def isPartialOrder (R : U) : Prop :=
      isReflexive R ∧ isAntiSymmetric R ∧ isTransitive R

    noncomputable def isStrictOrder (R : U) : Prop :=
      isAsymmetric R ∧ isTransitive R

    noncomputable def isWellDefined (R : U) : Prop :=
      ∀ (x y₁ y₂ : U), ⟨ x , y₁ ⟩ ∈ R → ⟨ x , y₂ ⟩ ∈ R → y₁ = y₂

    noncomputable def isTotalOrder (R : U) : Prop :=
      isPartialOrder R ∧ ∀ (x y : U), x ≠ y → ⟨ x , y ⟩ ∈ R ∨ ⟨ y , x ⟩ ∈ R

    noncomputable def isWellFounded (R : U) : Prop :=
      ∀ (A : U), A ≠ ∅ → ∃ (x : U), x ∈ A ∧ ∀ (y : U), ⟨ y , x ⟩ ∈ R → y ∉ A

    noncomputable def isFunction (A R : U) : Prop :=
      ∀ (x : U), x ∈ A → ∃ (y₁ : U), ∀ (y₂ : U), ⟨ x , y₁ ⟩ ∈ R → ⟨ x , y₂ ⟩ ∈ R → y₁ = y₂

    noncomputable def isInyective (R : U) : Prop :=
      ∀ (x₁ x₂ : U), ∃ (y : U), ⟨ x₁ , y ⟩ ∈ R → ⟨ x₂ , y ⟩ ∈ R → x₁ = x₂

    noncomputable def isSurjectiveFunction (A B R : U) : Prop :=
      ∀ (y : U), y ∈ B → ∃ (x : U), x ∈ A ∧ ⟨ x , y ⟩ ∈ R

    noncomputable def isBijectiveFunction (A B R : U) : Prop :=
      isFunction A R ∧ isInyective R ∧ isSurjectiveFunction A B R

  end PairingAxiom
end SetUniverse

export SetUniverse.PairingAxiom (
    Pairing PairingUniqueSet
    PairSet PairSet_is_specified PairSet_unique
    Singleton Singleton_is_specified Singleton_unique
    PairSet_is_nonempty PairSet_singleton_is_nonempty
    member_intersection Intersection Intersection_is_specified
    Intersection_unique_set Intersection_subset
    OrderedPair OrderedPair_is_specified OrderedPair_unique
    fst snd
    OrderedPairSet_is_specified OrderedPairSet_unique
    OrderedPairSet_is_WellConstructed
    Intersection_of_pair Intersection_of_singleton
    Intersection_subset_of_superset
    Intersection_empty_if_empty
    isRelation isRelation_in_Sets
    domain range
    isReflexive isReflexive_in_Set
    isIReflexive isSymmetric isAsymmetric isAntiSymmetric
    isTransitive isEquivalenceRelation isEquivalenceRelation_in_Set
    isPartialOrder isStrictOrder isWellDefined
    isFunction isInyective isSurjectiveFunction isBijectiveFunction
)

/-
  w = ⟨ x, y ⟩ = { { x } , { x , y } }

  fst w = choose (∃ (z : U), z ∈ (⋂ w))
  snd w = choose (∃ (z : U), z ∈ ( ( w \ { ⋂ w } ) \ (⋂ w) ) )

  w = ⟨ x, y ⟩ = { { x } , { x , y } }
  fst w  -- No interfiere si x = y o si x ≠ y
    ⋂ w = { x } ∩ { x, y } = { x }
    ∃! (z: U), z ∈ ⋂ w ↔ z = x
    ∃! (z: U), z ∈ { x } ↔ z = x

  w = { }
  { x } = ∅ !!!
  { x , y } = ∅ !!!

  snd w
    -- caso x ≠ y
    ⋂ w = { x } ∩ { x, y } = { x }
    {⋂ w} ={ { x } }
    s = w \ { ⋂ w } = { { x }, { x  , y } } \ { { x } } =
      = { { x  , y } }
    z = choose ( ∃ (z : U), z ∈ s )
    z == { x , y }
    t = z \ ⋂ w
    t == { x , y } \ { x } == { y }
    snd w = choose ( ∃ (z : U), z ∈ t )
    -- caso x = y
    ⋂ w = { x } ∩ { x, x } = { x }
    {⋂ w} ={ { x } }
    s = w \ { ⋂ w } = { { x }, { x  , x } } \ { { x } } =
      = { { x } } \ { { x } } = ∅
    snd w = s

    -- en general
    -- ⋂ w = { x } ∩ { x, y } = { x }
    -- {⋂ w} ={ { x } }
    -- s = w \ { ⋂ w } = { { x }, { x  , y } } \ { { x } } =
    --   = { { x  , y } }
    let s : U := w \ { (⋂ w) }
    if h: s = ∅ then
      ∅
    else
      let z : U := choose ( ∃ (z : U), z ∈ s )
      -- z == { x , y }
      let t : U := z \ (⋂ w)
      -- t == { x , y } \ { x } == { y }
      choose ( ∃ (z : U), z ∈ t )

    let s : U := w \ { (⋂ w) }
    if h: s = ∅ then
      ∅
    else
      let z : U := choose ( ∃ (z : U), z ∈ s )
      let t : U := z \ (⋂ w)
      choose ( ∃ (z : U), z ∈ t )
-/
