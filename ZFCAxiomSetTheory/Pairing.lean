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
    @[simp]
    noncomputable def ExistsAnElementInSet {U : Type u} (w : U) (h : ∃ y, y ∈ w) : ∃ y, y ∈ w := h

    /-! ### Axioma de Pares (No Ordenados) ### -/
    @[simp]
    axiom Pairing (x y : U) :
      ∃ (z : U), ∀ (w : U), w ∈ z ↔ (w = x ∨ w = y)

    /-! ### Teorema de Existencia Única para el Axioma de Pares ### -/
    /-! ### PairingUnique : existe un único conjunto que cumple la especificación {x,y} ### -/
    @[simp]
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
    @[simp]
    noncomputable def PairSet (x y : U) : U :=
    choose (PairingUniqueSet x y)

    @[simp]
    theorem PairSet_is_specified (x y : U) :
    ∀ (z : U), z ∈ PairSet x y ↔ (z = x ∨ z = y)
      := by
    intro z
    exact (choose_spec (PairingUniqueSet x y)).1 z

    @[simp]
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

    @[simp]
    noncomputable def Singleton (x : U) : U := ({ x , x } : U)

    @[simp]
    theorem Singleton_is_specified (x z : U) :
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

    @[simp]
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

    @[simp]
    theorem PairSet_is_nonempty (x y : U) :
    PairSet x y ≠ ∅
      := by
    intro h_empty
    have h_pairing := choose_spec (PairingUniqueSet x y)
    have h_x_in_pairing : x ∈ PairSet x y := (h_pairing.1 x).mpr (Or.inl rfl)
    rw [h_empty] at h_x_in_pairing
    exfalso
    exact EmptySet_is_empty x h_x_in_pairing

    @[simp]
    theorem PairSet_singleton_is_nonempty (x : U) :
    Singleton x ≠ ∅
      := by
    intro h_empty
    have h_singleton := Singleton_is_specified x x
    have h_x_in_singleton : x ∈ Singleton x := h_singleton.mpr rfl
    rw [h_empty] at h_x_in_singleton
    exfalso
    exact EmptySet_is_empty x h_x_in_singleton

    /-! ### Definición de ser miembro (∈) de la Intersección de una Familia de Conjuntos ### -/
    @[simp] def
    member_intersection (w v : U) : Prop :=
      ∀ (y : U), ( y ∈ w ) → ( v ∈ y )

    /-! ### Definición del conjunto Intersección de una Familia de Conjuntos ### -/
    @[simp]
    noncomputable def Intersection (w : U) : U :=
    if h : ∃ y, y ∈ w then
      let y₀ := choose h
      SpecSet y₀ (fun v => ∀ y, y ∈ w → v ∈ y)
    else
      ∅ -- convención, debería ser U

    /-! ### Notación estándar de la Intersección de una Familia de Conjuntos ### -/
    notation " ⋂ " w => Intersection w

    @[simp]
    lemma nonempty_iff_exists_mem (w : U) : w ≠ ∅ ↔ ∃ y, y ∈ w := by
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

    @[simp]
    theorem Intersection_is_specified
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
    @[simp]
    theorem Intersection_unique_set (w : U) : w ≠ (∅ : U) → ∃! (z : U), ∀ (v : U), v ∈ z ↔ member_intersection w v
        := by
      intro h_nonempty
      have h_exists_y : ∃ y, y ∈ w := (nonempty_iff_exists_mem w).mp h_nonempty
      apply ExistsUnique.intro (⋂ w)
      · -- Existencia: (⋂ w) satisface la propiedad.
        intro v
        exact Intersection_is_specified w v h_nonempty h_exists_y
      · -- Unicidad: cualquier z que satisface la propiedad es igual a (⋂ w).
        intro z hz_spec
        apply ExtSet
        intro v
        constructor
        · -- Dirección: v ∈ z → v ∈ (⋂ w)
          intro hv_in_z
          have h_v_mem_inter_w := (hz_spec v).mp hv_in_z
          exact (Intersection_is_specified w v h_nonempty h_exists_y).mpr h_v_mem_inter_w
        · -- Dirección: v ∈ (⋂ w) → v ∈ z
          intro hv_in_inter_w
          have h_v_mem_inter_w := (Intersection_is_specified w v h_nonempty h_exists_y).mp hv_in_inter_w
          exact (hz_spec v).mpr h_v_mem_inter_w

    -- Theorem: Intersection is specified by the intersection of a family of sets
    /-! ### Teorema que ∀ (x : U), x ∈ W → ⋂ W ⊆ x ### -/
    @[simp]
    theorem Intersection_subset (W x : U) :
      x ∈ W → (⋂ W) ⊆ x
        := by
      intro hx_in_W z hz_in_intersection
      let h_intersection_nonempty : U → Prop := fun W => ∃ (y : U), y ∈ ((⋂ W) : U)
      have h_nonempty : W ≠ ∅ := by
        intro h_empty
        rw [h_empty] at hx_in_W
        exact EmptySet_is_empty x hx_in_W
      by_cases h_intersection_nonempty : ∃ (y : U), y ∈ ((⋂ (W : U)) : U)
      case pos =>
        have h_intersection := choose_spec (Intersection_unique_set W h_nonempty)
        let h_exists_y := (nonempty_iff_exists_mem W).mp h_nonempty
        have hz_member_intersection := (Intersection_is_specified W z h_nonempty h_exists_y).mp hz_in_intersection
        unfold member_intersection at hz_member_intersection
        exact hz_member_intersection x hx_in_W
      case neg =>
        -- If the intersection is empty, then it is a subset of any set
        have h_empty_intersection : ((⋂ (W : U)) : U) = (∅ : U) := by
          apply ExtSet
          intro y
          constructor
          · intro hy_in_intersection
            -- If y ∈ ⋂ W, then ∃ y, y ∈ ⋂ W, contradiction
            exfalso
            exact h_intersection_nonempty ⟨y, hy_in_intersection⟩
          · intro hy_in_empty
            -- y ∈ ∅ is impossible
            exfalso
            exact EmptySet_is_empty y hy_in_empty
        have hz_in_empty : z ∈ ∅ := by rw [←h_empty_intersection]; exact hz_in_intersection
        exfalso
        exact EmptySet_is_empty z hz_in_empty

    /-! ### Inversión de ser subconjunto W ⊆ V → ⋂V ⊆ ⋂W ### --/
    @[simp]
    theorem Intersection_subset_of_superset (W V : U) :
      ( W ≠ ∅ ∧ V ≠ ∅ ) → ( W ⊆ V → (⋂ V) ⊆ (⋂ W) )
        := by
      intro h_nonempty h_w_subs_v z hz_in_intersection_v
      have h_nonempty_w : W ≠ ∅ := h_nonempty.1
      have h_nonempty_v : V ≠ ∅ := h_nonempty.2
      have h_exists_y : ∃ y, y ∈ V := (nonempty_iff_exists_mem V).mp h_nonempty_v
      have hz_member_intersection_v := (Intersection_is_specified V z h_nonempty_v h_exists_y).mp hz_in_intersection_v
      unfold member_intersection at hz_member_intersection_v
      have hz_member_intersection_w : member_intersection W z := by
        unfold member_intersection
        intro y hy_in_w
        exact hz_member_intersection_v y (h_w_subs_v y hy_in_w)
      let h_exists_y := (nonempty_iff_exists_mem W).mp h_nonempty_w
      exact (Intersection_is_specified W z h_nonempty_w h_exists_y).mpr hz_member_intersection_w

    /-! ### Si un elemento de la familia a interseccionar es vacío, la intersección es vacía ### -/
    @[simp]
    theorem Intersection_empty_if_empty (W : U) : (∃ (x : U), x ∈ W ∧ x = ∅) → ((⋂ W) = ∅)
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
          let h_exists_y := (nonempty_iff_exists_mem W).mp h_nonempty
          have hz_member_intersection := (Intersection_is_specified W z h_nonempty h_exists_y).mp hz_in_intersection
          unfold member_intersection at hz_member_intersection
          exact hz_member_intersection (choose h_exists_empty) h_empty_in_w
        rw [h_empty_eq] at hz_in_empty
        exact EmptySet_is_empty z hz_in_empty
      · -- Dirección <-
        intro hz_in_empty
        exfalso
        exact EmptySet_is_empty z hz_in_empty

    /-! ### ⋂{A , B} = A ∩ B ### -/
    @[simp]
    theorem Intersection_of_pair (A B : U) : (⋂ { A , B }) = (A ∩ B)
        := by
      apply ExtSet
      intro z
      constructor
      · -- Dirección ->
        intro hz_in_intersection
        have h_nonempty : ({ A , B }) ≠ EmptySet := PairSet_is_nonempty A B
        have h_exists_y : ∃ y, y ∈ ({ A , B } : U) := (nonempty_iff_exists_mem ({ A , B } : U)).mp h_nonempty
        have hz_member_intersection := (Intersection_is_specified ({ A , B } : U) z h_nonempty h_exists_y).mp hz_in_intersection
        unfold member_intersection at hz_member_intersection
        have hz_in_A : z ∈ A := hz_member_intersection A ((PairSet_is_specified A B A).mpr (Or.inl rfl))
        have hz_in_B : z ∈ B := hz_member_intersection B ((PairSet_is_specified A B B).mpr (Or.inr rfl))
        exact (BinIntersection_is_specified A B z).mpr ⟨hz_in_A, hz_in_B⟩
      · -- Dirección <-
        intro hz_in_A_and_B
        unfold Intersection
        have h_exists : ∃ y, y ∈ ({ A , B } : U) := by
          -- Directly construct an element in the pair set
          exact ⟨A, (PairSet_is_specified A B A).mpr (Or.inl rfl)⟩
        simp only [dif_pos h_exists]
        have h := SpecSet_is_specified (choose h_exists) z (fun v => ∀ y, y ∈ ({ A , B } : U) → (v ∈ y))
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
    @[simp]
    theorem Intersection_of_singleton (A : U) : (⋂ { A }) = A
        := by
      apply ExtSet
      intro z
      constructor
      · -- Dirección ->
        intro hz_in_intersection
        have h_nonempty : ({ A } : U) ≠ EmptySet := PairSet_singleton_is_nonempty A
        have h_exists_y : ∃ y, y ∈ ({ A } : U) := (nonempty_iff_exists_mem ({ A } : U)).mp h_nonempty
        have hz_member_intersection := (Intersection_is_specified ({ A } : U) z h_nonempty h_exists_y).mp hz_in_intersection
        unfold member_intersection at hz_member_intersection
        exact hz_member_intersection A ((PairSet_is_specified A A A).mpr (Or.inl rfl))
      · -- Dirección <-
        intro hz_in_A
        unfold Intersection
        have h_exists : ∃ y, y ∈ ({ A } : U) := ⟨A, (PairSet_is_specified A A A).mpr (Or.inl rfl)⟩
        simp only [dif_pos h_exists]
        have h := SpecSet_is_specified (choose h_exists) z (fun v => ∀ y, y ∈ ({ A } : U) → (v ∈ y))
        have h_choose_in_singleton := choose_spec h_exists
        have h_choose_spec := Singleton_is_specified A (choose h_exists)
        have h_choose_eq_A : choose h_exists = A := h_choose_spec.mp h_choose_in_singleton
        exact h.mpr ⟨h_choose_eq_A.symm ▸ hz_in_A, fun y hy_in_singleton =>
          have h_spec := Singleton_is_specified A y
          (h_spec.mp hy_in_singleton) ▸ hz_in_A⟩

    /-! ### Definición del Par Ordenado (x,y) = { { x } , { x , y } } ### -/
    @[simp]
    noncomputable def OrderedPair (x y : U) : U
        :=
      (({ (({ x }): U) , (({ x , y }): U) }): U)

    /-! ### Notación estándar del Par Ordenado (x,y) = { { x } , { x , y } } ### -/
    notation " ⟨ " x " , " y " ⟩ " => OrderedPair x y

    @[simp]
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

    @[simp]
    theorem OrderedPair_unique
      {z : U} (x y : U)
      (hz_ordered_pair : ∀ (w : U), w ∈ z ↔ (w = { x } ∨ w = { x , y })) :
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

    /-! ### Función que dice (`Prop`) si un conjunto `w` tiene un solo elemento ### -/
    @[simp]
    def isSingleton_concept (w : U) : Prop :=
      (w ≠ ∅) → (∀ (x : U), x ∈ w → ∀ (y : U), y ∈ w → x = y)

    @[simp]
    def isSingleton (w : U) : Prop :=
      ∀ (t : U), t ∈ w → t = ({ ((⋂ w) : U) } : U)


    /-! ### Función que dice (`Prop`) si un conjunto `w` tiene dos elementos ### -/
    @[simp]
    def isPairOfElements_concept (w : U) : Prop :=
      (w ≠ ∅) ∧ (∃ (x y : U), (x ≠ y) ∧ (w = ({ x , y }: U)))

    @[simp]
    def isPairOfElements (w : U) : Prop :=
      if h : ∃ (v : U), v ∈ w then
        let v₁ : U := Classical.choose h
        let w₁ : U := Difference w ({ v₁} : U)
        if h₁ : ∃ (v : U), v ∈ w₁ then
          let v₂ : U := Classical.choose h₁
          let w₂ : U := Difference w₁ ({ v₂ } : U)
          (isSingleton w₂) -- Verifica si el conjunto resultante tiene un solo elemento o tiene más de uno
        else
          False -- Caso que tiene un solo elemento (singleton)
      else
        False -- El vacío no tiene elementos (0)

    /-! ### Función que dice (`Prop`) si un conjunto `w` es un par ordenado diagonal ### -/
    @[simp]
    def isDiagonalOrderedPair_concept (w : U) : Prop :=
      (isSingleton_concept w) ∧ (isSingleton_concept (⋂ w))

    @[simp]
    def isDiagonalOrderedPair_concept_2 (w : U) : Prop :=
      ∃ (x : U), w = ({ ({ x }: U) } : U)

    @[simp]
    def isDiagonalOrderedPair_concept_3 (w : U) : Prop :=
      ∃ (x : U), w = ( ⟨ x , x ⟩ : U )

    @[simp]
    def isDiagonalOrderedPair (w : U) : Prop :=
      if h : ∀ (x : U), x ∉ w then
        False -- El vacío no tiene elementos (0)
      else
        if isSingleton w then
          let v : U := choose (not_forall.mp h)
          isSingleton v
        else
          False

    /-! ### Función que dice (`Prop`) si un conjunto `w` es un par ordenado no diagonal ### -/
    @[simp]
    def isNonDiagonalOrderedPair_concept (w : U) : Prop :=
      ∃ (x y : U), (x ≠ y) ∧ w = ({ ({ x }: U), ({ x , y }: U) }: U)

    @[simp]
    def isNonDiagonalOrderedPair_concept_2 (w : U) : Prop :=
      ∃ (x y : U), (x ≠ y) ∧ w = (⟨ x , y ⟩ : U)

    @[simp]
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
    @[simp]
    def isOrderedPair_concept (w : U) : Prop :=
      ∃ (x y : U), w = (⟨ x , y ⟩  : U)

    @[simp]
    def isOrderedPair (w : U) : Prop :=
      isDiagonalOrderedPair w ∨ isNonDiagonalOrderedPair w

    /-! ### Teorema de que un par ordenado es un conjunto no vacío ### -/
    @[simp]
    theorem OrderedPair_is_nonempty (x y : U) :
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

    @[simp]
    theorem IntersectionOrderedPair_is_nonempty (x y : U) :
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
        constructor
        · -- Prove z ∈ {x} ↔ z = x and z ∈ {x, y} ↔ (z = x ∨ z = y)
          intro h
          have h₁ : z ∈ ({x} : U) ↔ z = x := Singleton_is_specified x z
          have h₂ : z ∈ ({x, y} : U) ↔ (z = x ∨ z = y) := PairSet_is_specified x y z
          -- h : z ∈ {x} ∧ z ∈ {x, y}
          cases h with
          | intro hz_in_singleton hz_in_pairset =>
            exact hz_in_singleton
        · -- Converse
          intro h
          have h₁ : z ∈ ({x} : U) ↔ z = x := Singleton_is_specified x z
          have h₂ : z ∈ ({x, y} : U) ↔ (z = x ∨ z = y) := PairSet_is_specified x y z
          exact And.intro h (Or.inl h)
      rw [h_intersection] at h_empty
      have h_singleton_nonempty := PairSet_singleton_is_nonempty x
      exact h_singleton_nonempty h_empty

    @[simp]
    noncomputable def fst (w : U) : U := (⋂ (⋂ w))

    @[simp]
    noncomputable def fst_concept (w : U) : U :=
      if h : ∃ (v₀ : U), v₀ ∈ w then
        let u₀ : U := Classical.choose h
        u₀
      else
        (∅: U) -- convención, debería ser U

    @[simp]
    noncomputable def snd (w : U) : U :=
      let I := ⋂ w -- Esto es {x}
      let s := w \ {I} -- Esto es {{x, y}} si x≠y, y es ∅ si x=y
      if h : s = ∅ then -- Esta condición ahora distingue perfectamente el caso diagonal
        ⋂ I -- Si s es vacío, x=y, así que devolvemos x (que es y)
      else -- Si s no es vacío, entonces x≠y
        -- 's' no es vacío, así que podemos tomar su único elemento, que es {x,y}
        have h_exists : ∃ y, y ∈ s := (nonempty_iff_exists_mem s).mp h
        let s_elem := choose h_exists
        -- A {x,y} le quitamos {x}, lo que nos deja {y}
        let r := s_elem \ I
        -- La intersección de {y} es y
        ⋂ r

    @[simp]
    noncomputable def snd_concept (w : U) : U :=
      -- Como fst_concept pero para el segundo elemento.
      if h : ∃ (x y : U), w = (⟨ x , y ⟩  : U) then
        let uv : U := (choose h)
        snd uv
      else
        (∅: U) -- convención, debería ser U

    @[simp]
    theorem OrderedPairSet_is_specified (x y : U) :
      ∀ (z : U), z ∈ (⟨ x , y ⟩: U) ↔ (z = ({ x }: U) ∨ z = ({ x , y }: U))
        := by
      intro z
      exact OrderedPair_is_specified x y z

    @[simp]
    theorem OrderedPairSet_unique
        (x y z : U)
        (hz_ordered_pair : ∀ (w : U), w ∈ z ↔ (w = ({ x }: U) ∨ w = ({ x , y }: U))) :
      z = ⟨ x, y ⟩
        := by
      apply OrderedPair_unique x y hz_ordered_pair

    /-! ### Necesitamos unos cuantos lemas para usar en el teroema principal. ### TO DO -/ -- TO DO
    @[simp]
    theorem OrderedPair_functRet_isOrderedPair_x_eq_y (x y : U) (h_eq : x = y) :
      isOrderedPair_concept (⟨ x , y ⟩ : U)
        := by
      -- El objetivo es demostrar: ∃ a b, ⟨ x, y ⟩ = ⟨ a, b ⟩
      unfold isOrderedPair_concept
      -- Usamos la hipótesis h_eq para simplificar el par ordenado
      rw [h_eq]
      -- Ahora el objetivo es: ∃ a b, ⟨ y, y ⟩ = ⟨ a, b ⟩
      -- Proporcionamos 'y' y 'y' como los testigos para 'a' y 'b'
      apply Exists.intro y
      apply Exists.intro y
      -- El objetivo se convierte en ⟨ y, y ⟩ = ⟨ y, y ⟩, lo cual es verdadero por reflexividad.
      rfl

    @[simp]
    theorem OrderedPair_functRet_isOrderedPair (x y : U) :
      isOrderedPair_concept (⟨ x , y ⟩ : U)
        := by
      -- El objetivo es demostrar: ∃ a b, ⟨ x, y ⟩ = ⟨ a, b ⟩
      unfold isOrderedPair_concept
      -- Proporcionamos 'x' y 'y' como los testigos para 'a' y 'b'
      apply Exists.intro x
      apply Exists.intro y
      -- El objetivo se convierte en ⟨ x, y ⟩ = ⟨ x, y ⟩, lo cual es verdadero por reflexividad.
      rfl

    -- Demostración de que fst recupera el primer elemento.
    @[simp]
    theorem fst_of_ordered_pair (x y : U) :
      fst (⟨x, y⟩ : U) = x
        := by
      unfold fst
      -- El objetivo es: (⋂ (⋂ ⟨x, y⟩)) = x
      -- Paso 1: Demostrar que ⋂ ⟨x, y⟩ = {x}
      have h_inter_w : (⋂ ⟨x, y⟩) = {x} := by
        rw [OrderedPair, Intersection_of_pair, BinIntersection_with_subseteq_full]
        -- Para usar BinIntersection_with_subseteq_full, debemos probar que {x} ⊆ {x, y}
        intro z hz_in_singleton
        have hz_eq_x := (Singleton_is_specified x z).mp hz_in_singleton
        exact (PairSet_is_specified x y z).mpr (Or.inl hz_eq_x)
      -- Paso 2: Sustituir y usar el teorema de la intersección de un singleton
      rw [h_inter_w, Intersection_of_singleton]

    -- Demostración de que snd recupera el segundo elemento.
    -- Esta prueba es más compleja porque debe considerar si x = y o no.
    @[simp]
    theorem snd_of_ordered_pair (x y : U) : snd ⟨x, y⟩ = y
        := by sorry

    -- El teorema principal que une todo.
    @[simp]
    theorem OrderedPairSet_is_WellConstructed (w : U) :
      (isOrderedPair w) → w = (⟨ fst w, snd w ⟩ : U)
        := by
      intro h
      -- Usamos la hipótesis h para simplificar el par ordenado
      unfold isOrderedPair at h
      cases h with
      | inl h_diag =>
        -- Caso diagonal
        -- TODO: Demostrar w = ⟨ fst w, snd w ⟩ para el caso diagonal
        sorry
      | inr h_nondiag =>
        -- Caso no diagonal
        -- TODO: Demostrar w = ⟨ fst w, snd w ⟩ para el caso no diagonal
        sorry

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
