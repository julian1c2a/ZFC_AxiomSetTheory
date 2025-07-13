import Mathlib.Logic.ExistsUnique
import Init.Classical
import Mathlib.Tactic
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

  /-! ### Definición de ser miembro (∈) de la Intersección de una Familia de Conjuntos ### -/
  def member_intersection (w v : U) : Prop :=
    ∀ (y : U), ( y ∈ w ) → ( v ∈ y )

  /-! ### Definición del conjunto Intersección de una Familia de Conjuntos ### -/
  noncomputable def Intersection (w : U) : U :=
    if h : ∃ y, y ∈ w then
      let y₀ := choose h
      SpecSet y₀ (fun v => ∀ y, y ∈ w → v ∈ y)
    else
      ∅ -- convención, debería ser U

  /-! ### Notación estándar de la Intersección de una Familia de Conjuntos ### -/
  notation " ⋂ " w => Intersection w

  /-! ### Teorema de especificación del conjunto Intersección ### -/
  theorem Intersection_is_specified (w : U) :
    w ≠ ∅ → ∀ ( z : U ), z ∈ ( ⋂ w ) ↔ member_intersection w z
      := by
    intro h_nonempty z
    constructor
    · -- Dirección ->
      intro hz_in_intersection
      unfold Intersection at hz_in_intersection
      have h_exists : ∃ y, y ∈ w := by
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
      simp only [dif_pos h_exists] at hz_in_intersection
      have h := SpecSet_is_specified (choose h_exists) (fun v => ∀ y, y ∈ w → v ∈ y) z
      exact (h.mp hz_in_intersection).2
    · -- Dirección <-
      intro hz_member_intersection
      unfold Intersection
      have h_exists : ∃ y, y ∈ w := by
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
      simp only [dif_pos h_exists]
      have h := SpecSet_is_specified (choose h_exists) (fun v => ∀ y, y ∈ w → v ∈ y) z
      exact h.mpr ⟨hz_member_intersection (choose h_exists) (choose_spec h_exists), hz_member_intersection⟩

  /-! ### Teorema de existencia única del conjunto Intersección ### -/
  theorem Intersection_unique_set (w : U) : w ≠ ∅ → ∃! (z : U), ∀ (v : U), v ∈ z ↔ member_intersection w v
      := by
    intro h_nonempty
    apply ExistsUnique.intro (⋂ w)
    · -- Existencia del conjunto especificado por la Intersección
      exact Intersection_is_specified w h_nonempty
    · -- Unicidad del conjunto especificado por la Intersección
      intro z hz_intersection
      apply ExtSet
      intro v
      constructor
      · -- Dirección ->
        intro hv_in_z
        exact (Intersection_is_specified w h_nonempty v).mpr ((hz_intersection v).mp hv_in_z)
      · -- Dirección <-
        intro hv_in_intersection
        exact (hz_intersection v).mpr ((Intersection_is_specified w h_nonempty v).mp hv_in_intersection)

  /-! ### Teorema que ∀ (x : U), x ∈ W → ⋂ W ⊆ x ### -/
  theorem Intersection_subset (W : U) (x : U) : x ∈ W → (⋂ W) ⊆ x
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
  theorem Intersection_subset_of_superset (W V : U) : ( W ≠ ∅ ∧ V ≠ ∅ ) → ( W ⊆ V → (⋂ V) ⊆ (⋂ W) )
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
  theorem Intersection_of_pair (A B : U) : (⋂ { A , B }) = (A ∩ B)
      := by
    apply ExtSet
    intro z
    constructor
    · -- Dirección ->
      intro hz_in_intersection
      have h_nonempty : ({ A , B }) ≠ EmptySet := PairSet_is_nonempty A B
      have hz_member_intersection := (Intersection_is_specified { A , B } h_nonempty z).mp hz_in_intersection
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
  theorem Intersection_of_singleton (A : U) : (⋂ { A }) = A
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
  noncomputable def OrderedPair (x y : U) : U := { { x } , { x , y } }

  /-! ### Notación estándar del Par Ordenado (x,y) = { { x } , { x , y } } ### -/
  notation " ⟨ " x ", " y " ⟩ " => OrderedPair x y

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

  lemma nonempty_iff_exists_mem (w : U) : w ≠ ∅ ↔ ∃ y, y ∈ w := by
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
  def isSingleton (w : U) : Prop :=
    if h : ∀ (x : U), x ∉ w then
      False -- El conjunto vacío no es un singleton
            -- El vacío no tiene elementos (0)
    else
      have h_exists : ∃ t, t ∈ w := by push_neg at h; exact h
      let v : U := choose h_exists
      let y : U := w \ ({ v } : U)
      if ∃ (t : U), t ∈ y then
        False  -- Caso que más de un solo elemento
      else
        True   -- Caso que tiene un solo elemento (par diagonal o singleton)

  /-! ### Función que dice (`Prop`) si un conjunto `w` tiene dos elementos ### -/
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
  def isOrderedPair (w : U) : Prop :=
    isDiagonalOrderedPair w ∨ isNonDiagonalOrderedPair w

  /-! ### Teorema de que un par ordenado es un conjunto no vacío ### -/
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
      tauto
    rw [h_intersection] at h_empty
    have h_singleton_nonempty := PairSet_singleton_is_nonempty x
    exact h_singleton_nonempty h_empty


  noncomputable def fst (w : U) : U :=
    if isOrderedPair w then
      if h : ∃ (z : U), z ∈ (⋂ w) then
        choose h
      else
        (∅ : U)
    else
      (∅ : U)

  noncomputable def snd (w : U) : U :=
    if isDiagonalOrderedPair w then
      ⋂ w
    else if isNonDiagonalOrderedPair w then
      if h : ∃ (z : U), z ∈ (w \ (⋂ w)) then
        let v : U := {choose h}
        let s : U := w\v
        have h_s_nonempty : s ≠ ∅ := by
          intro h_empty
          have h := choose_spec h
          have h_s_in_w : choose h ∈ w := h.left
          have h_s_empty : choose h ∈ s := h_empty ▸ h_s_in_w
          exact EmptySet_is_empty (choose h) h_s_empty
          exact h_s_nonempty h_empty
        let y : U := choose (by
          use choose h
          exact h_s_nonempty)
        sorry
      else
        (∅ : U)
    else
      (∅ : U)


  /-! ### Teorema de que fst y snd son miembros del par ordenado w = ⟨ x, y ⟩ ### -/
  theorem fst_in_ordered_pair (w : U) (x : U) {y : U} (hw : w = ⟨x, y⟩) : {fst w} ∈ w := by sorry
    -- unfold fst
    -- have h_nonempty : w ≠ ∅ := by
    --   rw [hw]
    --   exact PairSet_is_nonempty {x} {x, y}
    -- by_cases h_exists : ∃ (z : U), z ∈ (⋂ w)
    -- · -- Caso en que existe un elemento en la intersección de w
    --   simp only [dif_pos h_exists]
    --   have h := choose_spec h_exists
    --   -- h : choose h_exists ∈ ⋂ w
    --   have h_intersection : ⋂ w = { x } := by
    --     rw [hw]
    --     unfold OrderedPair
    --     rw [Intersection_of_pair]
    --     apply ExtSet
    --     intro z
    --     constructor
    --     · intro hz_in_inter
    --       have h_spec := BinIntersection_is_specified {x} {x, y} z
    --       have hz_in_both := h_spec.mp hz_in_inter
    --       exact hz_in_both.1
    --     · intro hz_in_singleton
    --       have h_spec := BinIntersection_is_specified {x} {x, y} z
    --       have hz_in_x := Singleton_is_specified x z
    --       have hz_eq_x := hz_in_x.mp hz_in_singleton
    --       have hz_in_pair := PairSet_is_specified x y z
    --       exact h_spec.mpr ⟨hz_in_singleton, hz_in_pair.mpr (Or.inl hz_eq_x)⟩
    --   rw [h_intersection] at h
    --   have h_x_in_singleton : x ∈ {x} := Singleton_is_specified x x |>.mpr rfl
    --   have h_choose_eq_x : choose h_exists = x := Singleton_is_specified x (choose h_exists) |>.mp h
    --   rw [h_choose_eq_x, hw]
    --   exact PairSet_is_specified {x} {x, y} {x} |>.mpr (Or.inl rfl)
    -- · -- Caso en que no existe un elemento en la intersección de w
    --   simp only [dif_neg h_exists]
    --   rw [hw]
    --   unfold OrderedPair
    --   have h_intersection : (⋂ ({ ({ x }) , ({ x , y }) }))  = ({ x }) := by
    --     rw [Intersection_of_pair]
    --     apply ExtSet
    --     intro z
    --     constructor
    --     · intro hz_in_inter
    --       have h_spec := BinIntersection_is_specified {x} {x, y} z
    --       have hz_in_both := h_spec.mp hz_in_inter
    --       exact hz_in_both.1
    --     · intro hz_in_singleton
    --       have h_spec := BinIntersection_is_specified {x} {x, y} z
    --       have hz_in_x := Singleton_is_specified x z
    --       have hz_eq_x := hz_in_x.mp hz_in_singleton
    --       have hz_in_pair := PairSet_is_specified x y z
    --       exact h_spec.mpr ⟨hz_in_singleton, hz_in_pair.mpr (Or.inl hz_eq_x)⟩
    --   have h_x_exists : ∃ (z : U), z ∈ (⋂ { { x } , { x , y } }) := by
    --     use x
    --     rw [h_intersection]
    --     exact Singleton_is_specified x x |>.mpr rfl
    --   exact absurd h_x_exists h_exists

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
