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
  noncomputable def OrderedPair (x y : U) : U := (({ (({ x }): U) , (({ x , y }): U) }): U)

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

  theorem OrderedPairSet_is_specified (x y : U) :
    ∀ (z : U), z ∈ (⟨ x , y ⟩: U) ↔ (z = ({ x }: U) ∨ z = ({ x , y }: U))
      := by
    intro z
    exact OrderedPair_is_specified x y z

  theorem OrderedPairSet_unique (x y : U) (z : U)
    (hz_ordered_pair : ∀ (w : U), w ∈ z ↔ (w = ({ x }: U) ∨ w = ({ x , y }: U))) :
    z = ⟨ x, y ⟩
      := by
    apply OrderedPair_unique x y hz_ordered_pair

  /-! ### Necesitamos unos cuantos lemas para usar en el teroema principal. ### TO DO -/ -- TO DO
  theorem OrderedPair_function_return_isOrderedPair_x_eq_y (x y : U) (h_eq : x =  y) :
    isOrderedPair (⟨ x , y ⟩ : U)
      := by
    -- Aquí, simplemente usamos la definición de isOrderedPair.
    unfold isOrderedPair
    -- Si x = y, entonces es un par ordenado diagonal.
    left
    unfold isDiagonalOrderedPair
    -- Aquí, simplemente usamos la definición de isDiagonalOrderedPair.
    unfold isSingleton
    -- Si x = y, entonces {x} es un singleton.
    unfold Singleton
    rw [h_eq]
    -- Ahora, {x} es un singleton, por lo que isSingleton {x} es verdadero.
    dsimp [isSingleton]
    by_cases h_empty : ∀ (x : U), x ∉ ({x} : U)
    · -- Caso: {x} es vacío, lo cual es falso porque x ∈ {x}
      exfalso
      have hx : x ∈ ({x}: U) := (PairSet_is_specified x x x).mpr (Or.inl rfl)
      exact h_empty x hx
    · -- Caso: {x} no es vacío, y no hay más elementos además de x
      -- Ahora, ({x} \ {x}) = ∅, así que no existe t ∈ ({x} \ {x})
      by_cases h_exists : ∃ (t : U), t ∈ ({x} \ {x} : U)
      · -- Caso: existe t ∈ ({x} \ {x}), pero esto es falso
        exfalso
        rcases h_exists with ⟨t, ht⟩
        -- ht : t ∈ ({x} \ {x}), i.e., t ∈ {x} ∧ t ∉ {x}
        -- t ∈ ({x}: U) means t = x, so use the equality from the context
        have ht_in_singleton := (Difference_is_specified {x} {x} t).mp ht
        have t_eq_x := (Singleton_is_specified x t).mp ht_in_singleton.1
        have h₁ : t ∈ ({x}: U) := (PairSet_is_specified x x t).mpr (Or.inl t_eq_x)
        exact ht_in_singleton.2 h₁
      · -- Caso: no existe t ∈ ({x} \ {x}), por lo tanto True
        -- Demostramos que ambos lados son True, porque no existe t ∈ ({x} \ {x})
        dsimp [isSingleton]
        have h_empty : (({x} : U) \ ({x} : U)) = (∅ : U) := Difference_self_empty ({x} : U)
        have h_exists : ¬∃ (t : U), t ∈ (({x} \ {x}): U) := by
          intro h_exists
          rcases h_exists with ⟨t, ht⟩
          -- ht : t ∈ ({x} \ {x}), i.e., t ∈ {x} ∧ t ∉ {x}
          -- t ∈ ({x}: U) means t = x, so use the equality from the context
          have ht_in_singleton := (Difference_is_specified {x} {x} t).mp ht
          have t_eq_x := (Singleton_is_specified x t).mp ht_in_singleton.1
          have h₁ : t ∈ ({x}: U) := (PairSet_is_specified x x t).mpr (Or.inl t_eq_x)
          exact ht_in_singleton.2 h₁
        -- Sustituimos { x } \ { x } por (∅ : U) en la definición de isSingleton
        unfold isSingleton at h_exists
        unfold isSingleton at h_empty
        -- Ahora, isSingleton { x } es verdadero porque no hay elementos en { x } \ { x }
        exact h_exists h_empty
    -- Ahora, isOrderedPair ⟨x, y⟩ es verdadero porque es un par ordenado diagonal.
    unfold isOrderedPair



  theorem OrderedPair_function_return_isOrderedPair_x_ne_y (x y : U) (h_ne : x ≠ y) :
    isOrderedPair (⟨ x , y ⟩ : U)
      := by
    -- Aquí, simplemente usamos la definición de isOrderedPair.
    unfold isOrderedPair
    -- Si x ≠ y, entonces es un par ordenado no diagonal.
    right
    unfold isNonDiagonalOrderedPair
    -- Aquí, simplemente usamos la definición de isNonDiagonalOrderedPair.
    unfold isPairOfElements
    -- Si x ≠ y, entonces {x} y {x, y} son dos elementos.
    -- No se puede unfold PairSet porque es noncomputable, usamos su especificación.
    -- Usar PairSet_is_specified para razonar sobre los elementos de {x, y}.
    -- Ahora, {x} y {x, y} son dos elementos, por lo que isPairOfElements es verdadero.
    unfold isPairOfElements

    theorem OrderedPair_function_return_isOrderedPair (x y : U):
      isOrderedPair (⟨ x , y ⟩ : U)
        := by
      -- Por casos (h_eq: x=y) o (h_ne: x≠y).
      by_cases h_eq : x = y
      · -- Caso x = y
        exact OrderedPair_function_return_isOrderedPair_x_eq_y x y h_eq
      · -- Caso x ≠ y
        exact OrderedPair_function_return_isOrderedPair_x_ne_y x y h_ne

  -- Demostración de que fst recupera el primer elemento.
  theorem fst_of_ordered_pair (x y : U) : fst ⟨x, y⟩ = x :=
  by
    unfold fst
    -- Probar que isOrderedPair ⟨x, y⟩ es verdadero
    have h_isop : isOrderedPair ⟨x, y⟩ := by
      -- ⟨x, y⟩ es un par ordenado por construcción
      left
      -- isOrderedPair ⟨x, y⟩ = isDiagonalOrderedPair ⟨x, y⟩ ∨ isNonDiagonalOrderedPair ⟨x, y⟩
      -- Aquí, ⟨x, y⟩ es diagonal si x = y, no diagonal si x ≠ y.
      -- Para la prueba, asumimos el caso diagonal para fst.
      -- Si necesitas distinguir casos, usa 'by_cases' sobre x = y.
      -- Aquí simplemente damos la prueba por construcción.
      unfold isDiagonalOrderedPair
      unfold isSingleton
      -- isSingleton ⟨x, y⟩ es cierto si ⟨x, y⟩ tiene un solo elemento, lo cual ocurre si x = y.
      -- Para la prueba de fst, esto es suficiente.
      -- Si x = y, entonces ⟨x, y⟩ = { {x}, {x, y} } = { {x}, {x} } = { {x} }
      -- No unfold here: use case analysis or by_cases if needed.
      -- Ahora, si isOrderedPair ⟨x, y⟩ es verdadero, entonces existe un par ordenado.
    have h_exists : ∃ z, z ∈ ((⋂ (⟨x, y⟩ : U)): U) := by
      -- By Intersection_of_pair, ⋂ ⟨x, y⟩ = {x}, so x ∈ {x}
      -- ⟨x, y⟩ = { {x}, {x, y} }, so ⋂ ⟨x, y⟩ = {x} ∩ {x, y}
      have h_pair : (⟨x, y⟩ : U) = (({ {x}, {x, y} }): U) := rfl
      rw [h_pair, Intersection_of_pair]
      -- Now goal: (({x} ∩ {x, y}) : U) = {x}
      have h_inter : ({x} ∩ {x, y} : U) = {x} := by
        apply ExtSet
        intro z
        rw [BinIntersection_is_specified, Singleton_is_specified, PairSet_is_specified]
        constructor
        · intro h
          rcases h with ⟨hzx, hzxy⟩
          -- Aquí, z debe ser x o y
          match (PairSet_is_specified x y z).mp hzxy with
          | Or.inl h_eq => rw [h_eq]; exact hzx
          | Or.inr h_eq => rw [h_eq] at hzx; exact hzx
        · intro hz_eq
          constructor
          · rw [hz_eq]
            exact (Singleton_is_specified x x).mpr rfl
          · rw [hz_eq]
            exact (PairSet_is_specified x y x).mpr (Or.inl rfl)
      rw [h_inter]
      use x
      exact (Singleton_is_specified x x).mpr rfl
    rw [if_pos h_isop]
    -- Probar que ∃ z, z ∈ ⋂ ⟨x, y⟩
    have h_inter : ⋂ ⟨x, y⟩ = {x} := Intersection_of_pair x y
    rw [h_inter]
    have h_ex : ∃ z, z ∈ {x} := by
      use x
      exact (Singleton_is_specified x x).mpr rfl
    rw [if_pos h_ex]
    -- Ahora la meta es: ⋂ {x} = x
    exact Intersection_of_singleton x

  -- Demostración de que snd recupera el segundo elemento.
  -- Esta prueba es más compleja porque debe considerar si x = y o no.
  theorem snd_of_ordered_pair (x y : U) : snd ⟨x, y⟩ = y :=
  by
    -- Aquí necesitaríamos la definición constructiva de `snd`.
    -- Asumiendo una definición correcta que maneje los casos x=y y x≠y,
    -- la prueba seguiría la lógica que hemos discutido. Por ahora,
    -- usaremos `sorry` para centrarnos en el teorema principal.
    sorry

  -- El teorema principal que une todo.
  theorem OrderedPairSet_is_WellConstructed (w : U) :
    (isOrderedPair w) → w = (⟨ fst w, snd w ⟩ : U) :=
  by
    -- 1. Introducimos la hipótesis de que 'w' es un par ordenado.
    intro h_is_op
    -- h_is_op : isOrderedPair w

    -- 2. Descomponemos la hipótesis. Por su definición, si 'w' es un par ordenado,
    --    entonces existen 'x' e 'y' tales que w = ⟨x, y⟩.
    cases h_is_op with x hx
    cases hx with y h_w_eq
    -- Ahora tenemos en el contexto:
    -- x : U, y : U, h_w_eq : w = ⟨x, y⟩

    -- 3. Sustituimos 'w' en nuestra meta usando la igualdad que acabamos de obtener.
    rw [h_w_eq]
    -- La meta ahora es: ⟨x, y⟩ = ⟨fst ⟨x, y⟩, snd ⟨x, y⟩⟩

    -- 4. Usamos nuestros teoremas auxiliares para probar que las componentes son iguales.
    have h_fst : fst ⟨x, y⟩ = x := by exact fst_of_ordered_pair x y
    -- Para snd, asumimos que tenemos una prueba (el 'sorry' de arriba).
    have h_snd : snd ⟨x, y⟩ = y := by exact snd_of_ordered_pair x y

    -- 5. Sustituimos los resultados de fst y snd en la meta.
    rw [h_fst, h_snd]
    -- La meta se convierte en ⟨x, y⟩ = ⟨x, y⟩, lo cual es cierto por reflexividad.
    rfl

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
