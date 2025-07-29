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

    /-! ### Axioma de Pares (No Ordenados) ### -/
    @[simp]
    axiom Pairing (x y : U) :
      ∃ (z : U), ∀ (w : U), w ∈ z ↔ (w = x ∨ w = y)

    /-! ### Teorema de Existencia Única para el Axioma de Pares ### -/
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
      constructor
      · intro h
        apply Classical.byContradiction
        intro h_not_exists
        apply h
        apply ExtSet
        intro y
        constructor
        · intro hy
          exfalso
          apply h_not_exists
          exact ⟨y, hy⟩
        · intro hy
          exfalso
          exact EmptySet_is_empty y hy
      · intro h h_empty
        obtain ⟨y, hy⟩ := h
        rw [h_empty] at hy
        exact EmptySet_is_empty y hy

    /-! ### ⋂{A} = A ### -/
    @[simp]
    theorem Intersection_of_singleton (A : U) : (⋂ { A }) = A := by
      apply ExtSet
      intro z
      constructor
      · intro hz_in_inter
        have h_nonempty : {A} ≠ (∅ : U) := by
          intro h_empty
          have hA : A ∈ ({A} : U) := (Singleton_is_specified A A).mpr rfl
          rw [h_empty] at hA
          exact EmptySet_is_empty A hA
        have h_exists : ∃ y, y ∈ ({A} : U) := (nonempty_iff_exists_mem _).mp h_nonempty
        unfold Intersection at hz_in_inter
        simp only [dif_pos h_exists] at hz_in_inter
        let y₀ := choose h_exists
        have hy₀ : y₀ ∈ ({A} : U) := choose_spec h_exists
        have hy₀_eq_A : y₀ = A := (Singleton_is_specified A y₀).mp hy₀
        rw [SpecSet_is_specified] at hz_in_inter
        let hA : A ∈ ({A} : U) := (Singleton_is_specified A A).mpr rfl
        exact (hz_in_inter.2 A) hA
      · intro hz_in_A
        have h_nonempty : {A} ≠ (∅ : U) := by
          intro h_empty
          have hA : A ∈ ({A} : U) := (Singleton_is_specified A A).mpr rfl
          rw [h_empty] at hA
          exact EmptySet_is_empty A hA
        have h_exists : ∃ y, y ∈ ({A} : U) := (nonempty_iff_exists_mem _).mp h_nonempty
        unfold Intersection
        simp only [dif_pos h_exists]
        rw [SpecSet_is_specified]
        constructor
        · have hy₀ : choose h_exists ∈ ({A} : U) := choose_spec h_exists
          have hy₀_eq_A : choose h_exists = A := (Singleton_is_specified A _).mp hy₀
          rw [hy₀_eq_A]
          exact hz_in_A
        · intro y hy
          have hy_eq_A : y = A := (Singleton_is_specified A y).mp hy
          rw [hy_eq_A]
          exact hz_in_A

    /-! ### Definición del Par Ordenado (x,y) = { { x } , { x , y } } ### -/
    @[simp]
    noncomputable def OrderedPair (x y : U) : U
        := (({ (({ x }): U) , (({ x , y }): U) }): U)

    /-! ### Notación estándar del Par Ordenado (x,y) = { { x } , { x , y } } ### -/
    notation " ⟨ " x " , " y " ⟩ " => OrderedPair x y

    @[simp]
    theorem OrderedPair_is_specified (x y : U) :
    ∀ (z : U), z ∈ OrderedPair x y ↔ (z = ({ x } : U) ∨ z = ({ x , y } : U))
      := by
    intro z
    unfold OrderedPair
    exact PairSet_is_specified {x} {x, y} z

    /-! ### Función que dice (`Prop`) si un conjunto `w` es un par ordenado ### -/
    @[simp]
    def isOrderedPair (w : U) : Prop :=
      ∃ (x y : U), w = (⟨ x , y ⟩  : U)

    @[simp]
    noncomputable def fst (w : U) : U := (⋂ (⋂ w))

    @[simp]
    noncomputable def snd (w : U) : U :=
      let I := ⋂ w
      let s := w \ {I}
      if h : s = ∅ then
        ⋂ I
      else
        have h_exists : ∃ y, y ∈ s := (nonempty_iff_exists_mem s).mp h
        let s_elem := choose h_exists
        let r := s_elem \ I
        ⋂ r

    -- Demostración de que fst recupera el primer elemento.
    @[simp]
    theorem fst_of_ordered_pair (x y : U) :
      fst (⟨x, y⟩ : U) = x
        := by
      unfold fst
      have h_inter_w : (⋂ ⟨x, y⟩) = {x} := by
        apply ExtSet
        intro z
        constructor
        · intro hz_in_inter
          have h_nonempty : ⟨x, y⟩ ≠ (∅ : U) := by
            intro h_empty; have hx : ({x} : U) ∈ (⟨x, y⟩ : U) := (OrderedPair_is_specified x y ({x} : U)).mpr (Or.inl rfl);
              rw [h_empty] at hx; exact EmptySet_is_empty {x} hx
          have h_exists : ∃ elem, elem ∈ (⟨x, y⟩ : U) := (nonempty_iff_exists_mem _).mp h_nonempty
          unfold Intersection at hz_in_inter
          simp only [dif_pos h_exists] at hz_in_inter
          rw [SpecSet_is_specified] at hz_in_inter
          exact hz_in_inter.2 {x} ((OrderedPair_is_specified x y {x}).mpr (Or.inl rfl))
        · intro hz_in_singleton
          have h_nonempty : ⟨x, y⟩ ≠ (∅ : U) := by
            intro h_empty; have hx : ({x} : U) ∈ (⟨x, y⟩ : U) := (OrderedPair_is_specified x y {x}).mpr (Or.inl rfl); rw [h_empty] at hx; exact EmptySet_is_empty {x} hx
          have h_exists : ∃ elem, elem ∈ (⟨x, y⟩ : U) := (nonempty_iff_exists_mem _).mp h_nonempty
          unfold Intersection
          simp only [dif_pos h_exists]
          rw [SpecSet_is_specified]
          constructor
          · have hz_eq_x : z = x := (Singleton_is_specified x z).mp hz_in_singleton
            have h_choose_spec := choose_spec h_exists
            have h_choose_cases := (OrderedPair_is_specified x y (choose h_exists)).mp h_choose_spec
            cases h_choose_cases with
            | inl h_choose_eq_singleton => rw [h_choose_eq_singleton]; exact hz_in_singleton
            | inr h_choose_eq_pair => rw [h_choose_eq_pair]; exact (PairSet_is_specified x y z).mpr (Or.inl hz_eq_x)
          · intro w hw_in_pair
            have hw_cases := (OrderedPair_is_specified x y w).mp hw_in_pair
            have hz_eq_x : z = x := (Singleton_is_specified x z).mp hz_in_singleton
            cases hw_cases with
            | inl hw_eq_singleton => rw [hw_eq_singleton]; exact hz_in_singleton
            | inr hw_eq_pair => rw [hw_eq_pair]; exact (PairSet_is_specified x y z).mpr (Or.inl hz_eq_x)
      rw [h_inter_w, Intersection_of_singleton]

    -- Demostración de que snd recupera el segundo elemento.
    @[simp]
    theorem snd_of_ordered_pair (x y : U) :
    snd (⟨x, y⟩ : U) = y
      := by sorry
    -- Aquí se debe demostrar que snd recupera el segundo elemento del par ordenado.
    -- Primero vemos qué significa ⟨x, y⟩ = { { x } , { x , y } }
    -- Luego, usamos la definición de snd y la intersección para demostrar que efectivamente
    -- snd (⟨x, y⟩) = y.
    -- Nota: La demostración de snd_of_ordered_pair es más compleja y requiere un análisis detallado
    -- de cómo se construye el par ordenado y cómo se define snd en términos de la intersección de conjuntos.
    -- (La demostración auxiliar h_inter_w fue movida/eliminada porque no puede estar sola en el archivo Lean.)


    -- El teorema principal que une todo.
    @[simp]
    theorem OrderedPairSet_is_WellConstructed (w : U) :
      (isOrderedPair w) → w = (⟨ fst w, snd w ⟩ : U) := by
      unfold isOrderedPair
      intro h_is_op
      obtain ⟨x, y, h_w_eq⟩ := h_is_op
      rw [h_w_eq, fst_of_ordered_pair, snd_of_ordered_pair]

    /-! ### Relaciones y Funciones: Inyectividad, Sobreyectividad, Equivalencia y Orden ### -/

    noncomputable def isRelation (w : U) : Prop :=
      ∀ (z : U), (z ∈ w) ↔ (isOrderedPair z)

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
    Pairing, PairingUniqueSet,
    PairSet, PairSet_is_specified,
    Singleton, Singleton_is_specified,
    member_intersection, Intersection,
    OrderedPair, OrderedPair_is_specified, isOrderedPair,
    fst, snd, fst_of_ordered_pair, snd_of_ordered_pair, OrderedPairSet_is_WellConstructed,
    isRelation, isRelation_in_Sets, domain, range,
    isReflexive, isReflexive_in_Set, isIReflexive,
    isSymmetric, isAsymmetric, isAntiSymmetric, isTransitive,
    isEquivalenceRelation, isEquivalenceRelation_in_Set,
    isPartialOrder, isStrictOrder, isWellDefined, isTotalOrder, isWellFounded,
    isFunction, isInyective, isSurjectiveFunction, isBijectiveFunction
)

/-!
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
